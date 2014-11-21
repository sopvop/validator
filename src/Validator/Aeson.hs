{-# LANGUAGE DeriveDataTypeable         #-}
{-# LANGUAGE DeriveFunctor              #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE OverloadedStrings          #-}

module Validator.Aeson
       where

import Control.Applicative
import Data.Traversable (sequenceA, traverse)

import Control.Monad (join, liftM, (>=>))
import Data.Bifunctor
import Data.Typeable
import Data.Maybe (fromMaybe)
import Data.Text (Text)
import Data.Monoid
import Data.Vector ((!?), toList)
import qualified Data.Text as Text
import qualified Data.Text.Lazy as LT
import qualified Data.Text.Lazy.Builder as LB
import qualified Data.Text.Lazy.Builder.Int as LB


import Data.Aeson (Value (..), FromJSON(..), (.=), object, ToJSON(..))
import Data.Aeson.Types (parseEither)
import qualified Data.HashMap.Strict as HM

import Validator.Types (Validator(..), InputValidator(..))
import qualified Validator.Types as V


data PathElem = PathKey Text
              | PathIndex Int
              deriving (Eq, Ord, Show, Typeable)

data LookupResult a = LookupResult a
                    | NotFound
                    | NotArray
                    | NotObject
                    deriving (Show, Eq, Ord, Typeable, Functor)

instance ToJSON PathElem where
  toJSON (PathKey t) = toJSON t
  toJSON (PathIndex i) = toJSON i

toJsonPath (x:xs) = LT.toStrict . LB.toLazyText $ mconcat (toFirst x:map fromPath xs)
  where
    toFirst (PathKey t) = LB.fromText t
    toFirst (PathIndex i) = fromIdx i
    fromPath (PathKey t) = LB.singleton '.' <> LB.fromText t
    fromPath (PathIndex i) = fromIdx i
    fromIdx i = LB.singleton '[' <> LB.decimal i <> LB.singleton ']'
toJsonPath _ = ""

data JsonError err = JsonError err
                   | JsonParsingError String
                   | JsonIsNotObject
                   | JsonIsNotArray
                   | JsonMissing
                   deriving (Eq,Ord,Show,Typeable, Functor)

newtype JsonValidator m err a = JsonValidator (InputValidator [PathElem]
                                                (LookupResult Value) m (JsonError err) a)
        deriving (Functor, Applicative)


instance Functor m => Bifunctor (JsonValidator m) where
  first f (JsonValidator v) = JsonValidator $ first (fmap f) v
  second f (JsonValidator v) = JsonValidator $ second f v
  bimap f g (JsonValidator v) = JsonValidator $ bimap (fmap f) g v

proveFromJSON :: FromJSON a => Value -> Either (JsonError err) a
proveFromJSON v = first JsonParsingError $ parseEither parseJSON v

proveLookup (LookupResult a) = Right a
proveLookup NotFound = Left JsonMissing
proveLookup NotArray = Left JsonIsNotArray
proveLookup NotObject = Left JsonIsNotObject

justNotFound NotFound = Right Nothing
justNotFound (LookupResult r) = Right (Just r)
justNotFound NotArray = Left JsonIsNotArray
justNotFound NotObject = Left JsonIsNotObject

path :: (FromJSON a, Applicative m) => [PathElem] -> JsonValidator m err a
path p = JsonValidator $ V.item p `V.prove` (proveLookup >=> proveFromJSON)

field :: (FromJSON a, Applicative m) => Text -> JsonValidator m err a
field key = path [PathKey key]

fieldOpt :: (FromJSON b, Applicative m) => Text -> JsonValidator m err (Maybe b)
fieldOpt key = JsonValidator $ V.item [PathKey key]
              `V.prove` (justNotFound >=> traverse proveFromJSON)

fieldDefault :: (FromJSON a, Applicative m)
             => Text -> a -> JsonValidator m err a
fieldDefault key def = JsonValidator $ V.item [PathKey key]
                    `V.prove` (justNotFound >=> traverse proveFromJSON)
                    `V.transform` fromMaybe def

jsonLookup v [] = LookupResult v
jsonLookup (Object hm) (PathKey t:ps) =
  case HM.lookup t hm of
      Nothing -> NotFound
      Just v -> jsonLookup v ps
jsonLookup _ (PathKey _:_) = NotObject
jsonLookup (Array arr) (PathIndex i:ps) =
  case arr !? i of
    Nothing -> NotFound
    Just v -> jsonLookup v ps
jsonLookup _ (PathIndex _:_) = NotArray


validateJson :: [PathElem] -- root path
             -> Value -- input value
             -> JsonValidator m t a -- Validator
             -> m (Validator [([PathElem], JsonError t)] a)
validateJson root inp (JsonValidator validator) = unValidator validator (jsonLookup inp) root

validateJsonEither :: Monad m =>
                   [PathElem]
                   -> Value
                   -> JsonValidator m t b
                   -> m (Either [([PathElem], JsonError t)] b)
validateJsonEither root inp val = do
  r <- validateJson root inp val
  return $ case r of
    Invalid e -> Left e
    Valid v -> Right v

fieldObject :: Monad m => Text -> JsonValidator m err a -> JsonValidator m err a
fieldObject key validator = JsonValidator . InputValidator $ \i k -> do
    case proveLookup $ i [path] of
      Left e -> return $ Invalid [(path:k, e)]
      Right v -> validateJson (path:k) v validator
  where
    path = PathKey key

fieldArray key validator = JsonValidator . InputValidator $ \i k -> do
    case proveLookup $ i [path] of
      Left e -> return $ Invalid [(k ++ [path], e)]
      Right (Array v) -> liftM sequenceA . traverse (go k) $ zip [(0 :: Int)..] (toList v)
  where
    go root (i, val) = validateJson (root ++ [path, PathIndex i]) val validator
    path = PathKey key

prove :: Functor m => JsonValidator m err a
      -> (a -> Either err b) -> JsonValidator m err b
prove (JsonValidator m) f = JsonValidator $ V.prove m (first JsonError . f)

proveM :: (Functor m, Monad m) =>
       JsonValidator m err a
       -> (a -> m (Either err b))
       -> JsonValidator m err b
proveM (JsonValidator m) f = JsonValidator $ V.proveM m (fmap (first JsonError) . f)

transformM :: (Functor m, Monad m) =>
           JsonValidator m err a -> (a -> m b) -> JsonValidator m err b
transformM (JsonValidator m) f = JsonValidator $ V.transformM m f

{-
testq :: JsonValidator IO String (Int, [Int])
testq = (,) <$> ( fieldObject "sub" $ field "hui" `prove` checkOne)
            <*> ( fieldArray "arr" $ (field "elems" `prove` checkOne))

checkOne i = if i == 1 then Right i else Left "nope"

test = object [ "hui" .= (1::Int)
              , "sub" .= object [ "hui" .= (1::Int), "bar" .= ("baz" ::Text)]
              , "arr" .= [object [ "elems" .= (2::Int)] ]
              ]

runT inp test = liftM (first (fmap (first toJsonPath))) $ validateJson [PathKey "root"] inp test
-}
