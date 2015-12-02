{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE OverloadedStrings  #-}
module Validator.Aeson
       where

import           Control.Applicative
import           Control.Monad.State.Strict (StateT (..), evalStateT, get, gets)
import           Control.Monad.Trans        (lift)
import           Control.Monad.Trans.Except (ExceptT (..), runExceptT, throwE)
import           Data.Foldable              (toList)
import           Data.Functor.Identity
import           Data.Monoid
import           Data.Text                  (Text)
import qualified Data.Text.Lazy             as LT
import qualified Data.Text.Lazy.Builder     as LB
import qualified Data.Text.Lazy.Builder.Int as LB
import           Data.Traversable           (forM)
import           Data.Typeable


import           Data.Aeson                 (FromJSON (..), ToJSON (..), Value (..))
import           Data.Aeson.Types           (parseEither)
import qualified Data.HashMap.Strict        as HM

import           Validator.Types


data PathElem = PathKey Text
              | PathIndex Int
              deriving (Eq, Ord, Show, Typeable)

type JsonPath = [PathElem]

instance ToJSON PathElem where
  toJSON (PathKey t) = toJSON t
  toJSON (PathIndex i) = toJSON i

renderJsonPath :: JsonPath -> Text
renderJsonPath (x:xs) = LT.toStrict . LB.toLazyText $ mconcat (toFirst x:map fromPath xs)
  where
    toFirst (PathKey t) = LB.fromText t
    toFirst (PathIndex i) = fromIdx i
    fromPath (PathKey t) = LB.singleton '.' <> LB.fromText t
    fromPath (PathIndex i) = fromIdx i
    fromIdx i = LB.singleton '[' <> LB.decimal i <> LB.singleton ']'
renderJsonPath _ = ""

data JsonError err = JsonError err
                   | JsonParsingError String
                   | JsonMissing
                   deriving (Eq, Ord, Show, Typeable)

instance Functor JsonError where
  fmap f (JsonError err) = JsonError (f err)
  fmap _ (JsonParsingError e) = JsonParsingError e
  fmap _ JsonMissing = JsonMissing


data JsonState = JsonState
     { jsonPath  :: !JsonPath
     , jsonInput :: !(HM.HashMap Text Value)
     } deriving (Eq, Show, Typeable)

type JsonValidator err m a = ValidatorT [(JsonPath, JsonError err)]
                                        (StateT JsonState m) a


type JsonProof err m a = ExceptT [(JsonPath,JsonError err)]
                                 (StateT JsonState m) a

reqField :: (Monad m, FromJSON a) => Text -> JsonProof err m a
reqField key = do
   JsonState path hm <- get
   case HM.lookup key hm of
      Nothing -> throwE [(path++[PathKey key], JsonMissing)]
      Just v -> case parseEither parseJSON v of
        Left e -> throwE [(path++[PathKey key], JsonParsingError e)]
        Right r -> pure r

{-# INLINE reqField #-}

optField :: (Monad m, FromJSON a) => Text -> JsonProof err m (Maybe a)
optField key = do
   JsonState path hm <- get
   case HM.lookup key hm of
      Nothing -> pure Nothing
      Just v -> case parseEither parseJSON v of
        Left e -> throwE [(path++[PathKey key], JsonParsingError e)]
        Right r -> pure r

{-# INLINE optField #-}

defField :: (Monad m, FromJSON a) => a -> Text -> JsonProof err m a
defField def key = do
   JsonState path hm <- get
   case HM.lookup key hm of
      Nothing -> pure def
      Just v -> case parseEither parseJSON v of
        Left e -> throwE [(path++[PathKey key], JsonParsingError e)]
        Right r -> pure r

{-# INLINE defField #-}

check :: Monad m => (a -> Bool) -> err -> a -> JsonProof err m a
check f msg v = do
 path <- gets jsonPath
 case f v of
   False -> throwE [(path, JsonError msg)]
   True -> return v

checkM :: Monad m => (a -> m Bool) -> err -> a -> JsonProof err m a
checkM f msg v = do
 path <- gets jsonPath
 c <- lift . lift $ f v
 case c of
   False -> throwE [(path, JsonError msg)]
   True -> return v

prove :: Monad m => (t -> Either err b) -> t -> JsonProof err m b
prove chk v = do
  path <- gets jsonPath
  case chk v of
    Left e -> throwE [(path, JsonError e)]
    Right r -> pure r

proveM :: Monad m => (t -> m (Either err b)) -> t -> JsonProof err m b
proveM chk v = do
  path <- gets jsonPath
  c <- lift . lift $ chk v
  case c of
    Left e -> throwE [(path, JsonError e)]
    Right r -> pure r

proveJson :: Monad m
          => JsonPath
          -> HM.HashMap Text Value
          -> JsonProof e m a
          -> m (Either [(JsonPath, JsonError e)] a)
proveJson p hm act = evalStateT (runExceptT act) (JsonState p hm)
{-# INLINE proveJson #-}

fieldObject :: Monad m => Text -> JsonProof err m a -> JsonProof err m a
fieldObject key proof = do
  v <- reqField key
  JsonState p _ <- get
  case v of
    Object hm -> ExceptT $ do
      lift $ evalStateT (runExceptT proof) $ JsonState (p <> [PathKey key]) hm
    _ -> throwE [(p ++ [PathKey key], JsonParsingError "Expected object")]

fieldArray :: Monad m => Text -> JsonProof err m a -> JsonProof err m [a]
fieldArray key proof = do
  v <- reqField key
  JsonState p _ <- get
  case v of
    Array arr -> let elems = zip [(0::Int)..] (toList arr)
      in forM elems $ \(i, val) ->
          ExceptT . lift $ validateJson (p <> [PathKey key, PathIndex i]) proof val
    _ -> ExceptT $ pure $ Left [(p <> [PathKey key], JsonParsingError "Expected array")]

validateJson :: Monad m
              => JsonPath
              -> JsonProof e m a
              -> Value
              -> m (Either [(JsonPath, JsonError e)] a)
validateJson p proof val = case val of
  Object hm -> proveJson p hm proof
  _ -> pure $ Left [([], JsonParsingError "Expected array")]

{-# INLINE validateJson #-}
