{-# LANGUAGE DeriveDataTypeable    #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Validator.Types
       where

import Control.Applicative
import Data.Bifunctor
import Control.Monad.Trans.State.Strict (StateT(..))

import Data.Typeable (Typeable)
import Data.Monoid
import Data.Maybe

-- | Either like data type, but with applicative instance accumulating
--   error values.
data Validator err a = Invalid err
                     | Valid a
                     deriving (Show, Ord, Eq, Typeable)

instance Functor (Validator err) where
  fmap f (Valid v) = Valid (f v)
  fmap f (Invalid err) = Invalid err

instance Monoid err => Applicative (Validator err) where
  pure = Valid
  Valid f <*> Valid v = Valid (f v)
  Invalid a <*> Invalid b = Invalid (a `mappend` b)
  Invalid a <*> _ = Invalid a
  _ <*> Invalid b = Invalid b

instance Bifunctor Validator where
  second = fmap
  first f v = case v of
               Valid v -> Valid v
               Invalid e -> Invalid (f e)
  bimap f g v = case v of
      Valid v -> Valid (g v)
      Invalid e -> Invalid (f e)

type Input key a = key -> a

-- | Validator for key-value input
newtype InputValidator key input m err a = InputValidator
  { unValidator :: Input key input -> key -> m (Validator [(key, err)] a) }
  deriving (Typeable)

instance Functor m => Functor (InputValidator key input m err) where
  fmap f (InputValidator val) = InputValidator $ \i k -> fmap (fmap f) (val i k)

instance (Applicative m) => Applicative (InputValidator key input m err) where
  pure v = InputValidator $ \_ _ -> pure (Valid v)
  InputValidator mf <*> InputValidator mv = InputValidator $ \i k ->
      (<*>) <$> mf i k <*> mv i k

instance Functor m => Bifunctor (InputValidator key input m) where
  second = fmap
  bimap f g (InputValidator mf) = InputValidator $ \i k ->
     bimap mapErrs g <$> mf i k
    where
      mapErrs = map (second f)
  first f (InputValidator mf) = InputValidator $ \ i k ->
      first mapErrs <$> mf i k
    where
      mapErrs = map (second f)

mapErrors :: (Functor m)
          => InputValidator key input m err a
          -> (err -> err')
          -> InputValidator key input m err' a
mapErrors m f = first f m


validateKey :: key
     -> (a -> Either err b)
     -> Validator [(key, err)] a
     -> Validator [(key, err)] b
validateKey key f (Invalid e) = Invalid e
validateKey key f (Valid v) = case f v of
   Left err -> Invalid [(key, err)]
   Right r -> Valid r

-- | Monadically prove validity of result
proveM :: Monad m => InputValidator key input m err a
                  -> (a -> m (Either err b))
                  -> InputValidator key input m err b
proveM (InputValidator mv) f = InputValidator $ \i key -> do
    v <- mv i key
    case v of
      Invalid e -> return $ Invalid e
      Valid val -> do
         r <- f val
         return $ case r of
           Left err -> Invalid [(key, err)]
           Right r -> Valid r

-- | Purely prove input
prove :: Functor m => InputValidator key input m err a
     -> (a -> Either err b)
     -> InputValidator key input m err b
prove (InputValidator mv) f = InputValidator $ \i key ->
    validateKey key f <$> mv i key

item :: Applicative m => key -> InputValidator key a m err a
item key = InputValidator $ \inp _ -> pure $ pure (inp key)

-- | Map over value. You can just use `flip fmap`
transform :: Functor m
          => InputValidator key input m err a
          -> (a -> b)
          -> InputValidator key input m err b
transform m f = fmap f m

transformM :: (Functor m, Monad m)
           => InputValidator key input m err a
           -> (a -> m b)
           -> InputValidator key input m err b
transformM m f = proveM m (fmap Right <$> f)

