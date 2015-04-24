{-# LANGUAGE DeriveDataTypeable    #-}
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Validator.Types
       where

import Control.Applicative
import Control.Monad (liftM)
import Data.Bifunctor
import Control.Monad.Trans
import Control.Monad.Trans.State.Strict (StateT(..), evalStateT)

import Data.Typeable (Typeable)
import Data.Monoid
import Data.Maybe

-- | Either like data type, but with applicative instance accumulating
--   error values.
data Result err a = Failure err
                  | Success a
                  deriving (Show, Ord, Eq, Typeable)

instance Functor (Result err) where
  fmap f (Success v) = Success (f v)
  fmap f (Failure err) = Failure err

instance Monoid err => Applicative (Result err) where
  pure = Success
  Success f <*> Success v = Success (f v)
  Failure a <*> Failure b = Failure (a `mappend` b)
  Failure a <*> _ = Failure a
  _ <*> Failure b = Failure b

instance Bifunctor Result where
  second = fmap
  first f v = case v of
               Success v -> Success v
               Failure e -> Failure (f e)
  bimap f g v = case v of
      Success v -> Success (g v)
      Failure e -> Failure (f e)

validatorToEither :: Result a b -> Either a b
validatorToEither (Failure e) = Left e
validatorToEither (Success v) = Right v

eitherValid :: key -> Either err a -> Result [(key, err)] a
eitherValid key (Left e) = Failure [(key, e)]
eitherValid _ (Right r) = Success r

-- | Validator for key-value input
newtype InputValidator key s m err a = InputValidator
  { unValidator :: key -> StateT s m (Result [(key, err)] a) }
  deriving (Typeable)

instance Functor m => Functor (InputValidator key input m err) where
  fmap f (InputValidator val) = InputValidator $ \k -> fmap (fmap f) (val k)

instance (Monad m) => Applicative (InputValidator key input m err) where
  pure v = InputValidator $ \_ -> pure (Success v)
  InputValidator mf <*> InputValidator mv = InputValidator $ \k ->
      (<*>) <$> mf k <*> mv k

instance Functor m => Bifunctor (InputValidator key input m) where
  second = fmap
  bimap f g (InputValidator mf) = InputValidator $ \k ->
     bimap mapErrs g <$> mf k
    where
      mapErrs = map (second f)
  first f (InputValidator mf) = InputValidator $ \k ->
      first mapErrs <$> mf k
    where
      mapErrs = map (second f)

mapErrors :: (Functor m)
          => InputValidator key input m err a
          -> (err -> err')
          -> InputValidator key input m err' a
mapErrors m f = first f m


validateKey :: key
     -> (a -> Either err b)
     -> Result [(key, err)] a
     -> Result [(key, err)] b
validateKey key f (Failure e) = Failure e
validateKey key f (Success v) = case f v of
   Left err -> Failure [(key, err)]
   Right r -> Success r

-- | Monadically prove validity of result
proveM :: Monad m => InputValidator key input m err a
                  -> (a -> m (Either err b))
                  -> InputValidator key input m err b
proveM (InputValidator mv) f = InputValidator $ \key -> do
    v <- mv key
    case v of
      Failure e -> return $ Failure e
      Success val -> do
         v <- lift (f val)
         return $ eitherValid key v

-- | Purely prove input
prove :: Functor m => InputValidator key input m err a
     -> (a -> Either err b)
     -> InputValidator key input m err b
prove (InputValidator mv) f = InputValidator $ \key ->
    validateKey key f <$> mv key

validate :: (Monad m)
         => InputValidator key input m err a
         -> InputValidator key a m err b
         -> InputValidator key input m err b
validate (InputValidator m) (InputValidator f) = InputValidator $ \key -> do
     r <- m key
     case r of
       Failure e -> return $ Failure e
       Success r -> lift $ evalStateT (f key) r

validateSub :: (Monad m, Monoid key)
         => key
         -> InputValidator key input m err a
         -> InputValidator key a m err b
         -> InputValidator key input m err b
validateSub k (InputValidator m) (InputValidator f) = InputValidator $ \key -> do
     r <- m key
     case r of
       Failure e -> return $ Failure e
       Success r -> lift $ evalStateT (f (key <> k)) r

{-
item :: Applicative m => key -> InputValidator key a m err a
item key = InputValidator $ \_ -> pure <$> inp key
-}
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


wrap :: (key -> StateT s m (Result [(key, err)] a))  -> InputValidator key s m err a
wrap f = InputValidator $ f

runInputValidator :: key -> s -> InputValidator key s m err a -> m (Result [(key, err)] a, s)
runInputValidator key st (InputValidator val) = runStateT (val key) st

evalInputValidator :: (Monad m) => key -> s
                   -> InputValidator key s m err a
                   -> m (Result [(key, err)] a)
evalInputValidator key st (InputValidator val) = evalStateT (val key) st
