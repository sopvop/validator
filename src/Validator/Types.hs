{-# LANGUAGE DeriveDataTypeable         #-}
{-# LANGUAGE DeriveFunctor              #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE FunctionalDependencies     #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE KindSignatures             #-}
{-# LANGUAGE MultiParamTypeClasses      #-}

module Validator.Types
       where

import           Control.Applicative
import           Control.Monad.Trans.Except (ExceptT (..))
import           Data.Bifunctor
import           Data.Typeable              (Typeable)

-- | Either like data type, but with applicative instance accumulating
--   error values.
data Result err a = Failure err
                  | Success a
                  deriving (Show, Ord, Eq, Typeable)

instance Functor (Result err) where
  fmap f (Success v) = Success (f v)
  fmap _ (Failure err) = Failure err

instance Monoid err => Applicative (Result err) where
  pure = Success
  Success f <*> Success v = Success (f v)
  Failure a <*> Failure b = Failure (a `mappend` b)
  Failure a <*> _ = Failure a
  _ <*> Failure b = Failure b

instance Bifunctor Result where
  second = fmap
  first f v = case v of
               Success s -> Success s
               Failure e -> Failure (f e)
  bimap f g v = case v of
      Success s -> Success (g s)
      Failure e -> Failure (f e)


newtype ValidatorT err m a = ValidatorT { runValidatorT :: m (Result err a) }
        deriving (Functor)


instance (Monad m, Monoid err) => Applicative (ValidatorT err m) where
  pure = ValidatorT . pure . Success
  (ValidatorT mf) <*> (ValidatorT ma) = ValidatorT $ do
     f <- mf
     a <- ma
     pure $ f <*> a


eitherToResult :: Either err a -> Result err a
eitherToResult (Left e) = Failure e
eitherToResult (Right r) = Success r

resultToEither :: Result a b -> Either a b
resultToEither (Failure e) = Left e
resultToEither (Success r) = Right r

validate :: Monad m => ExceptT err m a -> ValidatorT err m a
validate (ExceptT f) = ValidatorT $ eitherToResult <$> f

collect :: Functor m => ValidatorT e m a -> ExceptT e m a
collect (ValidatorT f) = ExceptT $  resultToEither <$> f

proveIt :: Monad m => ValidatorT e m t -> (t -> m (Either e a)) -> ExceptT e m a
proveIt (ValidatorT ma) f = ExceptT $ do
   a <- ma
   case a of
     Failure e -> pure $ Left e
     Success s -> f s

collectAll :: (Monad m, Monoid err) => [ExceptT err m a] -> ExceptT err m [a]
collectAll = collect . traverse validate
