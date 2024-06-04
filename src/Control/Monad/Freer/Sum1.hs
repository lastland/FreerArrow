{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}

module Control.Monad.Freer.Sum1 where

import Data.Kind

data Sum1 (l :: Type -> Type) (r :: Type -> Type) a where
  Inl1 :: l a -> Sum1 l r a
  Inr1 :: r a -> Sum1 l r a

class Inj1 (a :: Type -> Type) (b :: Type -> Type) where
  inj1 :: a x -> b x

instance Inj1 l l where
  inj1 = id

instance Inj1 l (Sum1 l r) where 
  inj1 = Inl1

instance Inj1 r r' => Inj1 r (Sum1 l r') where
  inj1 = Inr1 . inj1
