{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}

module Control.Arrow.Freer.Sum2 where

import Data.Kind

data Sum2 (l :: Type -> Type -> Type) (r :: Type -> Type -> Type) a b where
  Inl2 :: l a b -> Sum2 l r a b
  Inr2 :: r a b -> Sum2 l r a b

class Inj2 (a :: Type -> Type -> Type) (b :: Type -> Type -> Type) where
  inj2 :: a x y -> b x y

instance Inj2 l l where
  inj2 = id

instance Inj2 l (Sum2 l r) where 
  inj2 = Inl2

instance Inj2 r r' => Inj2 r (Sum2 l r') where
  inj2 = Inr2 . inj2
