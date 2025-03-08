{-# LANGUAGE GADTs                 #-}

module Control.Arrow.Freer.Router where

import Data.Profunctor
import Data.Functor.Contravariant

data Router x a b y where
  IdRouter :: Router x x y y

  FstRouter :: Router x a b y -> Router (x, c) a b (y, c)
  LeftRouter :: Router x a b y -> Router (Either x c) a b (Either y c)

  LmapRouter :: (w -> x) -> Router x a b y -> Router w a b y

cmapRouter :: (w -> x) -> Router x a b y -> Router w a b y
cmapRouter f (LmapRouter g r) = LmapRouter (g . f) r
cmapRouter f r = LmapRouter f r

route :: (Strong p, Choice p) => Router x a b y -> p a b -> p x y
route IdRouter = id
-- route (LeftRotate r) = dimap assoc unassoc . route r
route (FstRouter r) = first' . route r
route (LeftRouter r) = left'. route r
--route LeftFstRouter = left' . first'
--route FstLeftRouter = first' . left'
route (LmapRouter f r) = lmap f . route r

newtype ContraRouter a b y x = ContraRouter (Router x a b y) 

instance Contravariant (ContraRouter a b y) where
  contramap f (ContraRouter r) = ContraRouter $ cmapRouter f r
