{-# LANGUAGE GADTs                 #-}

module Control.Arrow.Freer.Router where

import Data.Profunctor
import Data.Functor.Contravariant

-- ((x, y), z), (x, (y, z)), and (x, y, z) are all different in Haskell, unlike
-- in Rocq Prover.
data Router x a b y where
  IdRouter :: Router x x y y
  FstRouter :: Router (a, c) a b (b, c) 
  AllRouter :: Router (Either (a, c) w) a b (Either (b, c) w)
  LmapRouter :: (w -> x) -> Router x a b y -> Router w a b y

cmapRouter :: (w -> x) -> Router x a b y -> Router w a b y
cmapRouter f (LmapRouter g r) = LmapRouter (g . f) r
cmapRouter f r = LmapRouter f r

route :: (Strong p, Choice p) => Router x a b y -> p a b -> p x y
route IdRouter = id
route FstRouter = first'
route AllRouter = left' . first'
route (LmapRouter f r) = lmap f . route r

newtype ContraRouter a b y x = ContraRouter (Router x a b y) 

instance Contravariant (ContraRouter a b y) where
  contramap f (ContraRouter r) = ContraRouter $ cmapRouter f r
