{-# LANGUAGE GADTs                 #-}

module Control.Arrow.Freer.Router where

import Data.Profunctor
import Data.Functor.Contravariant

data Router x a b y where
  IdRouter :: Router x x y y

  FstRouter :: Router x a b y -> Router (x, c) a b (y, c)
  SndRouter :: Router x a b y -> Router (c, x) a b (c, y)
  
  LeftRouter  :: Router x a b y -> Router (Either x c) a b (Either y c)
  RightRouter :: Router x a b y -> Router (Either c x) a b (Either c y)

  LmapRouter :: (w -> x) -> Router x a b y -> Router w a b y

cmapRouter :: (w -> x) -> Router x a b y -> Router w a b y
cmapRouter f (LmapRouter g r) = LmapRouter (g . f) r
cmapRouter f r = LmapRouter f r

route :: (Strong p, Choice p) => Router x a b y -> p a b -> p x y
route IdRouter = id
route (FstRouter r) = first' . route r
route (SndRouter r) = second' . route r
route (LeftRouter r) = left'. route r
route (RightRouter r) = right'. route r
route (LmapRouter f r) = lmap f . route r

-- | We don't use this. This is just to show that Router is a contravariant
-- functor.
newtype ContraRouter a b y x = ContraRouter (Router x a b y) 

instance Contravariant (ContraRouter a b y) where
  contramap f (ContraRouter r) = ContraRouter $ cmapRouter f r
