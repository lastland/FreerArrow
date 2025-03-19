{-# LANGUAGE GADTs                 #-}

module Control.Arrow.Freer.Router where

import Data.Profunctor
import Data.Functor.Contravariant
import Control.Arrow.Freer.Internal 

data Router x a b y where
  IdRouter :: Router x x y y

  FirstRouter :: Router x a b y -> Router (x, c) a b (y, c)
  SecondRouter :: Router x a b y -> Router (c, x) a b (c, y)
  
  LeftRouter  :: Router x a b y -> Router (Either x c) a b (Either y c)
  RightRouter :: Router x a b y -> Router (Either c x) a b (Either c y)

  SwapRouter :: Router (x, y) a b c -> Router (y, x) a b c

  LeftRotRouter :: Router ((x, y), z) a b c -> Router (x, (y, z)) a b c 
  RightRotRouter  :: Router (x, (y, z)) a b c -> Router ((x, y), z) a b c

  DupRouter :: Router (x, x) a b c -> Router x a b c

  LmapRouter :: (w -> x) -> Router x a b y -> Router w a b y

cmapRouter :: (w -> x) -> Router x a b y -> Router w a b y
cmapRouter f (LmapRouter g r) = LmapRouter (g . f) r
cmapRouter f r = LmapRouter f r


-- first swap :: ((x, y), z) -> ((y, x), z)
-- second :: ((y, x), z) -> ((y, x), a)

-- ((x, y), z) -> ((y, x), a)

-- e z a :: IdRouter
-- (w, z) -> (w, a) :: SecondRouter IdRouter

-- If the first router is routing an id profunctor
compRouter :: Router x a a y -> Router y b c z -> Router x b c z
compRouter IdRouter r = r
compRouter (FirstRouter r) (FirstRouter r') = FirstRouter (compRouter r r')
compRouter (SecondRouter r) (SecondRouter r') = SecondRouter (compRouter r r')
compRouter (LeftRouter r) (LeftRouter r') = LeftRouter (compRouter r r')
compRouter (RightRouter r) (RightRouter r') = RightRouter (compRouter r r')
compRouter (SwapRouter r) r' = SwapRouter (compRouter r r')
compRouter (LeftRotRouter r) r' = LeftRotRouter (compRouter r r')
compRouter (RightRotRouter r) r' = RightRotRouter (compRouter r r')
compRouter (DupRouter r) r' = DupRouter (compRouter r r')
compRouter (LmapRouter f r) r' = LmapRouter f (compRouter r r')


route :: (Strong p, Choice p) => Router x a b y -> p a b -> p x y
route IdRouter = id
route (FirstRouter r) = first' . route r
route (SecondRouter r) = second' . route r
route (LeftRouter r) = left'. route r
route (RightRouter r) = right'. route r
route (SwapRouter r) = lmap swap . route r
route (LeftRotRouter r) = lmap unassoc . route r
route (RightRotRouter r) = lmap assoc . route r
route (DupRouter r) = lmap dup . route r
route (LmapRouter f r) = lmap f . route r

-- | We don't use this. This is just to show that Router is a contravariant
-- functor.
newtype ContraRouter a b y x = ContraRouter (Router x a b y) 

instance Contravariant (ContraRouter a b y) where
  contramap f (ContraRouter r) = ContraRouter $ cmapRouter f r
