{-# LANGUAGE TupleSections         #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE ImpredicativeTypes    #-}

module Control.Arrow.Freer.FreerArrowSimple where

import qualified Data.Bifunctor as B (first)
import Control.Category
import Control.Arrow
import Data.Profunctor
import Prelude hiding (id, (.))

-- |- Freer arrows. This is essentially free arrows (Notions of computation as
-- monoids, Rivas & Jaskelioff, JFP) inlined with free strong profunctors.
{-- begin FreerArrow --}
data FreerArrow e x y where
  Hom   :: (x -> y) -> FreerArrow e x y
  Comp  :: e x z ->
           FreerArrow e z y -> FreerArrow e x y
  CompP :: (x -> a) -> (b -> z) -> e a b ->
           FreerArrow e z y -> FreerArrow e x y
  CompS :: (x -> (a, c)) -> ((b, c) -> z) -> e a b ->
           FreerArrow e z y -> FreerArrow e x y
{-- end FreerArrow --}

-- A function that counts the number of effects in a freer arrow. This
-- illustrates that some static analysis can be performed on freer arrows. Even
-- if the effect can be stateful, we do not need to provide an initial state.
count :: FreerArrow e x y -> Int
count (Hom _) = 0
count (Comp  _ y) = 1 + count y
count (CompP _ _ _ y) = 1 + count y
count (CompS _ _ _ y) = 1 + count y

-- The following is what I call a reified arrow. It is free if we define an
-- equality that satisifies arrow laws and profunctor laws.
{--
data ReifiedArrow e x y where
  HomR :: (x -> y) -> ReifiedArrow e x y
  Embed :: e x y -> ReifiedArrow e x y
  CompR :: (x -> (a, c)) -> ((b, c) -> y) ->
    ReifiedArrow e a b -> ReifiedArrow e y z -> ReifiedArrow e x z
--}

-- |- Embed an effect in freer arrows.                        
embed :: e x y -> FreerArrow e x y
embed f = Comp f id

{-- begin Arrow_FreerArrow --}
-- |- Freer arrows are arrows.
instance Arrow (FreerArrow e) where
  arr = Hom
  first = first'
{-- end Arrow_FreerArrow --}

{-- begin Strong_FreerArrow --}
-- |- Freer arrows are profunctors.
instance Profunctor (FreerArrow e) where
  dimap f g (Hom h) = Hom (g . h . f)
  dimap f g (Comp x y) = CompP f id x (dimap id g y)
  dimap f g (CompP f' g' x y) = CompP (f' . f) g' x (dimap id g y)
  dimap f g (CompS f' g' x y) = CompS (f' . f) g' x (dimap id g y)
    -- Alternatively:
    --   Comp (f' . f) id x (dimap g' g y)

  -- lmap can be implemented more efficiently without recursion
  lmap f (Hom h) = Hom (h . f)
  lmap f (Comp x y) = CompP f id x y
  lmap f (CompP f' g' x y) = CompP (f' . f) g' x y
  lmap f (CompS f' g' x y) = CompS (f' . f) g' x y

-- |- Freer arrows are strong profunctors.
instance Strong (FreerArrow e) where
  first' (Hom f) = Hom $ B.first f
  first' (Comp a b) =
    first' $ CompP id id a b
  first' (CompP f g a b) =
    CompS (\(x, c) ->
             let x' = f x in (x',  c))
          (B.first g)
          a (first' b)
  first' (CompS f g a b) =
    CompS (\(x, c) ->
             let (x', z) = f x in (x', (z, c)))
          (\(y, (z, x)) -> (g (y, z), x))
          a (first' b)
{-- end Strong_FreerArrow --}

{-- begin Category_FreerArrow --}
-- |- Freer arrows are categories.
instance Category (FreerArrow e) where
  id = Hom id

  f . (Hom g) = lmap g f
  f . (Comp x y) = Comp x (f . y)
  f . (CompP f' g' x y) = CompP f' g' x (f . y)
  f . (CompS f' g' x y) = CompS f' g' x (f . y)
{-- end Category_FreerArrow --}
  
-- |- The type for effect handlers.
type x ~> y = forall a b. x a b -> y a b

-- |- Freer arrows can be interpreted into any arrows, as long as we can provide
-- an effect handler.
interp :: (Profunctor arr, Arrow arr) => (e ~> arr) -> FreerArrow e x y -> arr x y
interp _       (Hom f) = arr f
interp handler (Comp x y)      = handler x >>> interp handler y
interp handler (CompP f g x y) = dimap f g (handler x) >>> interp handler y
interp handler (CompS f g x y) = dimap f g (first (handler x)) >>> interp handler y
