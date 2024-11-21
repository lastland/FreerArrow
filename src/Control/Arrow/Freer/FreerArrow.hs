{-# LANGUAGE TupleSections  #-}
{-# LANGUAGE TypeOperators  #-}
{-# LANGUAGE RankNTypes     #-}
{-# LANGUAGE GADTs          #-}
{-# LANGUAGE KindSignatures #-}

module Control.Arrow.Freer.FreerArrow where

import qualified Data.Bifunctor as B (first)
import Control.Category
import Control.Arrow
import Data.Profunctor
import Prelude hiding (id, (.))

-- |- Freer arrows. This is essentially free arrows (Notions of computation as
-- monoids, Rivas & Jaskelioff, JFP) inlined with free strong profunctors.
{-- begin FreerArrow --}
data FreerArrow e x y where
  Hom :: (x -> y) -> FreerArrow e x y
  Comp :: (x -> (a, c)) ->
          ((b, c) -> z) ->
          e a b ->
          FreerArrow e z y ->
          FreerArrow e x y
{-- end FreerArrow --}

-- A function that counts the number of effects in a freer arrow. This
-- illustrates that some static analysis can be performed on freer arrows. Even
-- if the effect can be stateful, we do not need to provide an initial state.
count :: FreerArrow e x y -> Int
count (Hom _) = 0
count (Comp _ _ _ y) = 1 + count y

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
embed f = Comp (,()) fst f id

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
  dimap f g (Comp f' g' x y) =
    Comp (f' . f) g' x (dimap id g y)
    -- Alternatively:
    --   Comp (f' . f) id x (dimap g' g y)

  -- lmap can be implemented more efficiently without recursion
  lmap f (Hom h) = Hom (h . f)
  lmap f (Comp f' g' x y) = Comp (f' . f) g' x y

-- |- Freer arrows are strong profunctors.
instance Strong (FreerArrow e) where
  first' (Hom f) = Hom $ B.first f
  first' (Comp f g a b) =
    Comp (\(x, c) ->
             let (x', z) = f x in (x', (z, c)))
         (\(y, (z, x)) -> (g (y, z), x))
         a (first' b)
{-- end Strong_FreerArrow --}

{-- begin Category_FreerArrow --}
-- |- Freer arrows are categories.
instance Category (FreerArrow e) where
  id = Hom id

  f . (Hom g) = lmap g f
  f . (Comp f' g' x y) = Comp f' g' x (f . y)
{-- end Category_FreerArrow --}

-- |- Freer arrows can be interpreted into any arrows, as long as we can provide
-- an effect handler.
interp :: (Profunctor arr, Arrow arr) =>
  (e :-> arr) -> FreerArrow e :-> arr
interp _       (Hom f) = arr f
interp handler (Comp f g x y) = dimap f g (first (handler x)) >>>
                                        interp handler y
