{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE ImpredicativeTypes    #-}
{-# LANGUAGE QuantifiedConstraints #-}

module Control.Arrow.Freer.FreerArrowRouter where

import Control.Category
import Control.Arrow
import Data.Profunctor
import Prelude hiding (id, (.))
import Control.Arrow.Freer.Router
import qualified Data.Bifunctor as B

-- |- Freer arrows. This is essentially free arrows (Notions of computation as
-- monoids, Rivas & Jaskelioff, JFP) inlined with free strong profunctors.
{-- begin FreerArrow --}
data FreerArrow e x y where
  Hom :: (x -> y) -> FreerArrow e x y
  Comp :: Router x a b z -> e a b ->
          FreerArrow e z y -> FreerArrow e x y
{-- end FreerArrow --}

-- A function that counts the number of effects in a freer arrow. This
-- illustrates that some static analysis can be performed on freer arrows. Even
-- if the effect can be stateful, we do not need to provide an initial state.
count :: FreerArrow e x y -> Int
count (Hom _) = 0
count (Comp _ _ y) = 1 + count y

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
embed f = Comp IdRouter f id


-- |- Freer arrows are profunctors.
instance Profunctor (FreerArrow e) where
  dimap f g (Hom h) = Hom (g . h . f)
  dimap f g (Comp r x y) = Comp (cmapRouter f r) x (dimap id g y)

  -- lmap can be implemented more efficiently without recursion
  lmap f (Hom h) = Hom (h . f)
  lmap f (Comp r x y) = Comp (cmapRouter f r) x y

{-- begin Strong_FreerArrow --}
instance Strong (FreerArrow e) where
  first' (Hom f) = Hom $ B.first f
  first' (Comp (LmapRouter f r) a b) =
    lmap (first f) $ first' (Comp r a b)
  first' (Comp r a b) =
    Comp (FstRouter r) a (first' b)

  second' (Hom f) = Hom $ B.second f
  second' (Comp (LmapRouter f r) a b) =
    lmap (second f) $ second' (Comp r a b)
  second' (Comp r a b) =
    Comp (SndRouter r) a (second' b)
{-- end Strong_FreerArrow --}

{-- begin Arrow_FreerArrow --}
-- |- Freer arrows are arrows.
instance Arrow (FreerArrow e) where
  arr = Hom
  first = first'
  second = second'
{-- end Arrow_FreerArrow --}

instance Choice (FreerArrow e) where
  left' (Hom f) = Hom $ B.first f
  left' (Comp (LmapRouter f r) a b) =
    lmap (left f) $ left' (Comp r a b)
  left' (Comp r a b) =
    Comp (LeftRouter r) a (left' b)

  right' (Hom f) = Hom $ B.second f
  right' (Comp (LmapRouter f r) a b) =
    lmap (right f) $ right' (Comp r a b)
  right' (Comp r a b) =
    Comp (RightRouter r) a (right' b)

instance ArrowChoice (FreerArrow e) where
  left = left'

{-- begin Category_FreerArrow --}
-- |- Freer arrows are categories.
instance Category (FreerArrow e) where
  id = Hom id

  f . (Hom g) = lmap g f
  f . (Comp f' x y) = Comp f' x (f . y)
{-- end Category_FreerArrow --}

-- |- Freer arrows can be interpreted into any arrows, as long as we can provide
-- an effect handler.
interp :: (Strong arr, Choice arr, Arrow arr) =>
  (e :-> arr) -> FreerArrow e x y -> arr x y
interp _       (Hom f) = arr f
interp handler (Comp f x y) = route f (handler x) >>> interp handler y
