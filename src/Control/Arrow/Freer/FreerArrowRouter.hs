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

-- |- Freer arrows. This is essentially free arrows (Notions of computation as
-- monoids, Rivas & Jaskelioff, JFP) inlined with free strong profunctors.
{-- begin FreerArrow --}
data FreerArrow e x y where
  HomR :: Router x a a y -> FreerArrow e x y
  Comp :: Router x a b z -> e a b ->
          FreerArrow e z y -> FreerArrow e x y
{-- end FreerArrow --}

-- A function that counts the number of effects in a freer arrow. This
-- illustrates that some static analysis can be performed on freer arrows. Even
-- if the effect can be stateful, we do not need to provide an initial state.
count :: FreerArrow e x y -> Int
count (HomR _) = 0
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
  dimap f g (HomR h) = HomR $ LmapRouter (g . route h id . f) IdRouter
  dimap f g (Comp r x y) = Comp (cmapRouter f r) x (dimap id g y)

  -- lmap can be implemented more efficiently without recursion
  lmap f (HomR h) = HomR (cmapRouter f h)
  lmap f (Comp r x y) = Comp (cmapRouter f r) x y

{-- begin Strong_FreerArrow --}
instance Strong (FreerArrow e) where
  first' (HomR IdRouter) = HomR IdRouter
  first' (HomR r) = HomR $ FirstRouter r
  first' (Comp (LmapRouter f r) a b) =
    lmap (first f) $ first' (Comp r a b)
  first' (Comp r a b) =
    Comp (FirstRouter r) a (first' b)

  second' (HomR IdRouter) = HomR IdRouter
  second' (HomR r) = HomR $ SecondRouter r
  second' (Comp (LmapRouter f r) a b) =
    lmap (second f) $ second' (Comp r a b)
  second' (Comp r a b) =
    Comp (SecondRouter r) a (second' b)
{-- end Strong_FreerArrow --}

{-- begin Arrow_FreerArrow --}
-- |- Freer arrows are arrows.
instance Arrow (FreerArrow e) where
  arr f = HomR $ LmapRouter f IdRouter
  first = first'
  second = second'
{-- end Arrow_FreerArrow --}

instance Choice (FreerArrow e) where
  left' (HomR r) = HomR $ LeftRouter r 
  left' (Comp (LmapRouter f r) a b) =
    lmap (left f) $ left' (Comp r a b)
  left' (Comp r a b) =
    Comp (LeftRouter r) a (left' b)

  right' (HomR r) = HomR $ RightRouter r 
  right' (Comp (LmapRouter f r) a b) =
    lmap (right f) $ right' (Comp r a b)
  right' (Comp r a b) =
    Comp (RightRouter r) a (right' b)

instance ArrowChoice (FreerArrow e) where
  left = left'

{-- begin Category_FreerArrow --}
-- |- Freer arrows are categories.
instance Category (FreerArrow e) where
  id = HomR IdRouter

--  f . (HomR r) = HomR $ compRouter r f
  f . (Comp f' x y) = Comp f' x (f . y)
{-- end Category_FreerArrow --}

-- |- Freer arrows can be interpreted into any arrows, as long as we can provide
-- an effect handler.
interp :: (Strong arr, Choice arr, Arrow arr) =>
  (e :-> arr) -> FreerArrow e x y -> arr x y
interp _       (HomR r) = route r id
interp handler (Comp f x y) = route f (handler x) >>> interp handler y
