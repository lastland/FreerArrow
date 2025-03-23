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
import Control.Arrow.Routed.Classes

-- |- Freer arrows. This is essentially free arrows (Notions of computation as
-- monoids, Rivas & Jaskelioff, JFP) inlined with free strong profunctors.
{-- begin FreerArrow --}
data FreerArrow e x y where
  Hom :: Router x y -> FreerArrow e x y
  Comp :: Bridge x a b z -> e a b ->
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
embed f = Comp IdBridge f id


-- |- Freer arrows are profunctors.
instance Profunctor (FreerArrow e) where
  dimap f g (Hom h) = Hom $ dimap f g h
  dimap f g (Comp r x y) = Comp (cmapBridge f r) x (dimap id g y)

  -- lmap can be implemented more efficiently without recursion
  lmap f (Hom h) = Hom $ lmap f h
  lmap f (Comp r x y) = Comp (cmapBridge f r) x y

{-- begin Strong_FreerArrow --}
instance Strong (FreerArrow e) where
  first' (Hom IdRoute) = Hom IdRoute
  first' (Hom r) = Hom $ AppFirst r
  first' (Comp (LmapBridge f r) a b) =
    lmap (first f) $ first' (Comp r a b)
  first' (Comp r a b) =
    Comp (FirstBridge r) a (first' b)

  second' (Hom IdRoute) = Hom IdRoute
  second' (Hom r) = Hom $ AppSecond r
  second' (Comp (LmapBridge f r) a b) =
    lmap (second f) $ second' (Comp r a b)
  second' (Comp r a b) =
    Comp (SecondBridge r) a (second' b)
{-- end Strong_FreerArrow --}

{-- begin Arrow_FreerArrow --}
-- |- Freer arrows are arrows.
instance Arrow (FreerArrow e) where
  arr f = Hom $ FunRoute f
  first = first'
  second = second'
{-- end Arrow_FreerArrow --}

-- instance Choice (FreerArrow e) where
--   left' (Hom IdRoute) = Hom IdRoute
--   left' (Hom r) = Hom $ AppLeft r
--   left' (Comp (LmapBridge f r) a b) =
--     lmap (left f) $ left' (Comp r a b)
--   left' (Comp r a b) =
--     Comp (LeftBridge r) a (left' b)

--   right' (Hom IdRoute) = Hom IdRoute
--   right' (Hom r) = Hom $ AppRight r
--   right' (Comp (LmapBridge f r) a b) =
--     lmap (right f) $ right' (Comp r a b)
--   right' (Comp r a b) =
--     Comp (RightBridge r) a (right' b)

-- instance ArrowChoice (FreerArrow e) where
--   left = left'

instance RoutedProfunctor (FreerArrow e) where
  lmapR r1 (Hom r2) = Hom $ CompRoute r1 r2
  lmapR r1 (Comp b e x) = Comp (cmapRouterBridge r1 b) e x

{-- begin Category_FreerArrow --}
-- |- Freer arrows are categories.
instance Category (FreerArrow e) where
  id = Hom IdRoute

  f . (Hom r) = lmapR r f
  f . (Comp f' x y) = Comp f' x (f . y)
{-- end Category_FreerArrow --}

-- |- Freer arrows can be interpreted into any arrows, as long as we can provide
-- an effect handler.
interp :: (Strong arr, Arrow arr) =>
  (e :-> arr) -> FreerArrow e x y -> arr x y
interp _       (Hom r) = arr $ route r
interp handler (Comp f x y) = bridge f (handler x) >>> interp handler y

instance (forall a b. Show (e a b)) => Show (FreerArrow e x y) where
  show (Hom r) = "Hom[" ++ show r ++ "]"
  show (Comp f e c) = "(" ++ show f ++ "[" ++ show e ++ "] >>>\n" ++ show c ++ ")"
