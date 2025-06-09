{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE ImpredicativeTypes    #-}
{-# LANGUAGE QuantifiedConstraints #-}

module Control.Arrow.Freer.FreerArrowBridge where

import Control.Category
import Control.Arrow
import Data.Profunctor
import Prelude hiding (id, (.))
import Control.Arrow.Freer.Bridge

-- |- Freer arrows. This is essentially free arrows (Notions of computation as
-- monoids, Rivas & Jaskelioff, JFP) inlined with free strong profunctors.
{-- begin FreerArrow --}
data FreerArrow e x y where
  Id :: FreerArrow e x x
  Hom :: (x -> y) -> FreerArrow e x y
  Comp :: Bridge x a b z -> e a b ->
          FreerArrow e z y -> FreerArrow e x y
{-- end FreerArrow --}

-- |- This is called overCount because with FreerChoiceArrow, there is no
-- guarantee that the effect will happen. Instead, the static analyzer gives us
-- the worst case count---how many times effect would appear when all effects
-- happen. 
overCount :: FreerArrow e x y -> Int
overCount Id = 0
overCount (Hom _) = 0
overCount (Comp _  _ y) = 1 + overCount y

mightSkip :: Bridge x a b y -> Bool
mightSkip IdBridge = False
mightSkip (FirstBridge b) = mightSkip b
mightSkip (SecondBridge b) = mightSkip b
mightSkip (LeftBridge _) = True
mightSkip (RightBridge _) = True
mightSkip (LmapBridge _ b) = mightSkip b

-- |- We can also define underCount since we can match on the bridge to see
-- if there is a LeftBridge or RightBridge which represents that the effect
-- may not run.
underCount :: FreerArrow e x y -> Int
underCount Id = 0
underCount (Hom _) = 0
underCount (Comp b _ y) = (if mightSkip b then 0 else 1) + underCount y

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
  dimap f g Id = Hom $ g . f
  dimap f g (Hom h) = Hom $ dimap f g h
  dimap f g (Comp r x y) = Comp (cmapBridge f r) x (dimap id g y)

  -- lmap can be implemented more efficiently without recursion
  lmap f Id = Hom f
  lmap f (Hom h) = Hom $ lmap f h
  lmap f (Comp r x y) = Comp (cmapBridge f r) x y

{-- begin Strong_FreerArrow --}
instance Strong (FreerArrow e) where
  first' Id = Id
  first' (Hom r) = Hom $ first r
  first' (Comp (LmapBridge f r) a b) =
    lmap (first f) $ first' (Comp r a b)
  first' (Comp r a b) =
    Comp (FirstBridge r) a (first' b)

  second' Id = Id
  second' (Hom r) = Hom $ second r
  second' (Comp (LmapBridge f r) a b) =
    lmap (second f) $ second' (Comp r a b)
  second' (Comp r a b) =
    Comp (SecondBridge r) a (second' b)
{-- end Strong_FreerArrow --}

{-- begin Arrow_FreerArrow --}
-- |- Freer arrows are arrows.
instance Arrow (FreerArrow e) where
  arr f = Hom f
  first = first'
  second = second'
{-- end Arrow_FreerArrow --}

instance Choice (FreerArrow e) where
  left' Id = Id
  left' (Hom f) = Hom $ left f
  left' (Comp (LmapBridge f r) a b) =
    lmap (left f) $ left' (Comp r a b)
  left' (Comp r a b) =
    Comp (LeftBridge r) a (left' b)

  right' Id = Id
  right' (Hom f) = Hom $ right f
  right' (Comp (LmapBridge f r) a b) =
    lmap (right f) $ right' (Comp r a b)
  right' (Comp r a b) =
    Comp (RightBridge r) a (right' b)

instance ArrowChoice (FreerArrow e) where
  left = left'

-- instance RoutedProfunctor (FreerArrow e) where
--   lmapR r1 (Hom r2) = Hom $ CompRoute r1 r2
--   lmapR r1 (Comp b e x) = Comp (cmapRouterBridge r1 b) e x

{-- begin Category_FreerArrow --}
-- |- Freer arrows are categories.
instance Category (FreerArrow e) where
  id = Id

  f . Id = f
  f . (Hom r) = lmap r f
  f . (Comp f' x y) = Comp f' x (f . y)
{-- end Category_FreerArrow --}

-- |- Freer arrows can be interpreted into any arrows, as long as we can provide
-- an effect handler.
interp :: (Strong arr, Choice arr, Arrow arr) =>
  (e :-> arr) -> FreerArrow e x y -> arr x y
interp _       Id = id
interp _       (Hom r) = arr r
interp handler (Comp f x y) = bridge f (handler x) >>> interp handler y

instance (forall a b. Show (e a b)) => Show (FreerArrow e x y) where
  show Id = "Id"
  show (Hom _) = "Hom"
  show (Comp f e c) = "(" ++ show f ++ "[" ++ show e ++ "] >>>\n" ++ show c ++ ")"
