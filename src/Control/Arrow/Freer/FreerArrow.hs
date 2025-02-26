{-# LANGUAGE TupleSections         #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE ImpredicativeTypes    #-}

module Control.Arrow.Freer.FreerArrow where

import Control.Category
import Control.Arrow
import Data.Profunctor
import Prelude hiding (id, (.))

-- |- Freer arrows. This is essentially free arrows (Notions of computation as
-- monoids, Rivas & Jaskelioff, JFP) inlined with free strong profunctors.
{-- begin FreerArrow --}
data FreerArrow e x y where
  Hom :: (x -> y) -> FreerArrow e x y
  Comp :: (x -> (a, c)) -> e a b ->
          FreerArrow e (b, c) y -> FreerArrow e x y
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
embed f = Comp (,()) f (lmap fst id)

-- ((x, y), z), (x, (y, z)), and (x, y, z) are all different in Haskell, unlike
-- in Rocq Prover.
assoc :: ((x, y), z) -> ((x, y), z)
assoc ((x, y), z) = ((x, y), z)

unassoc :: (x, (y, z)) -> ((x, y), z)
unassoc (x, (y, z)) = ((x, y), z)

-- |- Freer arrows are profunctors.
instance Profunctor (FreerArrow e) where
  dimap f g (Hom h) = Hom (g . h . f)
  dimap f g (Comp f' x y) =
    Comp (f' . f) x (dimap id g y)

  -- lmap can be implemented more efficiently without recursion
  lmap f (Hom h) = Hom (h . f)
  lmap f (Comp f' x y) = Comp (f' . f) x y

{-- begin Strong_FreerArrow --}
-- |- Freer arrows are strong profunctors.
instance Strong (FreerArrow e) where
  first' (Hom f) = Hom $ \(x, a) -> (f x, a)
  first' (Comp f a b) =
    Comp (\(x, a') ->
             let (x', b') = f x in (x', (b', a')))
         a (lmap unassoc (first' b))
{-- end Strong_FreerArrow --}

{-- begin Arrow_FreerArrow --}
-- |- Freer arrows are arrows.
instance Arrow (FreerArrow e) where
  arr = Hom
  first = first'
{-- end Arrow_FreerArrow --}


{-- begin Category_FreerArrow --}
-- |- Freer arrows are categories.
instance Category (FreerArrow e) where
  id = Hom id

  f . (Hom g) = lmap g f
  f . (Comp f' x y) = Comp f' x (f . y)
{-- end Category_FreerArrow --}
  
-- |- Freer arrows can be interpreted into any arrows, as long as we can provide
-- an effect handler.
interp :: (Profunctor arr, Arrow arr) =>
  (e :-> arr) -> FreerArrow e x y -> arr x y
interp _       (Hom f) = arr f
interp handler (Comp f x y) = lmap f (first (handler x)) >>>
                              interp handler y

interp' :: (Profunctor arr, Arrow arr) =>
  (e :-> arr) -> FreerArrow e x y -> (arr x y, Int)
interp' _       (Hom f) = (arr f, 0)
interp' handler (Comp f x y) =
  let (z, n) = interp' handler y in
  (lmap f (first (handler x)) >>> z, n + 1)
