{-# LANGUAGE TupleSections         #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE ImpredicativeTypes    #-}

module Control.Arrow.Freer.FreerWeakArrow where

import Control.Category
import Control.Arrow
import Data.Profunctor
import Prelude hiding (id, (.))

-- |- Freer arrows. This is essentially free arrows (Notions of computation as
-- monoids, Rivas & Jaskelioff, JFP) inlined with free strong profunctors.
{-- begin FreerArrow --}
data FreerArrow e x y where
  Hom   :: (x -> y) -> FreerArrow e x y
  Comp  :: (x -> a) -> e a z ->
           FreerArrow e z y -> FreerArrow e x y
{--- end FreerArrow --}

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
embed f = Comp id f id

{-- begin Strong_FreerArrow --}
-- |- Freer arrows are profunctors.
instance Profunctor (FreerArrow e) where
  dimap f g (Hom h) = Hom (g . h . f)
  dimap f g (Comp f' x y) = Comp (f' . f) x (dimap id g y)
    -- Alternatively:
    --   Comp (f' . f) id x (dimap g' g y)

  -- lmap can be implemented more efficiently without recursion
  lmap f (Hom h) = Hom (h . f)
  lmap f (Comp f' x y) = Comp (f' . f) x y

{-- begin Category_FreerArrow --}
-- |- Freer arrows are categories.
instance Category (FreerArrow e) where
  id = Hom id

  f . (Hom g) = lmap g f
  f . (Comp f' x y) = Comp f' x (f . y)
{-- end Category_FreerArrow --}

-- |- The type for effect handlers.
type x ~> y = forall a b. x a b -> y a b

-- |- Freer arrows can be interpreted into any arrows, as long as we can provide
-- an effect handler.
interp :: (Profunctor arr, Arrow arr) => (e ~> arr) -> FreerArrow e x y -> arr x y
interp _       (Hom f)       = arr f
interp handler (Comp f x y)  = lmap f (handler x) >>> interp handler y
