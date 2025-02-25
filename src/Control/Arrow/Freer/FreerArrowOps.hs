{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE ImpredicativeTypes    #-}

module Control.Arrow.Freer.FreerArrowOps where

import qualified Control.Arrow.Freer.FreerWeakArrow as W
import Control.Category
import Control.Arrow
import Data.Profunctor
import Data.Kind
import Prelude hiding (id, (.))

import Control.Arrow.Freer.FreerWeakArrow (FreerArrow)

-- |- Freer arrows. This is essentially free arrows (Notions of computation as
-- monoids, Rivas & Jaskelioff, JFP) inlined with free strong profunctors.
{-- begin FreerArrowOps --}
data FreerArrowOps :: (Type -> Type -> Type) -> Type -> Type -> Type where
  One :: FreerArrow e x y -> FreerArrowOps e x y
  Seq :: FreerArrowOps e x y -> FreerArrowOps e y z -> FreerArrowOps e x z
  And :: FreerArrowOps e a c -> FreerArrowOps e b d ->
         FreerArrowOps e (a, b) (c, d)
  Or  :: FreerArrowOps e a c -> FreerArrowOps e b d ->
         FreerArrowOps e (Either a b) (Either c d)
{-- end FreerArrowOps --}

embed :: e x y -> FreerArrowOps e x y
embed f = One $ W.embed f 

{-- begin Strong_FreerArrow --}
-- |- Freer arrows are profunctors.
instance Profunctor (FreerArrowOps e) where
  dimap f g (One x) = One $ dimap f g x
  dimap f g (Seq x y) = Seq (lmap f x) (rmap g y)
  dimap f g (And x y) = arr f >>> And x y >>> arr g
  dimap f g (Or  x y) = arr f >>> Or  x y >>> arr g 
  -- dimap f g (Or  x y) = Or (dimap f g x) (dimap f g y)
    -- Alternatively:
    --   Comp (f' . f) id x (dimap g' g y)

  -- lmap can be implemented more efficiently without recursion
  lmap f (One x)   = One $ lmap f x
  lmap f (Seq x y) = Seq (lmap f x) y
  lmap f (And x y) = arr f >>> And x y
  lmap f (Or  x y) = arr f >>> Or  x y

instance Strong (FreerArrowOps e) where
  first' = first

instance Choice (FreerArrowOps e) where
  left'  = left

{-- begin Category_FreerArrow --}
-- |- Freer arrows are categories.
instance Category (FreerArrowOps e) where
  id = One id

  One y . One x = One (y . x)
  f . (Seq x y) = Seq x (f . y)
  (Seq x y) . g = Seq (x . g) y
  y . x         = Seq x y 
{-- end Category_FreerArrow --}

instance Arrow (FreerArrowOps e) where
  arr f = One $ W.Hom f

  x *** y = And x y

  x &&& y = arr (\b -> (b, b)) >>> And x y

instance ArrowChoice (FreerArrowOps e) where
  x +++ y = Or x y

  x ||| y = Or x y >>> arr g
    where g (Left  a) = a
          g (Right a) = a

-- |- Freer arrows can be interpreted into any arrows, as long as we can provide
-- an effect handler.
interp :: (Profunctor arr, ArrowChoice arr) =>
  (forall a b. e a b -> arr a b) -> FreerArrowOps e x y -> arr x y
interp h (One x) = W.interp h x
interp h (Seq x y) = interp h x >>> interp h y
interp h (And x y) = interp h x *** interp h y 
interp h (Or  x y) = interp h x +++ interp h y
