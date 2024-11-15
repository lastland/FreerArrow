{-# LANGUAGE GADTs          #-}
{-# LANGUAGE InstanceSigs   #-}

module Control.Arrow.Freer.FreerArrowApply where

import qualified Data.Bifunctor as B (first)
import Control.Category
import Control.Arrow
import Data.Profunctor
import Prelude hiding (id, (.))

data FreerArrowApply e x y where
  Hom :: (x -> y) -> FreerArrowApply e x y
  Comp :: (x -> (a, c)) ->
          ((b, c) -> z) ->
          e a b ->
          FreerArrowApply e z y ->
          FreerArrowApply e x y
  App :: FreerArrowApply e x (FreerArrowApply e a b, a) ->
         FreerArrowApply e b y ->
         FreerArrowApply e x y

instance Arrow (FreerArrowApply e) where
  arr = Hom
  first = first'

instance Profunctor (FreerArrowApply e) where
  dimap :: (x -> a) ->
           (b -> y) ->
           FreerArrowApply e a b ->
           FreerArrowApply e x y
  dimap f g (Hom h) = Hom (g . h . f)
  dimap f g (Comp f' g' x y) =
    Comp (f' . f) g' x (rmap g y)
  dimap f g (App c k) = App (lmap f c) (rmap g k)

instance Strong (FreerArrowApply e) where
  first' (Hom f) = Hom $ B.first f
  first' (Comp f g a b) =
    Comp (\(x, c) ->
             let (x', z) = f x in (x', (z, c)))
         (\(y, (z, x)) -> (g (y, z), x))
         a (first' b)
  first' (App c k) = _

instance Category (FreerArrowApply e) where
  id = Hom id
  f . (Hom g) = lmap g f
  f . (Comp f' g' x y) = Comp f' g' x (f . y)
  f . (App c k) = App c (f . k)

instance ArrowApply (FreerArrowApply e) where
  app = App (Hom id) (Hom id)


