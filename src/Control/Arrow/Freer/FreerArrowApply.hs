{-# LANGUAGE GADTs          #-}
{-# LANGUAGE InstanceSigs   #-}
{-# LANGUAGE RankNTypes     #-}
{-# LANGUAGE TypeOperators  #-}
{-# LANGUAGE TupleSections  #-}

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

--                  x
--          f   a ----- b   g       y
--      x ----<           >---- z ----- y
--              c . . . c


  App :: (x -> (a, c)) ->
         ((b, c) -> z) ->
         FreerArrowApply e a (FreerArrowApply e d b, d) ->
         FreerArrowApply e z y ->
         FreerArrowApply e x y

--    f    c _____
-- x --- a -<     |
--   \        d ----- b   g       k
--    \                 >---- z ------ y
--      c . . . . . . c

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
  dimap f g (App f' g' c k) = App (f' . f) g' c (rmap g k)



assoc1 :: (x -> (a, c)) ->
          (x, y) ->
          (a, (c, y))
assoc1 f = (\(x, c) ->
             let (x', z) = f x in (x', (z, c)))

assoc2 :: ((b, c) -> z) ->
          (b, (c, y)) ->
          (z, y)
assoc2 g = (\(y, (z, x)) -> (g (y, z), x))

instance Strong (FreerArrowApply e) where
  first' (Hom f) = Hom $ B.first f
  first' (Comp f g a b) =
    Comp (assoc1 f)
         (assoc2 g)
         a (first' b)
  first' (App f g c k) =
    App (assoc1 f)
        (assoc2 g)
        c (first' k)

instance Category (FreerArrowApply e) where
  id = Hom id
  f . (Hom g) = lmap g f
  f . (Comp f' g' x y) = Comp f' g' x (f . y)
  f . (App f' g' c k) = App f' g' c (f . k)

instance ArrowApply (FreerArrowApply e) where
  app :: FreerArrowApply e (FreerArrowApply e b c, b) c
  app = App (, ()) fst id id

type x ~> y = forall a b. x a b -> y a b

interp :: (Profunctor arr, ArrowApply arr) =>
  (e ~> arr) -> FreerArrowApply e x y -> arr x y
interp _       (Hom f) = arr f
interp handler (Comp f g x y) = dimap f g (first (handler x)) >>>
                                        interp handler y
interp handler (App f g c k) = (interp handler (lmap f (first (rmap (first (interp handler)) c))) >>>
                                first app) >>>
                               lmap g (interp handler k)


