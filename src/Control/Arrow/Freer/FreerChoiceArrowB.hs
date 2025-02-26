{-# LANGUAGE LambdaCase     #-}
{-# LANGUAGE TypeOperators  #-}
{-# LANGUAGE RankNTypes     #-}
{-# LANGUAGE GADTs          #-}
{-# LANGUAGE KindSignatures #-}

module Control.Arrow.Freer.FreerChoiceArrowB where

import qualified Data.Bifunctor as B (first)
import Control.Category
import Control.Arrow
import Data.Profunctor
import Prelude hiding (id, (.))

-- |- Freer arrow choice. Inspired by:
-- [https://www.reddit.com/r/haskell/comments/p7grsq/comment/h9k2anl/?utm_source=share&utm_medium=web3x&utm_name=web3xcss&utm_term=1&utm_content=share_button]
{-- begin FreerChoiceArrowB --}
data FreerChoiceArrowB e x y where
  Hom :: (x -> y) -> FreerChoiceArrowB e x y
  -- TODO: Perhaps the code would be simpler if we use [Either w (a, c)] instead
  -- of [Either (a, c) w] because the former is a monad/applicative/functor.
  Comp :: (x -> Either (a, c) w) ->
          (Either (b, c) w -> z) ->
          e a b ->
          FreerChoiceArrowB e z y ->
          FreerChoiceArrowB e x y
{-- end FreerChoiceArrowB --}

-- |- This is called overCount because with FreerChoiceArrowB, there is no
-- guarantee that theeffect will happen. Instead, the static analyzer gives us
-- the worst case count---how many times effect would appear when all effects
-- happen. (It is not clear to me how to define an underCount---this is possible
-- with selective functor but I don't see how with FreerChoiceArrowB.)
overCount :: FreerChoiceArrowB e x y -> Int
overCount (Hom _) = 0
overCount (Comp _ _ _ y) = 1 + overCount y

embed :: e x y -> FreerChoiceArrowB e x y
embed f = Comp (\x -> Left (x, ()))
               (\case
                   Left (b, _) -> b
                   Right b -> b) f id

instance Arrow (FreerChoiceArrowB e) where
  arr = Hom

  first = first'

instance ArrowChoice (FreerChoiceArrowB e) where
  left = left'

instance Profunctor (FreerChoiceArrowB e) where
  dimap f g (Hom h) = Hom (g . h . f)
  dimap f g (Comp f' g' x y) = Comp (f' . f) g' x (dimap id g y)

  lmap f (Hom h) = Hom (h . f)
  lmap f (Comp f' g' x y) = Comp (f' . f) g' x y

instance Strong (FreerChoiceArrowB e) where
  first' (Hom f) = Hom $ B.first f
  first' (Comp f g a b) = Comp f' g' a (first' b)
      where f' (x, c) = case f x of
              Left (x', z) -> Left (x', (z, c))
              Right x' -> Right (x', c)
            g' (Left (y, (z, x))) = (g (Left (y, z)), x)
            g' (Right (y, z))     = (g (Right y), z)

instance Choice (FreerChoiceArrowB e) where
  left' (Hom f) = Hom $ \case
    Left x -> Left $ f x
    Right y -> Right y
  left' (Comp f g a b) = Comp f' g' a (left' b)
        where f' (Left x)  = case f x of
                               Left (x', z) -> Left (x', z)
                               Right w -> Right (Left w)
              f' (Right y) = Right (Right y)
              g' (Left (y, z))     = Left $ g (Left (y, z))
              g' (Right (Left w))  = Left $ g (Right w)
              g' (Right (Right y)) = Right y

instance Category (FreerChoiceArrowB e) where
  id = Hom id

  f . (Hom g)          = lmap g f
  f . (Comp f' g' x y) = Comp f' g' x (f . y)

type x ~> y = forall a b. x a b -> y a b

interp :: (Profunctor arr, ArrowChoice arr) =>
  (e ~> arr) -> FreerChoiceArrowB e x y -> arr x y
interp _       (Hom f) = arr f
interp handler (Comp f g x y) = dimap f g (left (first (handler x))) >>>
                                        interp handler y
