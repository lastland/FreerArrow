{-# LANGUAGE LambdaCase     #-}
{-# LANGUAGE TypeOperators  #-}
{-# LANGUAGE RankNTypes     #-}
{-# LANGUAGE GADTs          #-}
{-# LANGUAGE KindSignatures #-}

module Control.Arrow.Freer.FreerArrowChoiceL where

import qualified Data.Bifunctor as B (first)
import Control.Category
import Control.Arrow
import Data.Profunctor
import Prelude hiding (id, (.))

-- |- Freer arrow choice. Inspired by:
-- [https://www.reddit.com/r/haskell/comments/p7grsq/comment/h9k2anl/?utm_source=share&utm_medium=web3x&utm_name=web3xcss&utm_term=1&utm_content=share_button]
{-- begin FreerArrowChoiceL --}
data FreerArrowChoiceL e x y where
  Hom :: (x -> y) -> FreerArrowChoiceL e x y
  Comp :: (x -> Either (a, c) w) ->
          e a b ->
          FreerArrowChoiceL e (Either (b, c) w) y ->
          FreerArrowChoiceL e x y
{-- end FreerArrowChoiceL --}

-- |- This is called overCount because with FreerArrowChoiceL, there is no
-- guarantee that the effect will happen. Instead, the static analyzer gives us
-- the worst case count---how many times effect would appear when all effects
-- happen. (It is not clear to me how to define an underCount---this is possible
-- with selective functor but I don't see how with FreerArrowChoiceL.)
overCount :: FreerArrowChoiceL e x y -> Int
overCount (Hom _) = 0
overCount (Comp _  _ y) = 1 + overCount y

embed :: e x y -> FreerArrowChoiceL e x y
embed f = Comp (\x -> Left (x, ())) f
                (arr (\case
                         Left (b, _) -> b
                         Right b -> b))

instance Arrow (FreerArrowChoiceL e) where
  arr = Hom

  first = first'

instance ArrowChoice (FreerArrowChoiceL e) where
  left = left'

instance Profunctor (FreerArrowChoiceL e) where
  dimap f g (Hom h) = Hom (g . h . f)
  dimap f g (Comp f' x y) = Comp (f' . f) x (dimap id g y)

  lmap f (Hom h) = Hom (h . f)
  lmap f (Comp f' x y) = Comp (f' . f) x y

{-- begin Strong_FreerArrowChoiceL --}
instance Strong (FreerArrowChoiceL e) where
  first' (Hom f) = Hom $ B.first f
  first' (Comp f a b) = Comp f' a (lmap g (first' b))
      where f' (x, c) = case f x of
              Left (x', z) -> Left (x', (z, c))
              Right x' -> Right (x', c)
            g (Left (y, (z, x))) = (Left (y, z), x)
            g (Right (y, z))     = (Right y, z)
{-- end Strong_FreerArrowChoiceL --}

{-- begin Choice_FreerArrowChoiceL --}
instance Choice (FreerArrowChoiceL e) where
  left' (Hom f) = Hom $ \case
    Left x -> Left $ f x
    Right y -> Right y
  left' (Comp f a b) = Comp f' a (lmap g (left' b))
        where f' (Left x)  = case f x of
                               Left (x', z) -> Left (x', z)
                               Right w -> Right (Left w)
              f' (Right y) = Right (Right y)
              g (Left (y, z))     = Left $ Left (y, z)
              g (Right (Left w))  = Left $ Right w
              g (Right (Right y)) = Right y
{-- end Choice_FreerArrowChoiceL --}

instance Category (FreerArrowChoiceL e) where
  id = Hom id

  f . (Hom g)          = lmap g f
  f . (Comp f' x y) = Comp f' x (f . y)

type x ~> y = forall a b. x a b -> y a b

interp :: (Profunctor arr, ArrowChoice arr) =>
  (e ~> arr) -> FreerArrowChoiceL e x y -> arr x y
interp _       (Hom f) = arr f
interp handler (Comp f x y) = lmap f (left (first (handler x))) >>>
                              interp handler y
