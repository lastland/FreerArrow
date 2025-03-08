{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE RankNTypes  #-}

module Control.Arrow.Freer.FreerArrowFinal where

import Control.Category
import Control.Arrow
import Data.Profunctor
import Prelude hiding (id, (.))

newtype FreerArrow e a b = FreerArrow {
  runFreer :: forall ar. (Strong ar, Arrow ar) =>
              (e :-> ar) -> ar a b }

embed :: e a b -> FreerArrow e a b
embed e = FreerArrow ($ e)

instance Category (FreerArrow e) where
  id = FreerArrow $ const id

  f . g = FreerArrow $ \h ->
    runFreer f h . runFreer g h

instance Profunctor (FreerArrow e) where
  dimap f g x = FreerArrow $ \h ->
    dimap f g (runFreer x h)

  lmap f x = FreerArrow $ \h ->
    lmap f (runFreer x h)

  rmap g x = FreerArrow $ \h ->
    rmap g (runFreer x h)

instance Strong (FreerArrow e) where
  first' x = FreerArrow $ \h ->
    first' (runFreer x h)

instance Arrow (FreerArrow e) where
  arr f = FreerArrow $ const (arr f)
  first = first'
