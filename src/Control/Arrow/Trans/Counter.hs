{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE LambdaCase #-}
module Control.Arrow.Trans.Counter where

import Prelude hiding (id, (.))
import Data.Profunctor
import Control.Arrow
import Control.Category
import Control.Arrow.Freer.FreerArrow

newtype CounterT i a b = CounterT (i (a, Int) (b, Int))  

instance Profunctor i => Profunctor (CounterT i) where
  dimap f g (CounterT x) = CounterT $ dimap (first f) (first g) x

instance Strong i => Strong (CounterT i) where
  first' (CounterT a) = CounterT $
                        dimap (\((a, c), n) -> ((a, n), c))
                              (\((b, n), c) -> ((b, c), n))
                              (first' a)  

instance Choice i => Choice (CounterT i) where
  left' (CounterT a) = CounterT $
                       dimap (\case
                                 (Left a, n)  -> Left (a, n)
                                 (Right c, n) -> Right (c, n))
                             (\case
                                 Left (b, n) -> (Left b, n)
                                 Right (c, n) -> (Right c, n))
                             (left' a)

instance Category i => Category (CounterT i) where 
  id = CounterT id
  CounterT b . CounterT a = CounterT $ b . a

{--
instance PreArrow i => PreArrow (CounterT i) where
  arr f = CounterT $ Control.Arrow.Arrow.arr $ first f
--}

instance (Strong i, Arrow i) => Arrow (CounterT i) where
  arr = CounterT . arr . first
  first = first'

tick :: (Arrow i) => i x y -> CounterT i x y
tick i = CounterT $ first i >>> arr (\(y, n) -> (y, n + 1))

interpC :: (Strong i, Arrow i) => (e :-> i) -> FreerArrow e x y -> CounterT i x y
interpC _       (Hom f) = arr f
interpC handler (Comp f e x) = lmap f (first (tick (handler e))) >>> interpC handler x
