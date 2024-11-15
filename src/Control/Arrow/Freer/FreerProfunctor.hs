{-# LANGUAGE GADTs          #-}
{-# LANGUAGE InstanceSigs   #-}

module Control.Arrow.Freer.FreerProfunctor where

import Data.Profunctor

data FreerProfunctor e x y where
  Dimap :: (x -> a) ->
           (b -> y) ->
           e a b ->
           FreerProfunctor e x y

instance Profunctor (FreerProfunctor e) where
  dimap :: (x -> a) ->
           (b -> y) ->
           FreerProfunctor e a b ->
           FreerProfunctor e x y
  dimap f g (Dimap h i e) = Dimap (h . f) (g . i) e

