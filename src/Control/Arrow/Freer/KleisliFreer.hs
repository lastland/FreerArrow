{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Control.Arrow.Freer.KleisliFreer where

import Control.Category
import Control.Arrow
import Control.Monad.Freer.FreerMonad
import Data.Profunctor
import Prelude hiding (id, (.))

newtype KleisliFreer e a b = KleisliFreer (Kleisli (FreerMonad e) a b)
  deriving (Category, Profunctor, Strong, Choice,
            Arrow, ArrowChoice, ArrowApply,
            Functor, Applicative, Monad)

embed :: (a -> e b) -> KleisliFreer e a b 
embed f = KleisliFreer $ Kleisli $ \x -> Bind (f x) Ret
