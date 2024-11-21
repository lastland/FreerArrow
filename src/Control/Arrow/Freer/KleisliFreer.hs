{-# LANGUAGE RankNTypes                 #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE TypeOperators              #-}
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

-- |- Freer arrows can be interpreted into any arrows, as long as we can provide
-- an effect handler.
interp :: forall e m. Monad m => (e ~> m) -> KleisliFreer e :-> Kleisli m
interp handler (KleisliFreer (Kleisli f)) =
  Kleisli $ go f
  where go :: forall a b. (a -> FreerMonad e b) -> a -> m b
        go f x = case f x of
                   Ret r    -> return r
                   Bind e k -> handler e >>= go k
