{-# LANGUAGE RankNTypes     #-}
{-# LANGUAGE GADTs          #-}
{-# LANGUAGE KindSignatures #-}

module Control.Arrow.Freer.Elgot where

import Control.Category
import Control.Arrow
import Data.Kind
import Prelude hiding (id, (.))

{-- begin Elgot --}
data Elgot f (e :: Type -> Type -> Type) x y where
  Elgot :: f e x (Either z x) -> f e z y -> Elgot f e x y
{-- end Elgot --}

interp :: ArrowChoice arr =>
  (forall a b. f e a b -> arr a b) -> Elgot f e x y -> arr x y
interp h (Elgot l k) = go
  where go = l' >>> k' ||| go
        l' = h l
        k' = h k

data Elgot1 f (e :: Type -> Type) x r where
  Elgot1 :: (x -> f e (Either z x)) -> (z -> f e r) -> Elgot1 f e x r  

interp1 :: (Monad (f e), Monad m) =>
  (forall a. f e a -> m a) -> Elgot1 f e x r -> x -> m r
interp1 h (Elgot1 l k) x = do
  r <- h $ l x
  case r of
    Left  z -> h $ k z
    Right x -> interp1 h (Elgot1 l k) x
