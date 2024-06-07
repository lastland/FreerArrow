{-# LANGUAGE RankNTypes     #-}
{-# LANGUAGE GADTs          #-}
{-# LANGUAGE KindSignatures #-}

module Control.Arrow.Freer.Elgot where

import Control.Category
import Control.Arrow
import Data.Profunctor
import Data.Kind
import Prelude hiding (id, (.))

{-- begin Elgot --}
data Elgot f (e :: Type -> Type -> Type) x y where
  Elgot :: f e x (Either z x) -> f e z y -> Elgot f e x y
{-- end Elgot --}

interp :: (Profunctor arr, ArrowChoice arr, Profunctor (f e), ArrowChoice (f e)) =>
  (forall a b. f e a b -> arr a b) -> Elgot f e x y -> arr x y
interp h (Elgot l k) = h l >>> h k ||| interp h (Elgot l k)
