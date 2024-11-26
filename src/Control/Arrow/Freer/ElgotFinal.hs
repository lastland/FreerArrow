{-# LANGUAGE RankNTypes     #-}
{-# LANGUAGE GADTs          #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE BangPatterns   #-}

module Control.Arrow.Freer.ElgotFinal where

import Control.Category
import Control.Arrow
import Data.Kind
import Prelude hiding (id, (.))

{-- begin Elgot --}
newtype Elgot f (e :: Type -> Type -> Type) x y =
  Elgot { runElgot :: forall ar. ArrowChoice ar =>
                      (forall a b. f e a b -> ar a b) -> ar x y }
{-- end Elgot --}

elgot :: f e x (Either z x) -> f e z y -> Elgot f e x y
elgot l k = Elgot $ \h ->
  let !l' = h l in
  let !k' = h k in
  let go = l' >>> k' ||| go in
    go
