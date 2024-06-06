{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}

module Control.Arrow.Exception.ArrowException where

import Control.Arrow
import Control.Arrow.Freer.FreerArrow
import Control.Arrow.Freer.Sum2
import Data.Kind
import Data.Profunctor
import Prelude hiding (id, (.))

class Arrow a => ArrowException e a where
  throwError :: a e x
  -- catchError :: a x y -> a e y -> a x y

-- |- Either is an ArrowException.
instance ArrowException e (Kleisli (Either e)) where
  throwError = Kleisli Left

-- |- An ADT for exception effect.
data ExceptionEff :: Type -> Type -> Type -> Type where
  Throw :: ExceptionEff e e a

-- |- A freer arrow is an ArrowException.
instance Inj2 (ExceptionEff ex) e => ArrowException ex (FreerArrow e) where
  throwError = embed $ inj2 Throw

type Ex ex e = Sum2 (ExceptionEff ex) e

catchError :: FreerArrow (Ex ex e) x y -> FreerArrow (Ex ex e) ex y -> FreerArrow (Ex ex e) x y
catchError (Hom f) _                   = Hom f 
catchError (Comp f g (Inl2 Throw) _) h = Comp f' g' (Inl2 Throw) $ lmap snd h
  where f' x = let (e, c) = f x in (e, (e, c))
        g' (b, (e, c)) = (g (b, c), e)
catchError (Comp f g e x) h            = Comp f g e $ catchError x h

handleException :: ArrowException e a => ExceptionEff e x y -> a x y
handleException Throw = throwError
