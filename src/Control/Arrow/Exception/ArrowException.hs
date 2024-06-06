{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}

module Control.Arrow.Exception.ArrowException where

import qualified Control.Arrow.Freer.FreerArrowChoice as C
import qualified Control.Arrow.Freer.KleisliFreer as K

import Control.Category
import Control.Arrow
import Control.Arrow.Freer.FreerArrow
import Control.Arrow.Freer.FreerArrowChoice (FreerArrowChoice)
import Control.Arrow.Freer.KleisliFreer     (KleisliFreer(..))
import Control.Monad.Freer.FreerMonad       (FreerMonad(..))
import Control.Monad.Freer.Sum1
import Control.Arrow.Freer.Sum2
import Data.Kind
import Prelude hiding (id, (.))

class Arrow a => ArrowException e a where
  throwError :: a e x

class ArrowException e a => ArrowCatch e a where
  catchError :: a x y -> a e y -> a x y

newtype EitherA e a b = EitherA (Kleisli (Either e) a b)
  deriving (Category, Arrow)

-- |- EitherA is an ArrowException.
instance ArrowException e (EitherA e) where
  throwError = EitherA $ Kleisli Left

-- |- EitherA is also an ArrowCatch.
instance ArrowCatch e (EitherA e) where
  catchError (EitherA (Kleisli f)) (EitherA (Kleisli h)) =
    EitherA $ Kleisli $
        \x -> case f x of
          Left e  -> h e
          Right y -> Right y

-- |- An ADT for exception effect.
data ExceptionEff :: Type -> Type -> Type -> Type where
  Throw :: ExceptionEff e e a
  
data ExceptionEff1 :: Type -> Type -> Type where
  Throw1 :: e -> ExceptionEff1 e a

-- |- A freer arrow is an ArrowException. (But it is not an [ArrowCatch].)
instance Inj2 (ExceptionEff ex) e => ArrowException ex (FreerArrow e) where
  throwError = embed $ inj2 Throw

instance Inj2 (ExceptionEff ex) e => ArrowException ex (FreerArrowChoice e) where
  throwError = C.embed $ inj2 Throw

instance Inj1 (ExceptionEff1 ex) e => ArrowException ex (KleisliFreer e) where
  throwError = K.embed $ inj1 . Throw1

type Ex  ex e = Sum2 (ExceptionEff  ex) e
type Ex1 ex e = Sum1 (ExceptionEff1 ex) e 

-- This only works when [ExceptionEff] is the leftmost effect.
catchErrorF :: FreerArrow (Ex ex e) x y ->
               FreerArrow (Ex ex e) ex y ->
               FreerArrow (Ex ex e) x y
catchErrorF (Hom f) _                   = Hom f 
catchErrorF (Comp f _ (Inl2 Throw) _) h = Comp f' g' (Inl2 Throw) h
  where f' x = let (e, c) = f x in (e, (e, c))
        g' (_, (e, _)) = e
catchErrorF (Comp f g e x) h            = Comp f g e $ catchErrorF x h

-- This only works when [ExceptionEff] is the leftmost effect.
catchErrorFC :: FreerArrowChoice (Ex ex e) x y ->
                FreerArrowChoice (Ex ex e) ex y ->
                FreerArrowChoice (Ex ex e) x y
catchErrorFC (C.Hom f) _                   = C.Hom f 
catchErrorFC (C.Comp f g (Inl2 Throw) k) h = C.Comp f' g' (Inl2 Throw) (h ||| k)
  where f' x = case f x of
          Left (e, c) -> Left (e, (e, c))
          Right w     -> Right w
        g' (Left (_, (e, _))) = Left e
        g' (Right w)          = Right $ g (Right w)
catchErrorFC (C.Comp f g e x) h            = C.Comp f g e $ catchErrorFC x h

-- This only works when [ExceptionEff1] is the leftmost effect.
catchErrorK :: KleisliFreer (Ex1 ex e) x y ->
               KleisliFreer (Ex1 ex e) ex y ->
               KleisliFreer (Ex1 ex e) x y
catchErrorK (KleisliFreer (Kleisli f)) (KleisliFreer (Kleisli h)) =
  KleisliFreer $ Kleisli $ go f h
  where go :: forall ex e x y.
              (x -> FreerMonad (Ex1 ex e) y) ->
              (ex -> FreerMonad (Ex1 ex e) y) ->
              x -> FreerMonad (Ex1 ex e) y 
        go f h x = case f x of
                     Ret r -> Ret r
                     Bind (Inl1 (Throw1 e)) _ -> h e
                     Bind e                 k -> Bind e (go k h) 


handleException :: ArrowException e a => ExceptionEff e x y -> a x y
handleException Throw = throwError
