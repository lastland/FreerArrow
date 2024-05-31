{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module Examples.StateM where

import Control.Monad
import Control.Monad.State.Class
import Data.Kind


data FreerMonad e r where
  Ret  :: r -> FreerMonad e r
  Bind :: e x -> (x -> FreerMonad e r) -> FreerMonad e r

embed :: e x -> FreerMonad e x
embed e = Bind e Ret 

instance Monad (FreerMonad e) where
  return     = pure
  Ret x    >>= k = k x
  Bind e f >>= k = Bind e (f >=> k)

instance Applicative (FreerMonad e) where
  pure = Ret
  (<*>) = ap

instance Functor (FreerMonad e) where
  fmap = liftM

interp :: Monad m =>
  (forall x. e x -> m x) -> FreerMonad e a -> m a
interp _       (Ret x)    = return x
interp handler (Bind e k) = handler e >>= interp handler . k

data StateMEff :: Type -> Type -> Type where
  Get :: StateMEff s s
  Put :: s -> StateMEff s ()

instance MonadState s (FreerMonad (StateMEff s)) where
  get = embed Get
  put = embed . Put

handleState :: MonadState s m => StateMEff s a -> m a
handleState Get     = get
handleState (Put x) = put x
