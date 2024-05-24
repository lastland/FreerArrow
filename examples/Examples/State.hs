{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE TupleSections         #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE KindSignatures        #-}

module Examples.State where

import Control.Category
import Control.Arrow
import Control.Arrow.ArrowState
import Control.Arrow.Freer.FreerArrow
import Data.Profunctor
import Data.Kind
import Prelude hiding ((.), id)

-- |- An ADT for stateful effect.
data StateEff :: Type -> Type -> Type -> Type where
  Get :: StateEff s a s
  Put :: StateEff s s s

-- |- A "smart constructor" for get effect.
get :: FreerArrow (StateEff s) a s
get = embed Get

-- |- A "smart constructor" for put effect.
put :: FreerArrow (StateEff s) s s
put = embed Put

instance ArrowState s (FreerArrow (StateEff s)) where
  getState = get

  setState = put

  changeState f = arr ((),) >>>
    first getState >>> arr (\(s, b) -> (f s b, b)) >>>
    first setState >>> arr snd

  accessState f = arr ((),) >>>
    first getState >>> arr (uncurry f)

-- |- A program that reads from the state and writes back the state.
echo :: ArrowState s arr => arr () s
echo = getState >>> setState

-- |- Echo but with data sharing. You get once but put twice.
echo2 :: ArrowState s arr => arr () (s, s)
-- (>>>) is from the Category typeclass. Every arrow is a category. (&&&) is an
-- arrow combinator.
echo2 = getState >>> setState &&& setState

handleState :: ArrowState s arr => StateEff s ~> arr 
handleState Get = getState
handleState Put = setState

interpState :: (Profunctor arr, ArrowState s arr) =>
  FreerArrow (StateEff s) ~> arr
interpState = interp handleState


-- The following code is adapted from Nicholas Coltharp.

newtype AState s a b = AState { runState :: a -> s -> (b, s) }

instance Category (AState s) where
  id = AState (,)

  AState f . AState g = AState $ \x s -> uncurry f (g x s)

instance Arrow (AState s) where
  arr f = AState $ \a s -> (f a, s)

  first (AState f) = AState $ \(a, c) s -> let (b, s') = f a s in ((b, c), s')

instance ArrowState s (AState s) where
  getState = AState $ \_ s -> (s, s)

  setState = AState $ \s _ -> (s, s)

  changeState f = arr ((),) >>>
    first getState >>> arr (\(s, b) -> (f s b, b)) >>>
    first setState >>> arr snd

  accessState f = arr ((),) >>>
    first getState >>> arr (uncurry f)

instance Profunctor (AState s) where
  dimap f g (AState h) = AState $ \a s ->
    let (b, s') = h (f a) s in (g b, s')
