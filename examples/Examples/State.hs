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
