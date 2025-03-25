{-# LANGUAGE Arrows                #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE KindSignatures        #-}

module Examples.State where

import Control.Category
import Control.Monad.Trans.State.Lazy hiding (get, put)
import Control.Arrow
import Control.Arrow.Freer.Router
import Control.Arrow.Freer.FreerArrowRouter
import Control.Arrow.State.ArrowState
import Prelude hiding ((.), id)

-- |- A program that reads from the state and writes back the state.
echo :: ArrowState s arr => arr () s
echo = get >>> put

-- |- Echo but with data sharing. You get once but put twice.
echo2 :: ArrowState s arr => arr () (s, s)
-- (>>>) is from the Category typeclass. Every arrow is a category. (&&&) is an
-- arrow combinator.
echo2 = get >>> put &&& put

-- |- Get the state before increasing it on two separate branches. This should
-- result in a state that is exactly 1 larger than the original state because
-- you only [get] once.
inc :: ArrowState Int arr => arr () (Int, Int)
inc = get >>> incPut &&& incPut
  where incPut = arr (+1) >>> put

-- |- Get the state on two different branches. This should result in a state
-- that is exactly 2 larger than the original state.
inc2 :: ArrowState Int arr => arr () (Int, Int)
inc2 = incPut &&& incPut
  where incPut = get >>> arr (+1) >>> put

-- |-
inc' :: ArrowState Int arr => arr a Int
inc' = proc x -> do
  s <- get -< x
  a <- put -< s + 1
  b <- put -< s + 1
  returnA -< a - b

instance Show (StateEff s a b) where
  show Get = "Get"
  show Put = "Put"

getput :: FreerArrow (StateEff s) a b -> FreerArrow (StateEff s) a b
getput (Comp f Get (Comp IdBridge Put k)) = Comp f Get k
getput (Comp f e k) = Comp f e $ getput k
getput x = x

getput_echo_Int :: FreerArrow (StateEff Int) () Int
getput_echo_Int = getput echo

getput_echo_Int_StateA :: StateA Int () Int
getput_echo_Int_StateA = interp handleState getput_echo_Int

getput_echo_pure :: Int -> Int
getput_echo_pure = execState ((runKleisli . unStateA $ getput_echo_Int_StateA) ())

