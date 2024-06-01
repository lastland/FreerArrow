{-# LANGUAGE FlexibleContexts #-}

module Imp.Arrow.FreeImp where

import Control.Arrow
import Control.Arrow.Freer.FreerArrow
import Control.Arrow.Freer.Sum2
import Control.Arrow.State.ArrowState
import Data.Map
import Imp.AST

aeval :: Inj2 (StateEff (Map Var Int)) e => AExp -> FreerArrow e a Int
aeval (ANum n) = arr (const n) 
aeval (AId v)  = get >>> arr (\env -> findWithDefault 0 v env)
