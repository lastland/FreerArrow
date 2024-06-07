module Examples.Countdown where

import qualified Control.Monad.State.MonadState      as S
import qualified Control.Monad.Freer.FreerMonad      as M
import qualified Control.Monad.Freer.FreerMonadFinal as F
import qualified Control.Arrow.Freer.FreerArrowFinal as AF
import           Control.Category
import           Control.Arrow
import           Control.Arrow.State.ArrowState
import           Control.Arrow.State.AState
import           Control.Arrow.Freer.FreerArrowChoice
import           Control.Monad.State hiding (get, put)
import           Control.Monad.State.StateEff
import           Control.Monad.Freer.Sum1()
import           Data.Profunctor
import           Prelude hiding (id, (.))

countM :: M.FreerMonad (StateEff1 Int) Int 
countM = do
  n <- S.get
  if n == 0 then return n
  else S.put (n - 1) >> countM

countMF :: F.FreerMonad (StateEff1 Int) Int 
countMF = do
  n <- S.get
  if n == 0 then return n
  else S.put (n - 1) >> countMF

-- This does not work because it's a piece of code with an infinite length!
countA :: FreerArrowChoice (StateEff Int) Int Int
countA = go
  where go = get >>> arr (\n -> if n <= 0 then Left n else Right n) >>>
             (id ||| (lmap (\x -> x - 1) put >>> countA))

compileA :: AState Int Int Int
compileA = interp handleState countA

compileM :: State Int Int
compileM = M.interp handleState1 countM

compileMF :: State Int Int
compileMF = F.runFreer countMF handleState1 
