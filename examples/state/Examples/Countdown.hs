{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE FlexibleContexts #-}

module Examples.Countdown where

import qualified Control.Monad.State.MonadState       as S
import qualified Control.Monad.Freer.FreerMonad       as M
import qualified Control.Monad.Freer.FreerMonadFinal  as F
import qualified Control.Arrow.Freer.FreerArrowFinal  as AF
import qualified Control.Arrow.Freer.FreerArrowChoice as AC
import           Control.Arrow.Freer.Elgot
import           Control.Category
import           Control.Arrow
import           Control.Arrow.State.ArrowState
import           Control.Arrow.State.AState
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

countME :: Elgot1 M.FreerMonad (StateEff1 Int) Int Int
countME = Elgot1 (\_ -> do
                      n <- S.get
                      if n == 0 then return $ Left n
                      else (S.put (n - 1) >> (return $ Right (n - 1)))) return

countMFE :: Elgot1 F.FreerMonad (StateEff1 Int) Int Int
countMFE = Elgot1 (\_ -> do
                      n <- S.get
                      if n == 0 then return $ Left n
                      else (S.put (n - 1) >> (return $ Right (n - 1)))) return 
  

countA :: Elgot AC.FreerArrowChoice (StateEff Int) Int Int
countA = Elgot go id
  where go :: AC.FreerArrowChoice (StateEff Int) Int (Either Int Int)
        go = get >>> arr (\n -> if n <= 0 then Left n else Right n) >>>
             (id +++ lmap (\x -> x - 1) put)

compileA :: AState Int Int Int
compileA = interp (AC.interp handleState) countA

compileM :: State Int Int
compileM = M.interp handleState1 countM

compileMF :: State Int Int
compileMF = F.runFreer countMF handleState1 

compileME :: State Int Int
compileME = interp1 (M.interp handleState1) countME 0

compileMFE :: State Int Int
compileMFE = interp1 f countMFE 0
  where f :: forall m a. MonadState Int m => F.FreerMonad (StateEff1 Int) a -> m a
        f m = F.runFreer m handleState1
