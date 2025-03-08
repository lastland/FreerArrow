{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE BangPatterns #-}

module Examples.Countdown where

import qualified Control.Monad.State.MonadState       as S
import qualified Control.Monad.Freer.FreerMonad       as M
import qualified Control.Monad.Freer.FreerMonadFinal  as F
import qualified Control.Arrow.Freer.FreerChoiceArrow as AC
import qualified Control.Arrow.Freer.FreerArrowRouter as AR
import qualified Control.Arrow.Freer.FreerArrowOps    as AO
import           Control.Arrow.Freer.Elgot
import qualified Control.Arrow.Freer.ElgotFinal       as EF
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
  

countA :: Elgot AC.FreerChoiceArrow (StateEff Int) Int Int
countA =
  let go :: AC.FreerChoiceArrow (StateEff Int) Int (Either Int Int)
      !go = get >>> arr (\n -> if n <= 0 then Left n else Right n) >>>
            (right $ lmap (\x -> x - 1) put) in
    Elgot go id

countAR :: Elgot AR.FreerArrow (StateEff Int) Int Int
countAR =
  let go :: AR.FreerArrow (StateEff Int) Int (Either Int Int)
      !go = get >>> arr (\n -> if n <= 0 then Left n else Right n) >>>
            (right $ lmap (\x -> x - 1) put) in
    Elgot go id

countAO :: Elgot AO.FreerArrowOps (StateEff Int) Int Int
countAO =
  let go :: AO.FreerArrowOps (StateEff Int) Int (Either Int Int)
      !go = get >>> arr (\n -> if n <= 0 then Left n else Right n) >>>
            (id +++ lmap (\x -> x - 1) put) in
    Elgot go id

countAO' :: ElgotC (AState Int) Int Int
countAO' =
  let body :: AO.FreerArrowOps (StateEff Int) Int (Either Int Int)
      body = get >>> arr (\n -> if n <= 0 then Left n else Right n) >>>
             (id +++ lmap (\x -> x - 1) put) in
  let go :: AState Int Int (Either Int Int)
      !go = AO.interp handleState body in
    ElgotC go id
    

countAEF :: EF.Elgot AC.FreerChoiceArrow (StateEff Int) Int Int
countAEF =
  let go :: AC.FreerChoiceArrow (StateEff Int) Int (Either Int Int)
      !go = get >>> arr (\n -> if n <= 0 then Left n else Right n) >>>
            (right $ lmap (\x -> x - 1) put) in
    EF.elgot go id

compileA :: AState Int Int Int
compileA = interp (AC.interp handleState) countA

compileAR :: AState Int Int Int
compileAR = interp (AR.interp handleState) countAR

compileAO :: AState Int Int Int
compileAO = interp (AO.interp handleState) countAO

compileAO' :: AState Int Int Int
compileAO' = interpC countAO'

compileAEF :: AState Int Int Int
compileAEF = EF.runElgot countAEF (AC.interp handleState)

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
