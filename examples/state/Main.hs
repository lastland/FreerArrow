{-# LANGUAGE RankNTypes       #-}
{-# LANGUAGE FlexibleContexts #-}

module Main where

import qualified Control.Monad.State.MonadState       as S
import qualified Control.Monad.Freer.FreerMonad       as M
import qualified Control.Monad.Freer.FreerMonadFinal  as F
import qualified Control.Arrow.Freer.FreerArrowFinal  as AF
import qualified Control.Arrow.Freer.FreerArrowSimple as AS
import qualified Control.Arrow.Freer.FreerArrowOps    as AO
import qualified Control.Arrow.Freer.FreerArrowRouter as AR
import           Control.Arrow
import           Control.Arrow.State.ArrowState
import           Control.Arrow.State.AState
import           Control.Arrow.Freer.FreerArrow
import           Control.Concurrent.Async
import           Control.Monad.State hiding (get, put)
import           Control.Monad.State.StateEff
import           Control.Monad.Freer.Sum1()
import           Data.Profunctor
import           Criterion.Main

import qualified Examples.Countdown as Count

num :: Int
num = 10000

incNA :: Int -> FreerArrow (StateEff Int) Int Int
incNA n | n > 0     = get >>> lmap (+1) put >>> incNA (n - 1)
        | otherwise = get

incNAF :: Int -> AF.FreerArrow (StateEff Int) Int Int
incNAF n | n > 0     = get >>> lmap (+1) put >>> incNAF (n - 1)
         | otherwise = get

incNAS :: Int -> AS.FreerArrow (StateEff Int) Int Int
incNAS n | n > 0     = get >>> lmap (+1) put >>> incNAS (n - 1)
         | otherwise = get

incNAO :: Int -> AO.FreerArrowOps (StateEff Int) Int Int
incNAO n | n > 0     = get >>> lmap (+1) put >>> incNAO (n - 1)
         | otherwise = get

incNAR :: Int -> AR.FreerArrow (StateEff Int) Int Int
incNAR n | n > 0     = get >>> lmap (+1) put >>> incNAR (n - 1)
         | otherwise = get

incNM :: Int -> M.FreerMonad (StateEff1 Int) Int
incNM n | n > 0     = S.get >>= S.put . (+(1 :: Int)) >> incNM (n - 1)
        | otherwise = S.get 

incNF :: Int -> F.FreerMonad (StateEff1 Int) Int
incNF n | n > 0     = S.get >>= S.put . (+(1 :: Int)) >> incNF (n - 1)
        | otherwise = S.get 

compileA :: AState Int Int Int
compileA = interp handleState (incNA num)

compileAF :: AState Int Int Int
compileAF = AF.runFreer (incNAF num) handleState

compileAS :: AState Int Int Int
compileAS = AS.interp handleState (incNAS num)

compileAO :: AState Int Int Int
compileAO = AO.interp handleState (incNAO num)

compileAR :: AState Int Int Int
compileAR = AR.interp handleState (incNAR num)

interpAConcurrently :: (Profunctor arr, Arrow arr) =>
                       (forall a b. e a b -> arr a b) ->
                       FreerArrow e x y -> IO (arr x y)
interpAConcurrently _       (Hom f) = pure $ arr f
interpAConcurrently handler (Comp f x y) = do
  (a, b) <- concurrently (pure $ lmap f (first (handler x)))
                         (interpAConcurrently handler y) 
  pure (a >>> b)

compileAConcurrently :: IO (AState Int Int Int)
compileAConcurrently = interpAConcurrently handleState (incNA num)

compileM :: State Int Int
compileM = M.interp handleState1 (incNM num)

compileF :: State Int Int
compileF = F.runFreer (incNF num) handleState1 

runA :: Int -> AState Int Int Int -> (Int, Int)
runA n a = runAState a 0 n

runA5 :: AState Int Int Int -> (Int, Int)
runA5 a = runAState a 0 0 `seq`
          runAState a 0 5 `seq`
          runAState a 0 10 `seq`
          runAState a 0 1000 `seq`
          runAState a 0 500
  
runM :: Int -> State Int Int -> (Int, Int)
runM n m = runState m n

runM5 :: State Int Int -> (Int, Int)
runM5 m = runState m 0 `seq`
          runState m 5 `seq`
          runState m 10 `seq`
          runState m 1000`seq`
          runState m 500

main :: IO ()
main = defaultMain [
  bgroup "inc"       [ bench "A from 0"   $ nf (runA 0) compileA
                     , bench "A from 1"   $ nf (runA 1) compileA
                     , bench "AS from 0"  $ nf (runA 0) compileAS
                     , bench "AS from 1"  $ nf (runA 1) compileAS
                     , bench "AF from 0"  $ nf (runA 0) compileAF
                     , bench "AF from 1"  $ nf (runA 1) compileAF
                     , bench "AO from 0"  $ nf (runA 0) compileAO
                     , bench "AO from 1"  $ nf (runA 1) compileAO
                     , bench "AR from 0"  $ nf (runA 0) compileAR
                     , bench "AR from 1"  $ nf (runA 1) compileAR
                     , bench "M from 0"   $ nf (runM 0) compileM
                     , bench "M from 1"   $ nf (runM 0) compileM
                     , bench "MF from 0"  $ nf (runM 0) compileF
                     , bench "MF from 1"  $ nf (runM 0) compileF
                     ],
  bgroup "inc5"      [ bench "A"   $ nf runA5 compileA
                     , bench "AS"  $ nf runA5 compileAS
                     , bench "AF"  $ nf runA5 compileAF
                     , bench "AO"  $ nf runA5 compileAO
                     , bench "AR"  $ nf runA5 compileAR
                     , bench "M"   $ nf runM5 compileM
                     , bench "MF"  $ nf runM5 compileF
                     ],
  bgroup "countdown" [ bench "A 1000"     $ nf (runAState Count.compileA 0) 1000
                     , bench "A 10000"    $ nf (runAState Count.compileA 0) 10000
                     , bench "A 100000"   $ nf (runAState Count.compileA 0) 100000
                     , bench "AO 1000"    $ nf (runAState Count.compileAO 0) 1000
                     , bench "AO 10000"   $ nf (runAState Count.compileAO 0) 10000
                     , bench "AO 100000"  $ nf (runAState Count.compileAO 0) 100000
                     , bench "AOC 1000"   $ nf (runAState Count.compileAO' 0) 1000
                     , bench "AOC 10000"  $ nf (runAState Count.compileAO' 0) 10000
                     , bench "AOC 100000" $ nf (runAState Count.compileAO' 0) 100000
                     , bench "AR 1000"    $ nf (runAState Count.compileAR 0) 1000
                     , bench "AR 10000"   $ nf (runAState Count.compileAR 0) 10000
                     , bench "AR 100000"  $ nf (runAState Count.compileAR 0) 100000
                     , bench "ARF 1000"    $ nf (runAState Count.compileARF 0) 1000
                     , bench "ARF 10000"   $ nf (runAState Count.compileARF 0) 10000
                     , bench "ARF 100000"  $ nf (runAState Count.compileARF 0) 100000
                     , bench "M 1000"     $ nf (runState Count.compileM) 1000
                     , bench "M 10000"    $ nf (runState Count.compileM) 10000
                     , bench "M 100000"   $ nf (runState Count.compileM) 100000
                     , bench "F 1000"     $ nf (runState Count.compileMF) 1000
                     , bench "F 10000"    $ nf (runState Count.compileMF) 10000
                     , bench "F 100000"   $ nf (runState Count.compileMF) 100000
                     , bench "ME 1000"     $ nf (runState Count.compileME) 1000
                     , bench "ME 10000"    $ nf (runState Count.compileME) 10000
                     , bench "ME 100000"   $ nf (runState Count.compileME) 100000
                     , bench "FE 1000"     $ nf (runState Count.compileMFE) 1000
                     , bench "FE 10000"    $ nf (runState Count.compileMFE) 10000
                     , bench "FE 100000"   $ nf (runState Count.compileMFE) 100000
                     ]
  ]

{--
testInc :: IO ()
testInc = do
  putStrLn "A:"
  let a = compileA
  let s = runA 0 a
  timeIt $ s `seq` pure s
  putStrLn $ "Result: " <> show s
  let s = runA 1 a
  timeIt $ s `seq` pure s
  putStrLn $ "Result: " <> show s
  hFlush stdout
  putStrLn "A(F):"
  let a = compileAF
  timeIt $ a `seq` pure ()
  let s = runA 0 a
  timeIt $ s `seq` pure s
  putStrLn $ "Result: " <> show s
  let s = runA 1 a
  timeIt $ s `seq` pure s
  putStrLn $ "Result: " <> show s
  hFlush stdout
  putStrLn "M:"
  let m = compileM
  timeIt $ m `seq` pure ()
  let r = runM 0 m
  timeIt $ r `seq` pure r
  putStrLn $ "Result: " <> show r
  let r = runM 1 m
  timeIt $ r `seq` pure r
  putStrLn $ "Result: " <> show r
  putStrLn "M(F):"
  let m = compileF
  timeIt $ m `seq` pure ()
  let r = runM 0 m
  timeIt $ r `seq` pure r
  putStrLn $ "Result: " <> show r
  let r = runM 1 m
  timeIt $ r `seq` pure r
  putStrLn $ "Result: " <> show r
--}
