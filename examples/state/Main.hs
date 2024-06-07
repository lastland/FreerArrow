{-# LANGUAGE RankNTypes       #-}
{-# LANGUAGE FlexibleContexts #-}

module Main where

import qualified Control.Monad.State.MonadState      as S
import qualified Control.Monad.Freer.FreerMonad      as M
import qualified Control.Monad.Freer.FreerMonadFinal as F
import qualified Control.Arrow.Freer.FreerArrowFinal as AF
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
num = 100000000

incNA :: Int -> FreerArrow (StateEff Int) Int Int
incNA n | n > 0     = get >>> lmap (+1) put >>> incNA (n - 1)
        | otherwise = get

incNAF :: Int -> AF.FreerArrow (StateEff Int) Int Int
incNAF n | n > 0     = get >>> lmap (+1) put >>> incNAF (n - 1)
         | otherwise = get

incNM :: Int -> M.FreerMonad (StateEff1 Int) Int
incNM n | n > 0     = ((+1) :: Int -> Int) <$> S.get >>= S.put >> incNM (n - 1)
        | otherwise = S.get 

incNF :: Int -> F.FreerMonad (StateEff1 Int) Int
incNF n | n > 0     = ((+1) :: Int -> Int) <$> S.get >>= S.put >> incNF (n - 1)
        | otherwise = S.get 

compileA :: AState Int Int Int
compileA = interp handleState (incNA num)

compileAF :: AState Int Int Int
compileAF = AF.runFreer (incNAF num) handleState

interpAConcurrently :: (Profunctor arr, Arrow arr) =>
                       (forall a b. e a b -> arr a b) ->
                       FreerArrow e x y -> IO (arr x y)
interpAConcurrently _       (Hom f) = pure $ arr f
interpAConcurrently handler (Comp f g x y) = do
  (a, b) <- concurrently (pure $ dimap f g (first (handler x)))
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
  
runM :: Int -> State Int Int -> (Int, Int)
runM n m = runState m n
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

testCountDown :: IO ()
testCountDown = defaultMain [
  bgroup "countdown" [ bench "A 1000"    $ nf (runAState Count.compileA 0) 1000
                     , bench "A 10000"   $ nf (runAState Count.compileA 0) 10000
                     , bench "A 100000"  $ nf (runAState Count.compileA 0) 100000
                     , bench "M 1000"    $ nf (runState Count.compileM) 1000
                     , bench "M 10000"   $ nf (runState Count.compileM) 10000
                     , bench "M 100000"  $ nf (runState Count.compileM) 100000
                     , bench "F 1000"    $ nf (runState Count.compileMF) 1000
                     , bench "F 10000"   $ nf (runState Count.compileMF) 10000
                     , bench "F 100000"  $ nf (runState Count.compileMF) 100000
                     ]
  ]

main :: IO ()
main = testCountDown
