{-# LANGUAGE RankNTypes       #-}
{-# LANGUAGE FlexibleContexts #-}

module Main where

import qualified Control.Monad.State.MonadState      as S
import qualified Control.Monad.Freer.FreerMonad      as M
import qualified Control.Monad.Freer.FreerMonadFinal as F
import           Control.Arrow
import           Control.Arrow.State.ArrowState
import           Control.Arrow.Freer.FreerArrow
import           Control.Concurrent.Async
import           Control.Monad.State hiding (get, put)
import           Control.Monad.State.StateEff
import           Control.Monad.Freer.Sum1()
import           Data.Profunctor
import           System.TimeIt
import           System.IO

num :: Int
num = 40000000

incNA :: Int -> FreerArrow (StateEff Int) Int Int
incNA n | n > 0     = get >>> lmap (+1) put >>> incNA (n - 1)
        | otherwise = get

incNM :: Int -> M.FreerMonad (StateEff1 Int) Int
incNM n | n > 0     = ((+1) :: Int -> Int) <$> S.get >>= S.put >> incNM (n - 1)
        | otherwise = S.get 

incNF :: Int -> F.FreerMonad (StateEff1 Int) Int
incNF n | n > 0     = ((+1) :: Int -> Int) <$> S.get >>= S.put >> incNF (n - 1)
        | otherwise = S.get 

compileA :: StateA Int Int Int
compileA = interp handleState (incNA num)

interpAConcurrently :: (Profunctor arr, Arrow arr) =>
                       (forall a b. e a b -> arr a b) ->
                       FreerArrow e x y -> IO (arr x y)
interpAConcurrently _       (Hom f) = pure $ arr f
interpAConcurrently handler (Comp f g x y) = do
  (a, b) <- concurrently (pure $ dimap f g (first (handler x)))
                         (interpAConcurrently handler y) 
  pure (a >>> b)

compileAConcurrently :: IO (StateA Int Int Int)
compileAConcurrently = interpAConcurrently handleState (incNA num)

compileM :: State Int Int
compileM = M.interp handleState1 (incNM num)

compileF :: State Int Int
compileF = F.runFreer (incNF num) handleState1 

runA :: Int -> StateA Int Int Int -> (Int, Int)
runA n (StateA (Kleisli a)) = runState (a 0) n 
  
runM :: Int -> State Int Int -> (Int, Int)
runM n m = runState m n

main :: IO ()
main = do
  putStrLn "A:"
  let a = compileA
  timeIt $ a `seq` pure ()
  let s = runA 0 a
  timeIt $ s `seq` pure s
  putStrLn $ "Result: " <> show s
  let s = runA 1 a
  timeIt $ s `seq` pure s
  putStrLn $ "Result: " <> show s
  hFlush stdout
  {--
  putStrLn "A (with concurrency):"
  a <- timeIt compileAConcurrently
  let s = runA 0 a
  timeIt $ s `seq` pure s
  putStrLn $ "Result: " <> show s
  let s = runA 1 a
  timeIt $ s `seq` pure s
  putStrLn $ "Result: " <> show s
  hFlush stdout
  --}
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
