{-# LANGUAGE RankNTypes       #-}
{-# LANGUAGE FlexibleContexts #-}

module Examples.Compare where

import qualified Examples.State  as A
import qualified Examples.StateM as M
import           Control.Arrow
import           Control.Arrow.ArrowState
import           Control.Arrow.Freer.FreerArrow
import           Control.Concurrent.Async
import           Control.Monad.State
import           Data.Profunctor
import           System.TimeIt
import           System.IO

num :: Int
num = 10000000

incNA :: Int -> FreerArrow (A.StateEff Int) Int Int
incNA n | n > 0    = getState >>> lmap (+1) setState >>> incNA (n - 1)
        | otherwise = getState

incNM :: Int -> M.FreerMonad (M.StateMEff Int) Int
incNM n | n > 0     = (+1) <$> get >>= put >> incNM (n - 1)
        | otherwise = get 

compileA :: A.AState Int Int Int
compileA = A.interpState (incNA num)

interpAConcurrently :: (Profunctor arr, Arrow arr) =>
                       (forall a b. e a b -> arr a b) ->
                       FreerArrow e x y -> IO (arr x y)
interpAConcurrently _       (Hom f) = pure $ arr f
interpAConcurrently handler (Comp f g x y) = do
  (a, b) <- concurrently (pure $ dimap f g (first (handler x)))
                         (interpAConcurrently handler y) 
  pure (a >>> b)

compileAConcurrently :: IO (A.AState Int Int Int)
compileAConcurrently = interpAConcurrently A.handleState (incNA num)

compileM :: State Int Int
compileM = M.interp M.handleState (incNM num)

runA :: Int -> A.AState Int Int Int -> (Int, Int)
runA n a = A.runState a 0 n 
  
runM :: Int -> State Int Int -> (Int, Int)
runM n m = runState m n

compare :: IO ()
compare = do
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
