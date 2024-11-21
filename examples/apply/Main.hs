{-# LANGUAGE EmptyDataDeriving #-}
{-# LANGUAGE TypeOperators     #-}
{-# LANGUAGE RankNTypes        #-}
{-# LANGUAGE EmptyCase         #-}
{-# LANGUAGE GADTs             #-}

module Main (main) where

import Data.Profunctor
import Control.Arrow
import Control.Arrow.Freer.FreerArrow
import qualified Control.Arrow.Freer.FreerArrowApply as AA

data Void2 a b
  deriving Show

instance Profunctor Void2 where
  dimap _ _ v = case v of {}

absurd2 :: Void2 :-> p
absurd2 v = case v of {}

ex1 :: AA.FreerArrowApply Void2 (Int, Int) Int
ex1 = arr (\(x, y) -> (arr (+x), y)) >>> app

data PrintE x y where
  Print :: Show a => PrintE a ()

interpWriterIO :: PrintE :-> Kleisli IO
interpWriterIO Print = Kleisli print

liftApply :: FreerArrow e :-> AA.FreerArrowApply e
liftApply (Hom f) = AA.Hom f
liftApply (Comp f g x y) = AA.Comp f g x (liftApply y)

ex2 :: AA.FreerArrowApply PrintE (Int, Int) ()
ex2 = AA.interp absurd2 ex1 >>> AA.embed Print

ex3 :: AA.FreerArrowApply (Kleisli IO) (Int, Int) ()
ex3 = AA.interp (rmap AA.embed interpWriterIO) ex2

ex4 :: Kleisli IO (Int, Int) ()
ex4 = AA.interp id ex3

main :: IO ()
main = runKleisli ex4 (5, 6)

