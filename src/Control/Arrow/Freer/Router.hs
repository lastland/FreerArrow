{-# LANGUAGE GADTs                 #-}
module Control.Arrow.Freer.Router where

import Data.Profunctor
import Control.Arrow

data Router x a b z where
  IdRouter :: Router x x z z
  LmapRouter :: (x -> a) -> Router x a z z
  FstIdRouter :: Router (a, c) a b (b, c)
  FstLmapRouter :: (x -> (a, c)) -> Router x a b (b, c)
  
lmapRouter :: (w -> x) -> Router x a b z -> Router w a b z
lmapRouter f IdRouter = LmapRouter f
lmapRouter f (LmapRouter g) = LmapRouter (g . f)
lmapRouter f FstIdRouter = FstLmapRouter f
lmapRouter f (FstLmapRouter g) = FstLmapRouter (g . f) 

route :: (Profunctor arr, Arrow arr) =>
  Router x a b z -> arr a b -> arr x z
route IdRouter = id
route (LmapRouter f) = lmap f
route FstIdRouter = first
route (FstLmapRouter f) = lmap f . first

