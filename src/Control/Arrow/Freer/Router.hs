{-# LANGUAGE GADTs                 #-}

module Control.Arrow.Freer.Router where

import Data.Profunctor
import Data.Functor.Contravariant

data Router a b z x where
  IdRouter :: Router x z z x
  LmapRouter :: (x -> a) -> Router a z z x
  FstIdRouter :: Router a b (b, c) (a, c) 
  FstLmapRouter :: (x -> (a, c)) -> Router a b (b, c) x

instance Contravariant (Router a b z) where
  contramap f IdRouter = LmapRouter f
  contramap f (LmapRouter g) = LmapRouter (g . f)
  contramap f FstIdRouter = FstLmapRouter f
  contramap f (FstLmapRouter g) = FstLmapRouter (g . f)

route :: Strong p => Router a b z x -> p a b -> p x z
route IdRouter = id
route (LmapRouter f) = lmap f
route FstIdRouter = first'
route (FstLmapRouter f) = lmap f . first'
