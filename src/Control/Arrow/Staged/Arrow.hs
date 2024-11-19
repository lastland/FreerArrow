{-# LANGUAGE MultiParamTypeClasses #-}
module Control.Arrow.Staged.Arrow where

import Language.Haskell.TH
import Control.Category
import Control.Arrow

class Category a => StagedArrow a where
  arrS :: Code Q (b -> c) -> a b c  
  andS :: a b c -> a d e -> a (b, d) (c, e)

class StagedArrow a => StagedArrowChoice a where
  orS :: a b c -> a d e -> a (Either b d) (Either c e)

class (StagedArrow a, Arrow a') => SpliceableArrow a a' where
  splice :: a b c -> a' b c
