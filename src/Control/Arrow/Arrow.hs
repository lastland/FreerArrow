{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
module Control.Arrow.Arrow where

import Prelude hiding (id, (.))
import Data.Kind

{-- begin Arrows --}
class Profunctor (p :: Type -> Type -> Type) where
  dimap :: (a -> b) -> (c -> d) -> p b c -> p a d

class Profunctor p => StrongProfunctor p where
  first' :: p a b -> p (a, c) (b, c)

class Category (cat :: k -> k -> Type) where
  id  :: forall (a :: k). cat a a
  (.) :: forall (b :: k) (c :: k) (a :: k).
         cat b c -> cat a b -> cat a c
         
class Category a => PreArrow a where
  arr :: (b -> c) -> a b c

class PreArrow a => Arrow a where
  first :: a b c -> a (b, d) (c, d)

-- PreArrows are Profunctors
instance PreArrow a => Profunctor a where
  dimap f g a = arr f >>> a >>> arr g

-- Arrows are StrongProfunctors
instance Arrow a => StrongProfunctor a where
  first' = first

-- A commonly used operator for categories
(>>>) :: forall k (a :: k) (b :: k) (c :: k) (cat :: k -> k -> Type).
  Category cat => cat a b -> cat b c -> cat a c
(>>>) = flip (.)
{-- end Arrows --}
