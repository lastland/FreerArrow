{-# LANGUAGE TupleSections         #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE ImpredicativeTypes    #-}
{-# LANGUAGE TemplateHaskell       #-}

module Control.Arrow.Freer.Staged.FreerWeakArrow where

import Control.Category
import Control.Arrow
import Data.Profunctor
import Prelude hiding (id, (.))
import Language.Haskell.TH

-- |- Freer arrows. This is essentially free arrows (Notions of computation as
-- monoids, Rivas & Jaskelioff, JFP) inlined with free strong profunctors.
{-- begin FreerArrow --}
data FreerArrow e x y where
  Hom   :: Code Q (x -> y) -> FreerArrow e x y
  Comp  :: Code Q (x -> a) -> e a z ->
           FreerArrow e z y -> FreerArrow e x y
{--- end FreerArrow --}

-- A function that counts the number of effects in a freer arrow. This
-- illustrates that some static analysis can be performed on freer arrows. Even
-- if the effect can be stateful, we do not need to provide an initial state.
count :: FreerArrow e x y -> Int
count (Hom _) = 0
count (Comp _ _ y) = 1 + count y

-- The following is what I call a reified arrow. It is free if we define an
-- equality that satisifies arrow laws and profunctor laws.
{--
data ReifiedArrow e x y where
  HomR :: (x -> y) -> ReifiedArrow e x y
  Embed :: e x y -> ReifiedArrow e x y
  CompR :: (x -> (a, c)) -> ((b, c) -> y) ->
    ReifiedArrow e a b -> ReifiedArrow e y z -> ReifiedArrow e x z
--}

-- |- Embed an effect in freer arrows.                        
embed :: e x y -> FreerArrow e x y
embed f = Comp [|| id ||] f idQ

dimapQ :: Code Q (x -> a) -> Code Q (b -> y) -> FreerArrow e a b -> FreerArrow e x y
dimapQ f g (Hom h) = Hom [|| $$g . $$h . $$f ||]
dimapQ f g (Comp f' x y) = Comp [|| $$f' . $$f ||] x (dimapQ [|| id ||] g y)

lmapQ :: Code Q (x -> a) -> FreerArrow e a b -> FreerArrow e x b
lmapQ f (Hom h) = Hom [|| $$h . $$f ||]
lmapQ f (Comp f' x y) = Comp [|| $$f' . $$f ||] x y

idQ :: FreerArrow e a a
idQ = Hom [|| id ||]

instance Category (FreerArrow e) where
  id = Hom [|| id ||]

  f . (Hom g) = lmapQ g f
  f . (Comp f' x y) = Comp f' x (f . y)

-- |- Freer arrows can be interpreted into any arrows, as long as we can provide
-- an effect handler.
interp :: (Profunctor arr, Arrow arr) => (forall a b. e a b -> Code Q (arr a b)) -> FreerArrow e x y -> Code Q (arr x y)
interp _       (Hom f)       = [|| arr $$f ||]
interp handler (Comp f x y)  = [|| lmap $$f $$(handler x) >>> $$(interp handler y) ||]
