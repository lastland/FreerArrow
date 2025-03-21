module Control.Arrow.Routed.ClassesChoice where

import Data.Profunctor
import Control.Arrow.Freer.RouterChoice

class Profunctor p => RoutedProfunctor p where
  dimapR :: Router x a -> Router b y -> p a b -> p x y
  dimapR f g = lmapR f . rmapR g
  
  lmapR :: Router x y -> p y z -> p x z
  lmapR f = dimapR f IdRoute
  rmapR :: Router y z -> p x y -> p x z
  rmapR = dimapR IdRoute
