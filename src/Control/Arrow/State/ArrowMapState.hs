{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}

module Control.Arrow.State.ArrowMapState where

import Control.Arrow
import Control.Arrow.Freer.FreerArrow as FA
import Control.Arrow.Freer.FreerChoiceArrow as FC
import Control.Arrow.Freer.FreerArrowBridge as FB
import Data.Kind
import Control.Monad.State (State)
import qualified Control.Monad.State as M
import Control.Category
import Data.Profunctor
import Prelude hiding (id, (.))

newtype Map k v = Map { mapLookup :: k -> v }
  deriving (Category, Arrow, ArrowChoice, ArrowApply, Profunctor, Strong, Choice)

mapLookup' :: k -> Map k v -> v
mapLookup' k m = mapLookup m k

mapUpdate :: Eq k => k -> v -> Map k v -> Map k v
mapUpdate k v m = Map $ \k' -> if k == k' then v else mapLookup m k'

class Arrow a => ArrowMapState k v a where
  getM :: a k v
  putM :: a (k, v) v

class Arrow a => ArrowIndexedMapState k v a where
  getIM :: k -> a b v
  putIM :: k -> a v v

newtype MapStateA k v a b = MapStateA { unMapStateA :: Kleisli (State (Map k v)) a b }
  deriving (Category, Arrow, ArrowChoice, ArrowApply, Profunctor, Strong, Choice)

-- |- MapStateA is an ArrowState
instance Eq k => ArrowMapState k v (MapStateA k v) where
  getM = MapStateA $ Kleisli $ \k -> mapLookup' k <$> M.get
  putM = MapStateA $ Kleisli $ \(k, v) -> mapUpdate k v <$> M.get >> pure v

-- |- IndexedMapStateA is an ArrowState
instance Eq k => ArrowIndexedMapState k v (MapStateA k v) where
  getIM k = MapStateA . Kleisli $ const $ mapLookup' k <$> M.get
  putIM k = MapStateA . Kleisli $ \v -> mapUpdate k v <$> M.get >> pure v

-- |- An ADT for stateful effect.
data MapStateEff :: Type -> Type -> Type -> Type -> Type where
  GetM :: MapStateEff k v k v
  PutM :: MapStateEff k v (k, v) v

data IndexedMapStateEff :: Type -> Type -> Type -> Type -> Type where
  GetIM :: k -> IndexedMapStateEff k v a v
  PutIM :: k -> IndexedMapStateEff k v v v

instance ArrowMapState k v (FA.FreerArrow (MapStateEff k v)) where
  getM = FA.embed GetM
  putM = FA.embed PutM

instance ArrowIndexedMapState k v (FA.FreerArrow (IndexedMapStateEff k v)) where
  getIM k = FA.embed $ GetIM k
  putIM k = FA.embed $ PutIM k

instance ArrowMapState k v (FB.FreerArrow (MapStateEff k v)) where
  getM = FB.embed GetM
  putM = FB.embed PutM

instance ArrowIndexedMapState k v (FB.FreerArrow (IndexedMapStateEff k v)) where
  getIM k = FB.embed $ GetIM k
  putIM k = FB.embed $ PutIM k

instance ArrowMapState k v (FC.FreerChoiceArrow (MapStateEff k v)) where
  getM = FC.embed GetM
  putM = FC.embed PutM

instance ArrowIndexedMapState k v (FC.FreerChoiceArrow (IndexedMapStateEff k v)) where
  getIM k = FC.embed $ GetIM k
  putIM k = FC.embed $ PutIM k

instance Show (MapStateEff k v a b) where
  show GetM = "Get"
  show PutM = "Put"

instance Show k => Show (IndexedMapStateEff k v a b) where
  show (GetIM k) = "Get " ++ show k
  show (PutIM k) = "Put " ++ show k

handleMapState :: ArrowMapState k v a => MapStateEff k v x y -> a x y
handleMapState GetM = getM
handleMapState PutM = putM

handleIndexedMapState :: ArrowIndexedMapState k v a => IndexedMapStateEff k v x y -> a x y
handleIndexedMapState (GetIM k) = getIM k
handleIndexedMapState (PutIM k) = putIM k

