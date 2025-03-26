{-# LANGUAGE Arrows                #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE KindSignatures        #-}

module Examples.MapState where

import Control.Category
import Control.Arrow.Freer.Bridge
import Control.Arrow.Freer.FreerArrowBridge
import Control.Arrow.State.ArrowMapState
import Prelude hiding ((.), id)

-- -- |- A program that reads from the state and writes back the state.
-- echo :: ArrowIndexedMapState k v arr => k -> arr () v
-- echo k = getIM k >>> putIM k

getget :: FreerArrow (IndexedMapStateEff k v) a b -> FreerArrow (IndexedMapStateEff k v) a b
getget (Comp _ (GetIM _) (Comp IdBridge (GetIM k2) c)) = Comp IdBridge (GetIM k2) c
getget (Comp f e c) = Comp f e $ getget c
getget x = x

getput :: Eq k => FreerArrow (IndexedMapStateEff k v) a b -> FreerArrow (IndexedMapStateEff k v) a b
getput (Comp _ (GetIM k) (Comp IdBridge (PutIM k') c))
  | k == k' = Comp IdBridge (GetIM k) c
getput (Comp f e c) = Comp f e $ getput c
getput x = x

putget :: Eq k => FreerArrow (IndexedMapStateEff k v) a b -> FreerArrow (IndexedMapStateEff k v) a b
-- Note the use of IdBridge here; we can't have an arbitrary bridge on the left
putget (Comp IdBridge (PutIM k) (Comp IdBridge (GetIM k') c))
  | k == k' = Comp IdBridge (PutIM k) c
putget (Comp f e c) = Comp f e $ putget c
putget x = x

putput :: Eq k => FreerArrow (IndexedMapStateEff k v) a b -> FreerArrow (IndexedMapStateEff k v) a b
putput (Comp f (PutIM k1) (Comp IdBridge (PutIM k2) c))
  | k1 == k2  = Comp f (PutIM k1) c
  -- otherwise, fall through; writes to different keys still need to happen
putput (Comp f e c) = Comp f e $ putput c
putput x = x

echo :: k -> FreerArrow (IndexedMapStateEff k v) () v
echo k = Comp IdBridge (GetIM k) $
         Comp IdBridge (PutIM k) id

echo_Int :: Int -> FreerArrow (IndexedMapStateEff Int Int) () Int
echo_Int = echo

getput_echo_Int :: Int -> FreerArrow (IndexedMapStateEff Int Int) () Int
getput_echo_Int x = getput $ echo_Int x

getput_echo_Int_StateA :: Int -> MapStateA Int Int () Int
getput_echo_Int_StateA x = interp handleIndexedMapState $ getput_echo_Int x

