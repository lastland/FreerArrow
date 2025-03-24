{-# LANGUAGE Arrows                #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE KindSignatures        #-}

module Examples.ReadWrite where

import Control.Category
import Control.Arrow
import Control.Arrow.Freer.FreerArrowRouter
import Control.Arrow.Freer.Router
import Prelude hiding ((.), id)

data StoreE k v where
  get :: StoreE k v
  put :: StoreE k ()

type StoreA = FreerArrow StoreE

getget :: StoreA k (v,v) -> StoreA k (v,v)
getget (Comp _ _ _)

