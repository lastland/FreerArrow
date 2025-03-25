{-# LANGUAGE GADTs                 #-}

module Control.Arrow.Freer.Bridge where

import Data.Profunctor
import Data.Functor.Contravariant

data Bridge x a b y where
  IdBridge :: Bridge x x y y

  FirstBridge :: Bridge x a b y -> Bridge (x, c) a b (y, c)
  SecondBridge :: Bridge x a b y -> Bridge (c, x) a b (c, y)
  
  LeftBridge  :: Bridge x a b y -> Bridge (Either x c) a b (Either y c)
  RightBridge :: Bridge x a b y -> Bridge (Either c x) a b (Either c y)

  LmapBridge :: (w -> x) -> Bridge x a b y -> Bridge w a b y

cmapBridge :: (w -> x) -> Bridge x a b y -> Bridge w a b y
cmapBridge f (LmapBridge g r) = LmapBridge (g . f) r
cmapBridge f r = LmapBridge f r

-- cmapRouterBridge :: Router w x -> Bridge x a b y -> Bridge w a b y
-- cmapRouterBridge f (LmapBridge g r) = LmapBridge (g . route f) r
-- cmapRouterBridge f (LRouterBridge g r) = LRouterBridge (CompRoute f g) r
-- cmapRouterBridge f r = LRouterBridge f r

-- route :: Router x y -> x -> y
-- route IdRoute = id
-- route LeftRot  = unassoc
-- route RightRot = assoc
-- route FstRoute = fst
-- route SndRoute = snd
-- route DupRoute = dup
-- route SwapRoute = swap
-- route (AppFirst r) = first' (route r) 
-- route (AppSecond r) = second' (route r)
-- route (AppLeft r) = left' (route r) 
-- route (AppRight r) = right' (route r)
-- route (CompRoute r1 r2) = route r2 . route r1
-- route (FunRoute f) = f

bridge :: (Strong p, Choice p) => Bridge x a b y -> p a b -> p x y
bridge IdBridge = id
bridge (FirstBridge r) = first' . bridge r
bridge (SecondBridge r) = second' . bridge r
bridge (LeftBridge r) = left' . bridge r
bridge (RightBridge r) = right' . bridge r
bridge (LmapBridge f r) = lmap f . bridge r

-- | We don't use this. This is just to show that Router is a contravariant
-- functor.
newtype ContraBridge a b y x = ContraBridge (Bridge x a b y) 

instance Contravariant (ContraBridge a b y) where
  contramap f (ContraBridge r) = ContraBridge $ cmapBridge f r

-- instance Show (Router x y) where
--   show IdRoute = "id"
--   show LeftRot = "LRot"
--   show RightRot = "RRot"
--   show FstRoute = "Fst"
--   show SndRoute = "Snd"
--   show DupRoute = "Dup"
--   show SwapRoute = "Swap"
--   show (AppFirst r) = "{AppFirst{" ++ show r ++ "}"
--   show (AppSecond r) = "AppSecond{" ++ show r ++ "}"
--   show (AppLeft r) = "AppLeft{" ++ show r ++ "}"
--   show (AppRight r) = "AppRight{" ++ show r ++ "}"
--   show (CompRoute r1 r2) = "{" ++ show r1 ++ " >>> " ++ show r2 ++ "}"
--   show (FunRoute _) = "Fun"

instance Show (Bridge x a b y) where
  show IdBridge = "_"
  show (FirstBridge r) = "First{" ++ show r ++ "}"
  show (SecondBridge r) = "Second{" ++ show r ++ "}"
  show (LeftBridge r) = "Left{" ++ show r ++ "}"
  show (RightBridge r) = "Right{" ++ show r ++ "}"
  -- show (LRouterBridge f r) = "LRouter{" ++ show f ++ " >>> " ++ show r ++ "}"
  show (LmapBridge _ r) = "LMap{" ++ show r ++ "}"

