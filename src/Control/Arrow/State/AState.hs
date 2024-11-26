{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE LambdaCase            #-}

module Control.Arrow.State.AState where

import Control.Category
import Control.Arrow
import Control.Arrow.State.ArrowState
import Data.Profunctor

-- The following code is adapted from Nicholas Coltharp.

newtype AState s a b = AState { runAState :: a -> s -> (b, s) }

instance Category (AState s) where
  id = AState (,)

  AState f . AState g = AState $ \x s -> uncurry f (g x s)

instance Arrow (AState s) where
  arr f = AState $ \a s -> (f a, s)

  first = first'

instance ArrowChoice (AState s) where
  left = left'

  (AState f) +++ (AState g) =
    AState $ \x s ->
               case x of
                 Left  a -> let (a', s') = f a s in (Left  a', s') 
                 Right b -> let (b', s') = g b s in (Right b', s')

  (AState f) ||| (AState g) =
    AState $ \x s ->
               case x of
                 Left  a -> let (a', s') = f a s in (a', s') 
                 Right b -> let (a', s') = g b s in (a', s')
    

instance ArrowState s (AState s) where
  get = AState $ \_ s -> (s, s)

  put = AState $ \s _ -> (s, s)

instance Profunctor (AState s) where
  dimap f g (AState h) = AState $ \a s ->
    let (b, s') = h (f a) s in (g b, s')

  lmap f (AState h) = AState $ \a s ->
    let (b, s') = h (f a) s in (b, s')
    
instance Strong (AState s) where
  first' (AState f) = AState $ \(a, c) s -> let (b, s') = f a s in ((b, c), s')
  
instance Choice (AState s) where
  left' (AState f) = AState $ \x s ->
    case x of
      Left  a -> let (x', s') = f a s in (Left x', s')
      Right b -> (Right b, s)
