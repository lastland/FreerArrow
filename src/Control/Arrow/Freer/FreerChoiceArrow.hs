{-# LANGUAGE LambdaCase     #-}
{-# LANGUAGE TypeOperators  #-}
{-# LANGUAGE RankNTypes     #-}
{-# LANGUAGE GADTs          #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE QuantifiedConstraints #-}

module Control.Arrow.Freer.FreerChoiceArrow where


import Control.Category
import Control.Arrow
import Data.Profunctor
import Prelude hiding (id, (.))

-- |- Freer arrow choice. Inspired by:
-- [https://www.reddit.com/r/haskell/comments/p7grsq/comment/h9k2anl/?utm_source=share&utm_medium=web3x&utm_name=web3xcss&utm_term=1&utm_content=share_button]
{-- begin FreerChoiceArrow --}
data FreerChoiceArrow e x y where
  Hom :: (x -> y) -> FreerChoiceArrow e x y
  Comp :: (x -> Either (a, c) w) ->
          e a b ->
          FreerChoiceArrow e (Either (b, c) w) y ->
          FreerChoiceArrow e x y
{-- end FreerChoiceArrow --}

-- |- This is called overCount because with FreerChoiceArrow, there is no
-- guarantee that the effect will happen. Instead, the static analyzer gives us
-- the worst case count---how many times effect would appear when all effects
-- happen. (It is not clear to me how to define an underCount---this is possible
-- with selective functor but I don't see how with FreerChoiceArrow.)
overCount :: FreerChoiceArrow e x y -> Int
overCount (Hom _) = 0
overCount (Comp _  _ y) = 1 + overCount y

embed :: e x y -> FreerChoiceArrow e x y
embed f = Comp (\x -> Left (x, ())) f
                (arr (\case
                         Left (b, _) -> b
                         Right b -> b))
                
assoc :: ((x, y), z) -> (x, (y, z))
assoc ((x, y), z) = (x, (y, z))

unassoc :: (x, (y, z)) -> ((x, y), z)
unassoc (x, (y, z)) = ((x, y), z)

distr :: (Either (a, b) c, d) -> Either ((a, b), d) (c, d)
distr (Left (a, b), d) = Left ((a, b), d)
distr (Right c, d) = Right (c, d)

undistr :: Either ((a, b), d) (c, d) -> (Either (a, b) c, d)
undistr (Left ((a, b), d)) = (Left (a, b), d)
undistr (Right (c, d)) = (Right c, d)

assocsum :: Either (Either a b) c -> Either a (Either b c)
assocsum (Left (Left x)) = Left x
assocsum (Left (Right y)) = Right (Left y)
assocsum (Right z) = Right (Right z)

unassocsum :: Either a (Either b c) -> Either (Either a b) c
unassocsum (Left x) = Left $ Left x
unassocsum (Right (Left y)) = Left $ Right y
unassocsum (Right (Right z)) = Right z

instance Arrow (FreerChoiceArrow e) where
  arr = Hom

  first = first'

instance ArrowChoice (FreerChoiceArrow e) where
  left = left'

instance Profunctor (FreerChoiceArrow e) where
  dimap f g (Hom h) = Hom (g . h . f)
  dimap f g (Comp f' x y) = Comp (f' . f) x (dimap id g y)

  lmap f (Hom h) = Hom (h . f)
  lmap f (Comp f' x y) = Comp (f' . f) x y

{-- begin Strong_FreerChoiceArrow --}
instance Strong (FreerChoiceArrow e) where
  first' (Hom f) = Hom $ first f
  first' (Comp f a b) = Comp (first f >>> distr >>> left assoc)
                          a (lmap (left unassoc >>> undistr) (first' b))
{-- end Strong_FreerChoiceArrow --}

{-- begin Choice_FreerChoiceArrow --}
instance Choice (FreerChoiceArrow e) where
  left' (Hom f) = Hom $ left f
  left' (Comp f a b) = Comp (left f >>> assocsum)
                        a (lmap unassocsum (left' b))
{-- end Choice_FreerChoiceArrow --}

instance Category (FreerChoiceArrow e) where
  id = Hom id

  f . (Hom g)          = lmap g f
  f . (Comp f' x y) = Comp f' x (f . y)

instance (forall a b. Show (e a b)) => Show (FreerChoiceArrow e x y) where
  show (Hom _) = "Hom"
  show (Comp _ e c) = "(" ++ show e ++ " >>> " ++ show c ++ ")"

-- |- Freer choice arrows can be interpreted into any choice arrows, as long as
-- we can provide an effect handler.
interp :: (Profunctor arr, ArrowChoice arr) =>
  (e :-> arr) -> FreerChoiceArrow e x y -> arr x y
interp _       (Hom f) = arr f
interp handler (Comp f x y) = lmap f (left (first (handler x))) >>>
                              interp handler y
