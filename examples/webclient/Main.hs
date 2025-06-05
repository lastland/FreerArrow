{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeOperators #-}

module Main where

import Control.Arrow.Freer.FreerChoiceArrow
import Data.Kind
import Data.Profunctor
import Control.Arrow
import Control.Arrow.State.ArrowMapState

data URL

data WebServiceOps :: Type -> Type -> Type where
  Get  :: URL -> [String] -> WebServiceOps () String
  Post :: URL -> [String] -> WebServiceOps String ()

get :: URL -> [String] -> FreerChoiceArrow WebServiceOps () String
get url params = embed $ Get url params

post :: URL -> [String] -> FreerChoiceArrow WebServiceOps String ()
post url params = embed $ Post url params

echo :: URL -> URL -> [String] -> FreerChoiceArrow WebServiceOps () ()
echo url1 url2 params = get url1 params >>> post url2 params

handleWebState :: ArrowIndexedMapState (URL, [String]) String ar => WebServiceOps :-> ar
handleWebState (Get url params) = getIM (url, params)
handleWebState (Post url params) = putIM (url, params) >>^ const ()

-- handleWebServiceOps :: WebServiceOps :-> Kleisli IO
-- handleWebServiceOps = _

main :: IO ()
main = pure ()

