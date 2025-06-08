{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeOperators #-}

module Main where

import Prelude hiding (id, (.))
import Control.Arrow.Freer.FreerArrow
import Control.Arrow.Freer.FreerChoiceArrow hiding (embed)
import qualified Control.Arrow.Freer.FreerChoiceArrow as C (embed)
import Control.Arrow.Freer.Elgot 
import Data.Kind
import Data.Profunctor
import Control.Category
import Control.Arrow
import Control.Arrow.State.ArrowMapState

data URL

data WebServiceOps :: Type -> Type -> Type where
  Get  :: URL -> [String] -> WebServiceOps () String
  Post :: URL -> [String] -> WebServiceOps String ()

get :: URL -> [String] -> FreerArrow WebServiceOps () String
get url params = embed $ Get url params

post :: URL -> [String] -> FreerArrow WebServiceOps String ()
post url params = embed $ Post url params

echo :: URL -> URL -> [String] -> FreerArrow WebServiceOps () ()
echo url1 url2 params = get url1 params >>> post url2 params

postNTimes :: URL -> [String] -> String ->
              Elgot FreerChoiceArrow WebServiceOps Int ()
postNTimes url params body =
  Elgot go id

postDepends :: URL -> [String] -> String ->
               ElgotFull FreerChoiceArrow WebServiceOps () ()
postDepends url params body =
  ElgotFull $ C.embed (Get url params) >>> arr read
            $ go id
  where
    go :: FreerChoiceArrow WebServiceOps Int (Either () Int)
    go = arr (\n -> if n <= 0 then Left () else Right (n - 1)) >>>
             (id +++ (arr (\n -> (body, n)) >>> first (C.embed $ Post url params) >>> arr snd))

handleWebState :: ArrowIndexedMapState (URL, [String]) String ar => WebServiceOps :-> ar
handleWebState (Get url params) = getIM (url, params)
handleWebState (Post url params) = putIM (url, params) >>^ const ()

handleWebStateFreer :: WebServiceOps :-> FreerArrow (IndexedMapStateEff (URL, [String]) String)
handleWebStateFreer = handleWebState

-- handleWebServiceOps :: WebServiceOps :-> Kleisli IO
-- handleWebServiceOps = _

main :: IO ()
main = pure ()

