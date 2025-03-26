module Control.Arrow.Freer.Translation where

import qualified Control.Arrow.Freer.FreerChoiceArrow as F 
import qualified Control.Arrow.Freer.FreerArrowBridge as B

translate :: B.FreerArrow e x y -> F.FreerChoiceArrow e x y
translate = B.interp F.embed
