module Component.Container where

import Prologue
import Data.Array (singleton)
import Halogen.Css (classNames)
import Halogen.HTML as HH

type ContainerOf
  = forall r w i.
    HH.Node ( class :: String | r ) w i ->
    Array String ->
    HH.HTML w i ->
    HH.HTML w i

type Container
  = forall w i.
    Array String ->
    HH.HTML w i ->
    HH.HTML w i

container :: Array String -> ContainerOf
container baseClasses node extraClasses = node [ classNames $ baseClasses <> extraClasses ] <<< singleton
