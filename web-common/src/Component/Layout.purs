module Component.Layout where

import Prologue
import Halogen.Css (classNames)
import Halogen.HTML as HH

type LayoutOf
  = forall r w i.
    HH.Node ( class :: String | r ) w i ->
    Array String ->
    Array (HH.HTML w i) ->
    HH.HTML w i

type Layout
  = forall w i.
    Array String ->
    Array (HH.HTML w i) ->
    HH.HTML w i

layout :: Array String -> LayoutOf
layout baseClasses node extraClasses = node [ classNames $ baseClasses <> extraClasses ]
