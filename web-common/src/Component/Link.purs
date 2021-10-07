module Component.Link (link) where

import Prologue
import Component.Layout (Layout)
import Halogen.Css (classNames)
import Halogen.HTML as HH
import Halogen.HTML.Properties as HP

link :: String -> Layout
link href extraClasses = HH.a [ classNames classes, HP.href href ]
  where
  classes =
    [ "font-semibold"
    , "underline"
    , "hover:text-lightpurple"
    , "active:text-purple"
    , "visited:text-red"
    ]
      <> extraClasses
