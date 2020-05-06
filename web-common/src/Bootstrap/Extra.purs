module Bootstrap.Extra where

import Halogen.HTML (ClassName(..), HTML, IProp, PropName(..), pre, prop)
import Halogen.HTML.Properties (class_)
import Prelude (show)

clickable :: ClassName
clickable = ClassName "clickable"

dataToggle :: forall r i. String -> IProp r i
dataToggle = prop (PropName "data-toggle")

ariaHasPopup :: forall r i. Boolean -> IProp r i
ariaHasPopup hasPopup = prop (PropName "data-toggle") (show hasPopup)

ariaExpanded :: forall r i. Boolean -> IProp r i
ariaExpanded expanded = prop (PropName "data-toggle") (show expanded)

ariaLabelledBy :: forall r i. String -> IProp r i
ariaLabelledBy label = prop (PropName "data-toggle") label

preWrap_ :: forall p i. Array (HTML p i) -> HTML p i
preWrap_ = pre [ class_ preWrap ]

preWrap :: ClassName
preWrap = ClassName "preWrap"
