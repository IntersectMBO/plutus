module Bootstrap where

import Halogen.HTML (ClassName(..), HTML, IProp, div)
import Halogen.HTML.Properties (class_, classes)
import Prelude (($))

container :: forall p i. Array (HTML p i) -> HTML p i
container = div [ classes [ ClassName "container" ] ]

row :: forall p i. Array (HTML p i) -> HTML p i
row = div [ classes [ ClassName "row" ] ]

col :: forall p i. Array (HTML p i) -> HTML p i
col = div [ class_ $ ClassName "col" ]

col9 :: forall p i. Array (HTML p i) -> HTML p i
col9 = div [ class_ $ ClassName "col col-9" ]

card :: forall p i. Array (HTML p i) -> HTML p i
card = div [ class_ $ ClassName "card"  ]

cardBody :: forall p i. Array (HTML p i) -> HTML p i
cardBody = div [ class_ $ ClassName "card-body" ]

cardImgTop :: forall p i. Array (HTML p i) -> HTML p i
cardImgTop = div [ class_ $ ClassName "card-img-top" ]

cardTitle :: forall p i. Array (HTML p i) -> HTML p i
cardTitle = div [ class_ $ ClassName "card-title" ]

cardText :: forall p i. Array (HTML p i) -> HTML p i
cardText = div [ class_ $ ClassName "card-text" ]

btn :: forall p i. IProp ("class" :: String | p) i
btn = class_ $ ClassName "btn"

btnGroup :: forall p i. IProp ("class" :: String | p) i
btnGroup = class_ $ ClassName "btn-group"

btnPrimary :: forall p i. IProp ("class" :: String | p) i
btnPrimary = class_ $ ClassName "btn btn-primary"

btnSecondary :: forall p i. IProp ("class" :: String | p) i
btnSecondary = class_ $ ClassName "btn btn-secondary"

btnLight :: forall p i. IProp ("class" :: String | p) i
btnLight = class_ $ ClassName "btn btn-light"

btnInfoSmall :: forall p i. IProp ("class" :: String | p) i
btnInfoSmall = class_ $ ClassName "btn btn-info btn-sm"
