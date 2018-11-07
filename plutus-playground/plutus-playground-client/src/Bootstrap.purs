-- | For most definitions in this file:
-- |
-- | `fooId` is the Bootstrap ClassName "foo-id"
-- | and
-- | `fooId_` is a div that has that class name as its sole attribute.
-- |
-- | Use `fooId_` for convenience and `div [ classes [ fooId ... ] ]` when you need more control.
-- |
-- | (Note: I'm not 100% convinced this is the best organisation, but we'll
-- | try it and see how it works out!)
module Bootstrap where

import Halogen.HTML (ClassName(ClassName), HTML, div)
import Halogen.HTML.Properties (class_, classes)

container :: ClassName
container = ClassName "container"

container_ :: forall p i. Array (HTML p i) -> HTML p i
container_ = div [ class_ container ]

row :: ClassName
row = ClassName "row"

row_ :: forall p i. Array (HTML p i) -> HTML p i
row_ = div [ class_ row ]

col :: ClassName
col = ClassName "col"

col_ :: forall p i. Array (HTML p i) -> HTML p i
col_ = div [ class_ col ]

col2 :: ClassName
col2 = ClassName "col-2"

col2_ :: forall p i. Array (HTML p i) -> HTML p i
col2_ = div [ classes [ col, col2 ] ]

col7 :: ClassName
col7 = ClassName "col-7"

col7_ :: forall p i. Array (HTML p i) -> HTML p i
col7_ = div [ classes [ col, col7 ] ]

col9 :: ClassName
col9 = ClassName "col-9"

col9_ :: forall p i. Array (HTML p i) -> HTML p i
col9_ = div [ classes [ col, col9 ] ]

card :: ClassName
card = ClassName "card"

card_ :: forall p i. Array (HTML p i) -> HTML p i
card_ = div [ class_ card ]

textWhite :: ClassName
textWhite = ClassName "text-white"

bgInfo :: ClassName
bgInfo = ClassName "bg-info"

cardHeader :: ClassName
cardHeader = ClassName "card-header"

cardHeader_ :: forall p i. Array (HTML p i) -> HTML p i
cardHeader_ = div [ class_ cardHeader ]

cardBody :: ClassName
cardBody = ClassName "card-body"

cardBody_ :: forall p i. Array (HTML p i) -> HTML p i
cardBody_ = div [ class_ cardBody ]

cardFooter :: ClassName
cardFooter = ClassName "card-footer"

cardFooter_ :: forall p i. Array (HTML p i) -> HTML p i
cardFooter_ = div [ class_ cardFooter ]

cardTitle :: ClassName
cardTitle = ClassName "card-title"

cardTitle_ :: forall p i. Array (HTML p i) -> HTML p i
cardTitle_ = div [ class_ cardTitle ]

cardText :: ClassName
cardText = ClassName "card-text"

cardText_ :: forall p i. Array (HTML p i) -> HTML p i
cardText_ = div [ class_ cardText ]

btn :: ClassName
btn = ClassName "btn"

btn_ :: forall p i. Array (HTML p i) -> HTML p i
btn_ = div [ class_ btn ]

btnGroup :: ClassName
btnGroup = ClassName "btn-group"

btnGroup_ :: forall p i. Array (HTML p i) -> HTML p i
btnGroup_ = div [ class_ btnGroup ]

btnPrimary :: ClassName
btnPrimary = ClassName "btn-primary"

btnPrimary_ :: forall p i. Array (HTML p i) -> HTML p i
btnPrimary_ = div [ classes [ btn, btnPrimary ] ]

btnSecondary :: ClassName
btnSecondary = ClassName "btn-secondary"

btnSecondary_ :: forall p i. Array (HTML p i) -> HTML p i
btnSecondary_ = div [ classes [ btn, btnSecondary ] ]

btnLight :: ClassName
btnLight = ClassName "btn-light"

btnLight_ :: forall p i. Array (HTML p i) -> HTML p i
btnLight_ = div [ classes [ btn, btnLight ] ]

btnDark :: ClassName
btnDark = ClassName "btn-dark"

btnDark_ :: forall p i. Array (HTML p i) -> HTML p i
btnDark_ = div [ classes [ btn, btnDark ] ]

btnInfo :: ClassName
btnInfo = ClassName "btn-info"

btnSuccess :: ClassName
btnSuccess = ClassName "btn-success"

btnDanger :: ClassName
btnDanger = ClassName "btn-danger"

btnSmall :: ClassName
btnSmall = ClassName "btn-sm"

pullLeft :: ClassName
pullLeft = ClassName "pull-left"

pullRight :: ClassName
pullRight = ClassName "pull-right"

listGroup :: ClassName
listGroup = ClassName "list-group"

listGroup_ :: forall i p. Array (HTML p i) -> HTML p i
listGroup_ = div [ class_ listGroup ]

listGroupItem :: ClassName
listGroupItem = ClassName "list-group-item"

listGroupItem_ :: forall i p. Array (HTML p i) -> HTML p i
listGroupItem_ = div [ class_ listGroupItem ]

alert :: ClassName
alert = ClassName "alert"

alertDanger :: ClassName
alertDanger = ClassName "alert-danger"

alertDanger_ :: forall i p. Array (HTML p i) -> HTML p i
alertDanger_ = div [ classes [ alert, alertDanger ] ]
