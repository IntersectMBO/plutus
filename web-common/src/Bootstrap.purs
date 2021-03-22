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

import Halogen.HTML (ClassName(ClassName), HTML, div, li, span, text, ul)
import Halogen.HTML.Properties (class_, classes)

container :: ClassName
container = ClassName "container"

container_ :: forall p i. Array (HTML p i) -> HTML p i
container_ = div [ class_ container ]

containerFluid :: ClassName
containerFluid = ClassName "container-fluid"

containerFluid_ :: forall p i. Array (HTML p i) -> HTML p i
containerFluid_ = div [ class_ containerFluid ]

noGutters :: ClassName
noGutters = ClassName "no-gutters"

row :: ClassName
row = ClassName "row"

row_ :: forall p i. Array (HTML p i) -> HTML p i
row_ = div [ class_ row ]

col :: ClassName
col = ClassName "col"

col_ :: forall p i. Array (HTML p i) -> HTML p i
col_ = div [ class_ col ]

col1 :: ClassName
col1 = ClassName "col-1"

col1_ :: forall p i. Array (HTML p i) -> HTML p i
col1_ = div [ classes [ col, col1 ] ]

col2 :: ClassName
col2 = ClassName "col-2"

col2_ :: forall p i. Array (HTML p i) -> HTML p i
col2_ = div [ classes [ col, col2 ] ]

col3 :: ClassName
col3 = ClassName "col-3"

col3_ :: forall p i. Array (HTML p i) -> HTML p i
col3_ = div [ classes [ col, col3 ] ]

col4 :: ClassName
col4 = ClassName "col-4"

col4_ :: forall p i. Array (HTML p i) -> HTML p i
col4_ = div [ classes [ col, col4 ] ]

col5 :: ClassName
col5 = ClassName "col-5"

col5_ :: forall p i. Array (HTML p i) -> HTML p i
col5_ = div [ classes [ col, col5 ] ]

col6 :: ClassName
col6 = ClassName "col-6"

col6_ :: forall p i. Array (HTML p i) -> HTML p i
col6_ = div [ classes [ col, col6 ] ]

col7 :: ClassName
col7 = ClassName "col-7"

col7_ :: forall p i. Array (HTML p i) -> HTML p i
col7_ = div [ classes [ col, col7 ] ]

col8 :: ClassName
col8 = ClassName "col-8"

col8_ :: forall p i. Array (HTML p i) -> HTML p i
col8_ = div [ classes [ col, col8 ] ]

col9 :: ClassName
col9 = ClassName "col-9"

col9_ :: forall p i. Array (HTML p i) -> HTML p i
col9_ = div [ classes [ col, col9 ] ]

col10 :: ClassName
col10 = ClassName "col-10"

col10_ :: forall p i. Array (HTML p i) -> HTML p i
col10_ = div [ classes [ col, col10 ] ]

col11 :: ClassName
col11 = ClassName "col-11"

col11_ :: forall p i. Array (HTML p i) -> HTML p i
col11_ = div [ classes [ col, col11 ] ]

col12 :: ClassName
col12 = ClassName "col-12"

col12_ :: forall p i. Array (HTML p i) -> HTML p i
col12_ = div [ classes [ col, col12 ] ]

colXs6 :: ClassName
colXs6 = ClassName "col-xs-6"

colXs12 :: ClassName
colXs12 = ClassName "col-xs-12"

colSm4 :: ClassName
colSm4 = ClassName "col-sm-4"

colSm5 :: ClassName
colSm5 = ClassName "col-sm-5"

colSm6 :: ClassName
colSm6 = ClassName "col-sm-6"

colSm7 :: ClassName
colSm7 = ClassName "col-sm-7"

colSm8 :: ClassName
colSm8 = ClassName "col-sm-8"

colSm12 :: ClassName
colSm12 = ClassName "col-sm-12"

colMd3 :: ClassName
colMd3 = ClassName "col-md-3"

colMd4 :: ClassName
colMd4 = ClassName "col-md-4"

colMd5 :: ClassName
colMd5 = ClassName "col-md-5"

colMd6 :: ClassName
colMd6 = ClassName "col-md-6"

colMd7 :: ClassName
colMd7 = ClassName "col-md-7"

colMd8 :: ClassName
colMd8 = ClassName "col-md-8"

colMd12 :: ClassName
colMd12 = ClassName "col-md-12"

colLg2 :: ClassName
colLg2 = ClassName "col-lg-2"

colLg4 :: ClassName
colLg4 = ClassName "col-lg-4"

colLg5 :: ClassName
colLg5 = ClassName "col-lg-5"

colLg7 :: ClassName
colLg7 = ClassName "col-lg-7"

colLg8 :: ClassName
colLg8 = ClassName "col-lg-8"

colAuto :: ClassName
colAuto = ClassName "col-auto"

colAuto_ :: forall p i. Array (HTML p i) -> HTML p i
colAuto_ = div [ class_ colAuto ]

offset3 :: ClassName
offset3 = ClassName "offset-3"

offset6 :: ClassName
offset6 = ClassName "offset-6"

offset7 :: ClassName
offset7 = ClassName "offset-7"

justifyContentBetween :: ClassName
justifyContentBetween = ClassName "justify-content-between"

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

btnBlock :: ClassName
btnBlock = ClassName "btn-block"

btnGroup :: ClassName
btnGroup = ClassName "btn-group"

btnGroupSmall :: ClassName
btnGroupSmall = ClassName "btn-group-sm"

btnGroup_ :: forall p i. Array (HTML p i) -> HTML p i
btnGroup_ = div [ class_ btnGroup ]

btnGroupVertical :: ClassName
btnGroupVertical = ClassName "btn-group-vertical"

btnGroupVertical_ :: forall p i. Array (HTML p i) -> HTML p i
btnGroupVertical_ = div [ class_ btnGroupVertical ]

btnPrimary :: ClassName
btnPrimary = ClassName "btn-primary"

btnPrimary_ :: forall p i. Array (HTML p i) -> HTML p i
btnPrimary_ = div [ classes [ btn, btnPrimary ] ]

btnSecondary :: ClassName
btnSecondary = ClassName "btn-secondary"

btnSecondary_ :: forall p i. Array (HTML p i) -> HTML p i
btnSecondary_ = div [ classes [ btn, btnSecondary ] ]

btnWarning :: ClassName
btnWarning = ClassName "btn-warning"

btnWarning_ :: forall p i. Array (HTML p i) -> HTML p i
btnWarning_ = div [ classes [ btn, btnWarning ] ]

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

btnDefault :: ClassName
btnDefault = ClassName "btn-default"

btnSuccess :: ClassName
btnSuccess = ClassName "btn-success"

btnDanger :: ClassName
btnDanger = ClassName "btn-danger"

btnSmall :: ClassName
btnSmall = ClassName "btn-sm"

btnExtraSmall :: ClassName
btnExtraSmall = ClassName "btn-xs"

btnLink :: ClassName
btnLink = ClassName "btn-link"

dropdownToggle :: ClassName
dropdownToggle = ClassName "dropdown-toggle"

pullLeft :: ClassName
pullLeft = ClassName "pull-left"

pullRight :: ClassName
pullRight = ClassName "pull-right"

floatLeft :: ClassName
floatLeft = ClassName "float-left"

floatRight :: ClassName
floatRight = ClassName "float-right"

displayFlex :: ClassName
displayFlex = ClassName "d-flex"

alignItemsCenter :: ClassName
alignItemsCenter = ClassName "align-items-center"

mlAuto :: ClassName
mlAuto = ClassName "ml-auto"

mrAuto :: ClassName
mrAuto = ClassName "mr-auto"

clearfix :: ClassName
clearfix = ClassName "clearfix"

clearfix_ :: forall i p. HTML p i
clearfix_ = div [ class_ clearfix ] []

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

alertInfo :: ClassName
alertInfo = ClassName "alert-info"

alertInfo_ :: forall i p. Array (HTML p i) -> HTML p i
alertInfo_ = div [ classes [ alert, alertInfo ] ]

alertPrimary :: ClassName
alertPrimary = ClassName "alert-primary"

alertPrimary_ :: forall i p. Array (HTML p i) -> HTML p i
alertPrimary_ = div [ classes [ alert, alertPrimary ] ]

empty :: forall p i. HTML p i
empty = text ""

nbsp :: forall p i. HTML p i
nbsp = text "\x00A0"

badge :: ClassName
badge = ClassName "badge"

badgePrimary :: ClassName
badgePrimary = ClassName "badge-primary"

badgePrimary_ :: forall p i. Array (HTML p i) -> HTML p i
badgePrimary_ = span [ classes [ badge, badgePrimary ] ]

wasValidated :: ClassName
wasValidated = ClassName "was-validated"

isValid :: ClassName
isValid = ClassName "is-valid"

isInvalid :: ClassName
isInvalid = ClassName "is-invalid"

colFormLabel :: ClassName
colFormLabel = ClassName "col-form-label"

formControl :: ClassName
formControl = ClassName "form-control"

formControl_ :: forall p i. Array (HTML p i) -> HTML p i
formControl_ = div [ class_ formControl ]

formRow :: ClassName
formRow = ClassName "form-row"

formRow_ :: forall p i. Array (HTML p i) -> HTML p i
formRow_ = div [ class_ formRow ]

formGroup :: ClassName
formGroup = ClassName "form-group"

formGroup_ :: forall p i. Array (HTML p i) -> HTML p i
formGroup_ = div [ class_ formGroup ]

formCheck :: ClassName
formCheck = ClassName "form-check"

formCheck_ :: forall p i. Array (HTML p i) -> HTML p i
formCheck_ = div [ class_ formCheck ]

formCheckInline :: ClassName
formCheckInline = ClassName "form-check-inline"

formCheckInput :: ClassName
formCheckInput = ClassName "form-check-input"

formCheckLabel :: ClassName
formCheckLabel = ClassName "form-check-label"

formText :: ClassName
formText = ClassName "form-text"

inputGroup :: ClassName
inputGroup = ClassName "input-group"

inputGroup_ :: forall p i. Array (HTML p i) -> HTML p i
inputGroup_ = div [ class_ inputGroup ]

inputGroupPrepend :: ClassName
inputGroupPrepend = ClassName "input-group-prepend"

inputGroupPrepend_ :: forall p i. Array (HTML p i) -> HTML p i
inputGroupPrepend_ = div [ class_ inputGroupPrepend ]

inputGroupAppend :: ClassName
inputGroupAppend = ClassName "input-group-append"

inputGroupAppend_ :: forall p i. Array (HTML p i) -> HTML p i
inputGroupAppend_ = div [ class_ inputGroupAppend ]

inputGroupText :: ClassName
inputGroupText = ClassName "input-group-text"

customSelect :: ClassName
customSelect = ClassName "custom-select"

validFeedback :: ClassName
validFeedback = ClassName "valid-feedback"

validFeedback_ :: forall p i. Array (HTML p i) -> HTML p i
validFeedback_ = div [ class_ validFeedback ]

invalidFeedback :: ClassName
invalidFeedback = ClassName "invalid-feedback"

invalidFeedback_ :: forall p i. Array (HTML p i) -> HTML p i
invalidFeedback_ = div [ class_ invalidFeedback ]

active :: ClassName
active = ClassName "active"

disabled :: ClassName
disabled = ClassName "disabled"

nav :: ClassName
nav = ClassName "nav"

navbar :: ClassName
navbar = ClassName "navbar"

navbarBrand :: ClassName
navbarBrand = ClassName "navbar-brand"

navbarText :: ClassName
navbarText = ClassName "navbar-text"

navbarNav :: ClassName
navbarNav = ClassName "navbar-nav"

navbarExpand :: ClassName
navbarExpand = ClassName "navbar-expand"

navbarExpandSmall :: ClassName
navbarExpandSmall = ClassName "navbar-expand-sm"

navPills_ :: forall p i. Array (HTML p i) -> HTML p i
navPills_ = ul [ classes [ nav, ClassName "nav-pills" ] ]

navTabs_ :: forall p i. Array (HTML p i) -> HTML p i
navTabs_ = ul [ classes [ nav, ClassName "nav-tabs" ] ]

navItem :: ClassName
navItem = ClassName "nav-item"

navItem_ :: forall p i. Array (HTML p i) -> HTML p i
navItem_ = li [ class_ navItem ]

navLink :: ClassName
navLink = ClassName "nav-link"

hidden :: ClassName
hidden = ClassName "d-none"

-- | A third of the screen, assuming a reasonable screen
-- size. Collapses sensibly as the size goes down to iPhone.
responsiveThird :: forall p i. Array (HTML p i) -> HTML p i
responsiveThird = div [ classes [ col12, colSm6, colMd4 ] ]

textTruncate :: ClassName
textTruncate = ClassName "text-truncate"

textCenter :: ClassName
textCenter = ClassName "text-center"

textLeft :: ClassName
textLeft = ClassName "text-left"

textRight :: ClassName
textRight = ClassName "text-right"

textMuted :: ClassName
textMuted = ClassName "text-muted"

-- | Because of the clash with the HTML tag, it's recommended to use this class name qualified.
-- eq. `table [ classes [ Bootstrap.table, tableStriped ] ] [ ... ] `
table :: ClassName
table = ClassName "table"

tableStriped :: ClassName
tableStriped = ClassName "table-striped"

tableBordered :: ClassName
tableBordered = ClassName "table-bordered"

tableSmall :: ClassName
tableSmall = ClassName "table-sm"
