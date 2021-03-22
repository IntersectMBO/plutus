module Halogen.Classes where

import Prelude hiding (div)
import Data.Lens (Getter', to)
import Halogen (ClassName(..))
import Halogen.HTML (HTML, IProp, div, span, text)
import Halogen.HTML.Properties (classes)

foreign import closeDrawerIcon :: String

foreign import closeDrawerArrowIcon :: String

foreign import closeModal :: String

foreign import githubIcon :: String

foreign import downloadIcon :: String

foreign import blocklyIcon :: String

foreign import blocklyIconColour :: String

foreign import infoIcon :: String

foreign import readMoreIconWhite :: String

foreign import iohkIcon :: String

foreign import simulationIcon :: String

foreign import walletIcon :: String

foreign import greenCircle :: String

foreign import greyCircle :: String

foreign import selectButton :: String

foreign import iohkLogo :: String

foreign import haskellIcon :: String

foreign import javascriptIcon :: String

foreign import marloweLogo :: String

foreign import marloweLogo2 :: String

foreign import option1 :: String

foreign import option2 :: String

foreign import option3 :: String

foreign import newProjectHaskellIcon :: String

foreign import newProjectJavascriptIcon :: String

foreign import newProjectMarloweIcon :: String

foreign import newProjectBlocklyIcon :: String

fullWidth :: ClassName
fullWidth = ClassName "full-width"

minW0 :: ClassName
minW0 = ClassName "min-w-0"

w30p :: ClassName
w30p = ClassName "w-30p"

fullHeight :: ClassName
fullHeight = ClassName "full-height"

minH0 :: ClassName
minH0 = ClassName "min-h-0"

maxH70p :: ClassName
maxH70p = ClassName "max-h-70p"

scroll :: ClassName
scroll = ClassName "scroll"

active :: ClassName
active = ClassName "active"

hide :: ClassName
hide = ClassName "hide"

noMargins :: ClassName
noMargins = ClassName "no-margins"

aHorizontal :: ClassName
aHorizontal = ClassName "a-horizontal"

spaceLeft :: ClassName
spaceLeft = ClassName "space-left"

spaceRight :: ClassName
spaceRight = ClassName "space-right"

spaceX :: ClassName
spaceX = ClassName "space-x"

spaceBottom :: ClassName
spaceBottom = ClassName "space-bottom"

smallSpaceBottom :: ClassName
smallSpaceBottom = ClassName "small-space-bottom"

paddingRight :: ClassName
paddingRight = ClassName "padding-right"

smallPaddingRight :: ClassName
smallPaddingRight = ClassName "small-padding-right"

paddingLeft :: ClassName
paddingLeft = ClassName "padding-left"

smallPaddingLeft :: ClassName
smallPaddingLeft = ClassName "small-padding-left"

paddingX :: ClassName
paddingX = ClassName "padding-x"

smallPaddingX :: ClassName
smallPaddingX = ClassName "small-padding-x"

paddingTop :: ClassName
paddingTop = ClassName "padding-top"

smallPaddingTop :: ClassName
smallPaddingTop = ClassName "small-padding-top"

paddingBottom :: ClassName
paddingBottom = ClassName "padding-bottom"

smallPaddingBottom :: ClassName
smallPaddingBottom = ClassName "small-padding-bottom"

paddingY :: ClassName
paddingY = ClassName "padding-y"

smallPaddingY :: ClassName
smallPaddingY = ClassName "small-padding-y"

spaceTop :: ClassName
spaceTop = ClassName "space-top"

uppercase :: ClassName
uppercase = ClassName "uppercase"

tabLink :: ClassName
tabLink = ClassName "tab-link"

aCenter :: ClassName
aCenter = ClassName "a-center"

tabIcon :: ClassName
tabIcon = ClassName "tab-icon"

flexLeft :: ClassName
flexLeft = ClassName "flex-left"

accentBorderBottom :: ClassName
accentBorderBottom = ClassName "accent-border-bottom"

accentBorderTop :: ClassName
accentBorderTop = ClassName "accent-border-top"

jFlexStart :: ClassName
jFlexStart = ClassName "j-flex-start"

smallBtn :: ClassName
smallBtn = ClassName "small-btn"

plusBtn :: ClassName
plusBtn = ClassName "plus-btn"

minusBtn :: ClassName
minusBtn = ClassName "minus-btn"

btn :: ClassName
btn = ClassName "btn"

btnSecondary :: ClassName
btnSecondary = ClassName "btn-secondary"

textSecondaryColor :: ClassName
textSecondaryColor = ClassName "text-secondary-color"

bold :: ClassName
bold = ClassName "bold"

underline :: ClassName
underline = ClassName "underline"

mAlignCenter :: ClassName
mAlignCenter = ClassName "m-align-center"

tAlignCenter :: ClassName
tAlignCenter = ClassName "t-align-center"

activeClass :: forall a. (a -> Boolean) -> Getter' a (Array ClassName)
activeClass p = to \x -> if p x then [ active ] else []

activeClasses :: forall r i a. (a -> Boolean) -> Getter' a (IProp ( class :: String | r ) i)
activeClasses p = activeClass p <<< to classes

rTable :: ClassName
rTable = ClassName "Rtable"

rTable6cols :: ClassName
rTable6cols = ClassName "Rtable--6cols"

rTable4cols :: ClassName
rTable4cols = ClassName "Rtable--4cols"

rTableCell :: ClassName
rTableCell = ClassName "Rtable-cell"

rTableCellHeader :: ClassName
rTableCellHeader = ClassName "Rtable-cell-header"

first :: ClassName
first = ClassName "first"

header :: ClassName
header = ClassName "header"

rTableEmptyRow :: ClassName
rTableEmptyRow = ClassName "RTable-empty-row"

rTableDataRow :: ClassName
rTableDataRow = ClassName "RTable-data-row"

pointer :: ClassName
pointer = ClassName "pointer"

expanded :: Boolean -> ClassName
expanded true = ClassName "expanded"

expanded false = ClassName ""

disabled :: Boolean -> ClassName
disabled true = ClassName "disabled"

disabled false = ClassName ""

spanText :: forall p i. String -> HTML p i
spanText s = span [] [ text s ]

sidebarComposer :: ClassName
sidebarComposer = ClassName "sidebar-composer"

minimizeIcon :: Boolean -> Array ClassName
minimizeIcon true = [ ClassName "minimize-icon", ClassName "expanded" ]

minimizeIcon false = [ ClassName "minimize-icon" ]

alignedButtonInTheMiddle :: ClassName
alignedButtonInTheMiddle = ClassName "aligned-button-in-the-middle"

alignedButtonLast :: ClassName
alignedButtonLast = ClassName "aligned-button-last"

collapsed :: ClassName
collapsed = ClassName "collapsed"

horizontalFlip :: ClassName
horizontalFlip = ClassName "flip"

modalContent :: ClassName
modalContent = ClassName "modal-content"

vl :: forall p a. HTML p a
vl = div [ classes [ ClassName "vl" ] ] [ text "|" ]

group :: ClassName
group = ClassName "group"

-- Tailwind's classes.
textBase :: ClassName
textBase = ClassName "text-base"

textXs :: ClassName
textXs = ClassName "text-xs"

textSm :: ClassName
textSm = ClassName "text-sm"

textLg :: ClassName
textLg = ClassName "text-lg"

text3xl :: ClassName
text3xl = ClassName "text-3xl"

fontSemibold :: ClassName
fontSemibold = ClassName "font-semibold"

fontBold :: ClassName
fontBold = ClassName "font-bold"

textLeft :: ClassName
textLeft = ClassName "text-left"

textCenter :: ClassName
textCenter = ClassName "text-center"

textRight :: ClassName
textRight = ClassName "text-right"

textJustify :: ClassName
textJustify = ClassName "text-justify"

textWhite :: ClassName
textWhite = ClassName "text-white"

border :: ClassName
border = ClassName "border"

borderBlue300 :: ClassName
borderBlue300 = ClassName "border-blue-300"

activeBorderBlue700 :: ClassName
activeBorderBlue700 = ClassName "active:border-blue-700"

flex :: ClassName
flex = ClassName "flex"

flexRow :: ClassName
flexRow = ClassName "flex-row"

flexRowReverse :: ClassName
flexRowReverse = ClassName "flex-row-reverse"

flexCol :: ClassName
flexCol = ClassName "flex-col"

flexColReverse :: ClassName
flexColReverse = ClassName "flex-col-reverse"

flex1 :: ClassName
flex1 = ClassName "flex-1"

flexAuto :: ClassName
flexAuto = ClassName "flex-auto"

flexInitial :: ClassName
flexInitial = ClassName "flex-initial"

flexNone :: ClassName
flexNone = ClassName "flex-none"

justifyStart :: ClassName
justifyStart = ClassName "justify-start"

justifyEnd :: ClassName
justifyEnd = ClassName "justify-end"

justifyCenter :: ClassName
justifyCenter = ClassName "justify-center"

justifyBetween :: ClassName
justifyBetween = ClassName "justify-between"

justifyAround :: ClassName
justifyAround = ClassName "justify-around"

justifyEvenly :: ClassName
justifyEvenly = ClassName "justify-evenly"

justifySelfAuto :: ClassName
justifySelfAuto = ClassName "justify-self-auto"

justifySelfStart :: ClassName
justifySelfStart = ClassName "justify-self-start"

justifySelfEnd :: ClassName
justifySelfEnd = ClassName "justify-self-end"

justifySelfCenter :: ClassName
justifySelfCenter = ClassName "justify-self-center"

justifySelfStretch :: ClassName
justifySelfStretch = ClassName "justify-self-stretch"

whitespaceNormal :: ClassName
whitespaceNormal = ClassName "whitespace-normal"

whitespaceNowrap :: ClassName
whitespaceNowrap = ClassName "whitespace-nowrap"

whitespacePre :: ClassName
whitespacePre = ClassName "whitespace-pre"

whitespacePreLine :: ClassName
whitespacePreLine = ClassName "whitespace-pre-line"

whitespacePreWrap :: ClassName
whitespacePreWrap = ClassName "whitespace-pre-wrap"

flexGrow :: ClassName
flexGrow = ClassName "flex-grow"

flexGrow0 :: ClassName
flexGrow0 = ClassName "flex-grow-0"

flexShrink :: ClassName
flexShrink = ClassName "flex-shrink"

flexShrink0 :: ClassName
flexShrink0 = ClassName "flex-shrink-0"

grid :: ClassName
grid = ClassName "grid"

gridColsDescriptionLocation :: ClassName
gridColsDescriptionLocation = ClassName "grid-cols-description-location"

bgDark :: ClassName
bgDark = ClassName "bg-dark"

bgWhite :: ClassName
bgWhite = ClassName "bg-white"

textInactive :: ClassName
textInactive = ClassName "text-inactive"

textSecondary :: ClassName
textSecondary = ClassName "text-secondary"

borderSeparator :: ClassName
borderSeparator = ClassName "border-separator"

overflowHidden :: ClassName
overflowHidden = ClassName "overflow-hidden"

overflowScroll :: ClassName
overflowScroll = ClassName "overflow-scroll"

overflowXScroll :: ClassName
overflowXScroll = ClassName "overflow-x-scroll"

boxShadowInverted :: ClassName
boxShadowInverted = ClassName "box-shadow-inverted"

hidden :: ClassName
hidden = ClassName "hidden"
