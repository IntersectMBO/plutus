module Halogen.Classes where

import Prelude hiding (div)
import Data.Lens (Getter', to)
import Halogen (ClassName(..))
import Halogen.HTML (HTML, IProp, div, span, text)
import Halogen.HTML.Properties (classes)

foreign import arrowLeftUp :: String

foreign import arrowLeftDown :: String

foreign import arrowRightUp :: String

foreign import arrowRightDown :: String

foreign import closeDrawerArrowIcon :: String

foreign import closeModal :: String

foreign import githubIcon :: String

foreign import downloadIcon :: String

foreign import blocklyIcon :: String

foreign import blocklyIconColour :: String

foreign import readMoreIconWhite :: String

foreign import iohkIcon :: String

foreign import simulationIcon :: String

foreign import simulationIconBlack :: String

foreign import walletIcon :: String

foreign import greenCircle :: String

foreign import greyCircle :: String

foreign import selectButton :: String

foreign import iohkLogo :: String

foreign import haskellIcon :: String

foreign import javascriptIcon :: String

foreign import marloweLogo :: String

foreign import marlowePlayLogo :: String

foreign import newProjectHaskellIcon :: String

foreign import newProjectJavascriptIcon :: String

foreign import newProjectBlocklyIcon :: String

fullWidth :: ClassName
fullWidth = ClassName "w-full"

minW0 :: ClassName
minW0 = ClassName "min-w-0"

w30p :: ClassName
w30p = ClassName "w-30p"

-- FIXME: rename to h-full
fullHeight :: ClassName
fullHeight = ClassName "h-full"

minH0 :: ClassName
minH0 = ClassName "min-h-0"

maxH70p :: ClassName
maxH70p = ClassName "max-h-70p"

active :: ClassName
active = ClassName "active"

noMargins :: ClassName
noMargins = ClassName "no-margins"

aHorizontal :: ClassName
aHorizontal = ClassName "a-horizontal"

-- FIXME: rename spaceXXX to mXXX
spaceLeft :: ClassName
spaceLeft = ClassName "ml-medium"

spaceRight :: ClassName
spaceRight = ClassName "mr-medium"

spaceX :: ClassName
spaceX = ClassName "mx-medium"

spaceBottom :: ClassName
spaceBottom = ClassName "mb-medium"

smallSpaceBottom :: ClassName
smallSpaceBottom = ClassName "mb-small"

spaceTop :: ClassName
spaceTop = ClassName "mt-medium"

-- FIXME: rename paddingXXX to pXXX
paddingRight :: ClassName
paddingRight = ClassName "pr-medium"

smallPaddingRight :: ClassName
smallPaddingRight = ClassName "pr-small"

paddingLeft :: ClassName
paddingLeft = ClassName "pl-medium"

smallPaddingLeft :: ClassName
smallPaddingLeft = ClassName "pl-small"

paddingX :: ClassName
paddingX = ClassName "px-medium"

smallPaddingX :: ClassName
smallPaddingX = ClassName "px-small"

paddingTop :: ClassName
paddingTop = ClassName "pt-medium"

smallPaddingTop :: ClassName
smallPaddingTop = ClassName "pt-small"

paddingBottom :: ClassName
paddingBottom = ClassName "pb-medium"

smallPaddingBottom :: ClassName
smallPaddingBottom = ClassName "pb-small"

paddingY :: ClassName
paddingY = ClassName "py-medium"

smallPaddingY :: ClassName
smallPaddingY = ClassName "py-small"

uppercase :: ClassName
uppercase = ClassName "uppercase"

tabLink :: ClassName
tabLink = ClassName "tab-link"

tabIcon :: ClassName
tabIcon = ClassName "tab-icon"

flexLeft :: ClassName
flexLeft = ClassName "flex-left"

accentBorderBottom :: ClassName
accentBorderBottom = ClassName "accent-border-bottom"

accentBorderTop :: ClassName
accentBorderTop = ClassName "accent-border-top"

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

cursorPointer :: ClassName
cursorPointer = ClassName "cursor-pointer"

expanded :: Boolean -> ClassName
expanded true = ClassName "expanded"

expanded false = ClassName ""

disabled :: Boolean -> ClassName
disabled true = ClassName "disabled"

disabled false = ClassName ""

spanText :: forall p i. String -> HTML p i
spanText s = span [] [ text s ]

spanTextBreakWord :: forall p i. String -> HTML p i
spanTextBreakWord s = span [ classes [ ClassName "break-word-span" ] ] [ text s ]

minimizeIcon :: Boolean -> Array ClassName
minimizeIcon true = [ ClassName "minimize-icon", ClassName "expanded" ]

minimizeIcon false = [ ClassName "minimize-icon" ]

alignedButtonInTheMiddle :: ClassName
alignedButtonInTheMiddle = ClassName "aligned-button-in-the-middle"

alignedButtonLast :: ClassName
alignedButtonLast = ClassName "aligned-button-last"

collapsed :: ClassName
collapsed = ClassName "collapsed"

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

bgGrayDark :: ClassName
bgGrayDark = ClassName "bg-gray-dark"

bgWhite :: ClassName
bgWhite = ClassName "bg-white"

textInactive :: ClassName
textInactive = ClassName "text-gray-darkest"

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

----------------------------------------------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------------------
----------------------------------------------------------------------------------------------------------------
-- FIXME These were copy and pasted from the dashboard and adapted to the defaults in this project.
--       we need to use the same resets and unify these styles in a style guide.
--- color gradients
bgBlueGradient :: Array String
bgBlueGradient = [ "bg-gradient-to-r", "from-purple", "to-lightpurple", "text-white" ]

-- buttons
button :: Array String
button =
  [ "px-6"
  , "py-4"
  , "rounded-full"
  , "font-bold"
  , "leading-none"
  , "whitespace-nowrap"
  , "transition-all"
  , "duration-200"
  , "outline-none"
  , "focus:outline-none"
  , "disabled:bg-none"
  , "disabled:bg-lightgray"
  , "disabled:text-darkgray"
  , "disabled:shadow-none"
  , "border-0"
  ]

withShadow :: Array String
withShadow = [ "shadow", "hover:shadow-lg" ]

primaryButton :: Array String
primaryButton = button <> bgBlueGradient <> withShadow

secondaryButton :: Array String
secondaryButton = button <> [ "bg-lightgray", "text-black", "hover:shadow" ]

whiteButton :: Array String
whiteButton = button <> withShadow <> [ "bg-white" ]
