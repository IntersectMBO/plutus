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

fullHeight :: ClassName
fullHeight = ClassName "full-height"

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

uppercase :: ClassName
uppercase = ClassName "uppercase"

tabLink :: ClassName
tabLink = ClassName "tab-link"

aCenter :: ClassName
aCenter = ClassName "a-center"

flexCol :: ClassName
flexCol = ClassName "flex-col"

tabIcon :: ClassName
tabIcon = ClassName "tab-icon"

panelContents :: ClassName
panelContents = ClassName "panel-contents"

flexLeft :: ClassName
flexLeft = ClassName "flex-left"

panelHeader :: ClassName
panelHeader = ClassName "panel-header"

panelSubHeader :: ClassName
panelSubHeader = ClassName "panel-sub-header"

panelSubHeaderMain :: ClassName
panelSubHeaderMain = ClassName "panel-sub-header-main"

panelSubHeaderSide :: ClassName
panelSubHeaderSide = ClassName "panel-sub-header-side"

panelHeaderMain :: ClassName
panelHeaderMain = ClassName "panel-header-main"

panelHeaderSide :: ClassName
panelHeaderSide = ClassName "panel-header-side"

accentBorderBottom :: ClassName
accentBorderBottom = ClassName "accent-border-bottom"

jFlexStart :: ClassName
jFlexStart = ClassName "j-flex-start"

smallBtn :: ClassName
smallBtn = ClassName "small-btn"

plusBtn :: ClassName
plusBtn = ClassName "plus-btn"

minusBtn :: ClassName
minusBtn = ClassName "minus-btn"

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

flex :: ClassName
flex = ClassName "flex"

flexFour :: ClassName
flexFour = ClassName "flex-four"

flexTen :: ClassName
flexTen = ClassName "flex-ten"

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

stateLabel :: ClassName
stateLabel = ClassName "state-label"

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

codeEditor :: Boolean -> Array ClassName
codeEditor true = [ ClassName "code-editor" ]

codeEditor false = [ ClassName "code-editor", ClassName "expanded" ]

haskellEditor :: Boolean -> Array ClassName
haskellEditor true = [ ClassName "code-panel", ClassName "haskell-editor" ]

haskellEditor false = [ ClassName "code-panel", ClassName "haskell-editor", ClassName "expanded" ]

minimizeIcon :: Boolean -> Array ClassName
minimizeIcon true = [ ClassName "minimize-icon", ClassName "expanded" ]

minimizeIcon false = [ ClassName "minimize-icon" ]

footerPanelBg :: ClassName
footerPanelBg = ClassName "footer-panel-bg"

analysisPanel :: ClassName
analysisPanel = ClassName "analysis-panel"

alignedButtonInTheMiddle :: ClassName
alignedButtonInTheMiddle = ClassName "aligned-button-in-the-middle"

alignedButtonLast :: ClassName
alignedButtonLast = ClassName "aligned-button-last"

collapsed :: ClassName
collapsed = ClassName "collapsed"

horizontalFlip :: ClassName
horizontalFlip = ClassName "flip"

vl :: forall p a. HTML p a
vl = div [ classes [ ClassName "vl" ] ] [ text "|" ]
