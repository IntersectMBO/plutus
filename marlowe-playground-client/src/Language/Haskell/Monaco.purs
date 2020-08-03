module Language.Haskell.Monaco where

import Prelude
import Data.Maybe (Maybe(..))
import Halogen (RefLabel(..))
import Halogen.Monaco (Settings)
import Monaco (Editor, IStandaloneThemeData, LanguageExtensionPoint(..), MonarchLanguage, Theme)

foreign import monarchTokensProvider_ :: MonarchLanguage

foreign import haskellDaylightTheme_ :: IStandaloneThemeData

languageExtensionPoint :: LanguageExtensionPoint
languageExtensionPoint = LanguageExtensionPoint { id: "haskell" }

daylightTheme :: Theme
daylightTheme = { name: "haskell-daylight", themeData: haskellDaylightTheme_ }

refLabel :: RefLabel
refLabel = RefLabel "haskellEditor"

settings :: forall m. (Editor -> m Unit) -> Settings m
settings setup =
  { languageExtensionPoint
  , theme: Just daylightTheme
  , monarchTokensProvider: Just monarchTokensProvider_
  , tokensProvider: Nothing
  , hoverProvider: Nothing
  , completionItemProvider: Nothing
  , codeActionProvider: Nothing
  , documentFormattingEditProvider: Nothing
  , refLabel
  , owner: "haskellEditor"
  , setup
  }
