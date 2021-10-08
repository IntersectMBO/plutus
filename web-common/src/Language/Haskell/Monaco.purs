module Language.Haskell.Monaco where

import Prelude
import Data.Maybe (Maybe(..))
import Data.Traversable (traverse)
import Effect (Effect)
import Effect.Class (class MonadEffect, liftEffect)
import Effect.Uncurried (EffectFn1, runEffectFn1)
import Halogen (RefLabel(..))
import Halogen.Monaco (Settings)
import Monaco (Editor, IStandaloneThemeData, LanguageExtensionPoint(..), MonarchLanguage, Theme)

foreign import monarchTokensProvider_ :: EffectFn1 Unit MonarchLanguage

foreign import haskellDaylightTheme_ :: IStandaloneThemeData

monarchTokensProvider :: Effect MonarchLanguage
monarchTokensProvider = runEffectFn1 monarchTokensProvider_ unit

languageExtensionPoint :: LanguageExtensionPoint
languageExtensionPoint = LanguageExtensionPoint { id: "haskell" }

daylightTheme :: Theme
daylightTheme = { name: "haskell-daylight", themeData: haskellDaylightTheme_ }

refLabel :: RefLabel
refLabel = RefLabel "haskellEditor"

settings :: forall m. MonadEffect m => (Editor -> m Unit) -> Settings m
settings setup =
  { languageExtensionPoint
  , theme: Just daylightTheme
  , monarchTokensProvider: traverse liftEffect $ Just monarchTokensProvider
  , tokensProvider: pure Nothing
  , hoverProvider: pure Nothing
  , completionItemProvider: pure Nothing
  , codeActionProvider: pure Nothing
  , documentFormattingEditProvider: pure Nothing
  , refLabel
  , owner: "haskellEditor"
  , setup
  }
