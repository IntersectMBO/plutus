module Marlowe.Monaco
  ( languageExtensionPoint
  , daylightTheme
  , completionItemProvider
  , codeActionProvider
  , documentFormattingEditProvider
  , refLabel
  , settings
  ) where

import Prelude
import Data.Function.Uncurried (Fn1, runFn1)
import Data.Maybe (Maybe(..))
import Halogen (RefLabel(..))
import Halogen.Monaco (Settings)
import Marlowe.Linter as Linter
import Monaco (CodeAction, CodeActionProvider, CompletionItem, CompletionItemProvider, DocumentFormattingEditProvider, Editor, IMarkerData, IRange, IStandaloneThemeData, LanguageExtensionPoint(..), Theme, TokensProvider, Uri)

foreign import completionItemProvider_ :: Fn1 (Boolean -> String -> IRange -> Array CompletionItem) CompletionItemProvider

foreign import codeActionProvider_ :: Fn1 (Uri -> Array IMarkerData -> Array CodeAction) CodeActionProvider

foreign import documentFormattingEditProvider_ :: Fn1 (String -> String) DocumentFormattingEditProvider

foreign import tokensProvider :: TokensProvider

foreign import daylightTheme_ :: IStandaloneThemeData

languageExtensionPoint :: LanguageExtensionPoint
languageExtensionPoint = LanguageExtensionPoint { id: "marlowe" }

daylightTheme :: Theme
daylightTheme = { name: "marlowe-playground-daylight", themeData: daylightTheme_ }

completionItemProvider :: CompletionItemProvider
completionItemProvider = runFn1 completionItemProvider_ Linter.suggestions

codeActionProvider :: CodeActionProvider
codeActionProvider = runFn1 codeActionProvider_ Linter.provideCodeActions

documentFormattingEditProvider :: DocumentFormattingEditProvider
documentFormattingEditProvider = runFn1 documentFormattingEditProvider_ Linter.format

refLabel :: RefLabel
refLabel = RefLabel "marloweEditor"

settings :: forall m. (Editor -> m Unit) -> Settings m
settings setup =
  { languageExtensionPoint
  , theme: daylightTheme
  , monarchTokensProvider: Nothing
  , tokensProvider: Just tokensProvider
  , completionItemProvider: Just completionItemProvider
  , codeActionProvider: Just codeActionProvider
  , documentFormattingEditProvider: Just documentFormattingEditProvider
  , refLabel
  , owner: "marloweEditor"
  , getModelMarkers: Linter.markers
  , setup
  }
