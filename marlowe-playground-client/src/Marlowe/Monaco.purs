module Marlowe.Monaco
  ( languageExtensionPoint
  , daylightTheme
  , completionItemProvider
  , codeActionProvider
  , updateAdditionalContext
  , documentFormattingEditProvider
  , refLabel
  , settings
  ) where

import Prelude
import Data.Function.Uncurried (Fn1, Fn2, Fn3, runFn1, runFn2, runFn3)
import Data.Maybe (Maybe(..))
import Data.Unfoldable as Unfoldable
import Halogen (RefLabel(..))
import Halogen.Monaco (Settings)
import Help as Help
import Marlowe.LinterText (AdditionalContext)
import Marlowe.LinterText as Linter
import Monaco (CodeAction, CodeActionProvider, CompletionItem, CompletionItemProvider, DocumentFormattingEditProvider, Editor, HoverProvider, IMarkdownString, IMarkerData, IRange, IStandaloneThemeData, LanguageExtensionPoint(..), Theme, TokensProvider, Uri)

foreign import hoverProvider_ :: Fn1 (String -> { contents :: Array IMarkdownString }) HoverProvider

foreign import completionItemProvider_ :: Fn1 (String -> Boolean -> String -> IRange -> AdditionalContext -> Array CompletionItem) CompletionItemProvider

foreign import codeActionProvider_ :: Fn2 (Uri -> Array IMarkerData -> AdditionalContext -> Array CodeAction) AdditionalContext CodeActionProvider

foreign import updateAdditionalContext_ :: Fn3 CodeActionProvider CompletionItemProvider AdditionalContext Unit

foreign import documentFormattingEditProvider_ :: Fn1 (String -> String) DocumentFormattingEditProvider

foreign import tokensProvider :: TokensProvider

foreign import daylightTheme_ :: IStandaloneThemeData

languageExtensionPoint :: LanguageExtensionPoint
languageExtensionPoint = LanguageExtensionPoint { id: "marlowe" }

daylightTheme :: Theme
daylightTheme = { name: "marlowe-playground-daylight", themeData: daylightTheme_ }

hoverProvider :: HoverProvider
hoverProvider =
  runFn1 hoverProvider_ \constructor ->
    let
      vs = Unfoldable.fromMaybe (Help.helpForConstructor constructor)

      items = map (\value -> { value }) vs
    in
      { contents: items }

completionItemProvider :: CompletionItemProvider
completionItemProvider = runFn1 completionItemProvider_ Linter.suggestions

codeActionProvider :: AdditionalContext -> CodeActionProvider
codeActionProvider = runFn2 codeActionProvider_ Linter.provideCodeActions

updateAdditionalContext :: CodeActionProvider -> CompletionItemProvider -> AdditionalContext -> Unit
updateAdditionalContext = runFn3 updateAdditionalContext_

documentFormattingEditProvider :: DocumentFormattingEditProvider
documentFormattingEditProvider = runFn1 documentFormattingEditProvider_ Linter.format

refLabel :: RefLabel
refLabel = RefLabel "marloweEditor"

settings :: forall m. (Editor -> m Unit) -> Settings m
settings setup =
  { languageExtensionPoint
  , theme: Just daylightTheme
  , monarchTokensProvider: Nothing
  , tokensProvider: Just tokensProvider
  , hoverProvider: Just hoverProvider
  , completionItemProvider: Just completionItemProvider
  , codeActionProvider: Just $ codeActionProvider { warnings: mempty, contract: Nothing }
  , documentFormattingEditProvider: Just documentFormattingEditProvider
  , refLabel
  , owner: "marloweEditor"
  , setup
  }
