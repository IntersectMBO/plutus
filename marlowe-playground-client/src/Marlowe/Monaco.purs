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
import Data.Maybe (Maybe(..))
import Data.Traversable (traverse)
import Data.Unfoldable as Unfoldable
import Effect (Effect)
import Effect.Class (class MonadEffect)
import Effect.Uncurried (EffectFn1, EffectFn2, EffectFn3, runEffectFn1, runEffectFn2, runEffectFn3)
import Halogen (RefLabel(..), liftEffect)
import Halogen.Monaco (Settings)
import Help as Help
import Marlowe.LinterText (AdditionalContext)
import Marlowe.LinterText as Linter
import Monaco (CodeAction, CodeActionProvider, CompletionItem, CompletionItemProvider, DocumentFormattingEditProvider, Editor, HoverProvider, IMarkdownString, IMarkerData, IRange, IStandaloneThemeData, LanguageExtensionPoint(..), Theme, TokensProvider, Uri)

foreign import hoverProvider_ :: EffectFn1 (String -> { contents :: Array IMarkdownString }) HoverProvider

foreign import completionItemProvider_ :: EffectFn1 (String -> Boolean -> String -> IRange -> AdditionalContext -> Array CompletionItem) CompletionItemProvider

foreign import codeActionProvider_ :: EffectFn2 (Uri -> Array IMarkerData -> AdditionalContext -> Array CodeAction) AdditionalContext CodeActionProvider

foreign import updateAdditionalContext_ :: EffectFn3 CodeActionProvider CompletionItemProvider AdditionalContext Unit

foreign import documentFormattingEditProvider_ :: EffectFn1 (String -> String) DocumentFormattingEditProvider

foreign import tokensProvider_ :: EffectFn1 Unit TokensProvider

foreign import daylightTheme_ :: IStandaloneThemeData

languageExtensionPoint :: LanguageExtensionPoint
languageExtensionPoint = LanguageExtensionPoint { id: "marlowe" }

daylightTheme :: Theme
daylightTheme = { name: "marlowe-playground-daylight", themeData: daylightTheme_ }

hoverProvider :: Effect HoverProvider
hoverProvider =
  runEffectFn1 hoverProvider_ \constructor ->
    let
      vs = Unfoldable.fromMaybe (Help.helpForConstructor constructor)

      items = map (\value -> { value }) vs
    in
      { contents: items }

completionItemProvider :: Effect CompletionItemProvider
completionItemProvider = runEffectFn1 completionItemProvider_ Linter.suggestions

codeActionProvider :: AdditionalContext -> Effect CodeActionProvider
codeActionProvider = runEffectFn2 codeActionProvider_ Linter.provideCodeActions

updateAdditionalContext :: CodeActionProvider -> CompletionItemProvider -> AdditionalContext -> Effect Unit
updateAdditionalContext = runEffectFn3 updateAdditionalContext_

documentFormattingEditProvider :: Effect DocumentFormattingEditProvider
documentFormattingEditProvider = runEffectFn1 documentFormattingEditProvider_ Linter.format

tokensProvider :: Effect TokensProvider
tokensProvider = runEffectFn1 tokensProvider_ unit

refLabel :: RefLabel
refLabel = RefLabel "marloweEditor"

settings :: forall m. MonadEffect m => (Editor -> m Unit) -> Settings m
settings setup =
  { languageExtensionPoint
  , theme: Just daylightTheme
  , monarchTokensProvider: pure Nothing
  , tokensProvider: traverse liftEffect $ Just tokensProvider
  , hoverProvider: traverse liftEffect $ Just hoverProvider
  , completionItemProvider: traverse liftEffect $ Just completionItemProvider
  , codeActionProvider: traverse liftEffect (Just $ codeActionProvider { warnings: mempty, contract: Nothing, metadataHints: mempty })
  , documentFormattingEditProvider: traverse liftEffect $ Just documentFormattingEditProvider
  , refLabel
  , owner: "marloweEditor"
  , setup
  }
