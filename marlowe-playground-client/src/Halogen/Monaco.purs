module Halogen.Monaco where

import Data.Either (Either(..))
import Data.Lens (view)
import Data.Maybe (Maybe(..))
import Data.Traversable (traverse)
import Effect.Aff.Class (class MonadAff)
import Effect.Class (class MonadEffect, liftEffect)
import Halogen (HalogenM, RefLabel)
import Halogen as H
import Halogen.HTML (HTML, div)
import Halogen.HTML.Properties (class_, ref)
import Halogen.Query.EventSource (Emitter(..), Finalizer(..), effectEventSource)
import Monaco (CodeActionProvider, CompletionItemProvider, DocumentFormattingEditProvider, Editor, IMarker, IMarkerData, IPosition, LanguageExtensionPoint, Theme, TokensProvider)
import Monaco as Monaco
import Prelude (Unit, bind, const, discard, pure, unit, void, ($), (>>=))

type State
  = { editor :: Maybe Editor }

data Query a
  = SetText String a
  | GetText (String -> a)
  | SetPosition IPosition a
  | Resize a

data Action
  = Init
  | HandleChange String (Array IMarker)

data Message
  = TextChanged String
  | MarkersChanged (Array IMarker)

type Settings m
  = { languageExtensionPoint :: LanguageExtensionPoint
    , theme :: Theme
    , tokensProvider :: TokensProvider
    , completionItemProvider :: CompletionItemProvider
    , codeActionProvider :: CodeActionProvider
    , documentFormattingEditProvider :: DocumentFormattingEditProvider
    , refLabel :: RefLabel
    , owner :: String
    , getModelMarkers :: String -> Array IMarkerData
    , setup :: Editor -> m Unit
    }

monacoComponent :: forall m. MonadAff m => MonadEffect m => Settings m -> H.Component HTML Query Unit Message m
monacoComponent setup =
  H.mkComponent
    { initialState: const { editor: Nothing }
    , render
    , eval:
      H.mkEval
        { handleAction: handleAction setup
        , handleQuery
        , initialize: Just Init
        , receive: const Nothing
        , finalize: Nothing
        }
    }

render :: forall p i. State -> HTML p i
render state =
  div
    [ ref $ H.RefLabel "monacoEditor"
    , class_ $ H.ClassName "monaco-editor-container"
    ]
    []

handleAction :: forall slots m. MonadAff m => MonadEffect m => Settings m -> Action -> HalogenM State Action slots Message m Unit
handleAction settings Init = do
  monaco <- liftEffect Monaco.getMonaco
  maybeElement <- H.getHTMLElementRef settings.refLabel
  case maybeElement of
    Just element -> do
      let
        languageId = view Monaco._id settings.languageExtensionPoint
      liftEffect do
        Monaco.registerLanguage monaco settings.languageExtensionPoint
        Monaco.defineTheme monaco settings.theme
        Monaco.setTokensProvider monaco languageId settings.tokensProvider
        Monaco.registerCompletionItemProvider monaco languageId settings.completionItemProvider
        Monaco.registerCodeActionProvider monaco languageId settings.codeActionProvider
        Monaco.registerDocumentFormattingEditProvider monaco languageId settings.documentFormattingEditProvider
      editor <- liftEffect $ Monaco.create monaco element languageId settings.theme.name
      void $ H.modify (const { editor: Just editor })
      void $ H.subscribe $ effectEventSource (changeContentHandler monaco editor)
      H.lift $ settings.setup editor
    Nothing -> pure unit
  where
  changeContentHandler monaco editor (Emitter emitter) = do
    Monaco.onDidChangeContent editor
      ( \_ -> do
          model <- Monaco.getModel editor
          Monaco.setModelMarkers monaco model settings.owner settings.getModelMarkers
          markers <- Monaco.getModelMarkers monaco model
          emitter $ Left $ HandleChange (Monaco.getValue model) markers
      )
    pure $ Finalizer $ pure unit

handleAction _ (HandleChange contents markers) = do
  H.raise $ TextChanged contents
  H.raise $ MarkersChanged markers

-- If the editor has been set then we can use it when handling our Query
withEditor :: forall input m a. MonadEffect m => (Editor -> HalogenM State Action input Message m a) -> HalogenM State Action input Message m (Maybe a)
withEditor f = H.gets _.editor >>= traverse f

handleQuery :: forall a input m. MonadEffect m => Query a -> HalogenM State Action input Message m (Maybe a)
handleQuery (SetText text next) = do
  withEditor \editor -> do
    model <- liftEffect $ Monaco.getModel editor
    liftEffect $ Monaco.setValue model text
    pure next

handleQuery (GetText f) = do
  withEditor \editor -> do
    model <- liftEffect $ Monaco.getModel editor
    let
      s = Monaco.getValue model
    pure $ f s

handleQuery (SetPosition position next) = do
  withEditor \editor -> do
    liftEffect $ Monaco.setPosition editor position
    liftEffect $ Monaco.revealLine editor position.lineNumber
    pure next

handleQuery (Resize next) = do
  withEditor \editor -> do
    liftEffect $ Monaco.layout editor
    pure next
