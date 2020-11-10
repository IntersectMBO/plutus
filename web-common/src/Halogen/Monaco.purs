module Halogen.Monaco
  ( KeyBindings(..)
  , Settings
  , Query(..)
  , Objects
  , Message(..)
  , monacoComponent
  ) where

import Data.Either (Either(..))
import Data.Enum (class BoundedEnum, class Enum)
import Data.Generic.Rep (class Generic)
import Data.Generic.Rep.Bounded (genericBottom, genericTop)
import Data.Generic.Rep.Enum (genericCardinality, genericFromEnum, genericPred, genericSucc, genericToEnum)
import Data.Generic.Rep.Eq (genericEq)
import Data.Generic.Rep.Ord (genericCompare)
import Data.Lens (view)
import Data.Maybe (Maybe(..))
import Data.Traversable (for_, traverse)
import Effect (Effect)
import Effect.Aff.Class (class MonadAff)
import Effect.Class (class MonadEffect, liftEffect)
import Halogen (HalogenM, RefLabel, get, modify_)
import Halogen as H
import Halogen.HTML (HTML, div)
import Halogen.HTML.Properties (class_, ref)
import Halogen.Query.EventSource (Emitter(..), Finalizer, effectEventSource)
import Monaco (CodeActionProvider, CompletionItemProvider, DocumentFormattingEditProvider, Editor, HoverProvider, IMarker, IMarkerData, IPosition, LanguageExtensionPoint, MonarchLanguage, Theme, TokensProvider, IRange)
import Monaco as Monaco
import Prelude (class Applicative, class Bounded, class Eq, class Ord, class Show, Unit, bind, const, discard, mempty, pure, unit, void, when, ($), (==), (>>=))

data KeyBindings
  = DefaultBindings
  | Vim
  | Emacs

derive instance genericKeyBindings :: Generic KeyBindings _

instance showKeyBindings :: Show KeyBindings where
  show DefaultBindings = "Default Key Bindings"
  show Vim = "Vim"
  show Emacs = "Emacs"

instance eqKeyBindings :: Eq KeyBindings where
  eq = genericEq

instance ordKeyBindings :: Ord KeyBindings where
  compare = genericCompare

instance enumKeyBindings :: Enum KeyBindings where
  succ = genericSucc
  pred = genericPred

instance boundedKeyBindings :: Bounded KeyBindings where
  bottom = genericBottom
  top = genericTop

instance boundedEnumKeyBindings :: BoundedEnum KeyBindings where
  cardinality = genericCardinality
  toEnum = genericToEnum
  fromEnum = genericFromEnum

type Objects
  = { codeActionProvider :: Maybe CodeActionProvider
    , completionItemProvider :: Maybe CompletionItemProvider
    }

newtype CancelBindings
  = CancelBindings (Effect Unit)

defaultCancelBindings :: CancelBindings
defaultCancelBindings = CancelBindings (pure unit)

type State
  = { editor :: Maybe Editor
    , deactivateBindings :: CancelBindings
    , objects :: Objects
    }

data Query a
  = SetText String a
  | GetText (String -> a)
  | GetLineCount (Int -> a)
  | GetModel (Monaco.ITextModel -> a)
  | GetModelMarkers (Array IMarker -> a)
  | GetDecorationRange String (IRange -> a)
  | SetDeltaDecorations Int Int (String -> a)
  | SetPosition IPosition a
  | Focus a
  | Resize a
  | SetTheme String a
  | SetModelMarkers (Array IMarkerData) (Array IMarker -> a)
  | SetKeyBindings KeyBindings a
  | GetObjects (Objects -> a)

data Action
  = Init
  | HandleChange String

data Message
  = TextChanged String

type Settings m
  = { languageExtensionPoint :: LanguageExtensionPoint
    , theme :: Maybe Theme
    , monarchTokensProvider :: Maybe MonarchLanguage
    , tokensProvider :: Maybe TokensProvider
    , hoverProvider :: Maybe HoverProvider
    , completionItemProvider :: Maybe CompletionItemProvider
    , codeActionProvider :: Maybe CodeActionProvider
    , documentFormattingEditProvider :: Maybe DocumentFormattingEditProvider
    , refLabel :: RefLabel
    , owner :: String
    , setup :: Editor -> m Unit
    }

monacoComponent :: forall m. MonadAff m => MonadEffect m => Settings m -> H.Component HTML Query Unit Message m
monacoComponent settings =
  H.mkComponent
    { initialState:
      const
        { editor: Nothing
        , deactivateBindings: defaultCancelBindings
        , objects:
          { codeActionProvider: settings.codeActionProvider
          , completionItemProvider: settings.completionItemProvider
          }
        }
    , render: render settings
    , eval:
      H.mkEval
        { handleAction: handleAction settings
        , handleQuery
        , initialize: Just Init
        , receive: const Nothing
        , finalize: Nothing
        }
    }

render :: forall m p i. Settings m -> State -> HTML p i
render settings state =
  div
    [ ref settings.refLabel
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
        when (languageId == "typescript") do
          Monaco.addExtraTypeScriptLibsJS monaco
          Monaco.setStrictNullChecks monaco true
        Monaco.registerLanguage monaco settings.languageExtensionPoint
        for_ settings.theme $ Monaco.defineTheme monaco
        for_ settings.monarchTokensProvider $ Monaco.setMonarchTokensProvider monaco languageId
        for_ settings.tokensProvider $ Monaco.setTokensProvider monaco languageId
        for_ settings.hoverProvider $ Monaco.registerHoverProvider monaco languageId
        for_ settings.completionItemProvider $ Monaco.registerCompletionItemProvider monaco languageId
        for_ settings.codeActionProvider $ Monaco.registerCodeActionProvider monaco languageId
        for_ settings.documentFormattingEditProvider $ Monaco.registerDocumentFormattingEditProvider monaco languageId
      editor <- liftEffect $ Monaco.create monaco element languageId
      void $ H.subscribe $ effectEventSource (changeContentHandler editor)
      void $ H.modify (_ { editor = Just editor })
      H.lift $ settings.setup editor
      model <- liftEffect $ Monaco.getModel editor
      H.raise $ TextChanged (Monaco.getValue model)
      pure unit
    Nothing -> pure unit

handleAction _ (HandleChange contents) = H.raise $ TextChanged contents

changeContentHandler ::
  forall m.
  Applicative m =>
  Editor ->
  Emitter Effect Action -> Effect (Finalizer m)
changeContentHandler editor (Emitter emitter) = do
  Monaco.onDidChangeContent editor
    ( \_ -> do
        model <- Monaco.getModel editor
        emitter $ Left $ HandleChange (Monaco.getValue model)
    )
  pure mempty

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

handleQuery (GetLineCount f) = do
  withEditor \editor -> do
    model <- liftEffect $ Monaco.getModel editor
    let
      i = Monaco.getLineCount model
    pure $ f i

handleQuery (GetModel f) = do
  withEditor \editor -> do
    m <- liftEffect $ Monaco.getModel editor
    pure $ f m

handleQuery (GetModelMarkers f) = do
  withEditor \editor ->
    liftEffect do
      monaco <- Monaco.getMonaco
      model <- Monaco.getModel editor
      markers <- Monaco.getModelMarkers monaco model
      pure $ f markers

handleQuery (GetDecorationRange decoratorId f) = do
  withEditor \editor -> do
    liftEffect do
      model <- liftEffect $ Monaco.getModel editor
      let
        decoRange = Monaco.getDecorationRange model decoratorId
      pure $ f decoRange

handleQuery (SetDeltaDecorations first last f) = do
  withEditor \editor -> do
    decoId <- liftEffect $ Monaco.setDeltaDecorations editor first last
    pure $ f decoId

handleQuery (SetPosition position next) = do
  withEditor \editor -> do
    liftEffect $ Monaco.setPosition editor position
    liftEffect $ Monaco.revealLine editor position.lineNumber
    pure next

handleQuery (Focus next) = do
  withEditor \editor -> do
    liftEffect $ Monaco.focus editor
    pure next

handleQuery (Resize next) = do
  withEditor \editor -> do
    liftEffect $ Monaco.layout editor
    pure next

handleQuery (SetTheme themeName next) = do
  liftEffect do
    monaco <- Monaco.getMonaco
    Monaco.setTheme monaco themeName
    pure $ Just next

handleQuery (SetModelMarkers markersData f) = do
  withEditor \editor ->
    liftEffect do
      let
        owner = Monaco.getEditorId editor
      monaco <- Monaco.getMonaco
      model <- Monaco.getModel editor
      Monaco.setModelMarkers monaco model owner markersData
      markers <- Monaco.getModelMarkers monaco model
      pure $ f markers

handleQuery (SetKeyBindings bindings next) =
  withEditor \editor -> do
    { deactivateBindings } <- get
    newDeactivateBindings <- liftEffect $ replaceKeyBindings bindings editor deactivateBindings
    modify_ (_ { deactivateBindings = newDeactivateBindings })
    pure next

handleQuery (GetObjects f) = do
  { objects } <- get
  pure $ Just $ f objects

replaceKeyBindings :: KeyBindings -> Editor -> CancelBindings -> Effect CancelBindings
replaceKeyBindings bindings editor (CancelBindings deactivateOldBindings) = do
  let
    enableFn :: KeyBindings -> Editor -> Effect (Effect Unit)
    enableFn DefaultBindings = pure $ pure $ pure unit

    enableFn Vim = Monaco.enableVimBindings

    enableFn Emacs = Monaco.enableEmacsBindings
  deactivateOldBindings
  deactivateNewBindings <- enableFn bindings editor
  pure $ CancelBindings deactivateNewBindings
