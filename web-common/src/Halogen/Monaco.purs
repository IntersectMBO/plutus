module Halogen.Monaco
  ( KeyBindings(..)
  , Settings
  , Query(..)
  , Objects
  , Message(..)
  , monacoComponent
  ) where

import Prelude hiding (div)
import Control.Monad.Maybe.Trans (MaybeT(..), runMaybeT)
import Control.Monad.Trans.Class (lift)
import Data.Array (catMaybes)
import Data.Either (Either(..))
import Data.Enum (class BoundedEnum, class Enum)
import Data.Generic.Rep (class Generic)
import Data.Generic.Rep.Bounded (genericBottom, genericTop)
import Data.Generic.Rep.Enum (genericCardinality, genericFromEnum, genericPred, genericSucc, genericToEnum)
import Data.Generic.Rep.Eq (genericEq)
import Data.Generic.Rep.Ord (genericCompare)
import Data.Lens (Lens', set, use, view)
import Data.Lens.Record (prop)
import Data.Maybe (Maybe(..))
import Data.Symbol (SProxy(..))
import Data.Traversable (for, for_, sequence, traverse)
import Effect (Effect)
import Effect.Aff.Class (class MonadAff)
import Effect.Class (class MonadEffect, liftEffect)
import Halogen (HalogenM, RefLabel, get, modify_)
import Halogen as H
import Halogen.ElementResize (elementResize)
import Halogen.HTML (HTML, div)
import Halogen.HTML.Properties (class_, ref)
import Halogen.Query.EventSource (Emitter(..), Finalizer, effectEventSource)
import Monaco (CodeActionProvider, CompletionItemProvider, DocumentFormattingEditProvider, Editor, HoverProvider, IDisposable, IMarker, IMarkerData, IModelDeltaDecoration, IPosition, IRange, LanguageExtensionPoint, MonarchLanguage, Theme, TokensProvider, dispose)
import Monaco as Monaco
import Web.DOM.ResizeObserver (ResizeObserverBoxOptions(..))
import Web.HTML.HTMLElement as HTMLElement

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
    , disposables :: Array IDisposable
    }

_editor :: Lens' State (Maybe Editor)
_editor = prop (SProxy :: SProxy "editor")

_mCodeActionProvider :: Lens' State (Maybe CodeActionProvider)
_mCodeActionProvider = prop (SProxy :: SProxy "objects") <<< prop (SProxy :: SProxy "codeActionProvider")

_mCompletionItemProvider :: Lens' State (Maybe CompletionItemProvider)
_mCompletionItemProvider = prop (SProxy :: SProxy "objects") <<< prop (SProxy :: SProxy "completionItemProvider")

_disposables :: Lens' State (Array IDisposable)
_disposables = prop (SProxy :: SProxy "disposables")

data Query a
  = SetText String a
  | GetText (String -> a)
  | GetLineCount (Int -> a)
  | GetModel (Monaco.ITextModel -> a)
  | GetModelMarkers (Array IMarker -> a)
  | GetDecorationRange String (IRange -> a)
  | SetDeltaDecorations (Array String) (Array IModelDeltaDecoration) (Array String -> a)
  | SetPosition IPosition a
  | RevealRange IRange a
  | Focus a
  | Resize a
  | SetTheme String a
  | SetModelMarkers (Array IMarkerData) (Array IMarker -> a)
  | SetKeyBindings KeyBindings a
  | GetObjects (Objects -> a)

data Action
  = Init
  | Finalize
  | HandleChange String
  | ResizeWorkspace

data Message
  = TextChanged String
  | EditorReady

type Settings m
  = { languageExtensionPoint :: LanguageExtensionPoint
    , theme :: Maybe Theme
    , monarchTokensProvider :: m (Maybe MonarchLanguage)
    , tokensProvider :: m (Maybe TokensProvider)
    , hoverProvider :: m (Maybe HoverProvider)
    , completionItemProvider :: m (Maybe CompletionItemProvider)
    , codeActionProvider :: m (Maybe CodeActionProvider)
    , documentFormattingEditProvider :: m (Maybe DocumentFormattingEditProvider)
    , refLabel :: RefLabel
    , owner :: String
    , setup :: Editor -> m Unit
    }

monacoComponent :: forall m. MonadAff m => Settings m -> H.Component HTML Query Unit Message m
monacoComponent settings =
  H.mkComponent
    { initialState:
        const
          { editor: Nothing
          , deactivateBindings: defaultCancelBindings
          , objects:
              { codeActionProvider: Nothing
              , completionItemProvider: Nothing
              }
          , disposables: []
          }
    , render: render settings.refLabel
    , eval:
        H.mkEval
          { handleAction: handleAction settings
          , handleQuery
          , initialize: Just Init
          , receive: const Nothing
          , finalize: Just Finalize
          }
    }

render :: forall p i. RefLabel -> State -> HTML p i
render label state =
  div
    [ ref label
    , class_ $ H.ClassName "monaco-editor-container"
    ]
    []

handleAction :: forall slots m. MonadAff m => Settings m -> Action -> HalogenM State Action slots Message m Unit
handleAction settings Init = do
  monaco <- liftEffect Monaco.getMonaco
  maybeElement <- H.getHTMLElementRef settings.refLabel
  case maybeElement of
    Just element -> do
      let
        languageId = view Monaco._id settings.languageExtensionPoint
      -- The monaco component receives in its settings multiple optional providers. The
      -- settings are created inside a view, but to create the provider we need access to Effect so
      -- we can call the FFI.
      -- To solve this in the least disrupting way I modified the existing `Settings m` so that we
      -- can pass an effectful computation that may return a provider (m (Maybe XProvider)).
      -- And the following code invokes the FFI function returning a Maybe XProvider.
      -- TODO: We should re-arrange the `Settings m` and move the logic from the view to the handleAction
      --       changing the `Settings m` to be just `Settings` and the `setup` logic not to be included in there.
      mMonarchTokensProvider <- H.lift $ settings.monarchTokensProvider
      mTokensProvider <- H.lift $ settings.tokensProvider
      mHoverProvider <- H.lift $ settings.hoverProvider
      mCodeActionProvider <- H.lift $ settings.codeActionProvider
      mCompletionItemProvider <- H.lift $ settings.completionItemProvider
      mDocumentFormattingEditProvider <- H.lift $ settings.documentFormattingEditProvider
      liftEffect do
        when (languageId == "typescript") do
          Monaco.addExtraTypeScriptLibsJS monaco
          Monaco.setStrictNullChecks monaco true
        Monaco.registerLanguage monaco settings.languageExtensionPoint
        for_ settings.theme $ Monaco.defineTheme monaco
      -- We set the defined providers and receive an array of the cleanup functions
      disposables :: Array IDisposable <-
        liftEffect $ catMaybes
          <$> sequence
              [ for mMonarchTokensProvider $ Monaco.setMonarchTokensProvider monaco languageId
              , for mTokensProvider $ Monaco.setTokensProvider monaco languageId
              , for mHoverProvider $ Monaco.registerHoverProvider monaco languageId
              , for mCompletionItemProvider $ Monaco.registerCompletionItemProvider monaco languageId
              , for mCodeActionProvider $ Monaco.registerCodeActionProvider monaco languageId
              , for mDocumentFormattingEditProvider $ Monaco.registerDocumentFormattingEditProvider monaco languageId
              ]
      editor <- liftEffect $ Monaco.create monaco element languageId
      void $ H.modify
        $ set _editor (Just editor)
        <<< set _mCodeActionProvider mCodeActionProvider
        <<< set _mCompletionItemProvider mCompletionItemProvider
        <<< set _disposables disposables
      H.lift $ settings.setup editor
      model <- liftEffect $ Monaco.getModel editor
      void $ H.subscribe $ elementResize ContentBox (const ResizeWorkspace) (HTMLElement.toElement element)
      H.raise EditorReady
      H.raise $ TextChanged (Monaco.getValue model)
      void $ H.subscribe $ effectEventSource (changeContentHandler editor)
    Nothing -> pure unit

handleAction _ Finalize = do
  disposables <- use _disposables
  for_ disposables $ liftEffect <<< dispose

handleAction _ (HandleChange contents) = H.raise $ TextChanged contents

handleAction _ ResizeWorkspace = do
  mEditor <- use _editor
  for_ mEditor \editor ->
    liftEffect $ Monaco.layout editor

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
    -- We want to avoid setting the same value because it will cause https://microsoft.github.io/monaco-editor/api/interfaces/monaco.editor.itextmodel.html#ondidchangecontent
    -- to fire even though the content didn't change
    when (text /= Monaco.getValue model) $ liftEffect $ Monaco.setValue model text
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

handleQuery (GetDecorationRange decoratorId f) =
  runMaybeT do
    editor <- MaybeT $ H.gets _.editor
    model <- lift $ liftEffect $ Monaco.getModel editor
    decoRange <- MaybeT $ liftEffect $ Monaco.getDecorationRange model decoratorId
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

handleQuery (RevealRange range next) = do
  withEditor \editor -> do
    liftEffect $ Monaco.revealRange editor range
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
    -- Changing keybindings can affect layout (by changing the status
    -- line in Vim/Emacs modes, for instance).
    liftEffect $ Monaco.layout editor
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
