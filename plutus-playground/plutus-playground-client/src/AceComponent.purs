module AceComponent
  ( AceQuery(..)
  , AceOutput(..)
  , Position
  , RawDocumentEvent
  , aceComponent
  ) where

import Ace as Ace
import Ace.EditSession as Session
import Ace.Editor as Editor
import Ace.Types (Editor)
import Data.Lens (Lens', assign)
import Data.Lens.Record (prop)
import Data.Maybe (Maybe(..))
import Data.Symbol (SProxy(..))
import Effect.Aff (Aff)
import Halogen as H
import Halogen.HTML (div)
import Halogen.HTML as HH
import Halogen.HTML.Properties as HP
import Halogen.Query (RefLabel)
import Prelude (type (~>), Unit, bind, const, discard, pure, unit, void, when, ($), (/=), (<<<), (>>=))

-- | The state for the ace component - we only need a reference to the editor,
-- | as Ace editor has its own internal state that we can query instead of
-- | replicating it within Halogen.
type AceState =
  { editor :: Maybe Editor }

type Position =
  { row :: Int
  , column :: Int
  }

type RawDocumentEvent =
  { action :: String
  , start :: Position
  , end :: Position
  , lines :: Array String
  }

-- | A basic query algebra for the Ace component.
data AceQuery a
  = Initialize (Maybe String) a
  | Finalize a
  | ChangeText String a
  | HandleChange RawDocumentEvent (H.SubscribeStatus -> a)

data AceOutput
  = TextChanged String

-- | The Ace component definition.
aceComponent :: Maybe String -> H.Component HH.HTML AceQuery Unit AceOutput Aff -- AceQuery Unit AceOutput Aff
aceComponent initialContents =
  H.lifecycleComponent
    { initialState: const initialState
    , render
    , eval
    , initializer: Just (H.action (Initialize initialContents))
    , finalizer: Just (H.action Finalize)
    , receiver: const Nothing
    }

initialState :: AceState
initialState =
  { editor: Nothing }

_editor :: forall s a. Lens' {editor :: a | s} a
_editor = prop (SProxy :: SProxy "editor")

aceRef :: RefLabel
aceRef = H.RefLabel "ace"

-- The query algebra for the component handles the initialization of the Ace
-- editor as well as responding to the `ChangeText` action that allows us to
-- alter the editor's state.
eval :: AceQuery ~> H.ComponentDSL AceState AceQuery AceOutput Aff
eval (Initialize initialContents next) = do
  H.getHTMLElementRef aceRef >>= case _ of
      Nothing -> pure unit
      Just element -> do
        editor <- H.liftEffect $ Ace.editNode element Ace.ace
        session <- H.liftEffect $ Editor.getSession editor
        assign _editor (Just editor)
        H.subscribe
          $ H.eventSource (Session.onChange session)
          $ Just <<< H.request <<< HandleChange
  case initialContents of
    Nothing -> pure next
    Just text -> eval (ChangeText text next)

-- Release the reference to the editor and do any other cleanup that a
-- real world component might need.
eval (Finalize next) = do
  void $ H.modify (_ { editor = Nothing })
  pure next

eval (ChangeText text next) = do
  H.gets _.editor >>= case _ of
    Nothing -> pure unit
    Just editor -> do
      current <- H.liftEffect $ Editor.getValue editor
      when (text /= current) do
        void $ H.liftEffect $ Editor.setValue text Nothing editor
  H.raise $ TextChanged text
  pure next

eval (HandleChange _ reply) = do
  H.gets _.editor >>= case _ of
    Nothing -> pure unit
    Just editor -> do
      text <- H.liftEffect (Editor.getValue editor)
      H.raise $ TextChanged text
  pure $ reply H.Listening

-- As we're embedding a 3rd party component we only need to create a
-- placeholder div here and attach the ref property which will let us reference
-- the element in eval.
render :: AceState -> H.ComponentHTML AceQuery
render _ =
   div [ HP.ref aceRef ] []
