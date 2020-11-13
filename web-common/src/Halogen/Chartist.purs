module Halogen.Chartist
  ( chartist
  , Query(..)
  , Message(..)
  ) where

import Chartist (Chart, ChartistData, ChartistOptions, resize, updateData)
import Chartist as Chartist
import Control.Applicative (pure)
import Control.Bind (bind, (>>=), discard)
import Control.Category ((<<<))
import Data.Function (const, ($))
import Data.Maybe (Maybe(Just, Nothing))
import Data.Unit (Unit, unit)
import Effect.Aff.Class (class MonadAff)
import Effect.Class (class MonadEffect, liftEffect)
import Halogen (HalogenM, RefLabel(..))
import Halogen as H
import Halogen.HTML (ClassName(..))
import Halogen.HTML as HH
import Halogen.HTML.Properties (classes)
import Halogen.HTML.Properties as HP

type State
  = { chart :: Maybe Chart
    }

data Query a
  = Resize a

data Action
  = Init ChartistOptions
  | SetData ChartistData

data Message
  = Initialized

chartist ::
  forall m.
  MonadAff m =>
  MonadEffect m =>
  ChartistOptions ->
  H.Component HH.HTML Query ChartistData Message m
chartist options =
  H.mkComponent
    { initialState: const { chart: Nothing }
    , render
    , eval:
        H.mkEval
          { handleAction
          , handleQuery
          , initialize: Just $ Init options
          , receive: Just <<< SetData
          , finalize: Nothing
          }
    }

handleQuery :: forall a input m. MonadEffect m => Query a -> HalogenM State Action input Message m (Maybe a)
handleQuery (Resize next) = do
  H.gets _.chart
    >>= case _ of
        Nothing -> pure unit
        Just chart -> liftEffect $ resize chart
  pure $ Just next

handleAction :: forall slots m. MonadEffect m => Action -> HalogenM State Action slots Message m Unit
handleAction (Init options) = do
  mElement <- H.getHTMLElementRef chartRefLabel
  case mElement of
    Nothing -> pure unit
    Just element -> do
      chart <- liftEffect $ Chartist.barChart element options
      _ <- H.modify _ { chart = Just chart }
      H.raise Initialized

handleAction (SetData chartistData) = do
  H.gets _.chart
    >>= case _ of
        Nothing -> pure unit
        Just chart -> liftEffect $ updateData chart chartistData

chartRefLabel :: RefLabel
chartRefLabel = RefLabel "chartist"

render ∷ forall p i. State -> HH.HTML p i
render state =
  HH.div
    [ classes
        [ ClassName "ct-chart"
        , ClassName "ct-major-twelfth"
        ]
    , HP.ref chartRefLabel
    ]
    []
