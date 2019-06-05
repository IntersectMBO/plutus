module Halogen.Chartist
       ( chartist
       , ChartistQuery(..)
       , ChartistMessage(..)
       ) where

import Chartist (Chart, ChartistData, ChartistOptions, updateData)
import Chartist as Chartist
import Control.Applicative (pure)
import Control.Bind (bind, discard, (>>=))
import Data.Function (($))
import Data.Maybe (Maybe(Just, Nothing))
import Data.NaturalTransformation (type (~>))
import Data.Unit (unit)
import Effect.Aff.Class (class MonadAff)
import Effect.Class (liftEffect)
import Halogen (RefLabel(..))
import Halogen as H
import Halogen.HTML (ClassName(..))
import Halogen.HTML as HH
import Halogen.HTML.Events as HE
import Halogen.HTML.Properties (classes)
import Halogen.HTML.Properties as HP

type ChartistState =
  { chart :: Maybe Chart
  }

data ChartistQuery a
  = Init ChartistOptions a
  | SetData ChartistData a

data ChartistMessage
  = Initialized

type HTML = H.ComponentHTML ChartistQuery

type DSL m = H.ComponentDSL ChartistState ChartistQuery ChartistMessage m

chartist ::
  forall m.
  MonadAff m
  => ChartistOptions
  -> H.Component HH.HTML ChartistQuery ChartistData ChartistMessage m
chartist options = H.lifecycleComponent
  { initialState: \_ -> { chart: Nothing }
  , render
  , eval
  , initializer: Just $ H.action $ Init options
  , finalizer: Nothing
  , receiver: HE.input SetData
  }

eval ::
  forall m.
  MonadAff m
  => ChartistQuery ~> DSL m
eval (Init options next) = do
  mElement <- H.getHTMLElementRef chartRefLabel
  case mElement of
    Nothing -> pure unit
    Just element -> do
      chart <- liftEffect $ Chartist.barChart element options
      _ <- H.modify _{ chart = Just chart }
      H.raise Initialized
  pure next

eval (SetData chartistData next) = do
  H.gets _.chart >>= case _ of
    Nothing -> pure unit
    Just chart -> liftEffect $ updateData chart chartistData
  pure next

chartRefLabel :: RefLabel
chartRefLabel = RefLabel "chartist"

render ∷ ChartistState → HTML
render state =
  HH.div
    [ classes [ ClassName "ct-chart"
              , ClassName "ct-major-twelfth"
              ]
    , HP.ref chartRefLabel
    ]
    []
