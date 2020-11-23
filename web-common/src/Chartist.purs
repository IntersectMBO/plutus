module Chartist
  ( barChart
  , Chart
  , ChartistOptions
  , ChartistPlugin
  , tooltipPlugin
  , axisTitlePlugin
  , AxisScale
  , intAutoScaleAxis
  , AxisTitleOptions
  , AxisTitleAxisOptions
  , updateData
  , resize
  , ChartistData
  , ChartistItem
  , ChartistPoint
  , toChartistData
  ) where

import Effect (Effect)
import Effect.Uncurried (EffectFn1, runEffectFn1, EffectFn2, runEffectFn2)
import Control.Semigroupoid ((<<<))
import Web.HTML.HTMLElement (HTMLElement)
import Data.Array as Array
import Data.Foldable (foldl)
import Data.Function (($))
import Data.Maybe (maybe)
import Data.Unit (Unit)

foreign import data Chart :: Type

foreign import data ChartistPlugin :: Type

foreign import data AxisScale :: Type

type ChartistPoint
  = { meta :: String
    , value :: Number
    }

type ChartistItem
  = { label :: String
    , points :: Array ChartistPoint
    }

toChartistData :: Array ChartistItem -> ChartistData
toChartistData xs = foldl reducer { labels: [], series: initialSeries } xs
  where
  initialSeries = Array.replicate n []

  n = maybe 0 (Array.length <<< _.points) $ Array.head xs

  reducer { labels, series } { label, points } =
    { labels: Array.snoc labels label
    , series: Array.zipWith Array.snoc series points
    }

type ChartistData
  = { labels :: Array String
    , series :: Array (Array ChartistPoint)
    }

type ChartistOptions
  = { seriesBarDistance :: Int
    , chartPadding ::
        { top :: Int
        , bottom :: Int
        , right :: Int
        , left :: Int
        }
    , axisY :: AxisScale
    , plugins :: Array ChartistPlugin
    }

type AxisTitleAxisOptions
  = { axisTitle :: String
    , axisClass :: String
    , offset ::
        { x :: Int
        , y :: Int
        }
    , textAnchor :: String
    , flipTitle :: Boolean
    }

type AxisTitleOptions
  = { axisX :: AxisTitleAxisOptions
    , axisY :: AxisTitleAxisOptions
    }

foreign import intAutoScaleAxis :: AxisScale

foreign import tooltipPlugin :: ChartistPlugin

foreign import axisTitlePlugin :: AxisTitleOptions -> ChartistPlugin

foreign import _barChart :: EffectFn2 HTMLElement ChartistOptions Chart

foreign import _updateData :: EffectFn2 Chart ChartistData Unit

foreign import _resize :: EffectFn1 Chart Unit

updateData :: Chart -> ChartistData -> Effect Unit
updateData = runEffectFn2 _updateData

resize :: Chart -> Effect Unit
resize = runEffectFn1 _resize

barChart ::
  HTMLElement ->
  ChartistOptions ->
  Effect Chart
barChart element options = runEffectFn2 _barChart element options
