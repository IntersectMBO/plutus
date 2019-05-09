module Chartist
       ( barChart
       , CHARTIST
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
       , ChartistData
       , ChartistItem
       , ChartistPoint
       , toChartistData
       ) where

import Control.Monad.Eff (Eff, kind Effect)
import Control.Monad.Eff.Exception (EXCEPTION)
import Control.Monad.Eff.Uncurried (EffFn2, runEffFn2)
import Control.Semigroupoid ((<<<))
import DOM (DOM)
import DOM.HTML.Types (HTMLElement)
import Data.Array as Array
import Data.Foldable (foldl)
import Data.Function (($))
import Data.Maybe (maybe)
import Data.Unit (Unit)

foreign import data Chart :: Type
foreign import data ChartistPlugin :: Type
foreign import data AxisScale :: Type
foreign import data CHARTIST :: Effect

type ChartistPoint =
  { meta :: String
  , value :: Number
  }

type ChartistItem =
  { label :: String
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

type ChartistData =
    { labels :: Array String
    , series :: Array (Array ChartistPoint)
    }

type ChartistOptions =
  { seriesBarDistance :: Int
  , chartPadding ::
       { top :: Int
       , bottom :: Int
       , right :: Int
       , left :: Int
       }
  , axisY :: AxisScale
  , plugins :: Array ChartistPlugin
  }

type AxisTitleAxisOptions =
  { axisTitle :: String
  , axisClass :: String
  , offset :: { x :: Int
              , y :: Int
              }
  , textAnchor :: String
  , flipTitle :: Boolean
  }

type AxisTitleOptions =
  { axisX :: AxisTitleAxisOptions
  , axisY :: AxisTitleAxisOptions
  }

foreign import intAutoScaleAxis :: AxisScale
foreign import tooltipPlugin :: ChartistPlugin
foreign import axisTitlePlugin :: AxisTitleOptions -> ChartistPlugin
foreign import _barChart :: forall eff. EffFn2 (dom :: DOM, chartist :: CHARTIST | eff) HTMLElement ChartistOptions Chart
foreign import _updateData :: forall eff. EffFn2 (dom :: DOM, chartist :: CHARTIST | eff) Chart ChartistData Unit

updateData :: forall eff. Chart -> ChartistData -> Eff (dom :: DOM , chartist :: CHARTIST | eff) Unit
updateData = runEffFn2 _updateData

barChart ::
  forall eff.
  HTMLElement
  -> ChartistOptions
  -> Eff (dom :: DOM, chartist :: CHARTIST, exception :: EXCEPTION | eff) Chart
barChart element options =
  runEffFn2 _barChart element options
