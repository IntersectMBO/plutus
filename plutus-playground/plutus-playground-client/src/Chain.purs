module Chain
       ( mockchainChartOptions
       , balancesChartOptions
       , evaluationPane
       ) where

import Bootstrap (empty, nbsp)
import Color (Color, rgb, white)
import Control.Monad.Aff.Class (class MonadAff)
import Data.Array as Array
import Data.Foldable (traverse_)
import Data.Generic (gShow)
import Data.Int as Int
import Data.Maybe (Maybe(Nothing))
import Data.Newtype (unwrap)
import Data.Tuple (Tuple, fst, snd)
import Data.Tuple.Nested ((/\))
import ECharts.Commands (addItem, addLink, axisLine, axisType, backgroundColor, bar, bottom, buildItems, buildLinks, color, colorSource, colors, formatterString, itemStyle, items, label, left, lineStyle, name, nameGap, nameLocationMiddle, nameRotate, normal, right, sankey, series, sourceName, splitLine, targetName, textStyle, tooltip, top, trigger, value, xAxis, yAxis) as E
import ECharts.Extras (focusNodeAdjacencyAllEdges, orientVertical, positionBottom)
import ECharts.Monad (CommandsT, DSL) as E
import ECharts.Types (AxisType(Value, Category), PixelOrPercent(Pixel), TooltipTrigger(ItemTrigger), numItem, strItem) as E
import ECharts.Types.Phantom (I)
import Halogen (HTML)
import Halogen.Component (ParentHTML)
import Halogen.ECharts (EChartsEffects, echarts)
import Halogen.HTML (ClassName(ClassName), br_, div, div_, h2_, h3_, slot', text)
import Halogen.HTML.Events (input)
import Halogen.HTML.Properties (class_)
import Ledger.Value.TH (Value)
import Ledger.Types (TxIdOf(..))
import Ledger.Interval (Slot(..))
import Playground.API (EvaluationResult(EvaluationResult))
import Prelude (class Monad, Unit, discard, map, show, unit, ($), (<$>), (<>), (>>>))
import Types (BalancesChartSlot(BalancesChartSlot), ChildQuery, ChildSlot, MockchainChartSlot(MockchainChartSlot), Query(HandleBalancesChartMessage, HandleMockchainChartMessage), cpBalancesChart, cpMockchainChart)
import Wallet.Emulator.Types (EmulatorEvent(..), Wallet(..))
import Wallet.Graph (FlowGraph(FlowGraph), FlowLink(FlowLink), TxRef(TxRef))

evaluationPane::
  forall m aff.
  MonadAff (EChartsEffects aff) m
  => EvaluationResult
  -> ParentHTML Query ChildQuery ChildSlot m
evaluationPane (EvaluationResult {emulatorLog}) =
  div_
    [ h2_ [ text "Transactions" ]
    , div_
        [ h3_ [ text "Chain" ]
        , slot' cpMockchainChart MockchainChartSlot
            (echarts Nothing)
            ({width: 930, height: 600} /\ unit)
            (input HandleMockchainChartMessage)
        ]
    , br_
    , div_
        [ h3_ [ text "Logs" ]
        , case emulatorLog of
            [] -> empty
            logs ->
              div
                [ class_ $ ClassName "logs" ]
                (emulatorEventPane <$> Array.reverse logs)
        ]
    , br_
    , div_
        [ h3_ [ text "Final Balances" ]
        , slot' cpBalancesChart BalancesChartSlot
            (echarts Nothing)
            ({width: 930, height: 300} /\ unit)
            (input HandleBalancesChartMessage)
        ]
    ]

emulatorEventPane :: forall i p. EmulatorEvent -> HTML p i
emulatorEventPane (TxnSubmit (TxIdOf txId)) =
  div_
    [ text $ "Submitting transaction: " <> txId.getTxId ]

emulatorEventPane (TxnValidate (TxIdOf txId)) =
  div_
    [ text $ "Validating transaction: " <> txId.getTxId ]

emulatorEventPane (TxnValidationFail (TxIdOf txId) error) =
  div [ class_ $ ClassName "error" ]
    [ text $ "Validation failed for transaction: " <> txId.getTxId
    , br_
    , nbsp
    , text $ gShow error
    ]

emulatorEventPane (SlotAdd (Slot slot)) =
  div [ class_ $ ClassName "info" ]
    [ text $ "Add slot #" <> show slot.getSlot ]

emulatorEventPane (WalletError (Wallet walletId) error) =
  div [ class_ $ ClassName "error" ]
    [ text $ "Error from wallet #" <> show walletId.getWallet <> ": " <> gShow error ]

emulatorEventPane (WalletInfo (Wallet walletId) info) =
  div_
    [ text $ "Message from wallet #" <> show walletId.getWallet <> ": " <> info ]

------------------------------------------------------------

offWhite :: Color
offWhite = rgb 188 188 193

lightPurple :: Color
lightPurple = rgb 163 128 188

lightBlue :: Color
lightBlue = rgb 88 119 182

fadedBlue :: Color
fadedBlue = rgb 35 39 64

softPalette :: Array Color
softPalette =
  [ rgb 55 68 106
  , rgb 54 93 72
  , rgb 94 50 62
  ]

hardPalette :: Array Color
hardPalette =
  [ rgb 210 112 240
  , rgb 252 255 119
  , rgb 255 126 119
  , rgb 112 240 130
  , rgb 163 128 188
  , rgb 112 156 240
  ]
------------------------------------------------------------

-- | Remember here that the Blockchain is latest-block *first*.
mockchainChartOptions ::
  forall m.
  Monad m
  => FlowGraph
  -> E.CommandsT (series :: I, tooltip :: I, color :: I) m Unit
mockchainChartOptions (FlowGraph {flowGraphLinks, flowGraphNodes}) = do
  E.tooltip $ do
    E.trigger E.ItemTrigger
  E.colors hardPalette
  E.series do
    E.sankey do
      traverse_ (\f -> f (E.Pixel 30)) [ E.top, E.right, E.bottom, E.left ]
      focusNodeAdjacencyAllEdges
      orientVertical
      E.lineStyle $ E.normal do
        E.colorSource
      E.buildLinks $ traverse_ toEchartLink flowGraphLinks
      E.buildItems $ traverse_ toEchartItem flowGraphNodes
      E.label $ E.normal do
        E.color white
        positionBottom

toEchartItem :: forall m i. Monad m => TxRef -> E.CommandsT (item :: I | i) m Unit
toEchartItem (TxRef name) =
  E.addItem do
    E.name name
    E.value 0.0

toEchartLink :: forall m i. Monad m => FlowLink -> E.CommandsT (link :: I | i) m Unit
toEchartLink (FlowLink link) =
  E.addLink do
    E.sourceName $ unwrap $ link.flowLinkSource
    E.targetName $ unwrap $ link.flowLinkTarget
    E.value $ Int.toNumber link.flowLinkValue

------------------------------------------------------------

balancesChartOptions ::
  forall m.
  Monad m
  => Array (Tuple Wallet Value)
  -> E.CommandsT ( series :: I
                 , grid :: I
                 , xAxis :: I
                 , yAxis :: I
                 , backgroundColor :: I
                 , tooltip :: I
                 , textStyle :: I
                 ) m Unit
balancesChartOptions wallets = do
  E.tooltip $ do
    E.trigger E.ItemTrigger
    E.formatterString "{c} ADA"
  E.textStyle $ E.color lightBlue
  E.backgroundColor fadedBlue
  E.xAxis do
    E.axisType E.Category
    E.items $ map (fst >>> unwrap >>> _.getWallet >>> show >>> (<>) "Wallet #" >>> E.strItem) wallets
    axisLineStyle
  E.yAxis do
    E.name "Final Balance"
    E.nameRotate 90.0
    E.nameLocationMiddle
    E.nameGap 30.0
    E.axisType E.Value
    axisLineStyle
  E.series do
    E.bar do
      E.items $ map (snd >>> unwrap >>> _.getValue >>> Int.toNumber >>> E.numItem) wallets
      E.itemStyle $ E.normal $ E.color lightPurple
  where
    axisLineStyle :: forall i. E.DSL (axisLine :: I, splitLine :: I | i) m
    axisLineStyle = do
      E.axisLine $ E.lineStyle $ E.color lightBlue
      E.splitLine $ E.lineStyle $ E.color lightBlue
