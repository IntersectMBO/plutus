module Chain
       ( mockchainChartOptions
       , balancesChartOptions
       , evaluationPane
       ) where

import Bootstrap (empty, nbsp)
import Color (Color, rgb, white)
import Control.Monad.Aff.Class (class MonadAff)
import Data.Array (mapWithIndex)
import Data.Array as Array
import Data.Foldable (traverse_)
import Data.Generic (class Generic, gShow)
import Data.Int as Int
import Data.Lens (to, toListOf, traversed)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..), maybe)
import Data.Newtype (unwrap)
import Data.Set (Set)
import Data.Set as Set
import Data.String as String
import Data.Tuple (Tuple(Tuple), fst, snd)
import Data.Tuple.Nested (tuple3, (/\))
import ECharts.Commands (addItem, addLink, axisLine, axisType, backgroundColor, bar, bottom, buildItems, buildLinks, color, colorSource, colors, formatterString, itemStyle, items, label, left, lineStyle, name, nameGap, nameLocationMiddle, nameRotate, normal, right, sankey, series, sourceName, splitLine, targetName, textStyle, tooltip, top, trigger, value, xAxis, yAxis) as E
import ECharts.Extras (focusNodeAdjacencyAllEdges, orientVertical, positionBottom)
import ECharts.Monad (CommandsT, DSL) as E
import ECharts.Types (AxisType(Value, Category), PixelOrPercent(Pixel), TooltipTrigger(ItemTrigger), numItem, strItem) as E
import ECharts.Types.Phantom (I)
import Halogen (HTML)
import Halogen.Component (ParentHTML)
import Halogen.ECharts (EChartsEffects, echarts)
import Halogen.HTML (ClassName(ClassName), br_, div, div_, h2, h2_, h3, slot', strong_, table, tbody_, td, text, th, thead_, tr_)
import Halogen.HTML.Events (input)
import Halogen.HTML.Properties (class_, classes, colSpan)
import Ledger.Ada.TH (Ada(..))
import Ledger.Interval (Slot(..))
import Ledger.Types (DataScript(..), PubKey(PubKey), RedeemerScript(..), Signature(Signature), Tx(Tx), TxIdOf(TxIdOf), TxInOf(TxInOf), TxInType(..), TxOutOf(TxOutOf), TxOutRefOf(TxOutRefOf), TxOutType(..))
import Ledger.Value.TH (CurrencySymbol(..), Value(..))
import Partial.Unsafe (unsafePartial)
import Playground.API (EvaluationResult(EvaluationResult), SimulatorWallet)
import Prelude (class Eq, class Monad, class Ord, class Semigroup, class Show, Unit, discard, map, show, unit, (#), ($), (+), (<#>), (<$>), (<*>), (<<<), (<>), (==))
import Types (BalancesChartSlot(BalancesChartSlot), ChildQuery, ChildSlot, MockchainChartSlot(MockchainChartSlot), Query(HandleBalancesChartMessage, HandleMockchainChartMessage), Blockchain, _ada, _simulatorWalletBalance, _simulatorWalletWallet, _walletId, cpBalancesChart, cpMockchainChart)
import Wallet.Emulator.Types (EmulatorEvent(..), Wallet(..))
import Wallet.Graph (FlowGraph(FlowGraph), FlowLink(FlowLink), TxRef(TxRef))

type SlotId = Int
type StepId = Int
type Hash = String

data Column
  = ForgeIx
  | FeeIx
  | OwnerIx Int Hash
  | ScriptIx String Hash

derive instance genericColumn :: Generic Column
derive instance eqColumn :: Eq Column
derive instance ordColumn :: Ord Column

instance showColumn :: Show Column where
  show FeeIx = "Fee"
  show ForgeIx = "Forge"
  show (OwnerIx owner hash) = show owner <> "-" <> String.take 7 hash
  show (ScriptIx owner hash) = owner <> "-" <> String.take 7 hash

type Row = Tuple SlotId StepId

type BalanceMap =
  Map (Tuple Column Row) Balance

evaluationPane::
  forall m aff.
  MonadAff (EChartsEffects aff) m
  => EvaluationResult
  -> ParentHTML Query ChildQuery ChildSlot m
evaluationPane e@(EvaluationResult {emulatorLog, resultBlockchain}) =
  div_
    [ blockchainExploration resultBlockchain
    , br_
    , div_
        [ h2_ [ text "Final Balances" ]
        , slot' cpBalancesChart BalancesChartSlot
            (echarts Nothing)
            ({width: 930, height: 300} /\ unit)
            (input HandleBalancesChartMessage)
        ]
    , br_
    , div_
        [ h2_ [ text "Logs" ]
        , case emulatorLog of
            [] -> empty
            logs ->
              div
                [ class_ $ ClassName "logs" ]
                (emulatorEventPane <$> Array.reverse logs)
        ]
    , br_
    , div_
        [ h2_ [ text "Chain" ]
        , slot' cpMockchainChart MockchainChartSlot
            (echarts Nothing)
            ({width: 930, height: 600} /\ unit)
            (input HandleMockchainChartMessage)
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

lightPurple :: Color
lightPurple = rgb 163 128 188

lightBlue :: Color
lightBlue = rgb 88 119 182

fadedBlue :: Color
fadedBlue = rgb 35 39 64

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
  => Array SimulatorWallet
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
    E.items $ toListOf (traversed <<< _simulatorWalletWallet <<< _walletId <<< to formatWalletId <<< to E.strItem) wallets
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
      E.items $ toListOf (traversed <<< _simulatorWalletBalance <<< _ada <<< to Int.toNumber <<< to E.numItem) wallets
      E.itemStyle $ E.normal $ E.color lightPurple
  where
    axisLineStyle :: forall i. E.DSL (axisLine :: I, splitLine :: I | i) m
    axisLineStyle = do
      E.axisLine $ E.lineStyle $ E.color lightBlue
      E.splitLine $ E.lineStyle $ E.color lightBlue
    formatWalletId id = "Wallet #" <> show id

------------------------------------------------------------

data Balance
  = AdaBalance Ada
  | CurrencyBalance (Array (Tuple CurrencySymbol Int))
  | Remainder

-- | TODO this is not even close to right.
instance semigroupBalance :: Partial => Semigroup Balance where
  append Remainder Remainder = Remainder
  append (CurrencyBalance x) (CurrencyBalance y) = CurrencyBalance (x <> y)
  append (AdaBalance (Ada {getAda: x})) (AdaBalance (Ada {getAda: y})) = AdaBalance (Ada { getAda: x + y })

blockchainExploration :: forall p i. Blockchain -> HTML p i
blockchainExploration blockchain =
  div_ [ h2_ [ text "Blockchain" ]
       , blockchainTable
       ]
  where
    blockchainTable =
      table [ classes [ ClassName "table"
                      , ClassName "balance-map"
                      ]
            ]
      [ thead_
        [ tr_ $ columns
                # Set.map (tuple3 <$> columnHeading <*> matchCount <*> columnClass)
                # Set.toUnfoldable
                <#> \(heading /\ count /\ cssClass /\ _) -> th [ colSpan count ]
                                                            [ h2 [ class_ cssClass ]
                                                              [ text heading ]
                                                            ]
        , tr_ $ columns
                # Set.toUnfoldable
                <#> \column -> th []
                               [ h3 [ class_ $ columnClass column ]
                                 [ text $ columnSubheading column ]
                               ]
        ]
      , tbody_ $ Array.reverse (Set.toUnfoldable rows) <#>
        (\row -> tr_ $ columns
                       # Set.toUnfoldable
                       # Array.sortWith columnHeading
                       <#> \column ->
                             let mBalance = Map.lookup (Tuple column row) balanceMap
                             in td
                                [ class_ $ columnClass column ]
                                [ maybe nbsp balanceView mBalance ]
        )
      ]

    balanceMap = toBalanceMap blockchain

    columnHeading FeeIx = "Fee"
    columnHeading ForgeIx = "Forge"
    columnHeading (OwnerIx owner hash) = "Wallet #" <> show owner
    columnHeading (ScriptIx owner hash) = "Script #" <> owner

    columnSubheading FeeIx = ""
    columnSubheading ForgeIx = ""
    columnSubheading (OwnerIx owner hash) = "Tx/" <> String.take 10 hash <> "..."
    columnSubheading (ScriptIx owner hash) = "Tx/" <> String.take 10 hash <> "..."

    matchCount :: Column -> Int
    matchCount owner = Array.length $ Array.filter (isOwner owner) $ Set.toUnfoldable columns

    isOwner :: Column -> Column -> Boolean
    isOwner FeeIx FeeIx = true
    isOwner ForgeIx ForgeIx = true
    isOwner (OwnerIx owner1 _) (OwnerIx owner2 _) = owner1 == owner2
    isOwner (ScriptIx owner1 _) (ScriptIx owner2 _) = owner1 == owner2
    isOwner _ _ = false

    columnClass :: Column -> ClassName
    columnClass ForgeIx = ClassName "forge"
    columnClass FeeIx = ClassName "fee"
    columnClass (OwnerIx _ _) = ClassName "owner"
    columnClass (ScriptIx _ _) = ClassName "script"

    columns :: Set Column
    columns = Set.fromFoldable $ map fst $ Map.keys $ balanceMap

    rows :: Set Row
    rows = Set.fromFoldable $ map snd $ Map.keys $ balanceMap

toBalanceMap :: Blockchain -> Map (Tuple Column (Tuple Int Int)) Balance
toBalanceMap =
  Map.fromFoldableWith (unsafePartial (<>))
  <<< Array.concat
  <<< Array.concat
  <<< mapWithIndex (\slotId -> mapWithIndex
                               (\stepId tx ->
                                 let row = Tuple slotId stepId
                                 in [ forgeTransactions row tx
                                    , feeTransactions row tx
                                    ]
                                    <> inputTransactions row tx
                                    <> outputTransactions row tx
                               ))
  where
    forgeTransactions :: Row -> Tuple (TxIdOf String) Tx -> Tuple (Tuple Column Row) Balance
    forgeTransactions row (Tuple _ (Tx {txForge: (Value { getValue: value})})) =
      Tuple (Tuple ForgeIx row) (CurrencyBalance value)

    feeTransactions :: Row -> Tuple (TxIdOf String) Tx -> Tuple (Tuple Column Row) Balance
    feeTransactions row (Tuple _ (Tx {txFee: ada})) =
      Tuple (Tuple FeeIx row) (AdaBalance ada)

    inputTransactions :: Row -> Tuple (TxIdOf String) Tx -> Array (Tuple (Tuple Column Row) Balance)
    inputTransactions row (Tuple _ (Tx {txInputs})) =
      fromTxIn <$> txInputs
      where
        fromTxIn :: TxInOf String -> Tuple (Tuple Column Row) Balance
        fromTxIn (TxInOf { txInRef: (TxOutRefOf {txOutRefId: (TxIdOf {getTxId: hash})})
                         , txInType: (ConsumePublicKeyAddress (Signature { getSignature: owner }))
                         })
          = Tuple (Tuple (OwnerIx owner hash) row) Remainder
        fromTxIn (TxInOf { txInRef: (TxOutRefOf {txOutRefId: (TxIdOf {getTxId: hash})})
                         , txInType: (ConsumeScriptAddress _ (RedeemerScript { getRedeemer: owner }))
                         })
          = Tuple (Tuple (ScriptIx owner hash) row) Remainder

    outputTransactions :: Row -> Tuple (TxIdOf String) Tx -> Array (Tuple (Tuple Column Row) Balance)
    outputTransactions row (Tuple (TxIdOf {getTxId: hash}) (Tx {txOutputs})) =
      fromTxOut <$> txOutputs
      where
        fromTxOut :: TxOutOf String -> Tuple (Tuple Column Row) Balance
        fromTxOut (TxOutOf { txOutType: (PayToPubKey (PubKey { getPubKey: owner }))
                           , txOutValue: (Value { getValue: currencyBalances })
                           })
          = Tuple (Tuple (OwnerIx owner hash) row) (CurrencyBalance currencyBalances)
        fromTxOut (TxOutOf { txOutType: (PayToScript (DataScript { getDataScript: owner }))
                           , txOutValue: (Value { getValue: currencyBalances })
                           })
          = Tuple (Tuple (ScriptIx owner hash) row) (CurrencyBalance currencyBalances)

balanceClassname :: ClassName
balanceClassname = ClassName "balance"

balanceView :: forall p i. Balance -> HTML p i
balanceView (AdaBalance (Ada {getAda: ada})) =
  div [ classes [ balanceClassname
                , if ada == 0
                  then ClassName "balance-no-ada"
                  else ClassName "balance-ada"
                ]
      ]
      [ amountView "ADA" ada ]

balanceView (CurrencyBalance currencyBalances) =
  div [ classes [ balanceClassname
                , if Array.null currencyBalances
                  then ClassName "balance-no-currencies"
                  else ClassName "balance-currencies"
                ]
      ]
      (map valueView currencyBalances)

balanceView Remainder =
  div [ classes [ balanceClassname
                , ClassName "balance-remainder"
                ]
      ]
      []

valueView :: forall p i. Tuple CurrencySymbol Int -> HTML p i
valueView (Tuple (CurrencySymbol sym) balance) =
  amountView (show sym) balance

amountView :: forall p i. String -> Int -> HTML p i
amountView name balance =
  div_ [ strong_ [ text name ]
       , text $ ": " <> show balance
       ]
