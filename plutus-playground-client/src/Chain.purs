module Chain
       ( balancesChartOptions
       , evaluationPane
       , extractAmount
       ) where

import Bootstrap (empty, nbsp)
import Chain.BlockchainExploration (blockchainExploration)
import Chartist (ChartistData, ChartistItem, ChartistOptions, ChartistPoint, toChartistData)
import Chartist as Chartist
import Data.Array as Array
import Data.Generic.Rep.Show (genericShow)
import Data.Int as Int
import Data.Lens (_2, _Just, preview, toListOf, traversed, view)
import Data.Lens.At (at)
import Data.List (List)
import Data.Map as Map
import Data.Maybe (Maybe, fromMaybe)
import Data.RawJson (JsonTuple(..))
import Data.Semiring (zero)
import Data.Set (Set)
import Data.Set as Set
import Data.Traversable (foldMap)
import Data.Tuple (Tuple(Tuple))
import Data.Tuple.Nested ((/\))
import Effect.Aff.Class (class MonadAff)
import Halogen (HTML)
import Halogen.Chartist (chartist)
import Halogen.Component (ParentHTML)
import Halogen.HTML (ClassName(ClassName), br_, div, div_, h2_, slot', text)
import Halogen.HTML.Events (input)
import Halogen.HTML.Properties (class_)
import Ledger.Extra (LedgerMap, collapse)
import Ledger.Index (ValidationError(..))
import Ledger.Slot (Slot(..))
import Ledger.Tx (TxInOf(..), TxOutOf(..), TxOutRefOf(..))
import Ledger.TxId (TxIdOf(TxIdOf))
import Ledger.Value (CurrencySymbol, TokenName)
import Playground.API (EvaluationResult(EvaluationResult), SimulatorWallet)
import Prelude (map, show, ($), (<$>), (<<<), (<>))
import Types (BalancesChartSlot(BalancesChartSlot), ChildQuery, ChildSlot, Query(HandleBalancesChartMessage), _pubKey, _simulatorWalletBalance, _simulatorWalletWallet, _tokenName, _value, _walletId, cpBalancesChart)
import Wallet.Emulator.Types (EmulatorEvent(..), Wallet(..))

evaluationPane::
  forall m.
  MonadAff m
  => EvaluationResult
  -> ParentHTML Query ChildQuery ChildSlot m
evaluationPane e@(EvaluationResult {emulatorLog, resultBlockchain, fundsDistribution, walletKeys}) =
  div_
    [ blockchainExploration
        (foldMap (\(JsonTuple (Tuple key wallet)) -> Map.singleton (view _pubKey key) wallet) walletKeys)
        resultBlockchain
    , br_
    , div_
        [ h2_ [ text "Final Balances" ]
        , slot'
            cpBalancesChart
            BalancesChartSlot
            (chartist balancesChartOptions)
            (balancesToChartistData fundsDistribution)
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
    , text $ showValidationError error
    ]

emulatorEventPane (SlotAdd (Slot slot)) =
  div [ class_ $ ClassName "info" ]
    [ text $ "Add slot #" <> show slot.getSlot ]

emulatorEventPane (WalletError (Wallet walletId) error) =
  div [ class_ $ ClassName "error" ]
    [ text $ "Error from wallet #" <> show walletId.getWallet <> ": " <> genericShow error ]

emulatorEventPane (WalletInfo (Wallet walletId) info) =
  div_
    [ text $ "Message from wallet #" <> show walletId.getWallet <> ": " <> info ]

------------------------------------------------------------

formatWalletId :: SimulatorWallet -> String
formatWalletId wallet = "Wallet #" <> show (view (_simulatorWalletWallet <<< _walletId) wallet)

extractAmount :: Tuple CurrencySymbol TokenName -> SimulatorWallet -> Maybe Int
extractAmount (Tuple currencySymbol tokenName) =
  preview
    (_simulatorWalletBalance
     <<< _value
     <<< at currencySymbol
     <<< _Just
     <<< at tokenName
     <<< _Just)

balancesToChartistData :: Array SimulatorWallet -> ChartistData
balancesToChartistData wallets = toChartistData $ toChartistItem <$> wallets
  where
    toChartistItem :: SimulatorWallet -> ChartistItem
    toChartistItem wallet =
      { label: formatWalletId wallet
      , points: toChartistPoint wallet <$> Set.toUnfoldable allCurrencies
      }

    toChartistPoint :: SimulatorWallet -> Tuple CurrencySymbol TokenName -> ChartistPoint
    toChartistPoint wallet key =
      { meta: view (_2 <<< _tokenName) key
      , value: Int.toNumber $ fromMaybe zero $ extractAmount key wallet
      }

    allValues :: List (LedgerMap CurrencySymbol (LedgerMap TokenName Int))
    allValues =
      toListOf (traversed
                <<< _simulatorWalletBalance
                <<< _value)
        wallets

    allCurrencies :: Set (Tuple CurrencySymbol TokenName)
    allCurrencies =
      Set.fromFoldable
      $ map (\(c /\ t /\ _) -> c /\ t)
      $ Array.concat
      $ map collapse
      $ Array.fromFoldable allValues

balancesChartOptions :: ChartistOptions
balancesChartOptions =
  { seriesBarDistance: 45
  , chartPadding:
      { top: 30
      , bottom: 30
      , right: 30
      , left: 30
      }
  , axisY: Chartist.intAutoScaleAxis
  , plugins: [ Chartist.tooltipPlugin
             , Chartist.axisTitlePlugin
                 { axisX: { axisTitle: "Wallet"
                          , axisClass: "ct-x-axis-title"
                          , offset: { x: 0
                                    , y: 40
                                    }
                          , textAnchor: "middle"
                          , flipTitle: false
                          }
                 , axisY: { axisTitle: "Final Balance"
                          , axisClass: "ct-y-axis-title"
                          , offset: { x: 0
                                    , y: (30)
                                    }
                          , textAnchor: "middle"
                          , flipTitle: true
                          }
                 }
             ]
  }

showValidationError :: ValidationError -> String
showValidationError (InOutTypeMismatch (TxInOf txIn) (TxOutOf txOut)) = "InOutTypeMismatch"
showValidationError (TxOutRefNotFound (TxOutRefOf txOut)) = "TxOutRefNotFound"
showValidationError (InvalidScriptHash hash) = "InvalidScriptHash"
showValidationError (InvalidSignature key signature) = "InvalidSignature"
showValidationError (ValueNotPreserved before after) = "ValueNotPreserved"
showValidationError (NegativeValue tx) = "NegativeValue"
showValidationError (ScriptFailure xs) = "ScriptFailure"
showValidationError (CurrentSlotOutOfRange slot) = "CurrentSlotOutOfRange"
showValidationError (SignatureMissing key) = "SignatureMissing"
showValidationError (ForgeWithoutScript str) = "ForgeWithoutScript"
