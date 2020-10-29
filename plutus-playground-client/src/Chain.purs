module Chain
  ( balancesChartOptions
  , evaluationPane
  , extractAmount
  ) where

import Bootstrap (empty, nbsp)
import Chain.Types (State, _value)
import Chain.View (chainView)
import Chartist (ChartistData, ChartistItem, ChartistOptions, ChartistPoint, toChartistData)
import Chartist as Chartist
import Data.Array as Array
import Data.Array.Extra (collapse)
import Data.BigInteger (BigInteger)
import Data.BigInteger as BigInteger
import Data.Lens (_2, preview, to, toListOf, traversed, view)
import Data.Lens.Index (ix)
import Data.List (List)
import Data.Maybe (Maybe(..), fromMaybe)
import Data.Newtype (wrap)
import Data.Semiring (zero)
import Data.Set (Set)
import Data.Set as Set
import Data.Tuple (Tuple(Tuple))
import Data.Tuple.Nested ((/\))
import Effect.Aff.Class (class MonadAff)
import Halogen (ComponentHTML)
import Halogen.Chartist (chartist)
import Halogen.HTML (ClassName(ClassName), HTML, br_, code_, div, div_, h2_, pre_, slot, text)
import Halogen.HTML.Properties (class_)
import Language.PlutusTx.AssocMap as AssocMap
import Ledger.Slot (Slot(..))
import Ledger.TxId (TxId(TxId))
import Ledger.Value (CurrencySymbol, TokenName)
import Playground.Lenses (_tokenName)
import Playground.Types (EvaluationResult(EvaluationResult), SimulatorWallet)
import Prelude (map, show, unit, ($), (<$>), (<<<), (<>))
import Types (ChildSlots, HAction(..), _balancesChartSlot, _simulatorWalletBalance, _simulatorWalletWallet, _walletId)
import Wallet.Emulator.Chain (ChainEvent(..))
import Wallet.Emulator.ChainIndex (ChainIndexEvent(..))
import Wallet.Emulator.MultiAgent (EmulatorEvent'(..))
import Wallet.Emulator.MultiAgent as MultiAgent
import Wallet.Emulator.NodeClient (NodeClientEvent(..))
import Wallet.Emulator.Wallet (Wallet(..), WalletEvent(..))

evaluationPane ::
  forall m.
  MonadAff m =>
  State ->
  EvaluationResult ->
  ComponentHTML HAction ChildSlots m
evaluationPane state evaluationResult@(EvaluationResult { emulatorLog, emulatorTrace, fundsDistribution, resultRollup, walletKeys }) =
  div_
    [ ChainAction <$> chainView namingFn state (wrap resultRollup)
    , br_
    , div_
        [ h2_ [ text "Logs" ]
        , case emulatorLog of
            [] -> empty
            logs ->
              div
                [ class_ $ ClassName "logs" ]
                ((emulatorEventPane <<< eveEvent) <$> Array.reverse logs)
        , h2_ [ text "Trace" ]
        , code_ [ pre_ [ text emulatorTrace ] ]
        ]
    , br_
    , div_
        [ h2_ [ text "Final Balances" ]
        , slot
            _balancesChartSlot
            unit
            (chartist balancesChartOptions)
            (balancesToChartistData fundsDistribution)
            (Just <<< HandleBalancesChartMessage)
        ]
    ]
  where
  namingFn pubKeyHash = preview (ix pubKeyHash <<< _walletId <<< to (\n -> "Wallet #" <> show n)) (AssocMap.Map walletKeys)

eveEvent :: forall a. MultiAgent.EmulatorTimeEvent a -> a
eveEvent (MultiAgent.EmulatorTimeEvent { _eteEvent }) = _eteEvent

emulatorEventPane :: forall i p. EmulatorEvent' -> HTML p i
emulatorEventPane (ChainIndexEvent _ (ReceiveBlockNotification numTransactions)) =
  div_
    [ text $ "Chain index receive block notification. " <> show numTransactions <> " transactions." ]

emulatorEventPane (ChainIndexEvent _ (AddressStartWatching address)) =
  div_
    [ text $ "Submitting transaction: " <> show address ]

emulatorEventPane (ChainIndexEvent _ (HandlingAddressChangeRequest rq _)) =
  div_
    [ text $ "Handling address change request: " <> show rq ]

emulatorEventPane (ClientEvent _ (TxSubmit (TxId txId))) =
  div_
    [ text $ "Submitting transaction: " <> txId.getTxId ]

emulatorEventPane (ChainEvent (TxnValidate (TxId txId))) =
  div_
    [ text $ "Validating transaction: " <> txId.getTxId ]

emulatorEventPane (NotificationEvent notificationEvent) =
  div_
    [ text $ "Notification event: " <> show notificationEvent ]

emulatorEventPane (ChainEvent (TxnValidationFail (TxId txId) error)) =
  div [ class_ $ ClassName "error" ]
    [ text $ "Validation failed: " <> txId.getTxId
    , br_
    , nbsp
    , text $ show error
    ]

emulatorEventPane (ChainEvent (SlotAdd (Slot slot))) =
  div [ class_ $ ClassName "info" ]
    [ text $ "Add slot #" <> show slot.getSlot ]

emulatorEventPane (WalletEvent (Wallet walletId) (GenericLog logMessageText)) =
  div [ class_ $ ClassName "error" ]
    [ text $ "Message from wallet #" <> show walletId.getWallet <> ": " <> logMessageText ]

emulatorEventPane (WalletEvent (Wallet walletId) logMessage) =
  div [ class_ $ ClassName "error" ]
    [ text $ "Message from wallet #" <> show walletId.getWallet <> ": " <> show logMessage ]

------------------------------------------------------------
formatWalletId :: SimulatorWallet -> String
formatWalletId wallet = "Wallet #" <> show (view (_simulatorWalletWallet <<< _walletId) wallet)

extractAmount :: Tuple CurrencySymbol TokenName -> SimulatorWallet -> Maybe BigInteger
extractAmount (Tuple currencySymbol tokenName) =
  preview
    ( _simulatorWalletBalance
        <<< _value
        <<< ix currencySymbol
        <<< ix tokenName
    )

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
    , value: BigInteger.toNumber $ fromMaybe zero $ extractAmount key wallet
    }

  allValues :: List (AssocMap.Map CurrencySymbol (AssocMap.Map TokenName BigInteger))
  allValues =
    toListOf
      ( traversed
          <<< _simulatorWalletBalance
          <<< _value
      )
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
  , plugins:
    [ Chartist.tooltipPlugin
    , Chartist.axisTitlePlugin
        { axisX:
          { axisTitle: "Wallet"
          , axisClass: "ct-x-axis-title"
          , offset:
            { x: 0
            , y: 40
            }
          , textAnchor: "middle"
          , flipTitle: false
          }
        , axisY:
          { axisTitle: "Final Balance"
          , axisClass: "ct-y-axis-title"
          , offset:
            { x: 0
            , y: 30
            }
          , textAnchor: "middle"
          , flipTitle: true
          }
        }
    ]
  }
