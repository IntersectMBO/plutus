module View (render) where

import AjaxUtils (ajaxErrorPane)
import Bootstrap (badge, badgePrimary, cardBody_, cardHeader_, card_, col10_, col12_, col3_, col8_, col9_, container_, nbsp, row_)
import Bootstrap.Extra (preWrap_)
import Chain.Types (AnnotatedBlockchain(..), ChainFocus)
import Chain.Types as Chain
import Chain.View (chainView)
import Data.Array as Array
import Data.Json.JsonMap (JsonMap, _JsonMap)
import Data.Json.JsonUUID (JsonUUID, _JsonUUID)
import Data.Lens (to, traversed, view)
import Data.Lens.Extra (toArrayOf)
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Newtype (unwrap)
import Data.RawJson as RawJson
import Data.Tuple (Tuple(..))
import Data.Tuple.Nested (type (/\), (/\))
import Data.UUID as UUID
import Effect.Aff.Class (class MonadAff)
import Halogen.HTML (ClassName(..), ComponentHTML, HTML, b_, code_, div, div_, h2_, h3_, pre_, span, span_, text)
import Halogen.HTML.Properties (class_, classes)
import Icons (Icon(..), icon)
import Ledger.Crypto (PubKeyHash)
import Ledger.Index (UtxoIndex)
import Ledger.Tx (Tx)
import Ledger.TxId (TxId)
import Network.RemoteData (RemoteData(..))
import Plutus.SCB.Events (ChainEvent(..))
import Plutus.SCB.Events.Contract (RequestEvent, ResponseEvent)
import Plutus.SCB.Events.Node (NodeEvent(..))
import Plutus.SCB.Events.User (UserEvent(..))
import Plutus.SCB.Events.Wallet (WalletEvent)
import Plutus.SCB.Types (ActiveContract(..), ActiveContractState(..), ContractExe(..))
import Plutus.SCB.Webserver.Types (FullReport(..))
import Prelude (class Eq, class Show, otherwise, show, ($), (+), (<$>), (<<<), (<>), (==))
import Types (HAction(..), State(State), _hooks, _partiallyDecodedResponse)
import Wallet.Emulator.Wallet (Wallet)
import Wallet.Rollup.Types (AnnotatedTx)

render ::
  forall m slots.
  MonadAff m =>
  State -> ComponentHTML HAction slots m
render (State { chainState, fullReport }) =
  div
    [ class_ $ ClassName "main-frame" ]
    [ container_
        [ div_
            $ case fullReport of
                Success report -> [ fullReportPane chainState report ]
                Failure error -> [ ajaxErrorPane error ]
                Loading -> [ icon Spinner ]
                NotAsked -> [ icon Spinner ]
        ]
    ]

fullReportPane :: forall p. Chain.State -> FullReport ContractExe -> HTML p HAction
fullReportPane chainState fullReport@(FullReport { events, latestContractStatus, transactionMap, utxoIndex, annotatedBlockchain, walletMap }) =
  row_
    [ col10_ [ contractStatusPane latestContractStatus ]
    , col12_ [ ChainAction <<< Just <$> annotatedBlockchainPane chainState walletMap annotatedBlockchain ]
    , col12_ [ eventsPane events ]
    , col8_ [ transactionPane transactionMap ]
    , col8_ [ utxoIndexPane utxoIndex ]
    ]

contractStatusPane :: forall p i. JsonMap JsonUUID (ActiveContractState ContractExe) -> HTML p i
contractStatusPane latestContractStatus =
  card_
    [ cardHeader_
        [ h2_ [ text "Active Contracts" ]
        ]
    , cardBody_
        [ div_
            ( ( \(Tuple k v) ->
                  row_
                    [ col3_ [ h3_ [ text $ view (_JsonUUID <<< to UUID.toString) k ] ]
                    , col9_ [ pre_ [ text $ RawJson.pretty $ view (_partiallyDecodedResponse <<< _hooks) v ] ]
                    ]
              )
                <$> (Map.toUnfoldable $ unwrap latestContractStatus :: Array (Tuple JsonUUID (ActiveContractState ContractExe)))
            )
        ]
    ]

annotatedBlockchainPane :: forall p. Chain.State -> JsonMap PubKeyHash Wallet -> Array (Array AnnotatedTx) -> HTML p ChainFocus
annotatedBlockchainPane chainState walletMap chain =
  card_
    [ cardHeader_
        [ h2_ [ text "Blockchain" ]
        ]
    , cardBody_
        [ chainView chainState (unwrap walletMap) $ AnnotatedBlockchain chain
        ]
    ]

transactionPane ::
  forall p i.
  JsonMap TxId Tx -> HTML p i
transactionPane txMap =
  card_
    [ cardHeader_
        [ h2_ [ text "Txs" ]
        ]
    , cardBody_
        ( toArrayOf
            ( _JsonMap
                <<< traversed
                <<< to (\x -> div_ [ code_ [ text $ show x ] ])
            )
            txMap
        )
    ]

utxoIndexPane :: forall p i. UtxoIndex -> HTML p i
utxoIndexPane utxoIndex =
  card_
    [ cardHeader_
        [ h2_ [ text "UtxoIndex" ]
        ]
    , cardBody_ [ div_ [ code_ [ text $ show utxoIndex ] ] ]
    ]

eventsPane :: forall p i. Array (ChainEvent ContractExe) -> HTML p i
eventsPane events =
  card_
    [ cardHeader_
        [ h2_ [ text "Event log" ]
        , text (show (Array.length events))
        , nbsp
        , text "Event(s)"
        ]
    , cardBody_ [ div_ (countedEventPane <$> countConsecutive events) ]
    ]

countedEventPane :: forall p i. Int /\ ChainEvent ContractExe -> HTML p i
countedEventPane (count /\ event) =
  div_
    [ preWrap_
        [ span [ classes [ badge, badgePrimary ] ]
            [ text $ show count <> "x" ]
        , nbsp
        , showEvent event
        ]
    ]

showEvent :: forall p i. ChainEvent ContractExe -> HTML p i
showEvent (RecordRequest subevent) =
  span_
    [ b_
        [ text "Request:"
        , nbsp
        ]
    , showRecordRequestEvent subevent
    ]

showEvent (RecordResponse subevent) =
  span_
    [ b_
        [ text "Response:"
        , nbsp
        ]
    , showRecordResponseEvent subevent
    ]

showEvent (UserEvent subevent) =
  span_
    [ b_
        [ text "User:"
        , nbsp
        ]
    , showUserEvent subevent
    ]

showEvent (WalletEvent subevent) =
  span_
    [ b_
        [ text "Wallet:"
        , nbsp
        ]
    , showWalletEvent subevent
    ]

showEvent (NodeEvent subevent) =
  span_
    [ b_
        [ text "Node:"
        , nbsp
        ]
    , showNodeEvent subevent
    ]

showUserEvent :: forall p i. UserEvent ContractExe -> HTML p i
showUserEvent (InstallContract (ContractExe { contractPath })) = text $ "Install " <> contractPath

showUserEvent ( ContractStateTransition
    ( ActiveContractState
      { activeContract: ActiveContract { activeContractInstanceId }
    , partiallyDecodedResponse
    }
  )
) = text $ "Update " <> show activeContractInstanceId

showNodeEvent :: forall p i. NodeEvent -> HTML p i
showNodeEvent (BlockAdded []) = text $ "Empty block(s) added"

showNodeEvent event = text $ show event

showWalletEvent :: forall p i. WalletEvent -> HTML p i
showWalletEvent event = text $ show event

showRecordRequestEvent :: forall p i e. Show e => RequestEvent e -> HTML p i
showRecordRequestEvent event = text $ show event

showRecordResponseEvent :: forall p i e. Show e => ResponseEvent e -> HTML p i
showRecordResponseEvent event = text $ show event

countConsecutive :: forall a. Eq a => Array a -> Array (Tuple Int a)
countConsecutive = h <<< f
  where
  f :: Array a -> (Int /\ Maybe a /\ Array (Tuple Int a))
  f = Array.foldl g (0 /\ Nothing /\ [])

  g :: (Int /\ Maybe a /\ Array (Tuple Int a)) -> a -> (Int /\ Maybe a /\ Array (Tuple Int a))
  g (count /\ Nothing /\ accum) y = (1 /\ Just y /\ accum)

  g (count /\ Just x /\ accum) y
    | x == y = ((count + 1) /\ Just x /\ accum)
    | otherwise = (1 /\ Just y /\ Array.snoc accum (count /\ x))

  h (count /\ Nothing /\ accum) = accum

  h (count /\ Just x /\ accum) = Array.snoc accum (count /\ x)
