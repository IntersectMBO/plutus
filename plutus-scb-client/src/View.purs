module View (render) where

import AjaxUtils (ajaxErrorPane)
import Bootstrap (badge, badgePrimary, btn, btnBlock, btnPrimary, btnSmall, cardBody_, cardFooter_, cardHeader_, card_, col10_, col12_, col2_, col4_, col6_, container_, nbsp, row_, tableBordered)
import Bootstrap as Bootstrap
import Bootstrap.Extra (preWrap_)
import Chain.Types (ChainFocus)
import Chain.Types as Chain
import Chain.View (chainView)
import Data.Array (null)
import Data.Array as Array
import Data.Foldable.Extra (countConsecutive, interleave)
import Data.FunctorWithIndex (mapWithIndex)
import Data.Json.JsonMap (JsonMap(..))
import Data.Json.JsonUUID (_JsonUUID)
import Data.Lens (to, traversed, view)
import Data.Lens.Extra (toArrayOf)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Newtype (unwrap, wrap)
import Data.Tuple.Nested (type (/\), (/\))
import Data.UUID as UUID
import Effect.Aff.Class (class MonadAff)
import Halogen.HTML (ClassName(..), ComponentHTML, HTML, b_, br_, button, code_, div, div_, h1, h2_, h3_, span, span_, table, tbody_, td_, text, th, th_, thead_, tr_)
import Halogen.HTML.Events (onClick)
import Halogen.HTML.Properties (class_, classes, colSpan)
import Icons (Icon(..), icon)
import Language.Plutus.Contract.Resumable (IterationID(..), Request(..), RequestID(..))
import Ledger.Index (UtxoIndex)
import Ledger.Tx (Tx)
import Ledger.TxId (TxId)
import NavTabs (mainTabBar, viewContainer)
import Network.RemoteData (RemoteData(..))
import Playground.Lenses (_endpointDescription, _getEndpointDescription, _schema)
import Playground.Schema (actionArgumentForm)
import Playground.Types (_FunctionSchema)
import Plutus.SCB.Events (ChainEvent(..))
import Plutus.SCB.Events.Contract (ContractEvent, ContractInstanceId, ContractInstanceState(..))
import Plutus.SCB.Events.Node (NodeEvent)
import Plutus.SCB.Events.User (UserEvent(..))
import Plutus.SCB.Events.Wallet (WalletEvent)
import Plutus.SCB.Types (ContractExe(..))
import Plutus.SCB.Webserver.Types (ChainReport(..), ContractReport(..), FullReport(..))
import Prelude (class Show, const, show, ($), (<$>), (<<<), (<>))
import Schema.Types (FormEvent)
import Types (EndpointForm, HAction(..), State(State), View(..), WebData, _contractInstanceId, _contractPath, _csContract, _csCurrentState, _hooks, _installedContracts, _transactionMap, _utxoIndex)
import Validation (_argument)

render ::
  forall m slots.
  MonadAff m =>
  State -> ComponentHTML HAction slots m
render (State { currentView, chainState, fullReport, contractSignatures }) =
  div
    [ class_ $ ClassName "main-frame" ]
    [ container_
        [ mainHeader
        , mainTabBar ChangeView tabs currentView
        , div_ (webDataPane (fullReportPane currentView chainState contractSignatures) fullReport)
        ]
    ]

webDataPane :: forall a p i. (a -> HTML p i) -> WebData a -> Array (HTML p i)
webDataPane successView (Success report) = [ successView report ]

webDataPane _ (Failure error) = [ ajaxErrorPane error ]

webDataPane _ (Loading) = [ icon Spinner ]

webDataPane _ (NotAsked) = [ icon Spinner ]

mainHeader :: forall p. HTML p HAction
mainHeader =
  div_
    [ h1
        [ class_ $ ClassName "main-title" ]
        [ text "Plutus Application Platform" ]
    ]

tabs :: Array { help :: String, link :: View, title :: String }
tabs =
  [ { link: ActiveContracts
    , title: "Contracts"
    , help: "See available and active contracts."
    }
  , { link: Blockchain
    , title: "Blockchain"
    , help: "See the current state of the chain."
    }
  , { link: EventLog
    , title: "Event Log"
    , help: "View the history of system events."
    }
  ]

fullReportPane ::
  forall p.
  View ->
  Chain.State ->
  Map ContractInstanceId (WebData (Array EndpointForm)) ->
  FullReport ContractExe ->
  HTML p HAction
fullReportPane currentView chainState contractSignatures fullReport@(FullReport { events, contractReport, chainReport }) =
  row_
    [ viewContainer currentView ActiveContracts
        [ row_
            [ col12_ [ contractStatusesPane contractSignatures contractReport ]
            , col12_ [ installedContractsPane (view _installedContracts contractReport) ]
            ]
        ]
    , viewContainer currentView Blockchain
        [ row_
            [ col12_ [ ChainAction <<< Just <$> annotatedBlockchainPane chainState chainReport ]
            ]
        ]
    , viewContainer currentView EventLog
        [ row_
            [ col12_ [ eventsPane events ]
            , col6_ [ transactionPane (view _transactionMap chainReport) ]
            , col6_ [ utxoIndexPane (view _utxoIndex chainReport) ]
            ]
        ]
    ]

installedContractsPane ::
  forall p.
  Array ContractExe ->
  HTML p HAction
installedContractsPane installedContracts =
  card_
    [ cardHeader_
        [ h2_ [ text "Installed Contracts" ]
        ]
    , cardBody_
        [ if null installedContracts then
            text "You do not have any contracts installed."
          else
            div_ (interleave br_ (installedContractPane <$> installedContracts))
        ]
    ]

installedContractPane ::
  forall p.
  ContractExe ->
  HTML p HAction
installedContractPane installedContract =
  row_
    [ col2_
        [ button
            [ classes [ btn, btnSmall, btnPrimary, btnBlock ]
            , onClick (const $ Just $ ActivateContract installedContract)
            ]
            [ text "Activate" ]
        ]
    , col10_ [ text $ view _contractPath installedContract ]
    ]

contractStatusesPane ::
  forall p t.
  Map ContractInstanceId (WebData (Array EndpointForm)) ->
  ContractReport t ->
  HTML p HAction
contractStatusesPane contractSignatures (ContractReport { latestContractStatuses }) =
  card_
    [ cardHeader_
        [ h2_ [ text "Active Contracts" ]
        ]
    , cardBody_
        [ if null latestContractStatuses then
            text "You do not have any active contracts."
          else
            div_ (contractStatusPane contractSignatures <$> latestContractStatuses)
        ]
    ]

contractStatusPane ::
  forall p t.
  Map ContractInstanceId (WebData (Array EndpointForm)) ->
  ContractInstanceState t -> HTML p HAction
contractStatusPane contractSignatures contractInstance =
  div_
    [ contractRequestView contractInstance
    , row_
        ( case Map.lookup contractInstanceId contractSignatures of
            Just (Success endpointForms) ->
              mapWithIndex
                (\index endpointForm -> actionCard contractInstanceId (ChangeContractEndpointCall contractInstanceId index) endpointForm)
                endpointForms
            Just (Failure err) -> [ ajaxErrorPane err ]
            Just Loading -> [ icon Spinner ]
            Just NotAsked -> []
            Nothing -> []
        )
    ]
  where
  contractInstanceId :: ContractInstanceId
  contractInstanceId = view _csContract contractInstance

contractRequestView :: forall t p i. ContractInstanceState t -> HTML p i
contractRequestView contractInstance =
  table [ classes [ Bootstrap.table, tableBordered ] ]
    [ thead_
        [ tr_
            [ th [ colSpan 3 ]
                [ h3_ [ text contractTitle ] ]
            ]
        , tr_
            [ th_ [ text "Iteration" ]
            , th_ [ text "Request", nbsp, text "ID" ]
            , th_ [ text "Request" ]
            ]
        ]
    , tbody_ (requestRow <$> requests)
    ]
  where
  contractTitle = view (_csContract <<< _contractInstanceId <<< _JsonUUID <<< to UUID.toString) contractInstance

  requests = view (_csCurrentState <<< _hooks) contractInstance

  requestRow (Request { itID: IterationID itID, rqID: RequestID rqID, rqRequest }) =
    tr_
      [ td_ [ text $ show itID ]
      , td_ [ text $ show rqID ]
      , td_ [ text $ show rqRequest ]
      ]

actionCard :: forall p. ContractInstanceId -> (FormEvent -> HAction) -> EndpointForm -> HTML p HAction
actionCard contractInstanceId wrapper endpointForm =
  col4_
    [ card_
        [ cardHeader_ [ h2_ [ text $ view (_schema <<< _FunctionSchema <<< _endpointDescription <<< _getEndpointDescription) endpointForm ] ]
        , cardBody_ [ actionArgumentForm wrapper (view _argument endpointForm) ]
        , cardFooter_
            [ button
                [ classes [ btn, btnSmall, btnPrimary ]
                , onClick $ const $ Just $ InvokeContractEndpoint contractInstanceId endpointForm
                ]
                [ text "Submit" ]
            ]
        ]
    ]

annotatedBlockchainPane :: forall t p. Chain.State -> ChainReport t -> HTML p ChainFocus
annotatedBlockchainPane chainState (ChainReport { walletMap, annotatedBlockchain }) =
  card_
    [ cardHeader_
        [ h2_ [ text "Blockchain" ]
        ]
    , cardBody_
        [ chainView chainState (unwrap walletMap) (wrap annotatedBlockchain)
        ]
    ]

transactionPane ::
  forall p i.
  JsonMap TxId Tx -> HTML p i
transactionPane (JsonMap txMap) =
  card_
    [ cardHeader_
        [ h2_ [ text "Txs" ]
        ]
    , cardBody_
        ( toArrayOf
            ( traversed
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
showEvent (ContractEvent subevent) =
  span_
    [ b_
        [ text "Contract:"
        , nbsp
        ]
    , showContractEvent subevent
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
    ( ContractInstanceState
      { csContract
    , csCurrentState
    }
  )
) = text $ "Update " <> show csContract

showNodeEvent :: forall p i. NodeEvent -> HTML p i
showNodeEvent event = text $ show event

showContractEvent :: forall p i a. Show a => ContractEvent a -> HTML p i
showContractEvent event = text $ show event

showWalletEvent :: forall p i. WalletEvent -> HTML p i
showWalletEvent event = text $ show event
