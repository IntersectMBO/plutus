module View.Contracts where

import Prelude
import Bootstrap (btn, btnBlock, btnPrimary, btnSmall, cardBody_, cardFooter_, cardHeader_, card_, col10_, col2_, col4_, nbsp, row_, tableBordered)
import Bootstrap as Bootstrap
import Data.Array (mapWithIndex, null)
import Data.Foldable.Extra (interleave)
import Data.Lens (_1, filtered, toArrayOf, traversed, view)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Tuple.Nested (type (/\), (/\))
import Halogen.HTML (HTML, br_, button, div_, h2_, h3_, table, tbody_, td_, text, th, th_, thead_, tr_)
import Halogen.HTML.Events (onClick)
import Halogen.HTML.Properties (classes, colSpan)
import Language.Plutus.Contract.Resumable (IterationID(..), Request(..), RequestID(..))
import Network.RemoteData (_Success)
import Playground.Lenses (_endpointDescription, _getEndpointDescription, _schema)
import Playground.Schema (actionArgumentForm)
import Playground.Types (_FunctionSchema)
import Plutus.SCB.Events.Contract (ContractInstanceId, ContractInstanceState)
import Plutus.SCB.Types (ContractExe)
import Schema.Types (FormEvent)
import Types (EndpointForm, HAction(..), WebData, _contractInstanceIdString, _contractPath, _csContract, _csCurrentState, _hooks)
import Validation (_argument)
import View.Pretty (pretty)
import View.Utils (webDataPane)

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
  Map ContractInstanceId (WebData (ContractInstanceState t /\ Array EndpointForm)) ->
  HTML p HAction
contractStatusesPane contractSignatures =
  card_
    [ cardHeader_
        [ h2_ [ text "Active Contracts" ]
        ]
    , cardBody_
        [ if null contractStates then
            text "You do not have any active contracts."
          else
            div_ (contractStatusPane contractSignatures <$> contractStates)
        ]
    ]
  where
  contractStates :: Array (ContractInstanceState t)
  contractStates = toArrayOf (traversed <<< _Success <<< _1) contractSignatures

contractStatusPane ::
  forall p t.
  Map ContractInstanceId (WebData (ContractInstanceState t /\ Array EndpointForm)) ->
  ContractInstanceState t -> HTML p HAction
contractStatusPane contractSignatures contractInstance =
  div_
    [ contractRequestView contractInstance
    , div_
        ( case Map.lookup contractInstanceId contractSignatures of
            Just remoteData ->
              webDataPane
                ( \(_ /\ endpointForms) ->
                    row_
                      ( mapWithIndex
                          (\index endpointForm -> actionCard contractInstanceId (ChangeContractEndpointCall contractInstanceId index) endpointForm)
                          endpointForms
                      )
                )
                remoteData
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
  contractTitle = view (_csContract <<< _contractInstanceIdString) contractInstance

  requests = view (_csCurrentState <<< _hooks) contractInstance

  requestRow (Request { itID: IterationID itID, rqID: RequestID rqID, rqRequest }) =
    tr_
      [ td_ [ text $ show itID ]
      , td_ [ text $ show rqID ]
      , td_ [ pretty rqRequest ]
      ]

hasActiveRequests :: forall t. ContractInstanceState t -> Boolean
hasActiveRequests contractInstance = not $ null $ view (_csCurrentState <<< _hooks) contractInstance

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
