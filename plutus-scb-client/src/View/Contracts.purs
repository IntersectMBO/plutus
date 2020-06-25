module View.Contracts where

import Halogen.HTML (HTML, br_, button, div_, h2_, h3_, table, tbody_, td_, text, th, th_, thead_, tr_)
import Halogen.HTML.Properties (classes, colSpan)
import Plutus.SCB.Events.Contract (ContractInstanceId, ContractInstanceState)
import Plutus.SCB.Types (ContractExe)
import Plutus.SCB.Webserver.Types (ContractReport(..))
import Prelude
import Types (EndpointForm, HAction(..), WebData, _contractInstanceId, _contractPath, _csContract, _csCurrentState, _hooks)
import AjaxUtils (ajaxErrorPane)
import Bootstrap (btn, btnBlock, btnPrimary, btnSmall, cardBody_, cardFooter_, cardHeader_, card_, col10_, col2_, col4_, nbsp, row_, tableBordered)
import Bootstrap as Bootstrap
import Data.Array (mapWithIndex, null)
import Data.Foldable.Extra (interleave)
import Data.Json.JsonUUID (_JsonUUID)
import Data.Lens (to, view)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.UUID as UUID
import Halogen.HTML.Events (onClick)
import Icons (Icon(..), icon)
import Language.Plutus.Contract.Resumable (IterationID(..), Request(..), RequestID(..))
import Network.RemoteData (RemoteData(..))
import Playground.Lenses (_endpointDescription, _getEndpointDescription, _schema)
import Playground.Schema (actionArgumentForm)
import Playground.Types (_FunctionSchema)
import Schema.Types (FormEvent)
import Validation (_argument)

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
contractStatusesPane contractSignatures (ContractReport { contractStates }) =
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

contractStatusPane ::
  forall p t.
  Map ContractInstanceId (WebData (Array EndpointForm)) ->
  ContractInstanceState t -> HTML p HAction
contractStatusPane contractSignatures contractInstance =
  div_
    [ row_
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
    , contractRequestView contractInstance
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
