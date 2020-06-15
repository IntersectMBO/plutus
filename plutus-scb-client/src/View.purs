module View (render) where

import Bootstrap (col12_, col5_, col7_, container_, row_)
import Chain.Types as Chain
import Data.Lens (traversed, view)
import Data.Lens.Extra (toArrayOf)
import Data.Map (Map)
import Data.Tuple.Nested (type (/\))
import Effect.Aff.Class (class MonadAff)
import Halogen.HTML (ClassName(..), ComponentHTML, HTML, div, div_, h1, text)
import Halogen.HTML.Properties (class_)
import NavTabs (mainTabBar, viewContainer)
import Plutus.SCB.Events.Contract (ContractInstanceId, ContractInstanceState)
import Plutus.SCB.Types (ContractExe)
import Plutus.SCB.Webserver.Types (FullReport(..))
import Prelude (($), (<$>), (<<<))
import Types (EndpointForm, HAction(..), State(..), View(..), WebData, _crAvailableContracts, _csrDefinition, _utxoIndex)
import View.Blockchain (annotatedBlockchainPane)
import View.Contracts (contractStatusesPane, installedContractsPane)
import View.Events (eventsPane, utxoIndexPane)
import View.Utils (webDataPane)

render ::
  forall m slots.
  MonadAff m =>
  State -> ComponentHTML HAction slots m
render (State { currentView, chainState, fullReport, contractSignatures, webSocketMessage }) =
  div
    [ class_ $ ClassName "main-frame" ]
    [ container_
        [ mainHeader
        , mainTabBar ChangeView tabs currentView
        , div_ (webDataPane (fullReportPane currentView chainState contractSignatures) fullReport)
        ]
    ]

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
  Map ContractInstanceId (WebData (ContractInstanceState ContractExe /\ Array EndpointForm)) ->
  FullReport ContractExe ->
  HTML p HAction
fullReportPane currentView chainState contractSignatures fullReport@(FullReport { events, contractReport, chainReport }) =
  row_
    [ viewContainer currentView ActiveContracts
        [ row_
            [ col12_ [ contractStatusesPane contractSignatures ]
            , col12_
                [ installedContractsPane
                    ( toArrayOf
                        ( _crAvailableContracts
                            <<< traversed
                            <<< _csrDefinition
                        )
                        contractReport
                    )
                ]
            ]
        ]
    , viewContainer currentView Blockchain
        [ row_
            [ col12_ [ ChainAction <$> annotatedBlockchainPane chainState chainReport ]
            ]
        ]
    , viewContainer currentView EventLog
        [ row_
            [ col7_ [ eventsPane events ]
            , col5_ [ utxoIndexPane (view _utxoIndex chainReport) ]
            ]
        ]
    ]
