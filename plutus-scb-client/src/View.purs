module View (render) where

import Bootstrap (col12_, col5_, col7_, container_, row_)
import Chain.Types as Chain
import Data.Lens (traversed, view)
import Data.Lens.Extra (toArrayOf)
import Effect.Aff.Class (class MonadAff)
import Halogen.HTML (ClassName(..), ComponentHTML, HTML, div, div_, h1, text)
import Halogen.HTML.Properties (class_)
import NavTabs (mainTabBar, viewContainer)
import Network.StreamData as Stream
import Plutus.SCB.Events (ChainEvent)
import Plutus.SCB.Types (ContractExe)
import Plutus.SCB.Webserver.Types (ChainReport)
import Prelude (($), (<$>), (<<<))
import Types (ContractSignatures, ContractStates, HAction(..), State(..), View(..), WebStreamData, _csrDefinition, _utxoIndex)
import View.Blockchain (annotatedBlockchainPane)
import View.Contracts (contractStatusesPane, installedContractsPane)
import View.Events (eventsPane, utxoIndexPane)
import View.Utils (streamErrorPane, webDataPane2, webStreamDataPane)

render ::
  forall m slots.
  MonadAff m =>
  State -> ComponentHTML HAction slots m
render (State { currentView, chainState, contractSignatures, chainReport, events, contractStates, webSocketMessage }) =
  div
    [ class_ $ ClassName "main-frame" ]
    [ container_
        [ mainHeader
        , mainTabBar ChangeView tabs currentView
        , div_
            $ case webSocketMessage of
                Stream.Failure error -> [ streamErrorPane error ]
                _ -> []
        , div_
            $ webDataPane2
                (mainPane currentView contractStates chainState contractSignatures)
                chainReport
                events
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

mainPane ::
  forall p t.
  View ->
  ContractStates ->
  Chain.State ->
  WebStreamData ContractSignatures ->
  ChainReport t ->
  Array (ChainEvent ContractExe) ->
  HTML p HAction
mainPane currentView contractStates chainState contractSignatures chainReport events =
  row_
    [ activeContractPane currentView contractSignatures contractStates
    , blockchainPane currentView chainState chainReport
    , eventLogPane currentView events chainReport
    ]

activeContractPane ::
  forall p.
  View ->
  WebStreamData ContractSignatures ->
  ContractStates ->
  HTML p HAction
activeContractPane currentView contractSignatures contractStates =
  let
    buttonsDisabled = Stream.isExpected contractSignatures
  in
    viewContainer currentView ActiveContracts
      [ row_
          [ col12_ [ contractStatusesPane contractStates ]
          , col12_
              ( webStreamDataPane
                  ( installedContractsPane buttonsDisabled
                      <<< ( toArrayOf
                            ( traversed
                                <<< _csrDefinition
                            )
                        )
                  )
                  contractSignatures
              )
          ]
      ]

blockchainPane ::
  forall p t.
  View ->
  Chain.State ->
  ChainReport t -> HTML p HAction
blockchainPane currentView chainState chainReport =
  viewContainer currentView Blockchain
    [ row_
        [ col12_ [ ChainAction <$> annotatedBlockchainPane chainState chainReport ]
        ]
    ]

eventLogPane :: forall p t. View -> Array (ChainEvent ContractExe) -> ChainReport t -> HTML p HAction
eventLogPane currentView events chainReport =
  viewContainer currentView EventLog
    [ row_
        [ col7_ [ eventsPane events ]
        , col5_ [ utxoIndexPane (view _utxoIndex chainReport) ]
        ]
    ]
