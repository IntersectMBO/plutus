module ContractHome.View where

import Prelude hiding (div)
import Contract.Lenses (_metadata, _step)
import Contract.Types (State) as Contract
import ContractHome.Lenses (_contracts, _status)
import ContractHome.Types (Action(..), ContractStatus(..), State)
import Css (classNames)
import Css as Css
import Data.Lens ((^.))
import Halogen.HTML (HTML, a, div, h2, p_, span, text)
import Halogen.HTML.Events.Extra (onClick_)
import Marlowe.Extended (contractTypeName, contractTypeInitials)
import Material.Icons as Icon

contractsScreen :: forall p. State -> HTML p Action
contractsScreen state =
  let
    selectorButton isActive =
      Css.button <> [ "font-bold", "w-48" ]
        <> case isActive of
            true -> [ "bg-white", "shadow-deep" ]
            false -> [ "bg-gray" ]

    viewSelector =
      div [ classNames [ "flex", "my-4", "justify-center" ] ]
        [ a
            [ classNames $ (selectorButton $ state ^. _status == Running) <> [ "mr-4" ]
            , onClick_ $ SelectView Running
            ]
            [ text "What's running" ]
        , a
            [ classNames $ selectorButton $ state ^. _status == Completed
            , onClick_ $ SelectView Completed
            ]
            [ text "History" ]
        ]
  in
    div
      [ classNames [ "p-4" ] ]
      [ h2 [ classNames [ "font-semibold" ] ]
          [ text "Home" ]
      , viewSelector
      , renderContractList state
      , a
          [ classNames Css.fixedPrimaryButton
          , onClick_ $ ToggleTemplateLibraryCard
          ]
          [ span
              [ classNames [ "mr-2" ] ]
              [ text "Create" ]
          , Icon.add_
          ]
      ]

renderContractList :: forall p. State -> HTML p Action
renderContractList { status: Running, contracts: [] } = p_ [ text "You have no running contracts. Tap create to begin" ]

renderContractList { status: Completed, contracts: [] } = p_ [ text "You have no completed contracts." ]

-- FIXME: Separate between running and completed contracts
renderContractList state =
  let
    contracts = state ^. _contracts
  in
    div
      [ classNames [ "space-y-4" ] ]
      $ contractCard
      <$> contracts

contractCard :: forall p. Contract.State -> HTML p Action
contractCard contractState =
  let
    metadata = contractState ^. _metadata

    longTitle = metadata.contractName

    contractType = contractTypeName metadata.contractType

    contractAcronym = contractTypeInitials metadata.contractType

    -- As programmers we use 0-indexed arrays and steps, but we number steps
    -- starting from 1
    stepNumber = contractState ^. _step + 1

    -- FIXME: hardcoded time slot
    timeoutStr = "8hr 10m left"
  in
    div
      -- NOTE: The overflow hidden helps fix a visual bug in which the background color eats away the border-radius
      [ classNames
          [ "cursor-pointer", "shadow-lg", "bg-white", "rounded-xl", "md:mx-auto", "md:w-96", "overflow-hidden" ]
      , onClick_ $ OpenContract contractState
      ]
      [ div [ classNames [ "flex", "px-4", "pt-4" ] ]
          [ span [ classNames [ "text-xl", "font-semibold" ] ] [ text contractAcronym ]
          , span [ classNames [ "flex-grow", "text-xs" ] ] [ text contractType ]
          , Icon.east_
          ]
      , div [ classNames [ "font-semibold", "px-4", "py-2" ] ]
          [ text longTitle
          ]
      , div [ classNames [ "bg-gray", "flex", "flex-col", "px-4", "py-2" ] ]
          [ span [ classNames [ "text-xs" ] ] [ text $ "Step " <> show stepNumber <> ":" ]
          , span [ classNames [ "text-xl" ] ] [ text timeoutStr ]
          ]
      ]
