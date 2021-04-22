module ContractHome.View where

import Prelude hiding (div)
import Contract.Lenses (_contractInstanceId, _executionState, _metadata)
import Contract.State (currentStep, isContractClosed)
import Contract.Types (State) as Contract
import ContractHome.Lenses (_status)
import ContractHome.State (partitionContracts)
import ContractHome.Types (Action(..), ContractStatus(..), State, PartitionedContracts)
import Css (classNames)
import Css as Css
import Data.Array (length)
import Data.Lens ((^.))
import Data.Maybe (maybe')
import Halogen.HTML (HTML, a, div, h2, p_, span, text)
import Halogen.HTML.Events.Extra (onClick_)
import Marlowe.Execution (_mNextTimeout)
import Marlowe.Extended (contractTypeName, contractTypeInitials)
import Marlowe.Semantics (Slot)
import Marlowe.Slot (secondsDiff)
import Material.Icons (Icon(..), icon_)
import TimeHelpers (humanizeDuration)

contractsScreen :: forall p. Slot -> State -> HTML p Action
contractsScreen currentSlot state =
  let
    buttonClasses = [ "w-40", "text-center" ]

    selectorButton true = Css.whiteButton <> buttonClasses

    selectorButton false = Css.secondaryButton <> buttonClasses

    -- TODO: This is going to be called every second, if we have a performance issue
    -- see if we can use Lazy or to store the partition result in the state
    contracts = partitionContracts state.contracts

    viewSelector =
      div [ classNames [ "flex", "my-4", "justify-between", "sm:justify-center", "px-4" ] ]
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
      [ classNames [ "pt-4", "flex", "flex-col", "h-full" ] ]
      [ h2
          [ classNames [ "font-semibold", "text-lg", "mb-4", "px-4", "md:px-5pc" ] ]
          [ text "Home" ]
      , viewSelector
      -- NOTE: This extra div is necesary to make the scroll only to work for the contract area.
      --       The parent flex with h-full and this element flex-grow makes the div to occupy the remaining
      --       vertical space.
      , div [ classNames [ "overflow-y-auto", "flex-grow", "px-4", "md:px-5pc" ] ]
          [ renderContracts currentSlot state contracts
          ]
      , a
          [ classNames $ Css.primaryButton <> Css.withIcon Add <> Css.fixedBottomRight
          , onClick_ $ OpenTemplateLibraryCard
          ]
          [ text "Create" ]
      ]

renderContracts :: forall p. Slot -> State -> PartitionedContracts -> HTML p Action
renderContracts currentSlot { status: Running } { running }
  | length running == 0 = p_ [ text "You have no running contracts. Tap create to begin" ]
  | otherwise = contractGrid currentSlot running

renderContracts currentSlot { status: Completed } { completed }
  | length completed == 0 = p_ [ text "You have no completed contracts." ]
  | otherwise = contractGrid currentSlot completed

contractGrid :: forall p. Slot -> Array Contract.State -> HTML p Action
contractGrid currentSlot contracts =
  div
    [ classNames [ "grid", "gap-4", "mb-4", "grid-cols-1", "sm:grid-cols-2-contract-home-card", "md:grid-cols-auto-fill-contract-home-card", "justify-center", "sm:justify-start" ] ]
    $ map (contractCard currentSlot) contracts

contractCard :: forall p. Slot -> Contract.State -> HTML p Action
contractCard currentSlot contractState =
  let
    metadata = contractState ^. _metadata

    longTitle = metadata.contractName

    contractType = contractTypeName metadata.contractType

    contractAcronym = contractTypeInitials metadata.contractType

    stepNumber = currentStep contractState + 1

    mNextTimeout = contractState ^. (_executionState <<< _mNextTimeout)

    contractId = contractState ^. _contractInstanceId

    timeoutStr =
      maybe'
        (\_ -> if isContractClosed contractState then "Contract closed" else "Timed out")
        (\nextTimeout -> humanizeDuration $ secondsDiff nextTimeout currentSlot)
        mNextTimeout
  in
    div
      -- NOTE: The overflow hidden helps fix a visual bug in which the background color eats away the border-radius
      [ classNames
          [ "cursor-pointer", "shadow", "bg-white", "rounded", "overflow-hidden" ]
      , onClick_ $ OpenContract contractId
      ]
      [ div [ classNames [ "flex", "px-4", "pt-4" ] ]
          [ span [ classNames [ "text-xl", "font-semibold" ] ] [ text contractAcronym ]
          , span [ classNames [ "flex-grow", "text-xs" ] ] [ text contractType ]
          , icon_ ArrowRight
          ]
      , div [ classNames [ "font-semibold", "px-4", "py-2" ] ]
          [ text longTitle
          ]
      , div [ classNames [ "bg-lightgray", "flex", "flex-col", "px-4", "py-2" ] ]
          [ span [ classNames [ "text-xs" ] ] [ text $ "Step " <> show stepNumber <> ":" ]
          , span [ classNames [ "text-xl" ] ] [ text timeoutStr ]
          ]
      ]
