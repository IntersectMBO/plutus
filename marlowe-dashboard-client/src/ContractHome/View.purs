module ContractHome.View where

import Prelude hiding (div)
import Contract.Lenses (_executionState, _followerAppId, _mMarloweParams, _metadata)
import Contract.State (currentStep, isContractClosed)
import Contract.Types (State) as Contract
import ContractHome.Lenses (_status)
import ContractHome.State (partitionContracts)
import ContractHome.Types (Action(..), ContractStatus(..), PartitionedContracts, State)
import Css (classNames)
import Css as Css
import Data.Array (length)
import Data.Lens ((^.))
import Data.Maybe (Maybe(..), maybe')
import Halogen.HTML (HTML, a, div, h2, p_, span, text)
import Halogen.HTML.Events.Extra (onClick_)
import Humanize (humanizeDuration)
import Marlowe.Execution.Lenses (_mNextTimeout)
import Marlowe.Extended (contractTypeName, contractTypeInitials)
import Marlowe.Semantics (Slot)
import Marlowe.Slot (secondsDiff)
import Material.Icons (Icon(..), icon)

contractsScreen :: forall p. Slot -> State -> HTML p Action
contractsScreen currentSlot state =
  let
    buttonClasses = [ "w-40", "text-center" ]

    selectorButton true = Css.button <> [ "shadow", "bg-white" ] <> buttonClasses

    selectorButton false = Css.secondaryButton <> buttonClasses

    -- TODO: This is going to be called every second, if we have a performance issue
    -- see if we can use Lazy or to store the partition result in the state
    contracts = partitionContracts state.contracts

    viewSelector =
      div [ classNames [ "flex", "my-4", "justify-center", "px-4" ] ]
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
  | length running == 0 = noContractsMessage "You have no running contracts. Tap create to begin."
  | otherwise = contractGrid currentSlot running

renderContracts currentSlot { status: Completed } { completed }
  | length completed == 0 = noContractsMessage "You have no completed contracts."
  | otherwise = contractGrid currentSlot completed

noContractsMessage :: forall p. String -> HTML p Action
noContractsMessage message =
  div
    [ classNames [ "h-full", "flex", "flex-col", "justify-center", "items-center" ] ]
    [ icon Contract [ "-mt-32", "text-big-icon", "text-gray" ]
    , p_ [ text message ]
    ]

contractGrid :: forall p. Slot -> Array Contract.State -> HTML p Action
contractGrid currentSlot contracts =
  div
    [ classNames [ "grid", "gap-4", "mb-4", "grid-cols-1", "sm:grid-cols-2-contract-home-card", "md:grid-cols-auto-fill-contract-home-card", "justify-center", "sm:justify-start" ] ]
    $ map (contractCard currentSlot) contracts

contractCard :: forall p. Slot -> Contract.State -> HTML p Action
contractCard currentSlot contractState =
  let
    mMarloweParams = contractState ^. _mMarloweParams

    metadata = contractState ^. _metadata

    longTitle = metadata.contractName

    contractType = contractTypeName metadata.contractType

    contractAcronym = contractTypeInitials metadata.contractType

    stepNumber = currentStep contractState + 1

    mNextTimeout = contractState ^. (_executionState <<< _mNextTimeout)

    contractInstanceId = contractState ^. _followerAppId

    timeoutStr =
      maybe'
        (\_ -> if isContractClosed contractState then "Contract closed" else "Timed out")
        (\nextTimeout -> humanizeDuration $ secondsDiff nextTimeout currentSlot)
        mNextTimeout

    attributes = case mMarloweParams of
      Just _ ->
        -- NOTE: The overflow hidden helps fix a visual bug in which the background color eats away the border-radius
        [ classNames [ "flex", "flex-col", "cursor-pointer", "shadow-sm", "hover:shadow", "active:shadow-lg", "bg-white", "rounded", "overflow-hidden" ]
        , onClick_ $ OpenContract contractInstanceId
        ]
      -- in this case the box shouldn't be clickable
      Nothing -> [ classNames [ "flex", "flex-col", "shadow-sm", "bg-white", "rounded", "overflow-hidden" ] ]
  in
    div
      attributes
      -- TODO: This part is really similar to contractTitle in Template.View, see if it makes sense to factor a component out
      [ div [ classNames [ "flex", "px-4", "pt-4", "items-center" ] ]
          [ span [ classNames [ "text-2xl", "leading-none", "font-semibold" ] ] [ text contractAcronym ]
          , span [ classNames [ "flex-grow", "ml-2", "self-start", "text-xs", "uppercase" ] ] [ text contractType ]
          , icon ArrowRight [ "text-28px" ]
          ]
      , div [ classNames [ "flex-1", "px-4", "py-2", "text-lg" ] ]
          [ text longTitle
          ]
      , div [ classNames [ "bg-lightgray", "flex", "flex-col", "px-4", "py-2" ] ] case mMarloweParams of
          Nothing -> [ text "pending confirmation" ]
          _ ->
            [ span [ classNames [ "text-xs", "font-semibold" ] ] [ text $ "Step " <> show stepNumber <> ":" ]
            , span [ classNames [ "text-xl" ] ] [ text timeoutStr ]
            ]
      ]
