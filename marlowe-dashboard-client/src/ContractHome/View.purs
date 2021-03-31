module ContractHome.View where

import Prelude hiding (div)
import Contract.Lenses (_mNextTimeout, _metadata)
import Contract.State (currentStep)
import Contract.Types (State) as Contract
import ContractHome.Lenses (_contracts, _status)
import ContractHome.Types (Action(..), ContractStatus(..), State)
import Css (classNames)
import Css as Css
import Data.FunctorWithIndex (mapWithIndex)
import Data.Lens ((^.))
import Data.Maybe (maybe)
import TimeHelpers (humanizeDuration)
import Halogen.HTML (HTML, a, div, h2, p_, span, text)
import Halogen.HTML.Events.Extra (onClick_)
import Marlowe.Extended (contractTypeName, contractTypeInitials)
import Marlowe.Semantics (Slot)
import Marlowe.Slot (secondsDiff)
import Material.Icons (Icon(..), icon_)

contractsScreen :: forall p. Slot -> State -> HTML p Action
contractsScreen currentSlot state =
  let
    buttonClasses = [ "w-40", "text-center" ]

    selectorButton true = Css.whiteButton <> buttonClasses

    selectorButton false = Css.secondaryButton <> buttonClasses

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
      [ classNames [ "p-4", "md:px-5pc" ] ]
      [ h2
          [ classNames [ "font-semibold", "text-lg", "mb-4" ] ]
          [ text "Home" ]
      , viewSelector
      , renderContractList currentSlot state
      , a
          [ classNames $ Css.primaryButton <> Css.withIcon Add <> Css.fixedBottomRight
          , onClick_ $ ToggleTemplateLibraryCard
          ]
          [ text "Create" ]
      ]

renderContractList :: forall p. Slot -> State -> HTML p Action
renderContractList _ { status: Running, contracts: [] } = p_ [ text "You have no running contracts. Tap create to begin" ]

renderContractList _ { status: Completed, contracts: [] } = p_ [ text "You have no completed contracts." ]

-- FIXME: Separate between running and completed contracts
renderContractList currentSlot state =
  let
    contracts = state ^. _contracts
  in
    div
      [ classNames [ "space-y-4" ] ]
      $ mapWithIndex (contractCard currentSlot) contracts

contractCard :: forall p. Slot -> Int -> Contract.State -> HTML p Action
contractCard currentSlot index contractState =
  let
    metadata = contractState ^. _metadata

    longTitle = metadata.contractName

    contractType = contractTypeName metadata.contractType

    contractAcronym = contractTypeInitials metadata.contractType

    stepNumber = currentStep contractState + 1

    mNextTimeout = contractState ^. _mNextTimeout

    timeoutStr =
      maybe "timed out"
        (\nextTimeout -> humanizeDuration $ secondsDiff nextTimeout currentSlot)
        mNextTimeout
  in
    div
      -- NOTE: The overflow hidden helps fix a visual bug in which the background color eats away the border-radius
      [ classNames
          [ "cursor-pointer", "shadow", "bg-white", "rounded", "mx-auto", "md:w-96", "overflow-hidden" ]
      , onClick_ $ OpenContract index
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
