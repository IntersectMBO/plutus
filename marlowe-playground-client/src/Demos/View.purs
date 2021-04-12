module Demos.View where

import Prelude hiding (div)
import Data.Maybe (Maybe(..))
import Data.Newtype (wrap)
import Demos.Types (Action(..), Demo)
import Effect.Aff.Class (class MonadAff)
import Halogen (ClassName(..), ComponentHTML)
import Halogen.Classes (group, modalContent)
import Halogen.HTML (HTML, button, div, div_, h2_, hr_, span, text)
import Halogen.HTML.Events (onClick)
import Halogen.HTML.Properties (class_, classes)
import MainFrame.Types (ChildSlots)
import Modal.ViewHelpers (modalHeader)
import Projects.Types (Lang(..))

render ::
  forall m state.
  MonadAff m =>
  state ->
  ComponentHTML Action ChildSlots m
render state =
  div_
    [ modalHeader "Demo Files" (Just Cancel)
    , div [ classes [ modalContent, ClassName "projects-container" ] ]
        [ demoFile (wrap "Escrow") "Escrow" "Regulates a money exchange between a \"Buyer\" and a \"Seller\". If there is a disagreement, an \"Arbiter\" will decide whether the money is refunded or paid to the \"Seller\"."
        , demoFile (wrap "EscrowWithCollateral") "Escrow With Collateral" "Regulates a money exchange between a \"Buyer\" and a \"Seller\" using a collateral from both parties to incentivize collaboration. If there is a disagreement the collateral is burned."
        , demoFile (wrap "ZeroCouponBond") "Zero Coupon Bond" "A simple loan. The investor pays the issuer the discounted price at the start, and is repaid the full (notional) price at the end."
        , demoFile (wrap "CouponBondGuaranteed") "Coupon Bond Guaranteed" "Debt agreement between an \"Investor\" and an \"Issuer\". \"Investor\" will advance the \"Principal\" amount at the beginning of the contract, and the \"Issuer\" will pay back \"Interest instalment\" every 30 slots and the \"Principal\" amount by the end of 3 instalments. The debt is backed by a collateral provided by the \"Guarantor\" which will be refunded as long as the \"Issuer\" pays back on time."
        , demoFile (wrap "Swap") "Swap" "Takes Ada from one party and dollar tokens from another party, and it swaps them atomically."
        , demoFile (wrap "CFD") "Contract For Differences" "\"Party\" and \"Counterparty\" deposit 100 Ada and after 60 slots is redistributed depending on the change in a given trade price reported by \"Oracle\". If the price increases, the difference goes to \"Counterparty\"; if it decreases, the difference goes to \"Party\", up to a maximum of 100 Ada."
        , demoFile (wrap "CFDWithOracle") "Contract For Differences with Oracle" "\"Party\" and \"Counterparty\" deposit 100 Ada and after 60 slots is redistributed depending on the change in price of 100 Ada worth of dollars by the end of the contract. If the price increases, the difference goes to \"Counterparty\"; if it decreases, the difference goes to \"Party\", up to a maximum of 100 Ada."
        ]
    ]

demoFile :: forall p. Demo -> String -> String -> HTML p Action
demoFile key name description =
  div []
    [ h2_ [ text name ]
    , div [ class_ group ]
        [ span [ class_ (ClassName "description") ] [ text description ]
        , div [ classes [ group, ClassName "open-buttons" ] ]
            [ button [ onClick $ const $ Just $ LoadDemo Haskell key ] [ text "Haskell" ]
            , button [ onClick $ const $ Just $ LoadDemo Javascript key ] [ text "Javascript" ]
            , button [ onClick $ const $ Just $ LoadDemo Marlowe key ] [ text "Marlowe" ]
            , button [ onClick $ const $ Just $ LoadDemo Blockly key ] [ text "Blockly" ]
            ]
        ]
    , hr_
    ]
