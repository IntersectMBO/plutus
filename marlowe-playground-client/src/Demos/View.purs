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
        [ demoFile (wrap "Escrow") "Escrow" "Escrow is a financial arrangement where a third party holds and regulates payment of the funds required for two parties involved in a given transaction."
        , demoFile (wrap "EscrowWithCollateral") "Escrow With Collateral" "Variation of Escrow contract that relies on a mutual collateral insteead of trusted third-party"
        , demoFile (wrap "ZeroCouponBond") "Zero Coupon Bond" "A zero-coupon bond is a debt security that does not pay interest but instead trades at a deep discount, rendering a profit at maturity, when the bond is redeemed for its full face value."
        , demoFile (wrap "CouponBondGuaranteed") "Coupon Bond Guaranteed" "A guaranteed bond is a debt security that offers a secondary guarantee that interest and principal payments will be made by a third party, should the issuer default. It can be backed by a bond insurance company, a fund or group entity, a government authority, or the corporate parents of subsidiaries or joint ventures that are issuing bonds."
        , demoFile (wrap "Swap") "Swap" "A swap is a derivative contract through which two parties exchange the cash flows or liabilities from two different financial instruments. Most swaps involve cash flows based on a notional principal amount such as a loan or bond, although the instrument can be almost anything. Usually, the principal does not change hands. Each cash flow comprises one leg of the swap. One cash flow is generally fixed, while the other is variable and based on a benchmark interest rate, floating currency exchange rate or index price. "
        , demoFile (wrap "CFD") "Contract For Differences" "A contract for differences (CFD) is an arrangement made in financial derivatives trading where the differences in the settlement between the open and closing trade prices are cash-settled"
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
