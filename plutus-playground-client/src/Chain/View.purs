module Chain.View (chainView) where

import Prelude hiding (div)

import Bootstrap (active, card, cardBody_, cardHeader, cardHeader_, col2, col3_, col4_, col6_, col_, empty, nbsp, row, row_, textTruncate)
import Chain.Types (ChainFocus(..), State, toBeneficialOwner)
import Data.Array as Array
import Data.Array.Extra (intersperse)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Newtype (unwrap)
import Data.Json.JsonTuple (JsonTuple(..))
import Data.Tuple (fst)
import Data.Tuple.Nested (type (/\), (/\))
import Halogen (action)
import Halogen.HTML (ClassName(..), HTML, br_, div, div_, h2_, hr_, small_, span, span_, strong_, text)
import Halogen.HTML.Events (onClick)
import Halogen.HTML.Properties (class_, classes)
import Language.PlutusTx.AssocMap as AssocMap
import Ledger.Ada (Ada(..))
import Ledger.Crypto (PubKey(..))
import Ledger.Extra (humaniseInterval, adaToValue)
import Ledger.Scripts (DataScript(..))
import Ledger.Tx (AddressOf(..), Tx(..), TxOutOf(..), TxOutType(..))
import Ledger.TxId (TxIdOf(..))
import Ledger.Value (CurrencySymbol(..), TokenName(..), Value(..))
import Playground.Types (AnnotatedTx(..), BeneficialOwner(..), SequenceId(..))
import Types (Query(..))
import Wallet.Emulator.Types (Wallet(..))

chainView :: forall p. State -> Map PubKey Wallet -> Array (Array AnnotatedTx) -> HTML p (Query Unit)
chainView state walletKeys annotatedBlockchain =
  div
    [ classes
        ( [ ClassName "chain", ClassName "animation" ]
            <> case state.chainFocusAge of
                LT -> [ ClassName "animation-newer" ]
                EQ -> []
                GT -> [ ClassName "animation-older" ]
            <> if state.chainFocusAppearing then
                []
              else
                [ ClassName "animation-done" ]
        )
    ]
    [ h2_
        [ text "Blockchain"
        , nbsp
        , small_ [ text "Click a transaction for details" ]
        ]
    , div
        [ classes [ row, ClassName "blocks" ] ]
        (chainSlotView state <$> Array.reverse annotatedBlockchain)
    , div [ class_ $ ClassName "detail" ]
        [ detailView state walletKeys annotatedBlockchain ]
    ]

slotEmpty :: ClassName
slotEmpty = ClassName "slot-empty"

slot :: ClassName
slot = ClassName "slot"

chainSlotView :: forall p. State -> Array AnnotatedTx -> HTML p (Query Unit)
chainSlotView state [] = empty

chainSlotView state chainSlot =
  div [ classes [ col2, slot ] ]
    (blockView state <$> chainSlot)

blockView :: forall p. State -> AnnotatedTx -> HTML p (Query Unit)
blockView state annotatedTx@(AnnotatedTx { txId, sequenceId }) =
  div
    [ classes ([ card, ClassName "transaction" ] <> if isActive then [ active ] else [])
    , onClick $ const $ Just $ action
        $ SetChainFocus
        $ Just
        $ FocusTx annotatedTx
    ]
    [ entryCardHeader sequenceId ]
  where
  isActive = case state of
    ({ chainFocus: Just (FocusTx focusTx) }) -> focusTx == annotatedTx
    _ -> false

detailView :: forall p. State -> Map PubKey Wallet -> Array (Array AnnotatedTx) -> HTML p (Query Unit)
detailView state@{ chainFocus:
  Just
  ( FocusTx
    ( AnnotatedTx
      annotatedTx@{ tx: Tx tx
    , dereferencedInputs
    , balances
    , sequenceId
    , txId: (TxIdOf { getTxId: txId })
    }
  )
)
} walletKeys annotatedBlockchain =
  div_
    [ row_
        [ col3_
            [ h2_ [ text "Inputs" ]
            , forgeView tx.txForge
            , div_ (txOutOfView true walletKeys <<< _.refersTo <<< unwrap <$> dereferencedInputs)
            ]
        , col6_
            [ h2_ [ text "Transaction" ]
            , div [ classes [ card, active ] ]
                [ entryCardHeader sequenceId
                , cardBody_
                    [ div
                        [ class_ textTruncate ]
                        [ strong_ [ text "Tx: " ]
                        , nbsp
                        , text txId
                        ]
                    , div_
                        [ strong_ [ text "Validity:" ]
                        , nbsp
                        , text $ humaniseInterval tx.txValidRange
                        ]
                    , div_
                        [ strong_ [ text "Signatures:" ]
                        , nbsp
                        , case unwrap tx.txSignatures of
                            [] -> text "None"
                            sigs -> div_ (showPubKey <<< fst <<< unwrap <$> sigs)
                        ]
                    ]
                ]
            ]
        , col3_
            [ h2_ [ text "Outputs" ]
            , feeView tx.txFee
            , div_ (txOutOfView false walletKeys <$> tx.txOutputs)
            ]
        ]
    , balancesView sequenceId walletKeys (AssocMap.toDataMap balances)
    ]

detailView state@{ chainFocus: Nothing } _ _ = div_ []

entryCardHeader :: forall i p. SequenceId -> HTML p i
entryCardHeader sequenceId =
  div [ classes [ cardHeader, textTruncate ] ]
    [ triangleRight
    , sequenceIdView sequenceId
    ]

entry :: ClassName
entry = ClassName "entry"

triangleRight :: forall p i. HTML p i
triangleRight = div [ class_ $ ClassName "triangle-right" ] []

feeView :: forall p i. Ada -> HTML p i
feeView (Lovelace { getLovelace: 0 }) = text ""

feeView txFee =
  div [ classes [ card, entry, ClassName "fee" ] ]
    [ cardHeader_ [ text "Fee" ]
    , cardBody_
        [ valueView $ adaToValue txFee
        ]
    ]

forgeView :: forall p i. Value -> HTML p i
forgeView (Value { getValue: (AssocMap.Map []) }) = text ""

forgeView txForge =
  div [ classes [ card, entry, ClassName "forge" ] ]
    [ cardHeader_ [ triangleRight, text "Forge" ]
    , cardBody_
        [ valueView txForge
        ]
    ]

balancesView :: forall p i. SequenceId -> Map PubKey Wallet -> Map BeneficialOwner Value -> HTML p i
balancesView sequenceId walletKeys m =
  div []
    [ h2_
        [ text "Balances Carried Forward"
        , nbsp
        , small_
            [ text "(as at "
            , sequenceIdView sequenceId
            , text ")"
            ]
        ]
    , row_ (balanceView <$> Map.toUnfoldable m)
    ]
  where
  balanceView :: BeneficialOwner /\ Value -> HTML p i
  balanceView (beneficialOwner /\ value) =
    col3_
      [ div
          [ classes [ card, entry, beneficialOwnerClass beneficialOwner ]
          ]
          [ cardHeaderOwnerView false walletKeys beneficialOwner
          , cardBody_ [ valueView value ]
          ]
      ]

sequenceIdView :: forall p i. SequenceId -> HTML p i
sequenceIdView sequenceId =
  span_
    [ text $ formatSequenceId sequenceId ]

formatSequenceId :: SequenceId -> String
formatSequenceId (SequenceId { slotIndex, txIndex }) = "Slot #" <> show slotIndex <> ", Tx #" <> show txIndex

txOutOfView :: forall p. Boolean -> Map PubKey Wallet -> TxOutOf String -> HTML p (Query Unit)
txOutOfView showArrow walletKeys txOutOf@(TxOutOf { txOutAddress, txOutType, txOutValue }) =
  div
    [ classes [ card, entry, beneficialOwnerClass beneficialOwner ] ]
    [ cardHeaderOwnerView showArrow walletKeys beneficialOwner
    , cardBody_
        [ valueView txOutValue ]
    ]
  where
  beneficialOwner = toBeneficialOwner txOutOf

beneficialOwnerClass :: BeneficialOwner -> ClassName
beneficialOwnerClass (OwnedByPubKey _) = ClassName "wallet"

beneficialOwnerClass (OwnedByScript _) = ClassName "script"

cardHeaderOwnerView :: forall p i. Boolean -> Map PubKey Wallet -> BeneficialOwner -> HTML p i
cardHeaderOwnerView showArrow walletKeys beneficialOwner =
  div [ classes [ cardHeader, textTruncate ] ]
    [ if showArrow then triangleRight else text ""
    , beneficialOwnerView walletKeys beneficialOwner
    ]

beneficialOwnerView :: forall p i. Map PubKey Wallet -> BeneficialOwner -> HTML p i
beneficialOwnerView walletKeys (OwnedByPubKey pubKey) = case Map.lookup pubKey walletKeys of
  Nothing -> showPubKey pubKey
  Just (Wallet { getWallet: n }) ->
    span
      [ class_ textTruncate ]
      [ showPubKey pubKey
      , br_
      , small_
          [ text "Wallet"
          , nbsp
          , text $ show n
          ]
      ]

beneficialOwnerView _ (OwnedByScript (AddressOf a)) =
  span_
    [ text "Script"
    , nbsp
    , text a.getAddress
    ]

txOutTypeView :: forall p i. Map PubKey Wallet -> TxOutType -> HTML p i
txOutTypeView walletKeys (PayToPubKey pubKey) = case Map.lookup pubKey walletKeys of
  Nothing -> showPubKey pubKey
  Just (Wallet { getWallet: n }) ->
    span
      [ class_ textTruncate ]
      [ showPubKey pubKey
      , br_
      , small_
          [ text "Wallet"
          , nbsp
          , text $ show n
          ]
      ]

txOutTypeView _ (PayToScript (DataScript d)) =
  span_
    [ text "Script"
    , nbsp
    , text d.getDataScript
    ]

showPubKey :: forall p i. PubKey -> HTML p i
showPubKey (PubKey { getPubKey: p }) =
  span_
    [ text "PubKey"
    , nbsp
    , text p
    ]

valueView :: forall p i. Value -> HTML p i
valueView (Value { getValue: (AssocMap.Map []) }) = empty

valueView (Value { getValue: (AssocMap.Map currencies) }) = div_ (intersperse hr_ (currencyView <$> currencies))
  where
  currencyView :: JsonTuple CurrencySymbol (AssocMap.Map TokenName Int) -> HTML p i
  currencyView (JsonTuple (currency /\ (AssocMap.Map tokens))) =
    row_
      [ col4_ [ text $ showCurrency currency ]
      , col_ (tokenView <$> tokens)
      ]

  tokenView :: JsonTuple TokenName Int -> HTML p i
  tokenView (JsonTuple (token /\ balance)) =
    div_
      [ text $ showToken token
      , text ": "
      , text $ show balance
      ]

  showCurrency (CurrencySymbol { unCurrencySymbol: "" }) = "Ada"

  showCurrency (CurrencySymbol { unCurrencySymbol: symbol }) = symbol

  showToken (TokenName { unTokenName: "" }) = "Lovelace"

  showToken (TokenName { unTokenName: name }) = name
