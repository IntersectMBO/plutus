module Chain.View where

import Prelude hiding (div)
import Bootstrap (active, card, cardBody_, cardHeader, cardHeader_, col2, col3_, col4_, col6_, col_, empty, nbsp, row, row_, textTruncate)
import Chain.Types (State, ChainFocus(..))
import Data.Array as Array
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Newtype (unwrap)
import Data.RawJson (JsonTuple(..))
import Data.Tuple (fst)
import Data.Tuple.Nested (type (/\), (/\))
import Halogen (action)
import Halogen.HTML (ClassName(..), HTML, br_, code_, div, div_, h2_, small_, span_, strong_, text)
import Halogen.HTML.Events (onClick)
import Halogen.HTML.Properties (class_, classes)
import Language.PlutusTx.AssocMap as AssocMap
import Ledger.Ada (Ada(..))
import Ledger.Crypto (PubKey(..))
import Ledger.Extra (humaniseInterval)
import Ledger.Scripts (DataScript(..))
import Ledger.Tx (Tx(..), TxOutOf(..), TxOutType(..))
import Ledger.TxId (TxIdOf(..))
import Ledger.Value (CurrencySymbol(..), TokenName(..), Value(..))
import Playground.Types (AnnotatedTx(..), SequenceId(..))
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
blockView state annotatedTx@(AnnotatedTx { txId }) =
  div
    [ classes ([ card, ClassName "transaction" ] <> if isActive then [ active ] else [])
    , onClick $ const $ Just $ action
        $ SetChainFocus
        $ Just
        $ FocusTx annotatedTx
    ]
    [ cardHeaderTxId txId ]
  where
  isActive = case state of
    ({ chainFocus: Just (FocusTx focusTx) }) -> focusTx == annotatedTx
    _ -> false

detailView :: forall p. State -> Map PubKey Wallet -> Array (Array AnnotatedTx) -> HTML p (Query Unit)
detailView state@{ chainFocus: Just (FocusTx (AnnotatedTx annotatedTx@{ tx: Tx tx, dereferencedInputs, balances, sequenceId })) } walletKeys annotatedBlockchain =
  div_
    [ row_
        [ col3_
            [ h2_ [ text "Inputs" ]
            , feeView tx.txFee
            , forgeView tx.txForge
            , div_ (txOutOfView true walletKeys <$> dereferencedInputs)
            ]
        , col6_
            [ h2_ [ text "Transaction" ]
            , div [ classes [ card, active ] ]
                [ cardHeaderTxId annotatedTx.txId
                , cardBody_
                    [ div_
                        [ strong_ [ text "Position:" ]
                        , nbsp
                        , showSequenceId sequenceId
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
            , div_ (txOutOfView false walletKeys <$> tx.txOutputs)
            ]
        ]
    , balancesView sequenceId walletKeys (AssocMap.toDataMap balances)
    ]

detailView state@{ chainFocus: Just (FocusAddress address) } _ _ = div_ [ code_ [ text $ show address ] ]

detailView state@{ chainFocus: Nothing } _ _ = div_ []

cardHeaderTxId :: forall i p. TxIdOf String -> HTML p i
cardHeaderTxId (TxIdOf { getTxId: t }) =
  div [ classes [ cardHeader, textTruncate ] ]
    [ triangleRight
    , strong_ [ text "Tx" ]
    , nbsp
    , text t
    ]

entry :: ClassName
entry = ClassName "entry"

triangleRight :: forall p i. HTML p i
triangleRight = div [ class_ $ ClassName "triangle-right" ] []

feeView :: forall p i. Ada -> HTML p i
feeView (Lovelace { getLovelace: 0 }) = text ""

feeView txFee =
  div [ classes [ card, entry, ClassName "fee" ] ]
    [ cardHeader_ [ triangleRight, text "Fee" ]
    , cardBody_
        [ div_ [ code_ [ text $ show txFee ] ]
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

balancesView :: forall p i. SequenceId -> Map PubKey Wallet -> Map TxOutType Value -> HTML p i
balancesView sequenceId walletKeys m =
  div []
    [ h2_
        [ text "Balances Carried Forward"
        , nbsp
        , small_
            [ text "(as at "
            , showSequenceId sequenceId
            , text ")"
            ]
        ]
    , row_ (balanceView <$> Map.toUnfoldable m)
    ]
  where
  balanceView :: TxOutType /\ Value -> HTML p i
  balanceView (txOutType /\ value) =
    col3_
      [ div
          [ classes [ card, entry, outTypeClass txOutType ]
          ]
          [ cardHeaderTxOutTypeView false walletKeys txOutType
          , cardBody_ [ valueView value ]
          ]
      ]

showSequenceId :: forall p i. SequenceId -> HTML p i
showSequenceId (SequenceId { slotIndex, txIndex }) =
  span_
    [ text "Slot #"
    , text $ show slotIndex
    , text ", "
    , text "Transaction #"
    , text $ show txIndex
    ]

txOutOfView :: forall p. Boolean -> Map PubKey Wallet -> TxOutOf String -> HTML p (Query Unit)
txOutOfView showArrow walletKeys txOutOf@(TxOutOf { txOutAddress, txOutType, txOutValue }) =
  div
    [ classes [ card, entry, outTypeClass txOutType ]
    , onClick
        $ const
        $ Just
        $ action
        $ SetChainFocus
        $ Just
        $ FocusAddress txOutAddress
    ]
    [ cardHeaderTxOutTypeView showArrow walletKeys txOutType
    , cardBody_
        [ valueView txOutValue ]
    ]

outTypeClass :: TxOutType -> ClassName
outTypeClass (PayToPubKey _) = ClassName "wallet"

outTypeClass (PayToScript _) = ClassName "script"

cardHeaderTxOutTypeView :: forall p i. Boolean -> Map PubKey Wallet -> TxOutType -> HTML p i
cardHeaderTxOutTypeView showArrow walletKeys txOutType =
  div [ classes [ cardHeader, textTruncate ] ]
    [ if showArrow then triangleRight else text ""
    , txOutTypeView walletKeys txOutType
    ]

txOutTypeView :: forall p i. Map PubKey Wallet -> TxOutType -> HTML p i
txOutTypeView walletKeys (PayToPubKey pubKey) = case Map.lookup pubKey walletKeys of
  Nothing -> showPubKey pubKey
  Just (Wallet { getWallet: n }) ->
    span_
      [ showPubKey pubKey
      , br_
      , small_
          [ text "Wallet"
          , nbsp
          , text $ show n
          ]
      ]

txOutTypeView _ (PayToScript dataScript) = showDataScript dataScript

showDataScript :: forall p i. DataScript -> HTML p i
showDataScript (DataScript { getDataScript: d }) =
  span_
    [ text "Script"
    , nbsp
    , text d
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

valueView (Value { getValue: (AssocMap.Map currencies) }) = div_ (currencyView <$> currencies)
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
