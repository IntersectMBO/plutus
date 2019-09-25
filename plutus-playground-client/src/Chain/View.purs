module Chain.View (chainView) where

import Prelude hiding (div)
import Bootstrap (active, card, cardBody_, cardHeader, cardHeader_, col, col2, col3_, col6_, col_, empty, nbsp, row, row_, tableBordered, tableSmall, textTruncate)
import Chain.Types (ChainFocus(..), State, toBeneficialOwner)
import Data.Array ((:))
import Data.Array as Array
import Data.Array.Extra (intersperse)
import Data.Foldable (foldMap, foldr)
import Data.FoldableWithIndex (foldMapWithIndex, foldrWithIndex)
import Data.Int (toNumber)
import Data.Json.JsonTuple (JsonTuple(..))
import Data.Lens (Fold', preview)
import Data.Lens.Index (ix)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..), fromMaybe)
import Data.Newtype (unwrap)
import Data.Number.Extra (toLocaleString)
import Data.Set (Set)
import Data.Set as Set
import Data.Tuple (fst)
import Data.Tuple.Nested ((/\))
import Halogen (action)
import Halogen.HTML (ClassName(..), HTML, br_, div, div_, h2_, hr_, small_, span, span_, strong_, table, tbody_, td, text, th, th_, thead_, tr, tr_)
import Halogen.HTML.Events (onClick)
import Halogen.HTML.Properties (class_, classes, colSpan, rowSpan)
import Language.PlutusTx.AssocMap as AssocMap
import Ledger.Ada (Ada(..))
import Ledger.Crypto (PubKey(..))
import Ledger.Extra (humaniseInterval, adaToValue)
import Ledger.Tx (AddressOf(..), Tx(..), TxOutOf(..))
import Ledger.TxId (TxIdOf(..))
import Ledger.Value (CurrencySymbol(..), TokenName(..), Value(..))
import Playground.Types (AnnotatedTx(..), BeneficialOwner(..), SequenceId(..))
import Types (Query(..), _value)
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
        ]
    , div_
        [ small_ [ text "Click a transaction for details" ] ]
    , div
        [ classes [ row, ClassName "blocks" ] ]
        (chainSlotView state <$> Array.reverse annotatedBlockchain)
    , div [ class_ $ ClassName "detail" ]
        [ detailView state walletKeys annotatedBlockchain ]
    ]

slotClass :: ClassName
slotClass = ClassName "slot"

feeClass :: ClassName
feeClass = ClassName "fee"

forgeClass :: ClassName
forgeClass = ClassName "forge"

amountClass :: ClassName
amountClass = ClassName "amount"

chainSlotView :: forall p. State -> Array AnnotatedTx -> HTML p (Query Unit)
chainSlotView state [] = empty

chainSlotView state chainSlot =
  div [ classes [ col2, slotClass ] ]
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
    , balancesTable sequenceId walletKeys (AssocMap.toDataMap balances)
    ]

detailView state@{ chainFocus: Nothing } _ _ = div_ []

entryCardHeader :: forall i p. SequenceId -> HTML p i
entryCardHeader sequenceId =
  div [ classes [ cardHeader, textTruncate ] ]
    [ triangleRight
    , sequenceIdView sequenceId
    ]

entryClass :: ClassName
entryClass = ClassName "entry"

triangleRight :: forall p i. HTML p i
triangleRight = div [ class_ $ ClassName "triangle-right" ] []

feeView :: forall p i. Ada -> HTML p i
feeView (Lovelace { getLovelace: 0 }) = text ""

feeView txFee =
  div [ classes [ card, entryClass, feeClass ] ]
    [ cardHeader_ [ text "Fee" ]
    , cardBody_
        [ valueView $ adaToValue txFee
        ]
    ]

forgeView :: forall p i. Value -> HTML p i
forgeView (Value { getValue: (AssocMap.Map []) }) = text ""

forgeView txForge =
  div [ classes [ card, entryClass, forgeClass ] ]
    [ cardHeader_ [ triangleRight, text "Forge" ]
    , cardBody_
        [ valueView txForge
        ]
    ]

balancesTable :: forall p i. SequenceId -> Map PubKey Wallet -> Map BeneficialOwner Value -> HTML p i
balancesTable sequenceId walletKeys balances =
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
    , table
        [ classes
            [ ClassName "table"
            , tableBordered
            , tableSmall
            , ClassName "balances-table"
            ]
        ]
        [ thead_
            [ tr_
                ( th [ rowSpan 2 ] [ text "Beneficial Owner" ]
                    : foldMapWithIndex (\currency s -> [ th [ colSpan (Set.size s) ] [ text $ showCurrency currency ] ]) headings
                )
            , tr_
                ( foldMap (foldMap tokenHeadingView) headings
                )
            ]
        , tbody_
            ( foldMap
                ( \owner ->
                    [ tr [ class_ $ beneficialOwnerClass owner ]
                        ( th_
                            [ beneficialOwnerView walletKeys owner ]
                            : foldMapWithIndex
                                ( \currency ->
                                    foldMap
                                      ( \token ->
                                          let
                                            _thisBalance :: forall m. Monoid m => Fold' m (Map BeneficialOwner Value) Int
                                            _thisBalance = ix owner <<< _value <<< ix currency <<< ix token

                                            amount :: Maybe Int
                                            amount = preview _thisBalance balances
                                          in
                                            [ td [ class_ amountClass ]
                                                [ text $ formatAmount $ fromMaybe 0 amount ]
                                            ]
                                      )
                                )
                                headings
                        )
                    ]
                )
                (Map.keys balances)
            )
        ]
    ]
  where
  headings :: Map CurrencySymbol (Set TokenName)
  headings = collectBalanceTableHeadings balances

  tokenHeadingView :: TokenName -> Array (HTML p i)
  tokenHeadingView token = [ th_ [ text $ showToken token ] ]

collectBalanceTableHeadings :: Map BeneficialOwner Value -> Map CurrencySymbol (Set TokenName)
collectBalanceTableHeadings balances = foldr collectCurrencies Map.empty $ Map.values balances
  where
  collectCurrencies :: Value -> Map CurrencySymbol (Set TokenName) -> Map CurrencySymbol (Set TokenName)
  collectCurrencies (Value { getValue: entries }) ownersBalance = foldrWithIndex collectTokenNames ownersBalance entries

  collectTokenNames :: CurrencySymbol -> AssocMap.Map TokenName Int -> Map CurrencySymbol (Set TokenName) -> Map CurrencySymbol (Set TokenName)
  collectTokenNames currency currencyBalances = Map.insertWith Set.union currency $ AssocMap.keys currencyBalances

sequenceIdView :: forall p i. SequenceId -> HTML p i
sequenceIdView sequenceId =
  span_ [ text $ formatSequenceId sequenceId ]

formatSequenceId :: SequenceId -> String
formatSequenceId (SequenceId { slotIndex, txIndex }) = "Slot #" <> show slotIndex <> ", Tx #" <> show txIndex

txOutOfView :: forall p. Boolean -> Map PubKey Wallet -> TxOutOf String -> HTML p (Query Unit)
txOutOfView showArrow walletKeys txOutOf@(TxOutOf { txOutAddress, txOutType, txOutValue }) =
  div
    [ classes [ card, entryClass, beneficialOwnerClass beneficialOwner ] ]
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
      [ col3_ [ text $ showCurrency currency ]
      , col_ (tokenView <$> tokens)
      ]

  tokenView :: JsonTuple TokenName Int -> HTML p i
  tokenView (JsonTuple (token /\ amount)) =
    row_
      [ col_ [ text $ showToken token ]
      , div [ classes [ col, amountClass ] ]
          [ text $ formatAmount amount ]
      ]

formatAmount :: Int -> String
formatAmount = toLocaleString <<< toNumber

showCurrency :: CurrencySymbol -> String
showCurrency (CurrencySymbol { unCurrencySymbol: "" }) = "Ada"

showCurrency (CurrencySymbol { unCurrencySymbol: symbol }) = symbol

showToken :: TokenName -> String
showToken (TokenName { unTokenName: "" }) = "Lovelace"

showToken (TokenName { unTokenName: name }) = name
