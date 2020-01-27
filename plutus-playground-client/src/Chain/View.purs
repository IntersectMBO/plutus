module Chain.View (chainView) where

import Prelude hiding (div)
import Bootstrap (active, card, cardBody_, cardFooter_, cardHeader, cardHeader_, col, col2, col3_, col6_, col_, empty, nbsp, row, row_, tableBordered, tableSmall, textTruncate)
import Bootstrap as Bootstrap
import Bootstrap.Extra (clickable)
import Chain.Types (AnnotatedBlockchain, ChainFocus(..), State, _FocusTx, _balances, _chainFocus, _dereferencedInputs, _findTx, _sequenceId, _tx, _txFee, _txForge, _txId, _txIdOf, _txInRef, _txOutRefId, _txOutputs, _txSignatures, _txValidRange, findConsumptionPoint, toBeneficialOwner)
import Data.Array ((:))
import Data.Array as Array
import Data.Array.Extra (intersperse)
import Data.Foldable (foldMap, foldr)
import Data.FoldableWithIndex (foldMapWithIndex, foldrWithIndex)
import Data.FunctorWithIndex (mapWithIndex)
import Data.Int (toNumber)
import Data.Json.JsonTuple (JsonTuple(..), _JsonTuple)
import Data.Lens (Traversal', _1, _Just, filtered, has, preview, toListOf, traversed, view)
import Data.Lens.Index (ix)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..), fromMaybe)
import Data.Newtype (unwrap)
import Data.Number.Extra (toLocaleString)
import Data.Set (Set)
import Data.Set as Set
import Data.Tuple.Nested ((/\))
import Halogen.HTML (ClassName(..), HTML, IProp, br_, div, div_, h2_, hr_, small_, span, span_, strong_, table, tbody_, td, text, th, th_, thead_, tr, tr_)
import Halogen.HTML.Events (onClick)
import Halogen.HTML.Properties (class_, classes, colSpan, rowSpan)
import Language.PlutusTx.AssocMap as AssocMap
import Ledger.Crypto (PubKey(..), PubKeyHash(..))
import Ledger.Extra (humaniseInterval)
import Ledger.Tx (TxOut(..))
import Ledger.TxId (TxId)
import Ledger.Value (CurrencySymbol(..), TokenName(..), Value(..))
import Types (HAction(..), _value)
import Wallet.Emulator.Wallet (Wallet(..))
import Wallet.Rollup.Types (AnnotatedTx(..), BeneficialOwner(..), DereferencedInput(..), SequenceId(..))
import Web.UIEvent.MouseEvent (MouseEvent)

chainView :: forall p. State -> Map PubKeyHash Wallet -> AnnotatedBlockchain -> HTML p HAction
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
        (chainSlotView state <$> Array.reverse (unwrap annotatedBlockchain))
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

chainSlotView :: forall p. State -> Array AnnotatedTx -> HTML p HAction
chainSlotView state [] = empty

chainSlotView state chainSlot =
  div [ classes [ col2, slotClass ] ]
    (blockView state <$> chainSlot)

blockView :: forall p. State -> AnnotatedTx -> HTML p HAction
blockView state annotatedTx@(AnnotatedTx { txId, sequenceId }) =
  div
    [ classes ([ card, clickable, ClassName "transaction" ] <> if isActive then [ active ] else [])
    , onClickFocusTx txId
    ]
    [ entryCardHeader sequenceId ]
  where
  isActive = has (_chainFocus <<< _Just <<< _FocusTx <<< filtered (eq txId)) state

detailView :: forall p. State -> Map PubKeyHash Wallet -> AnnotatedBlockchain -> HTML p HAction
detailView state@{ chainFocus: Just (FocusTx focussedTxId) } walletKeys annotatedBlockchain = case preview (_findTx focussedTxId) annotatedBlockchain of
  Just annotatedTx -> transactionDetailView walletKeys annotatedBlockchain annotatedTx
  Nothing -> empty

detailView state@{ chainFocus: Nothing } _ _ = empty

transactionDetailView :: forall p. Map PubKeyHash Wallet -> AnnotatedBlockchain -> AnnotatedTx -> HTML p HAction
transactionDetailView walletKeys annotatedBlockchain annotatedTx =
  div_
    [ row_
        [ col3_
            [ h2_ [ text "Inputs" ]
            , forgeView (view (_tx <<< _txForge) annotatedTx)
            , div_ (dereferencedInputView walletKeys annotatedBlockchain <$> (view _dereferencedInputs annotatedTx))
            ]
        , col6_
            [ h2_ [ text "Transaction" ]
            , div [ classes [ card, active ] ]
                [ entryCardHeader (view _sequenceId annotatedTx)
                , cardBody_
                    [ div
                        [ class_ textTruncate ]
                        [ strong_ [ text "Tx: " ]
                        , nbsp
                        , text (view (_txIdOf <<< _txId) annotatedTx)
                        ]
                    , div_
                        [ strong_ [ text "Validity:" ]
                        , nbsp
                        , text $ humaniseInterval (view (_tx <<< _txValidRange) annotatedTx)
                        ]
                    , div_
                        [ strong_ [ text "Signatures:" ]
                        , nbsp
                        , case Array.fromFoldable (toListOf (_tx <<< _txSignatures <<< AssocMap._Map <<< traversed <<< _JsonTuple <<< _1) annotatedTx) of
                            [] -> text "None"
                            pubKeys -> div_ (showPubKey <$> pubKeys)
                        ]
                    ]
                ]
            ]
        , col3_
            [ h2_ [ text "Outputs" ]
            , feeView (view (_tx <<< _txFee) annotatedTx)
            , div_ (mapWithIndex (outputView walletKeys (view _txIdOf annotatedTx) annotatedBlockchain) (view (_tx <<< _txOutputs) annotatedTx))
            ]
        ]
    , balancesTable
        (view _sequenceId annotatedTx)
        walletKeys
        (AssocMap.toDataMap (view _balances annotatedTx))
    ]

entryCardHeader :: forall i p. SequenceId -> HTML p i
entryCardHeader sequenceId =
  cardHeader_
    [ triangleRight
    , sequenceIdView sequenceId
    ]

entryClass :: ClassName
entryClass = ClassName "entry"

triangleRight :: forall p i. HTML p i
triangleRight = div [ class_ $ ClassName "triangle-right" ] []

feeView :: forall p i. Value -> HTML p i
feeView (Value { getValue: (AssocMap.Map []) }) = empty

feeView txFee =
  div [ classes [ card, entryClass, feeClass ] ]
    [ cardHeader_ [ text "Fee" ]
    , cardBody_
        [ valueView txFee
        ]
    ]

forgeView :: forall p i. Value -> HTML p i
forgeView (Value { getValue: (AssocMap.Map []) }) = empty

forgeView txForge =
  div [ classes [ card, entryClass, forgeClass ] ]
    [ cardHeader_ [ triangleRight, text "Forge" ]
    , cardBody_
        [ valueView txForge
        ]
    ]

balancesTable :: forall p i. SequenceId -> Map PubKeyHash Wallet -> Map BeneficialOwner Value -> HTML p i
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
            [ Bootstrap.table
            , tableBordered
            , tableSmall
            , ClassName "balances-table"
            ]
        ]
        [ thead_
            [ tr_
                ( th [ rowSpan 2 ] [ text "Beneficial Owner" ]
                    : foldMapWithIndex
                        ( \currency s ->
                            [ th [ colSpan (Set.size s) ]
                                [ text $ showCurrency currency ]
                            ]
                        )
                        headings
                )
            , tr_
                (foldMap (foldMap tokenHeadingView) headings)
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
                                            _thisBalance :: Traversal' (Map BeneficialOwner Value) Int
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
sequenceIdView sequenceId = span_ [ text $ formatSequenceId sequenceId ]

formatSequenceId :: SequenceId -> String
formatSequenceId (SequenceId { slotIndex, txIndex }) = "Slot #" <> show slotIndex <> ", Tx #" <> show txIndex

dereferencedInputView :: forall p. Map PubKeyHash Wallet -> AnnotatedBlockchain -> DereferencedInput -> HTML p HAction
dereferencedInputView walletKeys annotatedBlockchain (DereferencedInput { originalInput, refersTo }) =
  txOutOfView true walletKeys refersTo
    $ case originatingTx of
        Just tx ->
          Just
            $ div
                [ class_ clickable
                , onClickFocusTx txId
                ]
                [ text "Created by:", nbsp, sequenceIdView (view _sequenceId tx) ]
        Nothing -> Nothing
  where
  txId :: TxId
  txId = view (_txInRef <<< _txOutRefId) originalInput

  originatingTx :: Maybe AnnotatedTx
  originatingTx = preview (_findTx txId) annotatedBlockchain

outputView :: forall p. Map PubKeyHash Wallet -> TxId -> AnnotatedBlockchain -> Int -> TxOut -> HTML p HAction
outputView walletKeys txId annotatedBlockchain outputIndex txOut =
  txOutOfView false walletKeys txOut
    $ case consumedInTx of
        Just linkedTx ->
          Just
            $ div
                [ class_ clickable, onClickFocusTx (view _txIdOf linkedTx) ]
                [ text "Spent in:", nbsp, sequenceIdView (view _sequenceId linkedTx) ]
        Nothing ->
          Just
            $ div_
                [ text "Unspent" ]
  where
  consumedInTx :: Maybe AnnotatedTx
  consumedInTx = findConsumptionPoint outputIndex txId annotatedBlockchain

txOutOfView :: forall p. Boolean -> Map PubKeyHash Wallet -> TxOut -> Maybe (HTML p HAction) -> HTML p HAction
txOutOfView showArrow walletKeys txOut@(TxOut { txOutAddress, txOutType, txOutValue }) mFooter =
  div
    [ classes [ card, entryClass, beneficialOwnerClass beneficialOwner ] ]
    [ div [ classes [ cardHeader, textTruncate ] ]
        [ if showArrow then triangleRight else empty
        , beneficialOwnerView walletKeys beneficialOwner
        ]
    , cardBody_
        [ valueView txOutValue ]
    , case mFooter of
        Nothing -> empty
        Just footer -> cardFooter_ [ footer ]
    ]
  where
  beneficialOwner = toBeneficialOwner txOut

beneficialOwnerClass :: BeneficialOwner -> ClassName
beneficialOwnerClass (OwnedByPubKey _) = ClassName "wallet"

beneficialOwnerClass (OwnedByScript _) = ClassName "script"

beneficialOwnerView :: forall p i. Map PubKeyHash Wallet -> BeneficialOwner -> HTML p i
beneficialOwnerView walletKeys (OwnedByPubKey pubKey) = case Map.lookup pubKey walletKeys of
  Nothing -> showPubKeyHash pubKey
  Just (Wallet { getWallet: n }) ->
    span_
      [ showPubKeyHash pubKey
      , br_
      , small_
          [ text "Wallet"
          , nbsp
          , text $ show n
          ]
      ]

beneficialOwnerView _ (OwnedByScript a) =
  span_
    [ text "Script"
    , nbsp
    , text $ show a
    ]

showPubKey :: forall p i. PubKey -> HTML p i
showPubKey (PubKey { getPubKey: p }) =
  span
    [ class_ textTruncate ]
    [ text "PubKey"
    , nbsp
    , text p
    ]

showPubKeyHash :: forall p i. PubKeyHash -> HTML p i
showPubKeyHash (PubKeyHash { getPubKeyHash: p }) =
  span
    [ class_ textTruncate ]
    [ text "PubKeyHash"
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

onClickFocusTx :: forall p. TxId -> IProp ( onClick :: MouseEvent | p ) HAction
onClickFocusTx txId =
  onClick
    $ const
    $ Just
    $ SetChainFocus
    $ Just
    $ FocusTx
    $ txId
