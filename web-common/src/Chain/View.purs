module Chain.View
  ( chainView
  , txOutOfView
  ) where

import Chain.Types
import Animation (animationClass)
import Bootstrap (active, card, cardBody_, cardFooter_, cardHeader, cardHeader_, col, col3_, col6_, colLg2, colMd3, colSm6, colXs12, col_, empty, nbsp, row, row_, tableBordered, tableSmall, textTruncate)
import Bootstrap as Bootstrap
import Bootstrap.Extra (clickable)
import Clipboard (showShortCopyLong)
import Data.Array ((:))
import Data.Array as Array
import Data.Foldable (foldMap, foldr)
import Data.Foldable.Extra (interleave)
import Data.FoldableWithIndex (foldMapWithIndex, foldrWithIndex)
import Data.FunctorWithIndex (mapWithIndex)
import Data.Int (toNumber)
import Data.Json.JsonMap (_JsonMap)
import Data.Json.JsonTuple (JsonTuple(..))
import Data.Lens (Traversal', _Just, filtered, has, preview, to, view)
import Data.Lens.Index (ix)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..), fromMaybe)
import Data.Newtype (unwrap)
import Data.Number.Extra (toLocaleString)
import Data.Set (Set)
import Data.Set as Set
import Data.String.Extra (abbreviate)
import Data.Tuple.Nested ((/\))
import Halogen.HTML (ClassName(..), HTML, IProp, br_, div, div_, h2_, hr_, li_, small_, span_, strong_, table, tbody_, td, text, th, th_, thead_, tr, tr_, ul_)
import Halogen.HTML.Events (onClick)
import Halogen.HTML.Properties (class_, classes, colSpan, rowSpan)
import Language.PlutusTx.AssocMap as AssocMap
import Ledger.Crypto (PubKey(..), PubKeyHash(..))
import Ledger.Extra (humaniseInterval)
import Ledger.Tx (TxOut(..))
import Ledger.TxId (TxId(..))
import Ledger.Value (CurrencySymbol(..), TokenName(..), Value(..))
import Prelude (Ordering(..), const, eq, pure, show, ($), (<$>), (<<<), (<>))
import Wallet.Emulator.Wallet (Wallet(..))
import Wallet.Rollup.Types (AnnotatedTx(..), BeneficialOwner(..), DereferencedInput(..), SequenceId(..))
import Web.UIEvent.MouseEvent (MouseEvent)

chainView :: forall p. State -> Map PubKeyHash Wallet -> AnnotatedBlockchain -> HTML p Action
chainView state walletKeys annotatedBlockchain =
  div
    [ classes
        ( [ ClassName "chain" ]
            <> animationClass _chainFocusAppearing state
            <> case state.chainFocusAge of
                LT -> [ ClassName "chain-focus-newer" ]
                EQ -> []
                GT -> [ ClassName "chain-focus-older" ]
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

notFoundClass :: ClassName
notFoundClass = ClassName "not-found"

forgeClass :: ClassName
forgeClass = ClassName "forge"

amountClass :: ClassName
amountClass = ClassName "amount"

chainSlotView :: forall p. State -> Array AnnotatedTx -> HTML p Action
chainSlotView state [] = empty

chainSlotView state chainSlot =
  div [ classes [ colXs12, colSm6, colMd3, colLg2, slotClass ] ]
    (blockView state <$> chainSlot)

blockView :: forall p. State -> AnnotatedTx -> HTML p Action
blockView state annotatedTx@(AnnotatedTx { txId, sequenceId }) =
  div
    [ classes ([ card, clickable, ClassName "transaction" ] <> if isActive then [ active ] else [])
    , onClickFocusTx txId
    ]
    [ entryCardHeader sequenceId ]
  where
  isActive = has (_chainFocus <<< _Just <<< filtered (eq txId)) state

detailView :: forall p. State -> Map PubKeyHash Wallet -> AnnotatedBlockchain -> HTML p Action
detailView state@{ chainFocus: Just focussedTxId } walletKeys annotatedBlockchain = case preview (_findTx focussedTxId) annotatedBlockchain of
  Just annotatedTx -> transactionDetailView walletKeys annotatedBlockchain annotatedTx
  Nothing -> empty

detailView state@{ chainFocus: Nothing } _ _ = empty

transactionDetailView :: forall p. Map PubKeyHash Wallet -> AnnotatedBlockchain -> AnnotatedTx -> HTML p Action
transactionDetailView walletKeys annotatedBlockchain annotatedTx =
  div_
    [ row_
        [ col3_
            [ h2_ [ text "Inputs" ]
            , div_ (dereferencedInputView walletKeys annotatedBlockchain <$> (view _dereferencedInputs annotatedTx))
            ]
        , col6_
            [ h2_ [ text "Transaction" ]
            , div [ classes [ card, active ] ]
                [ entryCardHeader (view _sequenceId annotatedTx)
                , cardBody_
                    [ div
                        [ class_ textTruncate ]
                        [ txIdView (view _txIdOf annotatedTx) ]
                    , div [ class_ textTruncate ]
                        [ strong_ [ text "Validity:" ]
                        , nbsp
                        , text $ humaniseInterval (view (_tx <<< _txValidRange) annotatedTx)
                        ]
                    , div [ class_ textTruncate ]
                        [ strong_ [ text "Signatures:" ]
                        , case Array.fromFoldable (view (_tx <<< _txSignatures <<< _JsonMap <<< to Map.keys) annotatedTx) of
                            [] -> text "None"
                            pubKeys -> ul_ (li_ <<< pure <<< showPubKey <$> pubKeys)
                        ]
                    ]
                ]
            , forgeView (view (_tx <<< _txForge) annotatedTx)
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
        (view (_balances <<< _JsonMap) annotatedTx)
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
    [ cardHeader_ [ text "Forge" ]
    , cardBody_
        [ valueView txForge
        ]
    ]

balancesTable :: forall p. SequenceId -> Map PubKeyHash Wallet -> Map BeneficialOwner Value -> HTML p Action
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
                            [ th
                                [ colSpan (Set.size s)
                                , class_ textTruncate
                                ]
                                [ let
                                    formatted = showCurrency currency
                                  in
                                    ClipboardAction
                                      <$> showShortCopyLong
                                          formatted
                                          (Just [ text $ abbreviate 15 formatted ])
                                ]
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

  tokenHeadingView :: forall i. TokenName -> Array (HTML p i)
  tokenHeadingView token = [ th_ [ showToken token ] ]

collectBalanceTableHeadings :: Map BeneficialOwner Value -> Map CurrencySymbol (Set TokenName)
collectBalanceTableHeadings balances = foldr collectCurrencies Map.empty $ Map.values balances
  where
  collectCurrencies :: Value -> Map CurrencySymbol (Set TokenName) -> Map CurrencySymbol (Set TokenName)
  collectCurrencies (Value { getValue: entries }) ownersBalance = foldrWithIndex collectTokenNames ownersBalance entries

  collectTokenNames :: CurrencySymbol -> AssocMap.Map TokenName Int -> Map CurrencySymbol (Set TokenName) -> Map CurrencySymbol (Set TokenName)
  collectTokenNames currency currencyBalances = Map.insertWith Set.union currency $ AssocMap.keys currencyBalances

sequenceIdView :: forall p i. SequenceId -> HTML p i
sequenceIdView (SequenceId { slotIndex, txIndex }) =
  span_
    [ span_ [ text "Slot" ]
    , nbsp
    , span_ [ text $ "#" <> show slotIndex ]
    , span_ [ text ", " ]
    , span_ [ text "Tx" ]
    , nbsp
    , span_ [ text $ "#" <> show txIndex ]
    ]

txIdView :: forall p. TxId -> HTML p Action
txIdView (TxId { getTxId: str }) =
  ClipboardAction
    <$> showShortCopyLong
        str
        ( Just
            [ strong_ [ text "Tx: " ]
            , nbsp
            , text str
            ]
        )

dereferencedInputView :: forall p. Map PubKeyHash Wallet -> AnnotatedBlockchain -> DereferencedInput -> HTML p Action
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

dereferencedInputView walletKeys annotatedBlockchain (InputNotFound txKey) =
  div
    [ classes [ card, entryClass, notFoundClass ] ]
    [ div [ classes [ cardHeader, textTruncate ] ]
        [ text "Input Not Found" ]
    , cardBody_
        [ txIdView (view _txKeyTxId txKey)
        , br_
        , text $ "Index: " <> show (view _txKeyTxOutRefIdx txKey)
        ]
    ]

outputView :: forall p. Map PubKeyHash Wallet -> TxId -> AnnotatedBlockchain -> Int -> TxOut -> HTML p Action
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

txOutOfView :: forall p. Boolean -> Map PubKeyHash Wallet -> TxOut -> Maybe (HTML p Action) -> HTML p Action
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

beneficialOwnerView :: forall p. Map PubKeyHash Wallet -> BeneficialOwner -> HTML p Action
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
  ClipboardAction
    <$> showShortCopyLong a
        ( Just
            [ text "Script"
            , nbsp
            , text a
            ]
        )

showPubKey :: forall p. PubKey -> HTML p Action
showPubKey (PubKey { getPubKey: p }) =
  ClipboardAction
    <$> showShortCopyLong p
        ( Just
            [ text "PubKey"
            , nbsp
            , text p
            ]
        )

showPubKeyHash :: forall p. PubKeyHash -> HTML p Action
showPubKeyHash (PubKeyHash { getPubKeyHash: p }) =
  ClipboardAction
    <$> showShortCopyLong p
        ( Just
            [ text "PubKeyHash"
            , nbsp
            , text p
            ]
        )

valueView :: forall p i. Value -> HTML p i
valueView (Value { getValue: (AssocMap.Map []) }) = empty

valueView (Value { getValue: (AssocMap.Map currencies) }) = div_ (interleave hr_ (currencyView <$> currencies))
  where
  currencyView :: JsonTuple CurrencySymbol (AssocMap.Map TokenName Int) -> HTML p i
  currencyView (JsonTuple (currency /\ (AssocMap.Map tokens))) =
    div_
      [ div [ class_ Bootstrap.textTruncate ]
          [ strong_ [ text $ showCurrency currency ] ]
      , div_ (tokenView <$> tokens)
      ]

  tokenView :: JsonTuple TokenName Int -> HTML p i
  tokenView (JsonTuple (token /\ amount)) =
    row_
      [ col_ [ showToken token ]
      , div [ classes [ col, amountClass ] ]
          [ text $ formatAmount amount ]
      ]

formatAmount :: Int -> String
formatAmount = toLocaleString <<< toNumber

showCurrency :: CurrencySymbol -> String
showCurrency (CurrencySymbol { unCurrencySymbol: "" }) = "Ada"

showCurrency (CurrencySymbol { unCurrencySymbol: symbol }) = symbol

showToken :: forall p i. TokenName -> HTML p i
showToken (TokenName { unTokenName: "" }) = text "Lovelace"

showToken (TokenName { unTokenName: name }) = text name

onClickFocusTx :: forall p. TxId -> IProp ( onClick :: MouseEvent | p ) Action
onClickFocusTx txId =
  onClick
    $ const
    $ Just
    $ FocusTx
    $ Just txId
