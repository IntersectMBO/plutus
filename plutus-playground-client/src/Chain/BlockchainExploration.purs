module Chain.BlockchainExploration
       ( blockchainExploration
       ) where

import Bootstrap (nbsp)
import Data.Array (mapWithIndex)
import Data.Array as Array
import Data.Generic (class Generic)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..), fromJust, maybe)
import Data.Set (Set)
import Data.Set as Set
import Data.String as String
import Data.String.Extra (abbreviate)
import Data.Tuple (Tuple(Tuple), fst, snd)
import Data.Tuple.Nested (tuple3, (/\))
import Halogen (HTML)
import Halogen.HTML (ClassName(ClassName), div, div_, h2, h2_, h3, strong_, table, tbody_, td, text, th, thead_, tr_)
import Halogen.HTML.Properties (class_, classes, colSpan)
import Ledger.Ada.TH (Ada(..))
import Ledger.Crypto (PubKey(PubKey), Signature(Signature))
import Ledger.Extra (LedgerMap(..))
import Ledger.Scripts (DataScript(..), RedeemerScript(..))
import Ledger.Tx (Tx(Tx), TxInOf(TxInOf), TxInType(..), TxOutOf(TxOutOf), TxOutRefOf(TxOutRefOf), TxOutType(..))
import Ledger.TxId (TxIdOf(TxIdOf))
import Ledger.Value.TH (CurrencySymbol(..), Value(..))
import Partial.Unsafe (unsafePartial)
import Prelude (class Eq, class Ord, class Show, map, show, (#), ($), (+), (<#>), (<$>), (<*>), (<<<), (<>), (==))
import Types (Blockchain)

type SlotId = Int
type StepId = Int
type Hash = String

data Column
  = ForgeIx
  | FeeIx
  | OwnerIx String Hash
  | ScriptIx String Hash

derive instance genericColumn :: Generic Column
derive instance eqColumn :: Eq Column
derive instance ordColumn :: Ord Column

instance showColumn :: Show Column where
  show FeeIx = "Fee"
  show ForgeIx = "Forge"
  show (OwnerIx owner hash) = show owner <> "-" <> String.take 7 hash
  show (ScriptIx owner hash) = owner <> "-" <> String.take 7 hash

type Row = Tuple SlotId StepId

type BalanceMap =
  Map (Tuple Column Row) Balance

blockchainExploration :: forall p i. Blockchain -> HTML p i
blockchainExploration blockchain =
  div_ [ h2_ [ text "Blockchain" ]
       , blockchainTable
       ]
  where
    blockchainTable =
      table [ classes [ ClassName "table"
                      , ClassName "balance-map"
                      ]
            ]
      [ thead_
        [ tr_ $ columns
                # Set.map (tuple3 <$> columnHeading <*> matchCount <*> columnClass)
                # Set.toUnfoldable
                <#> \(heading /\ count /\ cssClass /\ _) -> th [ colSpan count ]
                                                            [ h2 [ class_ cssClass ]
                                                              [ text heading ]
                                                            ]
        , tr_ $ columns
                # Set.toUnfoldable
                <#> \column -> th []
                               [ h3 [ class_ $ columnClass column ]
                                 [ text $ columnSubheading column ]
                               ]
        ]
      , tbody_ $ Array.reverse (Set.toUnfoldable rows) <#>
        (\row -> tr_ $ columns
                       # Set.toUnfoldable
                       # Array.sortWith columnHeading
                       <#> \column ->
                             let mBalance = Map.lookup (Tuple column row) balanceMap
                             in td
                                [ class_ $ columnClass column ]
                                [ maybe nbsp balanceView mBalance ]
        )
      ]

    balanceMap = toBalanceMap blockchain

    columnHeading FeeIx = "Fee"
    columnHeading ForgeIx = "Forge"
    columnHeading (OwnerIx owner hash) = "Wallet #" <> abbreviate (show owner)
    columnHeading (ScriptIx owner hash) = "Script #" <> abbreviate owner

    columnSubheading FeeIx = ""
    columnSubheading ForgeIx = ""
    columnSubheading (OwnerIx owner hash) = "Tx/" <> abbreviate hash
    columnSubheading (ScriptIx owner hash) = "Tx/" <> abbreviate hash

    matchCount :: Column -> Int
    matchCount owner = Array.length $ Array.filter (isOwner owner) $ Set.toUnfoldable columns

    isOwner :: Column -> Column -> Boolean
    isOwner FeeIx FeeIx = true
    isOwner ForgeIx ForgeIx = true
    isOwner (OwnerIx owner1 _) (OwnerIx owner2 _) = owner1 == owner2
    isOwner (ScriptIx owner1 _) (ScriptIx owner2 _) = owner1 == owner2
    isOwner _ _ = false

    columnClass :: Column -> ClassName
    columnClass ForgeIx = ClassName "forge"
    columnClass FeeIx = ClassName "fee"
    columnClass (OwnerIx _ _) = ClassName "owner"
    columnClass (ScriptIx _ _) = ClassName "script"

    columns :: Set Column
    columns = Set.fromFoldable $ map fst $ Map.keys $ balanceMap

    rows :: Set Row
    rows = Set.fromFoldable $ map snd $ Map.keys $ balanceMap

data Balance
  = AdaBalance Ada
  | CurrencyBalance (Array (Tuple CurrencySymbol Int))
  | Remainder

merge :: Balance -> Balance -> Maybe Balance
merge Remainder Remainder = Just Remainder
merge (CurrencyBalance x) (CurrencyBalance y) = Just $ CurrencyBalance (x <> y)
merge (AdaBalance (Ada {getAda: x})) (AdaBalance (Ada {getAda: y})) = Just $ AdaBalance (Ada { getAda: x + y })
merge _ _ = Nothing

toBalanceMap :: Blockchain -> Map (Tuple Column (Tuple Int Int)) Balance
toBalanceMap =
  Map.fromFoldableWith (\a b -> unsafePartial $ fromJust $ merge a b)
  <<< Array.concat
  <<< Array.concat
  <<< mapWithIndex (\slotId -> mapWithIndex
                               (\stepId tx ->
                                 let row = Tuple slotId stepId
                                 in [ forgeTransactions row tx
                                    , feeTransactions row tx
                                    ]
                                    <> inputTransactions row tx
                                    <> outputTransactions row tx
                               ))
  where
    forgeTransactions :: Row -> Tuple (TxIdOf String) Tx -> Tuple (Tuple Column Row) Balance
    forgeTransactions row (Tuple _ (Tx {txForge: (Value { getValue: LedgerMap balances })})) =
      Tuple (Tuple ForgeIx row) (CurrencyBalance balances)

    feeTransactions :: Row -> Tuple (TxIdOf String) Tx -> Tuple (Tuple Column Row) Balance
    feeTransactions row (Tuple _ (Tx {txFee: ada})) =
      Tuple (Tuple FeeIx row) (AdaBalance ada)

    inputTransactions :: Row -> Tuple (TxIdOf String) Tx -> Array (Tuple (Tuple Column Row) Balance)
    inputTransactions row (Tuple _ (Tx {txInputs})) =
      fromTxIn <$> txInputs
      where
        fromTxIn :: TxInOf String -> Tuple (Tuple Column Row) Balance
        fromTxIn (TxInOf { txInRef: (TxOutRefOf {txOutRefId: (TxIdOf {getTxId: hash})})
                         , txInType: (ConsumePublicKeyAddress (PubKey { getPubKey: owner }))
                         })
          = Tuple (Tuple (OwnerIx owner hash) row) Remainder
        fromTxIn (TxInOf { txInRef: (TxOutRefOf {txOutRefId: (TxIdOf {getTxId: hash})})
                         , txInType: (ConsumeScriptAddress _ (RedeemerScript { getRedeemer: owner }))
                         })
          = Tuple (Tuple (ScriptIx owner hash) row) Remainder

    outputTransactions :: Row -> Tuple (TxIdOf String) Tx -> Array (Tuple (Tuple Column Row) Balance)
    outputTransactions row (Tuple (TxIdOf {getTxId: hash}) (Tx {txOutputs})) =
      fromTxOut <$> txOutputs
      where
        fromTxOut :: TxOutOf String -> Tuple (Tuple Column Row) Balance
        fromTxOut (TxOutOf { txOutType: (PayToPubKey (PubKey { getPubKey: owner }))
                           , txOutValue: (Value ({ getValue: LedgerMap currencyBalances }))
                           })
          = Tuple (Tuple (OwnerIx owner hash) row) (CurrencyBalance currencyBalances)
        fromTxOut (TxOutOf { txOutType: (PayToScript (DataScript { getDataScript: owner }))
                           , txOutValue: (Value ({ getValue: LedgerMap currencyBalances }))
                           })
          = Tuple (Tuple (ScriptIx owner hash) row) (CurrencyBalance currencyBalances)

balanceClassname :: ClassName
balanceClassname = ClassName "balance"
balanceView :: forall p i. Balance -> HTML p i
balanceView (AdaBalance (Ada {getAda: ada})) =
  div [ classes [ balanceClassname
                , if ada == 0
                  then ClassName "balance-no-ada"
                  else ClassName "balance-ada"
                ]
      ]
      [ amountView "ADA" ada ]

balanceView (CurrencyBalance currencyBalances) =
  div [ classes [ balanceClassname
                , if Array.null currencyBalances
                  then ClassName "balance-no-currencies"
                  else ClassName "balance-currencies"
                ]
      ]
      (map valueView currencyBalances)

balanceView Remainder =
  div [ classes [ balanceClassname
                , ClassName "balance-remainder"
                ]
      ]
      []

valueView :: forall p i. Tuple CurrencySymbol Int -> HTML p i
valueView (Tuple (CurrencySymbol { unCurrencySymbol: sym }) balance) =
  amountView ("λ" <> sym) balance

amountView :: forall p i. String -> Int -> HTML p i
amountView name balance =
  div_ [ strong_ [ text name ]
       , text $ ": " <> show balance
       ]
