{-# LANGUAGE DeriveAnyClass       #-}
{-# LANGUAGE DeriveGeneric        #-}
{-# LANGUAGE DerivingStrategies   #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE LambdaCase           #-}
{-# LANGUAGE MonoLocalBinds       #-}
{-# LANGUAGE NamedFieldPuns       #-}
{-# LANGUAGE NoImplicitPrelude    #-}
{-# LANGUAGE OverloadedStrings    #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-simplifiable-class-constraints #-}
{-# OPTIONS_GHC -fno-strictness #-}
{-# OPTIONS_GHC -fno-specialise #-}
{-# OPTIONS_GHC -fno-ignore-interface-pragmas #-}
{-# OPTIONS_GHC -fno-omit-interface-pragmas #-}
-- | Constraints for transactions
module Ledger.Constraints.TxConstraints where

import           Data.Aeson                 (FromJSON, ToJSON)
import           Data.Bifunctor             (Bifunctor (..))
import qualified Data.Map                   as Map
import           Data.Text.Prettyprint.Doc  hiding ((<>))
import           GHC.Generics               (Generic)

import qualified Language.PlutusTx          as PlutusTx
import           Language.PlutusTx.Prelude

import qualified Language.PlutusTx.AssocMap as AssocMap
import           Ledger.Crypto              (PubKeyHash)
import qualified Ledger.Interval            as I
import           Ledger.Scripts             (Datum (..), DatumHash, MonetaryPolicyHash, Redeemer, ValidatorHash)
import           Ledger.Slot                (SlotRange)
import           Ledger.Tx                  (TxOutRef)
import           Ledger.Value               (TokenName, Value, isZero)
import qualified Ledger.Value               as Value

import qualified Prelude                    as Haskell

-- | Constraints on transactions that want to spend script outputs
data TxConstraint =
    MustIncludeDatum Datum
    | MustValidateIn SlotRange
    | MustBeSignedBy PubKeyHash
    | MustSpendValue Value
    | MustSpendPubKeyOutput TxOutRef
    | MustSpendScriptOutput TxOutRef Redeemer
    | MustForgeValue MonetaryPolicyHash TokenName Integer
    | MustPayToPubKey PubKeyHash Value
    | MustPayToOtherScript ValidatorHash Datum Value
    | MustHashDatum DatumHash Datum
    deriving stock (Show, Generic, Haskell.Eq)
    deriving anyclass (ToJSON, FromJSON)

instance Pretty TxConstraint where
    pretty = \case
        MustIncludeDatum dv ->
            hang 2 $ vsep ["must include datum:", pretty dv]
        MustValidateIn range ->
            "must validate in:" <+> viaShow range
        MustBeSignedBy signatory ->
            "must be signed by:" <+> pretty signatory
        MustSpendValue vl ->
            hang 2 $ vsep ["must spend value:", pretty vl]
        MustSpendPubKeyOutput ref ->
            hang 2 $ vsep ["must spend pubkey output:", pretty ref]
        MustSpendScriptOutput ref red ->
            hang 2 $ vsep ["must spend script output:", pretty ref, pretty red]
        MustForgeValue mps tn i ->
            hang 2 $ vsep ["must forge value:", pretty mps, pretty tn <+> pretty i]
        MustPayToPubKey pk v ->
            hang 2 $ vsep ["must pay to pubkey:", pretty pk, pretty v]
        MustPayToOtherScript vlh dv vl ->
            hang 2 $ vsep ["must pay to script:", pretty vlh, pretty dv, pretty vl]
        MustHashDatum dvh dv ->
            hang 2 $ vsep ["must hash datum:", pretty dvh, pretty dv]

data InputConstraint a =
    InputConstraint
        { icRedeemer :: a
        , icTxOutRef :: TxOutRef
        } deriving stock (Show, Generic, Haskell.Functor)

addTxIn :: TxOutRef -> i -> TxConstraints i o -> TxConstraints i o
addTxIn outRef red tc =
    let ic = InputConstraint{icRedeemer = red, icTxOutRef = outRef}
    in tc { txOwnInputs = ic : txOwnInputs tc }

instance (Pretty a) => Pretty (InputConstraint a) where
    pretty InputConstraint{icRedeemer, icTxOutRef} =
        vsep
            [ "Redeemer:" <+> pretty icRedeemer
            , "TxOutRef:" <+> pretty icTxOutRef
            ]

deriving anyclass instance (ToJSON a) => ToJSON (InputConstraint a)
deriving anyclass instance (FromJSON a) => FromJSON (InputConstraint a)
deriving stock instance (Haskell.Eq a) => Haskell.Eq (InputConstraint a)

data OutputConstraint a =
    OutputConstraint
        { ocDatum :: a
        , ocValue :: Value
        } deriving stock (Show, Generic, Haskell.Functor)

instance (Pretty a) => Pretty (OutputConstraint a) where
    pretty OutputConstraint{ocDatum, ocValue} =
        vsep
            [ "Datum:" <+> pretty ocDatum
            , "Value:" <+> pretty ocValue
            ]

deriving anyclass instance (ToJSON a) => ToJSON (OutputConstraint a)
deriving anyclass instance (FromJSON a) => FromJSON (OutputConstraint a)
deriving stock instance (Haskell.Eq a) => Haskell.Eq (OutputConstraint a)

-- | Restrictions placed on the allocation of funds to outputs of transactions.
data TxConstraints i o =
    TxConstraints
        { txConstraints :: [TxConstraint]
        , txOwnInputs   :: [InputConstraint i]
        , txOwnOutputs  :: [OutputConstraint o]
        }
    deriving stock (Show, Generic)

instance Bifunctor TxConstraints where
    bimap f g txc =
        txc
            { txOwnInputs = Haskell.fmap (Haskell.fmap f) (txOwnInputs txc)
            , txOwnOutputs = Haskell.fmap (Haskell.fmap g) (txOwnOutputs txc)
            }

type UntypedConstraints = TxConstraints PlutusTx.Data PlutusTx.Data

instance Semigroup (TxConstraints i o) where
    l <> r =
        TxConstraints
            { txConstraints = txConstraints l <> txConstraints r
            , txOwnInputs = txOwnInputs l <> txOwnInputs r
            , txOwnOutputs = txOwnOutputs l <> txOwnOutputs r
            }

instance Haskell.Semigroup (TxConstraints i o) where
    (<>) = (<>) -- uses PlutusTx.Semigroup instance

instance Monoid (TxConstraints i o) where
    mempty = TxConstraints [] [] []

instance Haskell.Monoid (TxConstraints i o) where
    mappend = (<>)
    mempty  = mempty

deriving anyclass instance (ToJSON i, ToJSON o) => ToJSON (TxConstraints i o)
deriving anyclass instance (FromJSON i, FromJSON o) => FromJSON (TxConstraints i o)
deriving stock instance (Haskell.Eq i, Haskell.Eq o) => Haskell.Eq (TxConstraints i o)

{-# INLINABLE singleton #-}
singleton :: TxConstraint -> TxConstraints i o
singleton a = mempty { txConstraints = [a] }

{-# INLINABLE mustValidateIn #-}
-- | @mustValidateIn r@ requires the transaction's slot range to be contained
--   in @r@.
mustValidateIn :: forall i o. SlotRange -> TxConstraints i o
mustValidateIn = singleton . MustValidateIn

{-# INLINABLE mustBeSignedBy #-}
-- | Require the transaction to be signed by the public key.
mustBeSignedBy :: forall i o. PubKeyHash -> TxConstraints i o
mustBeSignedBy = singleton . MustBeSignedBy

{-# INLINABLE mustIncludeDatum #-}
-- | Require the transaction to include a datum.
mustIncludeDatum :: forall i o. Datum -> TxConstraints i o
mustIncludeDatum = singleton . MustIncludeDatum

{-# INLINABLE mustPayToTheScript #-}
-- | Lock the value with a script
mustPayToTheScript :: forall i o. PlutusTx.IsData o => o -> Value -> TxConstraints i o
mustPayToTheScript dt vl =
    TxConstraints
        { txConstraints = [MustIncludeDatum (Datum $ PlutusTx.toData dt)]
        , txOwnInputs = []
        , txOwnOutputs = [OutputConstraint dt vl]
        }

{-# INLINABLE mustPayToPubKey #-}
-- | Lock the value with a public key
mustPayToPubKey :: forall i o. PubKeyHash -> Value -> TxConstraints i o
mustPayToPubKey pk = singleton . MustPayToPubKey pk

{-# INLINABLE mustPayToOtherScript #-}
-- | Lock the value with a public key
mustPayToOtherScript :: forall i o. ValidatorHash -> Datum -> Value -> TxConstraints i o
mustPayToOtherScript vh dv vl =
    singleton (MustPayToOtherScript vh dv vl)
    <> singleton (MustIncludeDatum dv)

{-# INLINABLE mustForgeValue #-}
-- | Create the given value
mustForgeValue :: forall i o. Value -> TxConstraints i o
mustForgeValue = foldMap valueConstraint . (AssocMap.toList . Value.getValue) where
    valueConstraint (currencySymbol, mp) =
        let hs = Value.currencyMPSHash currencySymbol in
        foldMap (uncurry (mustForgeCurrency hs)) (AssocMap.toList mp)

{-# INLINABLE mustForgeCurrency #-}
-- | Create the given amount of the currency
mustForgeCurrency :: forall i o. MonetaryPolicyHash -> TokenName -> Integer -> TxConstraints i o
mustForgeCurrency mps tn = singleton . MustForgeValue mps tn

{-# INLINABLE mustSpendValue #-}
-- | Requirement to spend the given value
mustSpendValue :: forall i o. Value -> TxConstraints i o
mustSpendValue = singleton . MustSpendValue

{-# INLINABLE mustSpendPubKeyOutput #-}
mustSpendPubKeyOutput :: forall i o. TxOutRef -> TxConstraints i o
mustSpendPubKeyOutput = singleton . MustSpendPubKeyOutput

{-# INLINABLE mustSpendScriptOutput #-}
mustSpendScriptOutput :: forall i o. TxOutRef -> Redeemer -> TxConstraints i o
mustSpendScriptOutput txOutref = singleton . MustSpendScriptOutput txOutref

{-# INLINABLE mustHashDatum #-}
mustHashDatum :: DatumHash -> Datum -> TxConstraints i o
mustHashDatum dvh = singleton . MustHashDatum dvh

{-# INLINABLE isSatisfiable #-}
-- | Are the constraints satisfiable?
isSatisfiable :: forall i o. TxConstraints i o -> Bool
isSatisfiable TxConstraints{txConstraints} =
    let intervals = mapMaybe (\case { MustValidateIn i -> Just i; _ -> Nothing }) txConstraints
        itvl = foldl I.intersection I.always intervals
    in not (I.isEmpty itvl)

{-# INLINABLE pubKeyPayments #-}
pubKeyPayments :: forall i o. TxConstraints i o -> [(PubKeyHash, Value)]
pubKeyPayments TxConstraints{txConstraints} =
    Map.toList
    $ Map.fromListWith (<>)
      (txConstraints >>= \case { MustPayToPubKey pk vl -> [(pk, vl)]; _ -> [] })

{-# INLINABLE mustSpendValueTotal #-}
mustSpendValueTotal :: forall i o. TxConstraints i o -> Value
mustSpendValueTotal = foldMap f . txConstraints where
    f (MustSpendValue v) = v
    f _                  = mempty

{-# INLINABLE requiredSignatories #-}
requiredSignatories :: forall i o. TxConstraints i o -> [PubKeyHash]
requiredSignatories = foldMap f . txConstraints where
    f (MustBeSignedBy pk) = [pk]
    f _                   = []

{-# INLINABLE requiredMonetaryPolicies #-}
requiredMonetaryPolicies :: forall i o. TxConstraints i o -> [MonetaryPolicyHash]
requiredMonetaryPolicies = foldMap f . txConstraints where
    f (MustForgeValue mps _ _) = [mps]
    f _                        = []

{-# INLINABLE requiredDatums #-}
requiredDatums :: forall i o. TxConstraints i o -> [Datum]
requiredDatums = foldMap f . txConstraints where
    f (MustIncludeDatum dv) = [dv]
    f _                     = []

{-# INLINABLE modifiesUtxoSet #-}
-- | Check whether every transaction that satisfies the constraints has to
--   modify the UTXO set.
modifiesUtxoSet :: forall i o. TxConstraints i o -> Bool
modifiesUtxoSet TxConstraints{txConstraints, txOwnOutputs, txOwnInputs} =
    let requiresInputOutput = \case
            MustSpendValue{} -> True
            MustSpendPubKeyOutput{} -> True
            MustSpendScriptOutput{} -> True
            MustForgeValue{} -> True
            MustPayToPubKey _ vl -> not (isZero vl)
            MustPayToOtherScript _ _ vl -> not (isZero vl)
            _ -> False
    in any requiresInputOutput txConstraints
        || not (null txOwnOutputs)
        || not (null txOwnInputs)
