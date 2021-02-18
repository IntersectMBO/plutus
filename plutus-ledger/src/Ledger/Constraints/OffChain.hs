{-# LANGUAGE DataKinds                 #-}
{-# LANGUAGE DeriveAnyClass            #-}
{-# LANGUAGE DeriveGeneric             #-}
{-# LANGUAGE DerivingStrategies        #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleContexts          #-}
{-# LANGUAGE GADTs                     #-}
{-# LANGUAGE LambdaCase                #-}
{-# LANGUAGE NamedFieldPuns            #-}
{-# LANGUAGE OverloadedStrings         #-}
{-# LANGUAGE PolyKinds                 #-}
{-# LANGUAGE TemplateHaskell           #-}
{-# LANGUAGE TypeApplications          #-}
{-# LANGUAGE TypeFamilies              #-}
{-# LANGUAGE TypeOperators             #-}
{-# LANGUAGE UndecidableInstances      #-}
module Ledger.Constraints.OffChain(
    -- * Lookups
    ScriptLookups(..)
    , scriptInstanceLookups
    , unspentOutputs
    , monetaryPolicy
    , otherScript
    , otherData
    , ownPubKeyHash
    -- * Constraints resolution
    , SomeLookupsAndConstraints(..)
    , UnbalancedTx(..)
    , emptyUnbalancedTx
    , MkTxError(..)
    , mkTx
    , mkSomeTx
    ) where

import           Control.Lens
import           Control.Monad.Except
import           Control.Monad.Reader
import           Control.Monad.State

import           Data.Aeson                       (FromJSON, ToJSON)
import           Data.Foldable                    (traverse_)
import           Data.Map                         (Map)
import qualified Data.Map                         as Map
import           Data.Semigroup                   (First (..))
import           Data.Set                         (Set)
import qualified Data.Set                         as Set
import           Data.Text.Prettyprint.Doc
import           GHC.Generics                     (Generic)

import           Language.PlutusTx                (IsData (..))
import           Language.PlutusTx.Lattice
import qualified Language.PlutusTx.Numeric        as N

import           Ledger.Constraints.TxConstraints hiding (requiredSignatories)
import           Ledger.Orphans                   ()
import           Ledger.Typed.Scripts             (ScriptInstance, ScriptType (..))
import qualified Ledger.Typed.Scripts             as Scripts
import           Ledger.Typed.Tx                  (ConnectionError)
import qualified Ledger.Typed.Tx                  as Typed
import           Plutus.V1.Ledger.Address         (Address (..))
import qualified Plutus.V1.Ledger.Address         as Address
import           Plutus.V1.Ledger.Crypto          (PubKeyHash)
import           Plutus.V1.Ledger.Scripts         (Datum (..), DatumHash, MonetaryPolicy, MonetaryPolicyHash, Validator,
                                                   datumHash, monetaryPolicyHash)
import           Plutus.V1.Ledger.Tx              (Tx, TxOutRef, TxOutTx (..))
import qualified Plutus.V1.Ledger.Tx              as Tx
import qualified Plutus.V1.Ledger.Value           as Value

data ScriptLookups a =
    ScriptLookups
        { slMPS            :: Map MonetaryPolicyHash MonetaryPolicy
        -- ^ Monetary policies that the script interacts with
        , slTxOutputs      :: Map TxOutRef TxOutTx
        -- ^ Unspent outputs that the script may want to spend
        , slOtherScripts   :: Map Address Validator
        -- ^ Validators of scripts other than "our script"
        , slOtherData      :: Map DatumHash Datum
        -- ^ Datums that we might need
        , slScriptInstance :: Maybe (ScriptInstance a)
        -- ^ The script instance with the typed validator hash & actual compiled program
        , slOwnPubkey      :: Maybe PubKeyHash
        -- ^ The contract's public key address, used for depositing tokens etc.
        } deriving stock (Show, Generic)
          deriving anyclass (ToJSON, FromJSON)

instance Semigroup (ScriptLookups a) where
    l <> r =
        ScriptLookups
            { slMPS = slMPS l <> slMPS r
            , slTxOutputs = slTxOutputs l <> slTxOutputs r
            , slOtherScripts = slOtherScripts l <> slOtherScripts r
            , slOtherData = slOtherData l <> slOtherData r
            -- 'First' to match the semigroup instance of Map (left-biased)
            , slScriptInstance = fmap getFirst $ (First <$> slScriptInstance l) <> (First <$> slScriptInstance r)
            , slOwnPubkey = fmap getFirst $ (First <$> slOwnPubkey l) <> (First <$> slOwnPubkey r)

            }

instance Monoid (ScriptLookups a) where
    mappend = (<>)
    mempty  = ScriptLookups mempty mempty mempty mempty Nothing Nothing

-- | A script lookups value with a script instance. For convenience this also
--   includes the monetary policy script that forwards all checks to the
--   instance's validator.
scriptInstanceLookups :: ScriptInstance a -> ScriptLookups a
scriptInstanceLookups inst =
    ScriptLookups
        { slMPS = Map.singleton (Scripts.monetaryPolicyHash inst) (Scripts.monetaryPolicy inst)
        , slTxOutputs = Map.empty
        , slOtherScripts = Map.empty
        , slOtherData = Map.empty
        , slScriptInstance = Just inst
        , slOwnPubkey = Nothing
        }

-- | A script lookups value that uses the map of unspent outputs to resolve
--   input constraints.
unspentOutputs :: Map TxOutRef TxOutTx -> ScriptLookups a
unspentOutputs mp = mempty { slTxOutputs = mp }

-- | A script lookups value with a monetary policy script
monetaryPolicy :: MonetaryPolicy -> ScriptLookups a
monetaryPolicy pl =
    let hsh = monetaryPolicyHash pl in
    mempty { slMPS = Map.singleton hsh pl }

-- | A script lookups value with a validator script
otherScript :: Validator -> ScriptLookups a
otherScript vl =
    let addr = Address.scriptAddress vl in
    mempty { slOtherScripts = Map.singleton addr vl }

-- | A script lookups value with a datum
otherData :: Datum -> ScriptLookups a
otherData dt =
    let dh = datumHash dt in
    mempty { slOtherData = Map.singleton dh dt }

ownPubKeyHash :: PubKeyHash -> ScriptLookups a
ownPubKeyHash ph = mempty { slOwnPubkey = Just ph}

-- | An unbalanced transaction. It needs to be balanced and signed before it
--   can be submitted to the ledeger. See note [Submitting transactions from
--   Plutus contracts] in 'Language.Plutus.Contract.Wallet'.
data UnbalancedTx =
    UnbalancedTx
        { unBalancedTxTx                  :: Tx
        , unBalancedTxRequiredSignatories :: Set PubKeyHash
        }
    deriving stock (Eq, Generic, Show)
    deriving anyclass (FromJSON, ToJSON)

makeLensesFor [("unBalancedTxTx", "tx"), ("unBalancedTxRequiredSignatories", "requiredSignatories")] ''UnbalancedTx

emptyUnbalancedTx :: UnbalancedTx
emptyUnbalancedTx = UnbalancedTx mempty mempty

instance Pretty UnbalancedTx where
    pretty UnbalancedTx{unBalancedTxTx, unBalancedTxRequiredSignatories} =
        vsep
        [ hang 2 $ vsep ["Tx:", pretty unBalancedTxTx]
        , hang 2 $ vsep $ "Requires signatures:" : (pretty <$> Set.toList unBalancedTxRequiredSignatories)
        ]

data ConstraintProcessingState =
    ConstraintProcessingState
        { cpsUnbalancedTx      :: UnbalancedTx
        -- ^ The unbalanced transaction that we're building
        , cpsValueSpentBalance :: Value.Value
        -- ^ Balance of required vs actual value spent by the transaction. If positive, an output needs to be added.
        }

initialState :: ConstraintProcessingState
initialState = ConstraintProcessingState{ cpsUnbalancedTx = emptyUnbalancedTx, cpsValueSpentBalance = mempty }

makeLensesFor [("cpsUnbalancedTx", "unbalancedTx"), ("cpsValueSpentBalance", "valueSpentBalance")] ''ConstraintProcessingState

-- | Some typed 'TxConstraints' and the 'ScriptLookups' needed to turn them
--   into an 'UnbalancedTx'.
data SomeLookupsAndConstraints where
    SomeLookupsAndConstraints :: forall a. (IsData (DatumType a), IsData (RedeemerType a)) => ScriptLookups a -> TxConstraints (RedeemerType a) (DatumType a) -> SomeLookupsAndConstraints

-- | Given a list of 'SomeLookupsAndConstraints' describing the constraints
--   for several scripts, build a single transaction that runs all the scripts.
mkSomeTx
    :: [SomeLookupsAndConstraints]
    -> Either MkTxError UnbalancedTx
mkSomeTx xs =
    let process = \case
            SomeLookupsAndConstraints lookups constraints -> processLookupsAndConstraints lookups constraints
    in fmap cpsUnbalancedTx
        $ runExcept
        $ execStateT (traverse process xs) initialState

-- | Resolve some 'TxConstraints' by modifying the 'UnbalancedTx' in the
--   'ConstraintProcessingState'
processLookupsAndConstraints
    :: ( IsData (DatumType a)
       , IsData (RedeemerType a)
       , MonadState ConstraintProcessingState m
       , MonadError MkTxError m
       )
    => ScriptLookups a
    -> TxConstraints (RedeemerType a) (DatumType a)
    -> m ()
processLookupsAndConstraints lookups TxConstraints{txConstraints, txOwnInputs, txOwnOutputs} =
        flip runReaderT lookups $ do
            traverse_ processConstraint txConstraints
            traverse_ addOwnInput txOwnInputs
            traverse_ addOwnOutput txOwnOutputs
            addMissingValueSpent

-- | Turn a 'TxConstraints' value into an unbalanced transaction that satisfies
--   the constraints. To use this in a contract, see
--   'Language.Plutus.Contract.Effects.WriteTx.submitTxConstraints'
--   and related functions.
mkTx
    :: ( IsData (DatumType a)
       , IsData (RedeemerType a))
    => ScriptLookups a
    -> TxConstraints (RedeemerType a) (DatumType a)
    -> Either MkTxError UnbalancedTx
mkTx lookups txc = mkSomeTx [SomeLookupsAndConstraints lookups txc]

addMissingValueSpent
    :: ( MonadReader (ScriptLookups a) m
       , MonadState ConstraintProcessingState m
       , MonadError MkTxError m
       )
    => m ()
addMissingValueSpent = do
    ConstraintProcessingState{cpsValueSpentBalance} <- get

    -- 'missing' is the value that the transaction is supposed to spend, but
    -- that's not matched by an input or output.
    let (_, missing) = Value.split cpsValueSpentBalance

    if Value.isZero missing
        then pure ()
        else do
            -- add 'missing' to the transaction's outputs. This ensures that the
            -- wallet will add a corresponding input when balancing the
            -- transaction.
            pk <- asks slOwnPubkey >>= maybe (throwError OwnPubKeyMissing) pure
            unbalancedTx . tx . Tx.outputs %= (Tx.TxOut (PubKeyAddress pk) missing Tx.PayToPubKey :)

-- | Add a typed input, checking the type of the output it spends.
addOwnInput
    :: ( MonadReader (ScriptLookups a) m
        , MonadError MkTxError m
        , MonadState ConstraintProcessingState m
        , IsData (DatumType a)
        , IsData (RedeemerType a)
        )
    => InputConstraint (RedeemerType a)
    -> m ()
addOwnInput InputConstraint{icRedeemer, icTxOutRef} = do
    ScriptLookups{slTxOutputs, slScriptInstance} <- ask
    inst <- maybe (throwError ScriptInstanceMissing) pure slScriptInstance
    typedOutRef <-
        either (throwError . TypeCheckFailed) pure
        $ runExcept @ConnectionError
        $ Typed.typeScriptTxOutRef (`Map.lookup` slTxOutputs) inst icTxOutRef
    let txIn = Typed.makeTypedScriptTxIn inst icRedeemer typedOutRef
    unbalancedTx . tx . Tx.inputs %= Set.insert (Typed.tyTxInTxIn txIn)

addOwnOutput
    :: ( MonadReader (ScriptLookups a) m
        , MonadState ConstraintProcessingState m
        , IsData (DatumType a)
        , MonadError MkTxError m
        )
    => OutputConstraint (DatumType a)
    -> m ()
addOwnOutput OutputConstraint{ocDatum, ocValue} = do
    ScriptLookups{slScriptInstance} <- ask
    inst <- maybe (throwError ScriptInstanceMissing) pure slScriptInstance
    let txOut = Typed.makeTypedScriptTxOut inst ocDatum ocValue
        dsV   = Datum (toData ocDatum)
    unbalancedTx . tx . Tx.outputs %= (Typed.tyTxOutTxOut txOut :)
    unbalancedTx . tx . Tx.datumWitnesses . at (datumHash dsV) .= Just dsV

data MkTxError =
    TypeCheckFailed ConnectionError
    | TxOutRefNotFound TxOutRef
    | TxOutRefWrongType TxOutRef
    | DatumNotFound DatumHash
    | MonetaryPolicyNotFound MonetaryPolicyHash
    | ValidatorHashNotFound Address
    | OwnPubKeyMissing
    | ScriptInstanceMissing
    | DatumWrongHash DatumHash Datum
    deriving stock (Eq, Show, Generic)
    deriving anyclass (ToJSON, FromJSON)

instance Pretty MkTxError where
    pretty = \case
        TypeCheckFailed e        -> "Type check failed:" <+> pretty e
        TxOutRefNotFound t       -> "Tx out reference not found:" <+> pretty t
        TxOutRefWrongType t      -> "Tx out reference wrong type:" <+> pretty t
        DatumNotFound h          -> "No datum with hash" <+> pretty h <+> "was found"
        MonetaryPolicyNotFound h -> "No monetary policy with hash" <+> pretty h <+> "was found"
        ValidatorHashNotFound h  ->  "No validator with hash" <+> pretty h <+> "was found"
        OwnPubKeyMissing         -> "Own public key is missing"
        ScriptInstanceMissing    -> "Script instance is missing"
        DatumWrongHash h d       -> "Wrong hash for datum" <+> pretty d <> colon <+> pretty h

lookupTxOutRef
    :: ( MonadReader (ScriptLookups a) m
       , MonadError MkTxError m )
    => TxOutRef
    -> m TxOutTx
lookupTxOutRef outRef =
    let err = throwError (TxOutRefNotFound outRef) in
    asks slTxOutputs >>= maybe err pure . view (at outRef)

lookupDatum
    :: ( MonadReader (ScriptLookups a) m
       , MonadError MkTxError m )
    => DatumHash
    -> m Datum
lookupDatum dvh =
    let err = throwError (DatumNotFound dvh) in
    asks slOtherData >>= maybe err pure . view (at dvh)

lookupMonetaryPolicy
    :: ( MonadReader (ScriptLookups a) m
       , MonadError MkTxError m )
    => MonetaryPolicyHash
    -> m MonetaryPolicy
lookupMonetaryPolicy mph =
    let err = throwError (MonetaryPolicyNotFound mph) in
    asks slMPS >>= maybe err pure . view (at mph)

lookupValidator
    :: ( MonadReader (ScriptLookups a) m
       , MonadError MkTxError m )
    => Address
    -> m Validator
lookupValidator addr =
    let err = throwError (ValidatorHashNotFound addr) in
    asks slOtherScripts >>= maybe err pure . view (at addr)

-- | Modify the 'UnbalancedTx' so that it satisfies the constraints, if
--   possible. Fails if a hash is missing from the lookups, or if an output
--   of the wrong type is spent.
processConstraint
  :: ( MonadReader (ScriptLookups a) m
     , MonadError MkTxError m
     , MonadState ConstraintProcessingState m )
  => TxConstraint
  -> m ()
processConstraint = \case
    MustIncludeDatum dv ->
        let theHash = datumHash dv in
        unbalancedTx . tx . Tx.datumWitnesses %= set (at theHash) (Just dv)
    MustValidateIn slotRange ->
        unbalancedTx . tx . Tx.validRange %= (slotRange /\)
    MustBeSignedBy pk ->
        unbalancedTx . requiredSignatories %= Set.insert pk
    MustSpendValue vl -> valueSpentBalance <>= vl
    MustSpendPubKeyOutput txo -> do
        TxOutTx{txOutTxOut} <- lookupTxOutRef txo
        case Tx.txOutAddress txOutTxOut of
            PubKeyAddress pk -> do
                unbalancedTx . tx . Tx.inputs %= Set.insert (Tx.pubKeyTxIn txo)
                valueSpentBalance <>= N.negate (Tx.txOutValue txOutTxOut)
                unbalancedTx . requiredSignatories %= Set.insert pk
            _                 -> throwError (TxOutRefWrongType txo)
    MustSpendScriptOutput txo red -> do
        txOutTx <- lookupTxOutRef txo
        case Tx.txOutType (txOutTxOut txOutTx) of
            Tx.PayToScript dvh -> do
                let addr = view Tx.outAddress (Tx.txOutTxOut txOutTx)
                validator <- lookupValidator addr

                -- first check the 'txOutTx' for the datum, then
                -- look for it in the 'slOtherData' map.
                dataValue <- maybe (lookupDatum dvh) pure (Tx.txOutTxDatum txOutTx)
                -- TODO: When witnesses are properly segregated we can
                --       probably get rid of the 'slOtherData' map and of
                --       'lookupDatum'
                let input = Tx.scriptTxIn txo validator red dataValue
                unbalancedTx . tx . Tx.inputs %= Set.insert input
                valueSpentBalance <>= N.negate (Tx.txOutValue (txOutTxOut txOutTx))
            _                 -> throwError (TxOutRefWrongType txo)

    MustForgeValue mpsHash tn i -> do
        monetaryPolicyScript <- lookupMonetaryPolicy mpsHash
        let value = Value.singleton (Value.mpsSymbol mpsHash) tn i
        unbalancedTx . tx . Tx.forgeScripts %= Set.insert monetaryPolicyScript
        unbalancedTx . tx . Tx.forge <>= value
        -- If i is negative we are burning tokens. This counts as an output, so we should subtract
        -- the amount burned from valueSpentBalance, just as in `MustPayToPubKey` below.
        -- Subtracting the amount burned is the same as adding the (negative) amount forged.
        if i < 0 then valueSpentBalance <>= value
                 else valueSpentBalance  <>= N.negate value
    MustPayToPubKey pk vl -> do
        unbalancedTx . tx . Tx.outputs %= (Tx.TxOut (PubKeyAddress pk) vl Tx.PayToPubKey :)
        -- we can subtract vl from 'valueSpentRequired' because
        -- we know for certain that it will be matched by an input
        -- after balancing
        valueSpentBalance <>= N.negate vl
    MustPayToOtherScript vlh dv vl -> do
        let addr = Address.scriptHashAddress vlh
            theHash = datumHash dv
        unbalancedTx . tx . Tx.datumWitnesses %= set (at theHash) (Just dv)
        unbalancedTx . tx . Tx.outputs %= (Tx.scriptTxOut' vl addr dv :)
        valueSpentBalance <>= N.negate vl
    MustHashDatum dvh dv -> do
        unless (datumHash dv == dvh)
            (throwError $ DatumWrongHash dvh dv)
        unbalancedTx . tx . Tx.datumWitnesses %= set (at dvh) (Just dv)
