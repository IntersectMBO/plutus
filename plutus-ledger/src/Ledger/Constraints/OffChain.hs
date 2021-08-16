{-# LANGUAGE DataKinds                 #-}
{-# LANGUAGE DeriveAnyClass            #-}
{-# LANGUAGE DeriveGeneric             #-}
{-# LANGUAGE DerivingVia               #-}
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
    , typedValidatorLookups
    , unspentOutputs
    , mintingPolicy
    , otherScript
    , otherData
    , ownPubKeyHash
    , pubKey
    -- * Constraints resolution
    , SomeLookupsAndConstraints(..)
    , UnbalancedTx(..)
    , tx
    , requiredSignatories
    , utxoIndex
    , validityTimeRange
    , emptyUnbalancedTx
    , MkTxError(..)
    , mkTx
    , mkSomeTx
    -- * Internals exposed for testing
    , ValueSpentBalances(..)
    , provided
    , required
    , missingValueSpent
    ) where

import           Control.Lens
import           Control.Monad.Except
import           Control.Monad.Reader
import           Control.Monad.State

import           Data.Aeson                       (FromJSON, ToJSON)
import           Data.Foldable                    (traverse_)
import           Data.List                        (elemIndex)
import           Data.Map                         (Map)
import qualified Data.Map                         as Map
import           Data.Semigroup                   (First (..))
import qualified Data.Set                         as Set
import           Data.Text.Prettyprint.Doc
import           GHC.Generics                     (Generic)

import           PlutusTx                         (FromData (..), ToData (..))
import           PlutusTx.Lattice
import qualified PlutusTx.Numeric                 as N

import           Ledger.Address                   (Address (..), pubKeyHashAddress)
import qualified Ledger.Address                   as Address
import           Ledger.Constraints.TxConstraints hiding (requiredSignatories)
import           Ledger.Crypto                    (pubKeyHash)
import           Ledger.Orphans                   ()
import           Ledger.Scripts                   (Datum (..), DatumHash, MintingPolicy, MintingPolicyHash,
                                                   Redeemer (..), Validator, datumHash, mintingPolicyHash)
import           Ledger.Tx                        (RedeemerPtr (..), ScriptTag (..), Tx, TxOut (..), TxOutRef,
                                                   TxOutTx (..))
import qualified Ledger.Tx                        as Tx
import           Ledger.Typed.Scripts             (TypedValidator, ValidatorTypes (..))
import qualified Ledger.Typed.Scripts             as Scripts
import           Ledger.Typed.Tx                  (ConnectionError)
import qualified Ledger.Typed.Tx                  as Typed
import           Plutus.V1.Ledger.Crypto          (PubKey, PubKeyHash)
import           Plutus.V1.Ledger.Time            (POSIXTimeRange)
import           Plutus.V1.Ledger.Value           (Value)
import qualified Plutus.V1.Ledger.Value           as Value

data ScriptLookups a =
    ScriptLookups
        { slMPS            :: Map MintingPolicyHash MintingPolicy
        -- ^ Minting policies that the script interacts with
        , slTxOutputs      :: Map TxOutRef TxOutTx
        -- ^ Unspent outputs that the script may want to spend
        , slOtherScripts   :: Map Address Validator
        -- ^ Validators of scripts other than "our script"
        , slOtherData      :: Map DatumHash Datum
        -- ^ Datums that we might need
        , slPubKeyHashes   :: Map PubKeyHash PubKey
        -- ^ Public keys that we might need
        , slTypedValidator :: Maybe (TypedValidator a)
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
            , slPubKeyHashes = slPubKeyHashes l <> slPubKeyHashes r
            -- 'First' to match the semigroup instance of Map (left-biased)
            , slTypedValidator = fmap getFirst $ (First <$> slTypedValidator l) <> (First <$> slTypedValidator r)
            , slOwnPubkey = fmap getFirst $ (First <$> slOwnPubkey l) <> (First <$> slOwnPubkey r)
            }

instance Monoid (ScriptLookups a) where
    mappend = (<>)
    mempty  = ScriptLookups mempty mempty mempty mempty mempty Nothing Nothing

-- | A script lookups value with a script instance. For convenience this also
--   includes the minting policy script that forwards all checks to the
--   instance's validator.
typedValidatorLookups :: TypedValidator a -> ScriptLookups a
typedValidatorLookups inst =
    ScriptLookups
        { slMPS = Map.singleton (Scripts.forwardingMintingPolicyHash inst) (Scripts.forwardingMintingPolicy inst)
        , slTxOutputs = Map.empty
        , slOtherScripts = Map.empty
        , slOtherData = Map.empty
        , slPubKeyHashes = Map.empty
        , slTypedValidator = Just inst
        , slOwnPubkey = Nothing
        }

-- | A script lookups value that uses the map of unspent outputs to resolve
--   input constraints.
unspentOutputs :: Map TxOutRef TxOutTx -> ScriptLookups a
unspentOutputs mp = mempty { slTxOutputs = mp }

-- | A script lookups value with a minting policy script
mintingPolicy :: MintingPolicy -> ScriptLookups a
mintingPolicy pl =
    let hsh = mintingPolicyHash pl in
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

-- | A script lookups value with a public key
pubKey :: PubKey -> ScriptLookups a
pubKey pk = mempty { slPubKeyHashes = Map.singleton (pubKeyHash pk) pk }

ownPubKeyHash :: PubKeyHash -> ScriptLookups a
ownPubKeyHash ph = mempty { slOwnPubkey = Just ph}

-- | An unbalanced transaction. It needs to be balanced and signed before it
--   can be submitted to the ledeger. See note [Submitting transactions from
--   Plutus contracts] in 'Plutus.Contract.Wallet'.
data UnbalancedTx =
    UnbalancedTx
        { unBalancedTxTx                  :: Tx
        , unBalancedTxRequiredSignatories :: Map PubKeyHash (Maybe PubKey)
        , unBalancedTxUtxoIndex           :: Map TxOutRef TxOut
        , unBalancedTxValidityTimeRange   :: POSIXTimeRange
        }
    deriving stock (Eq, Generic, Show)
    deriving anyclass (FromJSON, ToJSON)

makeLensesFor
    [ ("unBalancedTxTx", "tx")
    , ("unBalancedTxRequiredSignatories", "requiredSignatories")
    , ("unBalancedTxUtxoIndex", "utxoIndex")
    , ("unBalancedTxValidityTimeRange", "validityTimeRange")
    ] ''UnbalancedTx

emptyUnbalancedTx :: UnbalancedTx
emptyUnbalancedTx = UnbalancedTx mempty mempty mempty top

instance Pretty UnbalancedTx where
    pretty (UnbalancedTx utx rs utxo vr) =
        vsep
        [ hang 2 $ vsep ["Tx:", pretty utx]
        , hang 2 $ vsep $ "Requires signatures:" : (pretty . fst <$> Map.toList rs)
        , hang 2 $ vsep $ "Utxo index:" : (pretty <$> Map.toList utxo)
        , hang 2 $ vsep ["Validity range:", pretty vr]
        ]

{- Note [Balance of value spent]

To build a transaction that satisfies the 'MustSpendAtLeast' and
'MustProduceAtLeast' constraints, we keep a tally of the required and
actual values we encounter on either side of the transaction. Then we
compute the missing value on both sides, and add an input with the
join of the positive parts [1] of the missing values.

[1] See 'Plutus.V1.Ledger.Value.split'

-}

-- | The balances we track for computing the missing 'Value' (if any)
--   that needs to be added to the transaction.
--   See note [Balance of value spent].
data ValueSpentBalances =
    ValueSpentBalances
        { vbsRequired :: Value
        -- ^ Required value spent by the transaction.
        , vbsProvided :: Value
        -- ^ Value provided by an input or output of the transaction.
        } deriving (Show, Generic)

instance Semigroup ValueSpentBalances where
    l <> r =
        ValueSpentBalances
            { vbsRequired = vbsRequired l \/ vbsRequired r
            , vbsProvided = vbsProvided l \/ vbsProvided r
            }

-- No @Monoid ValueSpentBalances@ because @max@ (used by 'convexUnion') is only
-- a semigroup. In this module we only use @Value@s with non-negative amounts,
-- so @mempty :: Value@ technically is the identity, but I'd rather not
-- define the instance. Maybe we need a type for non-negative @Value@s.

data ConstraintProcessingState =
    ConstraintProcessingState
        { cpsUnbalancedTx              :: UnbalancedTx
        -- ^ The unbalanced transaction that we're building
        , cpsMintRedeemers             :: Map.Map MintingPolicyHash Redeemer
        -- ^ Redeemers for minting policies.
        , cpsValueSpentBalancesInputs  :: ValueSpentBalances
        -- ^ Balance of the values given and required for the transaction's
        --   inputs
        , cpsValueSpentBalancesOutputs :: ValueSpentBalances
        -- ^ Balance of the values produced and required for the transaction's
        --   outputs
        }

missingValueSpent :: ValueSpentBalances -> Value
missingValueSpent ValueSpentBalances{vbsRequired, vbsProvided} =
    let
        difference = vbsRequired <> N.negate vbsProvided
        (_, missing) = Value.split difference
    in missing

totalMissingValue :: ConstraintProcessingState -> Value
totalMissingValue ConstraintProcessingState{cpsValueSpentBalancesInputs, cpsValueSpentBalancesOutputs} =
        missingValueSpent cpsValueSpentBalancesInputs \/
        missingValueSpent cpsValueSpentBalancesOutputs

makeLensesFor
    [ ("cpsUnbalancedTx", "unbalancedTx")
    , ("cpsMintRedeemers", "mintRedeemers")
    , ("cpsValueSpentBalancesInputs", "valueSpentInputs")
    , ("cpsValueSpentBalancesOutputs", "valueSpentOutputs")
    ] ''ConstraintProcessingState

initialState :: ConstraintProcessingState
initialState = ConstraintProcessingState
    { cpsUnbalancedTx = emptyUnbalancedTx
    , cpsMintRedeemers = mempty
    , cpsValueSpentBalancesInputs = ValueSpentBalances mempty mempty
    , cpsValueSpentBalancesOutputs = ValueSpentBalances mempty mempty
    }

provided :: Value -> ValueSpentBalances
provided v = ValueSpentBalances { vbsProvided = v, vbsRequired = mempty }

required :: Value -> ValueSpentBalances
required v = ValueSpentBalances { vbsRequired = v, vbsProvided = mempty }

-- | Some typed 'TxConstraints' and the 'ScriptLookups' needed to turn them
--   into an 'UnbalancedTx'.
data SomeLookupsAndConstraints where
    SomeLookupsAndConstraints :: forall a. (FromData (DatumType a), ToData (DatumType a), ToData (RedeemerType a)) => ScriptLookups a -> TxConstraints (RedeemerType a) (DatumType a) -> SomeLookupsAndConstraints

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
    :: ( FromData (DatumType a)
       , ToData (DatumType a)
       , ToData (RedeemerType a)
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
            addMintingRedeemers
            addMissingValueSpent
            updateUtxoIndex

-- | Turn a 'TxConstraints' value into an unbalanced transaction that satisfies
--   the constraints. To use this in a contract, see
--   'Plutus.Contract.submitTxConstraints'
--   and related functions.
mkTx
    :: ( FromData (DatumType a)
       , ToData (DatumType a)
       , ToData (RedeemerType a))
    => ScriptLookups a
    -> TxConstraints (RedeemerType a) (DatumType a)
    -> Either MkTxError UnbalancedTx
mkTx lookups txc = mkSomeTx [SomeLookupsAndConstraints lookups txc]

-- | Add the remaining balance of the total value that the tx must spend.
--   See note [Balance of value spent]
addMissingValueSpent
    :: ( MonadReader (ScriptLookups a) m
       , MonadState ConstraintProcessingState m
       , MonadError MkTxError m
       )
    => m ()
addMissingValueSpent = do
    missing <- gets totalMissingValue

    if Value.isZero missing
        then pure ()
        else do
            -- add 'missing' to the transaction's outputs. This ensures that the
            -- wallet will add a corresponding input when balancing the
            -- transaction.
            -- Step 4 of the process described in [Balance of value spent]
            pk <- asks slOwnPubkey >>= maybe (throwError OwnPubKeyMissing) pure
            unbalancedTx . tx . Tx.outputs %= (Tx.TxOut{txOutAddress=pubKeyHashAddress pk,txOutValue=missing,txOutDatumHash=Nothing} :)

addMintingRedeemers
    :: ( MonadState ConstraintProcessingState m
       , MonadError MkTxError m
       )
    => m ()
addMintingRedeemers = do
    reds <- use mintRedeemers
    txSoFar <- use (unbalancedTx . tx)
    let mpss = mintingPolicyHash <$> Set.toList (Tx.txMintScripts txSoFar)
    iforM_ reds $ \mpsHash red -> do
        let err = throwError (MintingPolicyNotFound mpsHash)
        ptr <- maybe err (pure . RedeemerPtr Mint . fromIntegral) $ elemIndex mpsHash mpss
        unbalancedTx . tx . Tx.redeemers . at ptr .= Just red

updateUtxoIndex
    :: ( MonadReader (ScriptLookups a) m
       , MonadState ConstraintProcessingState m
       )
    => m ()
updateUtxoIndex = do
    ScriptLookups{slTxOutputs} <- ask
    unbalancedTx . utxoIndex <>= fmap txOutTxOut slTxOutputs

-- | Add a typed input, checking the type of the output it spends. Return the value
--   of the spent output.
addOwnInput
    :: ( MonadReader (ScriptLookups a) m
        , MonadError MkTxError m
        , MonadState ConstraintProcessingState m
        , FromData (DatumType a)
        , ToData (DatumType a)
        , ToData (RedeemerType a)
        )
    => InputConstraint (RedeemerType a)
    -> m ()
addOwnInput InputConstraint{icRedeemer, icTxOutRef} = do
    ScriptLookups{slTxOutputs, slTypedValidator} <- ask
    inst <- maybe (throwError TypedValidatorMissing) pure slTypedValidator
    typedOutRef <-
        either (throwError . TypeCheckFailed) pure
        $ runExcept @ConnectionError
        $ Typed.typeScriptTxOutRef (`Map.lookup` slTxOutputs) inst icTxOutRef
    let txIn = Typed.makeTypedScriptTxIn inst icRedeemer typedOutRef
        vl   = Tx.txOutValue $ Typed.tyTxOutTxOut $ Typed.tyTxOutRefOut typedOutRef
    unbalancedTx . tx . Tx.inputs %= Set.insert (Typed.tyTxInTxIn txIn)
    valueSpentInputs <>= provided vl

-- | Add a typed output and return its value.
addOwnOutput
    :: ( MonadReader (ScriptLookups a) m
        , MonadState ConstraintProcessingState m
        , FromData (DatumType a)
        , ToData (DatumType a)
        , MonadError MkTxError m
        )
    => OutputConstraint (DatumType a)
    -> m ()
addOwnOutput OutputConstraint{ocDatum, ocValue} = do
    ScriptLookups{slTypedValidator} <- ask
    inst <- maybe (throwError TypedValidatorMissing) pure slTypedValidator
    let txOut = Typed.makeTypedScriptTxOut inst ocDatum ocValue
        dsV   = Datum (toBuiltinData ocDatum)
    unbalancedTx . tx . Tx.outputs %= (Typed.tyTxOutTxOut txOut :)
    unbalancedTx . tx . Tx.datumWitnesses . at (datumHash dsV) .= Just dsV
    valueSpentOutputs <>= provided ocValue

data MkTxError =
    TypeCheckFailed ConnectionError
    | TxOutRefNotFound TxOutRef
    | TxOutRefWrongType TxOutRef
    | DatumNotFound DatumHash
    | MintingPolicyNotFound MintingPolicyHash
    | ValidatorHashNotFound Address
    | OwnPubKeyMissing
    | TypedValidatorMissing
    | DatumWrongHash DatumHash Datum
    | CannotSatisfyAny
    deriving stock (Eq, Show, Generic)
    deriving anyclass (ToJSON, FromJSON)

instance Pretty MkTxError where
    pretty = \case
        TypeCheckFailed e       -> "Type check failed:" <+> pretty e
        TxOutRefNotFound t      -> "Tx out reference not found:" <+> pretty t
        TxOutRefWrongType t     -> "Tx out reference wrong type:" <+> pretty t
        DatumNotFound h         -> "No datum with hash" <+> pretty h <+> "was found"
        MintingPolicyNotFound h -> "No minting policy with hash" <+> pretty h <+> "was found"
        ValidatorHashNotFound h -> "No validator with hash" <+> pretty h <+> "was found"
        OwnPubKeyMissing        -> "Own public key is missing"
        TypedValidatorMissing   -> "Script instance is missing"
        DatumWrongHash h d      -> "Wrong hash for datum" <+> pretty d <> colon <+> pretty h
        CannotSatisfyAny        -> "Cannot satisfy any of the required constraints"

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

lookupMintingPolicy
    :: ( MonadReader (ScriptLookups a) m
       , MonadError MkTxError m )
    => MintingPolicyHash
    -> m MintingPolicy
lookupMintingPolicy mph =
    let err = throwError (MintingPolicyNotFound mph) in
    asks slMPS >>= maybe err pure . view (at mph)

lookupValidator
    :: ( MonadReader (ScriptLookups a) m
       , MonadError MkTxError m )
    => Address
    -> m Validator
lookupValidator addr =
    let err = throwError (ValidatorHashNotFound addr) in
    asks slOtherScripts >>= maybe err pure . view (at addr)

-- | Get the 'Map.Map PubKeyHash (Maybe PubKey)' for a pub key hash,
--   associating the pub key hash with the public key (if known).
--   This value that can be added to the
--   'unBalancedTxRequiredSignatories' field
getSignatories ::
    ( MonadReader (ScriptLookups a) m)
    => PubKeyHash
    -> m (Map.Map PubKeyHash (Maybe PubKey))
getSignatories pkh =
    Map.singleton pkh <$> asks (Map.lookup pkh . slPubKeyHashes)

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
        unbalancedTx . tx . Tx.datumWitnesses . at theHash .= Just dv
    MustValidateIn timeRange ->
        unbalancedTx . validityTimeRange %= (timeRange /\)
    MustBeSignedBy pk -> do
        sigs <- getSignatories pk
        unbalancedTx . requiredSignatories <>= sigs
    MustSpendAtLeast vl -> valueSpentInputs <>= required vl
    MustProduceAtLeast vl -> valueSpentOutputs <>= required vl
    MustSpendPubKeyOutput txo -> do
        TxOutTx{txOutTxOut} <- lookupTxOutRef txo
        case Address.toPubKeyHash (Tx.txOutAddress txOutTxOut) of
            Just{} -> do
                unbalancedTx . tx . Tx.inputs %= Set.insert (Tx.pubKeyTxIn txo)
                valueSpentInputs <>= provided (Tx.txOutValue txOutTxOut)
            _                 -> throwError (TxOutRefWrongType txo)
    MustSpendScriptOutput txo red -> do
        txOutTx <- lookupTxOutRef txo
        case Tx.txOutDatumHash (txOutTxOut txOutTx) of
            Just dvh -> do
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
                unbalancedTx . tx . Tx.datumWitnesses . at dvh .= Just dataValue
                valueSpentInputs <>= provided (Tx.txOutValue (txOutTxOut txOutTx))
            _                 -> throwError (TxOutRefWrongType txo)

    MustMintValue mpsHash red tn i -> do
        mintingPolicyScript <- lookupMintingPolicy mpsHash
        let value = Value.singleton (Value.mpsSymbol mpsHash) tn
        -- If i is negative we are burning tokens. The tokens burned must
        -- be provided as an input. So we add the value burnt to
        -- 'valueSpentInputs'. If i is positive then new tokens are created
        -- which must be added to 'valueSpentOutputs'.
        if i < 0
            then valueSpentInputs <>= provided (value (negate i))
            else valueSpentOutputs <>= provided (value i)

        unbalancedTx . tx . Tx.mintScripts %= Set.insert mintingPolicyScript
        unbalancedTx . tx . Tx.mint <>= value i
        mintRedeemers . at mpsHash .= Just red
    MustPayToPubKey pk vl -> do
        unbalancedTx . tx . Tx.outputs %= (Tx.TxOut{txOutAddress=pubKeyHashAddress pk,txOutValue=vl,txOutDatumHash=Nothing} :)
        valueSpentOutputs <>= provided vl
    MustPayToOtherScript vlh dv vl -> do
        let addr = Address.scriptHashAddress vlh
            theHash = datumHash dv
        unbalancedTx . tx . Tx.datumWitnesses . at theHash .= Just dv
        unbalancedTx . tx . Tx.outputs %= (Tx.scriptTxOut' vl addr dv :)
        valueSpentOutputs <>= provided vl
    MustHashDatum dvh dv -> do
        unless (datumHash dv == dvh)
            (throwError $ DatumWrongHash dvh dv)
        unbalancedTx . tx . Tx.datumWitnesses . at dvh .= Just dv
    MustSatisfyAnyOf xs -> do
        s <- get
        let tryNext [] =
                throwError CannotSatisfyAny
            tryNext (h:q) = do
                processConstraint h `catchError` \_ -> put s >> tryNext q
        tryNext xs
