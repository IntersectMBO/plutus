{-# LANGUAGE ConstraintKinds           #-}
{-# LANGUAGE DataKinds                 #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleContexts          #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE GADTs                     #-}
{-# LANGUAGE MultiParamTypeClasses     #-}
{-# LANGUAGE NamedFieldPuns            #-}
{-# LANGUAGE PolyKinds                 #-}
{-# LANGUAGE Rank2Types                #-}
{-# LANGUAGE ScopedTypeVariables       #-}
{-# LANGUAGE TypeApplications          #-}
{-# LANGUAGE TypeFamilies              #-}
{-# LANGUAGE TypeOperators             #-}
{-# LANGUAGE UndecidableInstances      #-}
{-# LANGUAGE ViewPatterns              #-}
-- | Typed transactions. This module defines typed versions of various ledger types. The ultimate
-- goal is to make sure that the script types attached to inputs and outputs line up, to avoid
-- type errors at validation time.
module Ledger.Typed.Tx where

import           Ledger.Crypto
import qualified Ledger.Interval            as Interval
import           Ledger.Scripts
import           Ledger.Slot
import           Ledger.Tx                  hiding (scriptAddress)
import           Ledger.Typed.Scripts
import qualified Ledger.Value               as Value

import           Ledger.Typed.TypeUtils

import qualified Language.PlutusCore        as PLC
import qualified Language.PlutusCore.Pretty as PLC

import           Language.PlutusTx
import           Language.PlutusTx.Lift     as Lift
import           Language.PlutusTx.Numeric

import qualified Language.PlutusIR.Compiler as PIR

import           Data.Coerce
import           Data.Kind
import           Data.List                  (foldl')
import           Data.Proxy
import qualified Data.Set                   as Set

import           Control.Monad.Except

-- | A 'TxIn' tagged by two phantom types: a list of the types of the data scripts in the transaction; and the connection type of the input.
newtype TypedScriptTxIn a = TypedScriptTxIn { unTypedScriptTxIn :: TxIn }
-- | Create a 'TypedScriptTxIn' from a correctly-typed validator, redeemer, and output ref.
makeTypedScriptTxIn
    :: forall inn
    . (IsData (RedeemerType inn))
    => ScriptInstance inn
    -> RedeemerType inn
    -> TypedScriptTxOutRef inn
    -> TypedScriptTxIn inn
makeTypedScriptTxIn si r (TypedScriptTxOutRef ref) =
    let vs = validatorScript si
        rs = RedeemerScript (toData r)
        txInType = ConsumeScriptAddress vs rs
    in TypedScriptTxIn @inn $ TxIn ref txInType

-- | A public-key 'TxIn'. We need this to be sure that it is not a script input.
newtype PubKeyTxIn = PubKeyTxIn { unPubKeyTxIn :: TxIn }
-- | Create a 'PubKeyTxIn'.
makePubKeyTxIn :: TxOutRef -> PubKey -> PubKeyTxIn
makePubKeyTxIn ref pubkey = PubKeyTxIn $ TxIn ref $ ConsumePublicKeyAddress pubkey

-- | A 'TxOut' tagged by a phantom type: and the connection type of the output.
newtype TypedScriptTxOut a = TypedScriptTxOut { unTypedScriptTxOut :: TxOut }
-- | Create a 'TypedScriptTxOut' from a correctly-typed data script, an address, and a value.
makeTypedScriptTxOut
    :: forall out
    . (IsData (DataType out))
    => ScriptInstance out
    -> DataType out
    -> Value.Value
    -> TypedScriptTxOut out
makeTypedScriptTxOut ct d value =
    let outTy = PayToScript (DataScript (toData d))
    in TypedScriptTxOut @out $ TxOut (scriptAddress ct) value outTy

-- | A 'TxOutRef' tagged by a phantom type: and the connection type of the output.
newtype TypedScriptTxOutRef a = TypedScriptTxOutRef { unTypedScriptTxOutRef :: TxOutRef }

-- | A public-key 'TxOut'. We need this to be sure that it is not a script output.
newtype PubKeyTxOut = PubKeyTxOut { unPubKeyTxOut :: TxOut }
-- | Create a 'PubKeyTxOut'.
makePubKeyTxOut :: Value.Value -> PubKey -> PubKeyTxOut
makePubKeyTxOut value pubKey = PubKeyTxOut $ pubKeyTxOut value pubKey

-- | A typed transaction, tagged by two phantom types: a list of connection types for the outputs,
-- and a list of connection types for the inputs. The script outputs and inputs must have the correct
-- corresponding types.
data TypedTx (ins :: [Type]) (outs :: [Type]) = TypedTx {
    tyTxTypedTxIns   :: HListF TypedScriptTxIn ins,
    tyTxPubKeyTxIns  :: [PubKeyTxIn],
    tyTxTypedTxOuts  :: HListF TypedScriptTxOut outs,
    tyTxPubKeyTxOuts :: [PubKeyTxOut],
    tyTxForge        :: !Value.Value,
    tyTxValidRange   :: !SlotRange
    }

baseTx :: TypedTx '[] '[]
baseTx = TypedTx {
    tyTxTypedTxIns = HNilF,
    tyTxPubKeyTxIns = [],
    tyTxTypedTxOuts = HNilF,
    tyTxPubKeyTxOuts = [],
    tyTxForge = mempty,
    tyTxValidRange = Interval.always
    }

-- | Adds a 'TypedScriptTxOut' to a 'TypedTx'.
--
-- Adding a new typed transaction output is only safe if there are no typed transaction
-- inputs yet. Otherwise those inputs would need to change to take the new data script as
-- an argument.
addTypedTxOut
    :: forall ins outs newOut
    . TypedScriptTxOut newOut
    -> TypedTx ins outs
    -> TypedTx ins (newOut ': outs)
-- We're changing the type so we can't use record update syntax :'(
addTypedTxOut out TypedTx {
    tyTxTypedTxOuts,
    tyTxPubKeyTxOuts,
    tyTxTypedTxIns,
    tyTxPubKeyTxIns,
    tyTxForge,
    tyTxValidRange } = TypedTx {
      tyTxTypedTxOuts=HConsF out tyTxTypedTxOuts,
      tyTxPubKeyTxOuts,
      tyTxTypedTxIns,
      tyTxPubKeyTxIns,
      tyTxForge,
      tyTxValidRange }

-- | Adds a 'TypedScriptTxIn' to a 'TypedTx'.
addTypedTxIn
    :: forall ins outs newIn
    . TypedScriptTxIn newIn
    -> TypedTx ins outs
    -> TypedTx (newIn ': ins) outs
-- We're changing the type so we can't use record update syntax :'(
addTypedTxIn inn TypedTx {
    tyTxTypedTxOuts,
    tyTxPubKeyTxOuts,
    tyTxTypedTxIns,
    tyTxPubKeyTxIns,
    tyTxForge,
    tyTxValidRange } = TypedTx {
      tyTxTypedTxOuts,
      tyTxPubKeyTxOuts,
      tyTxTypedTxIns=HConsF inn tyTxTypedTxIns,
      tyTxPubKeyTxIns,
      tyTxForge,
      tyTxValidRange }

-- | A wrapper around a 'TypedTx' that hides the input list type as an existential parameter.
-- This allows us to perform some operations more easily by not caring about the input connection
-- types, see 'addSomeTypedTxIn' particularly.
data TypedTxSomeIns (outs :: [Type]) = forall ins . TypedTxSomeIns (TypedTx ins outs)

-- | Add a 'TypedScriptTxIn' to a 'TypedTxSomeIns'. Note that we do not have to track
-- the input connection types explicitly.
addSomeTypedTxIn
    :: forall (outs :: [Type]) (newIn :: *)
    . TypedScriptTxIn newIn
    -> TypedTxSomeIns outs
    -> TypedTxSomeIns outs
addSomeTypedTxIn inn (TypedTxSomeIns tx) = TypedTxSomeIns $ addTypedTxIn inn tx

-- | Adds many homogeneous 'TypedScriptTxIn' to a 'TypedTx'.
addManyTypedTxIns
    :: forall (ins :: [Type]) (outs :: [Type]) (newIn :: Type)
    . [TypedScriptTxIn newIn]
    -> TypedTx ins outs
    -> TypedTxSomeIns outs
addManyTypedTxIns ins tx = foldl' (\someTx inn -> addSomeTypedTxIn inn someTx) (TypedTxSomeIns tx) ins

-- | Convert a 'TypedTx' to a 'Tx'.
toUntypedTx
    :: forall (ins :: [Type]) (outs :: [Type])
    . TypedTx ins outs
    -> Tx
toUntypedTx TypedTx{
    tyTxTypedTxOuts,
    tyTxPubKeyTxOuts,
    tyTxTypedTxIns,
    tyTxPubKeyTxIns,
    tyTxForge,
    tyTxValidRange } = Tx {
    txOutputs = hfOut coerce tyTxTypedTxOuts ++ coerce tyTxPubKeyTxOuts,
    txInputs = Set.fromList (hfOut coerce tyTxTypedTxIns ++ coerce tyTxPubKeyTxIns),
    txForge = tyTxForge,
    txFee = zero,
    txValidRange = tyTxValidRange,
    txSignatures = mempty }

-- Checking
-- TODO: these could be in a separate module

-- | An error we can get while trying to type an existing transaction part.
data ConnectionError =
    WrongValidatorHash ValidatorHash ValidatorHash
    | WrongOutType TxOutType
    | WrongInType TxInType
    | WrongValidatorType String
    | WrongRedeemerType
    | WrongDataType
    | UnknownRef
    deriving (Show, Eq, Ord)

-- | Checks that the given validator hash is consistent with the actual validator.
checkValidatorHash :: forall a m . (MonadError ConnectionError m) => ScriptInstance a -> ValidatorHash -> m ()
checkValidatorHash ct actualHash = do
    let expectedHash = plcValidatorDigest $ getAddress $ scriptAddress ct
    unless (actualHash == expectedHash) $ throwError $ WrongValidatorHash expectedHash actualHash

-- | Checks that the given validator script has the right type.
checkValidatorScript
    :: forall a m
    . (MonadError ConnectionError m)
    => ScriptInstance a
    -> ValidatorScript
    -> m (CompiledCode WrappedValidatorType)
checkValidatorScript _ (unValidatorScript -> (Script prog)) =
    case PLC.runQuote $ runExceptT @(PIR.Error (PIR.Provenance ())) $ Lift.typeCode (Proxy @WrappedValidatorType) prog of
        Right code -> pure code
        Left e     -> throwError $ WrongValidatorType $ show $ PLC.prettyPlcDef e

-- | Checks that the given redeemer script has the right type.
checkRedeemerScript
    :: forall inn m
    . (IsData (RedeemerType inn), MonadError ConnectionError m)
    => ScriptInstance inn
    -> RedeemerScript
    -> m (RedeemerType inn)
checkRedeemerScript _ (RedeemerScript d) =
    case fromData d of
        Just v  -> pure v
        Nothing -> throwError WrongRedeemerType

-- | Checks that the given data script has the right type.
checkDataScript
    :: forall a m . (IsData (DataType a), MonadError ConnectionError m)
    => ScriptInstance a
    -> DataScript
    -> m (DataType a)
checkDataScript _ (DataScript d) =
    case fromData d of
        Just v  -> pure v
        Nothing -> throwError WrongDataType

-- | Create a 'TypedScriptTxIn' from an existing 'TxIn' by checking the types of its parts.
typeScriptTxIn
    :: forall inn m
    . ( IsData (RedeemerType inn)
      , IsData (DataType inn)
      , MonadError ConnectionError m)
    => (TxOutRef -> Maybe TxOut)
    -> ScriptInstance inn
    -> TxIn
    -> m (TypedScriptTxIn inn)
typeScriptTxIn lookupRef si TxIn{txInRef,txInType} = do
    (vs, rs) <- case txInType of
        ConsumeScriptAddress vs rs -> pure (vs, rs)
        x                          -> throwError $ WrongInType x
    _ <- checkValidatorScript si vs
    rsVal <- checkRedeemerScript si rs
    -- If this succeeds we're okay
    typedOut <- typeScriptTxOutRef @inn lookupRef si txInRef
    pure $ makeTypedScriptTxIn si rsVal typedOut

-- | Create a 'PubKeyTxIn' from an existing 'TxIn' by checking that it has the right payment type.
typePubKeyTxIn
    :: forall m
    . (MonadError ConnectionError m)
    => TxIn
    -> m PubKeyTxIn
typePubKeyTxIn inn@TxIn{txInType} = do
    case txInType of
        ConsumePublicKeyAddress _ -> pure ()
        x                         -> throwError $ WrongInType x
    pure $ PubKeyTxIn inn

-- | Create a 'TypedScriptTxOut' from an existing 'TxOut' by checking the types of its parts.
typeScriptTxOut
    :: forall out m
    . ( IsData (DataType out)
      , MonadError ConnectionError m)
    => ScriptInstance out
    -> TxOut
    -> m (TypedScriptTxOut out)
typeScriptTxOut si TxOut{txOutAddress=Address addrHash,txOutValue,txOutType} = do
    ds <- case txOutType of
        PayToScript ds -> pure ds
        x              -> throwError $ WrongOutType x
    checkValidatorHash si (plcValidatorDigest addrHash)
    dsVal <- checkDataScript si ds
    pure $ makeTypedScriptTxOut si dsVal txOutValue

-- | Create a 'TypedScriptTxOut' from an existing 'TxOut' by checking the types of its parts. To do this we
-- need to cross-reference against the validator script and be able to look up the 'TxOut' to which this
-- reference points.
typeScriptTxOutRef
    :: forall out m
    . ( IsData (DataType out)
      , MonadError ConnectionError m)
    => (TxOutRef -> Maybe TxOut)
    -> ScriptInstance out
    -> TxOutRef
    -> m (TypedScriptTxOutRef out)
typeScriptTxOutRef lookupRef ct ref = do
    out <- case lookupRef ref of
        Just out -> pure out
        Nothing  -> throwError UnknownRef
    -- If this succeeds, we're good
    _ <- typeScriptTxOut @out ct out
    pure $ TypedScriptTxOutRef ref

-- | Create a 'PubKeyTxOUt' from an existing 'TxOut' by checking that it has the right payment type.
typePubKeyTxOut
    :: forall m
    . (MonadError ConnectionError m)
    => TxOut
    -> m PubKeyTxOut
typePubKeyTxOut out@TxOut{txOutType} = do
    case txOutType of
        PayToPubKey _ -> pure ()
        x             -> throwError $ WrongOutType x
    pure $ PubKeyTxOut out
