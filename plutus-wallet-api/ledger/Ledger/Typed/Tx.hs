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

import           Ledger.Address             hiding (scriptAddress)
import           Ledger.Crypto
import qualified Ledger.Interval            as Interval
import           Ledger.Scripts
import           Ledger.Slot
import           Ledger.Tx
import           Ledger.TxId
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
import qualified Data.Map                   as Map
import           Data.Proxy
import qualified Data.Set                   as Set

import           Codec.Serialise            (Serialise)
import           Control.Monad.Except

-- | A 'TxIn' tagged by two phantom types: a list of the types of the data scripts in the transaction; and the connection type of the input.
data TypedScriptTxIn uni a = TypedScriptTxIn { tyTxInTxIn :: TxIn uni, tyTxInOutRef :: TypedScriptTxOutRef a }
-- | Create a 'TypedScriptTxIn' from a correctly-typed validator, redeemer, and output ref.
makeTypedScriptTxIn
    :: forall inn uni
    . (IsData (RedeemerType inn), IsData (DataType inn))
    => ScriptInstance uni inn
    -> RedeemerType inn
    -> TypedScriptTxOutRef inn
    -> TypedScriptTxIn uni inn
makeTypedScriptTxIn si r tyRef@(TypedScriptTxOutRef ref TypedScriptTxOut{tyTxOutData=d}) =
    let vs = validatorScript si
        rs = RedeemerValue (toData r)
        ds = DataValue (toData d)
        txInType = ConsumeScriptAddress vs rs ds
    in TypedScriptTxIn @uni @inn (TxIn ref txInType) tyRef

txInValue :: TypedScriptTxIn uni a -> Value.Value
txInValue = txOutValue . tyTxOutTxOut . tyTxOutRefOut . tyTxInOutRef

-- | A public-key 'TxIn'. We need this to be sure that it is not a script input.
newtype PubKeyTxIn uni = PubKeyTxIn { unPubKeyTxIn :: TxIn uni }
-- | Create a 'PubKeyTxIn'.
makePubKeyTxIn :: TxOutRef -> PubKeyTxIn uni
makePubKeyTxIn ref = PubKeyTxIn $ TxIn ref ConsumePublicKeyAddress

-- | A 'TxOut' tagged by a phantom type: and the connection type of the output.
data TypedScriptTxOut a = IsData (DataType a) => TypedScriptTxOut { tyTxOutTxOut :: TxOut, tyTxOutData :: DataType a }

-- | Create a 'TypedScriptTxOut' from a correctly-typed data script, an address, and a value.
makeTypedScriptTxOut
    :: forall out uni
    . (IsData (DataType out))
    => ScriptInstance uni out
    -> DataType out
    -> Value.Value
    -> TypedScriptTxOut out
makeTypedScriptTxOut ct d value =
    let outTy = PayToScript $ dataValueHash $ DataValue $ toData d
    in TypedScriptTxOut @out (TxOut (scriptAddress ct) value outTy) d

-- | A 'TxOutRef' tagged by a phantom type: and the connection type of the output.
data TypedScriptTxOutRef a = TypedScriptTxOutRef { tyTxOutRefRef :: TxOutRef, tyTxOutRefOut :: TypedScriptTxOut a }

-- | A public-key 'TxOut'. We need this to be sure that it is not a script output.
newtype PubKeyTxOut = PubKeyTxOut { unPubKeyTxOut :: TxOut }
-- | Create a 'PubKeyTxOut'.
makePubKeyTxOut :: Value.Value -> PubKey -> PubKeyTxOut
makePubKeyTxOut value pubKey = PubKeyTxOut $ pubKeyTxOut value pubKey

-- | A typed transaction, tagged by two phantom types: a list of connection types for the outputs,
-- and a list of connection types for the inputs. The script outputs and inputs must have the correct
-- corresponding types.
data TypedTx uni (ins :: [Type]) (outs :: [Type]) = TypedTx {
    tyTxTypedTxIns   :: HListF (TypedScriptTxIn uni) ins,
    tyTxPubKeyTxIns  :: [PubKeyTxIn uni],
    tyTxTypedTxOuts  :: HListF TypedScriptTxOut outs,
    tyTxPubKeyTxOuts :: [PubKeyTxOut],
    tyTxForge        :: !Value.Value,
    tyTxValidRange   :: !SlotRange,
    tyTxForgeScripts :: Set.Set (MonetaryPolicy uni)
    }

baseTx :: (PLC.Closed uni, uni `PLC.Everywhere` Serialise) => TypedTx uni '[] '[]
baseTx = TypedTx {
    tyTxTypedTxIns = HNilF,
    tyTxPubKeyTxIns = [],
    tyTxTypedTxOuts = HNilF,
    tyTxPubKeyTxOuts = [],
    tyTxForge = mempty,
    tyTxValidRange = Interval.always,
    tyTxForgeScripts = mempty
    }

-- | Adds a 'TypedScriptTxOut' to a 'TypedTx'.
--
-- Adding a new typed transaction output is only safe if there are no typed transaction
-- inputs yet. Otherwise those inputs would need to change to take the new data script as
-- an argument.
addTypedTxOut
    :: forall ins outs newOut uni
    . TypedScriptTxOut newOut
    -> TypedTx uni ins outs
    -> TypedTx uni ins (newOut ': outs)
-- We're changing the type so we can't use record update syntax :'(
addTypedTxOut out TypedTx {
    tyTxTypedTxOuts,
    tyTxPubKeyTxOuts,
    tyTxTypedTxIns,
    tyTxPubKeyTxIns,
    tyTxForge,
    tyTxValidRange,
    tyTxForgeScripts } = TypedTx {
      tyTxTypedTxOuts=HConsF out tyTxTypedTxOuts,
      tyTxPubKeyTxOuts,
      tyTxTypedTxIns,
      tyTxPubKeyTxIns,
      tyTxForge,
      tyTxValidRange,
      tyTxForgeScripts }

-- | Adds a 'TypedScriptTxIn' to a 'TypedTx'.
addTypedTxIn
    :: forall ins outs newIn uni
    . TypedScriptTxIn uni newIn
    -> TypedTx uni ins outs
    -> TypedTx uni (newIn ': ins) outs
-- We're changing the type so we can't use record update syntax :'(
addTypedTxIn inn TypedTx {
    tyTxTypedTxOuts,
    tyTxPubKeyTxOuts,
    tyTxTypedTxIns,
    tyTxPubKeyTxIns,
    tyTxForge,
    tyTxValidRange,
    tyTxForgeScripts } = TypedTx {
      tyTxTypedTxOuts,
      tyTxPubKeyTxOuts,
      tyTxTypedTxIns=HConsF inn tyTxTypedTxIns,
      tyTxPubKeyTxIns,
      tyTxForge,
      tyTxValidRange,
      tyTxForgeScripts }

-- | A wrapper around a 'TypedTx' that hides the input list type as an existential parameter.
-- This allows us to perform some operations more easily by not caring about the input connection
-- types, see 'addSomeTypedTxIn' particularly.
data TypedTxSomeIns uni (outs :: [Type]) = forall ins . TypedTxSomeIns (TypedTx uni ins outs)

-- | Add a 'TypedScriptTxIn' to a 'TypedTxSomeIns'. Note that we do not have to track
-- the input connection types explicitly.
addSomeTypedTxIn
    :: forall (outs :: [Type]) (newIn :: *) uni
    . TypedScriptTxIn uni newIn
    -> TypedTxSomeIns uni outs
    -> TypedTxSomeIns uni outs
addSomeTypedTxIn inn (TypedTxSomeIns tx) = TypedTxSomeIns $ addTypedTxIn inn tx

-- | Adds many homogeneous 'TypedScriptTxIn' to a 'TypedTx'.
addManyTypedTxIns
    :: forall (ins :: [Type]) (outs :: [Type]) (newIn :: Type) uni
    . [TypedScriptTxIn uni newIn]
    -> TypedTx uni ins outs
    -> TypedTxSomeIns uni outs
addManyTypedTxIns ins tx = foldl' (\someTx inn -> addSomeTypedTxIn inn someTx) (TypedTxSomeIns tx) ins

-- | A wrapper around a 'TypedTx' that hides the output list type as an existential parameter.
data TypedTxSomeOuts uni (ins :: [Type]) = forall outs . TypedTxSomeOuts (TypedTx uni ins outs)

-- | Add a 'TypedScriptTxOut' to a 'TypedTxSomeOuts'. Note that we do not have to track
-- the output connection types explicitly.
addSomeTypedTxOut
    :: forall (ins :: [Type]) (newOut :: *) uni
    . TypedScriptTxOut newOut
    -> TypedTxSomeOuts uni ins
    -> TypedTxSomeOuts uni ins
addSomeTypedTxOut out (TypedTxSomeOuts tx) = TypedTxSomeOuts $ addTypedTxOut out tx

-- | Convert a 'TypedTx' to a 'Tx'.
toUntypedTx
    :: forall (ins :: [Type]) (outs :: [Type]) uni
    . (PLC.Closed uni, uni `PLC.Everywhere` Serialise)
    => TypedTx uni ins outs
    -> Tx uni
toUntypedTx TypedTx{
    tyTxTypedTxOuts,
    tyTxPubKeyTxOuts,
    tyTxTypedTxIns,
    tyTxPubKeyTxIns,
    tyTxForge,
    tyTxValidRange,
    tyTxForgeScripts } = Tx {
    txOutputs = hfOut tyTxOutTxOut tyTxTypedTxOuts ++ coerce tyTxPubKeyTxOuts,
    txInputs = Set.fromList (hfOut tyTxInTxIn tyTxTypedTxIns ++ coerce tyTxPubKeyTxIns),
    txForge = tyTxForge,
    txFee = zero,
    txValidRange = tyTxValidRange,
    txSignatures = mempty,
    txForgeScripts = tyTxForgeScripts,
    txData = Map.fromList $ hfOut dsEntry tyTxTypedTxOuts}
    where
        dsEntry TypedScriptTxOut{tyTxOutData=d} = let ds = DataValue $ toData d in (dataValueHash ds, ds)

-- Checking
-- TODO: these could be in a separate module

-- | An error we can get while trying to type an existing transaction part.
data ConnectionError uni =
    WrongValidatorAddress Address Address
    | WrongOutType TxOutType
    | WrongInType (TxInType uni)
    | WrongValidatorType String
    | WrongRedeemerType
    | WrongDataType
    | NoData TxId DataValueHash
    | UnknownRef
    deriving (Show, Eq, Ord)

-- | Checks that the given validator hash is consistent with the actual validator.
checkValidatorAddress :: forall a uni m . (MonadError (ConnectionError uni) m) => ScriptInstance uni a -> Address -> m ()
checkValidatorAddress ct actualAddr = do
    let expectedAddr = scriptAddress ct
    unless (expectedAddr == actualAddr) $ throwError $ WrongValidatorAddress expectedAddr actualAddr

-- | Checks that the given validator script has the right type.
checkValidatorScript
    :: forall a uni m . (MonadError (ConnectionError PLC.DefaultUni) m, uni ~ PLC.DefaultUni)
    => ScriptInstance uni a
    -> Validator uni
    -> m (CompiledCode uni WrappedValidatorType)
checkValidatorScript _ (unValidatorScript -> (Script prog)) =
    case PLC.runQuote $ runExceptT @(PIR.Error PLC.DefaultUni (PIR.Provenance ())) $ Lift.typeCode (Proxy @WrappedValidatorType) prog of
        Right code -> pure code
        Left e     -> throwError $ WrongValidatorType $ show $ PLC.prettyPlcDef e

-- | Checks that the given redeemer script has the right type.
checkRedeemerValue
    :: forall inn uni m
    . (IsData (RedeemerType inn), MonadError (ConnectionError uni) m)
    => ScriptInstance uni inn
    -> RedeemerValue
    -> m (RedeemerType inn)
checkRedeemerValue _ (RedeemerValue d) =
    case fromData d of
        Just v  -> pure v
        Nothing -> throwError WrongRedeemerType

-- | Checks that the given data script has the right type.
checkDataScript
    :: forall a uni m . (IsData (DataType a), MonadError (ConnectionError uni) m)
    => ScriptInstance uni a
    -> DataValue
    -> m (DataType a)
checkDataScript _ (DataValue d) =
    case fromData d of
        Just v  -> pure v
        Nothing -> throwError WrongDataType

-- | Create a 'TypedScriptTxIn' from an existing 'TxIn' by checking the types of its parts.
typeScriptTxIn
    :: forall inn uni m
    . ( IsData (RedeemerType inn)
      , IsData (DataType inn)
      , MonadError (ConnectionError uni) m
      , uni ~ PLC.DefaultUni)
    => (TxOutRef -> Maybe (TxOutTx uni))
    -> ScriptInstance uni inn
    -> TxIn uni
    -> m (TypedScriptTxIn uni inn)
typeScriptTxIn lookupRef si TxIn{txInRef,txInType} = do
    (vs, rs, ds) <- case txInType of
        ConsumeScriptAddress vs rs ds -> pure (vs, rs, ds)
        x                             -> throwError $ WrongInType x
    _ <- checkValidatorScript si vs
    rsVal <- checkRedeemerValue si rs
    _ <- checkDataScript si ds
    typedOut <- typeScriptTxOutRef @inn lookupRef si txInRef
    pure $ makeTypedScriptTxIn si rsVal typedOut

-- | Create a 'PubKeyTxIn' from an existing 'TxIn' by checking that it has the right payment type.
typePubKeyTxIn
    :: forall uni m
    . (MonadError (ConnectionError uni) m)
    => TxIn uni
    -> m (PubKeyTxIn uni)
typePubKeyTxIn inn@TxIn{txInType} = do
    case txInType of
        ConsumePublicKeyAddress -> pure ()
        x                       -> throwError $ WrongInType x
    pure $ PubKeyTxIn inn

-- | Create a 'TypedScriptTxOut' from an existing 'TxOut' by checking the types of its parts.
typeScriptTxOut
    :: forall out uni m
    . ( IsData (DataType out)
      , MonadError (ConnectionError uni) m)
    => ScriptInstance uni out
    -> TxOutTx uni
    -> m (TypedScriptTxOut out)
typeScriptTxOut si TxOutTx{txOutTxTx=tx, txOutTxOut=TxOut{txOutAddress,txOutValue,txOutType}} = do
    dsh <- case txOutType of
        PayToScript ds -> pure ds
        x              -> throwError $ WrongOutType x
    ds <- case lookupData tx dsh of
        Just ds -> pure ds
        Nothing -> throwError $ NoData (txId tx) dsh
    checkValidatorAddress si txOutAddress
    dsVal <- checkDataScript si ds
    pure $ makeTypedScriptTxOut si dsVal txOutValue

-- | Create a 'TypedScriptTxOut' from an existing 'TxOut' by checking the types of its parts. To do this we
-- need to cross-reference against the validator script and be able to look up the 'TxOut' to which this
-- reference points.
typeScriptTxOutRef
    :: forall out uni m
    . ( IsData (DataType out)
      , MonadError (ConnectionError uni) m)
    => (TxOutRef -> Maybe (TxOutTx uni))
    -> ScriptInstance uni out
    -> TxOutRef
    -> m (TypedScriptTxOutRef out)
typeScriptTxOutRef lookupRef ct ref = do
    out <- case lookupRef ref of
        Just res -> pure res
        Nothing  -> throwError UnknownRef
    tyOut <- typeScriptTxOut @out ct out
    pure $ TypedScriptTxOutRef ref tyOut

-- | Create a 'PubKeyTxOUt' from an existing 'TxOut' by checking that it has the right payment type.
typePubKeyTxOut
    :: forall uni m
    . (MonadError (ConnectionError uni) m)
    => TxOut
    -> m PubKeyTxOut
typePubKeyTxOut out@TxOut{txOutType} = do
    case txOutType of
        PayToPubKey -> pure ()
        x           -> throwError $ WrongOutType x
    pure $ PubKeyTxOut out
