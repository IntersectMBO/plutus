{-# LANGUAGE ConstraintKinds           #-}
{-# LANGUAGE DataKinds                 #-}
{-# LANGUAGE EmptyCase                 #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleContexts          #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE GADTs                     #-}
{-# LANGUAGE MultiParamTypeClasses     #-}
{-# LANGUAGE NamedFieldPuns            #-}
{-# LANGUAGE PolyKinds                 #-}
{-# LANGUAGE ScopedTypeVariables       #-}
{-# LANGUAGE TemplateHaskell           #-}
{-# LANGUAGE TypeApplications          #-}
{-# LANGUAGE TypeFamilies              #-}
{-# LANGUAGE TypeOperators             #-}
{-# LANGUAGE UndecidableInstances      #-}
{-# LANGUAGE ViewPatterns              #-}
{-# LANGUAGE Rank2Types              #-}
-- | Typed transactions. This module defines typed versions of various ledger types. The ultimate
-- goal is to make sure that the script types attached to inputs and outputs line up, to avoid
-- type errors at validation time.
module Ledger.Typed.Tx where

import qualified Ledger.Ada                   as Ada
import           Ledger.Crypto
import qualified Ledger.Interval              as Interval
import           Ledger.Scripts
import           Ledger.Slot
import           Ledger.Tx                    hiding (scriptAddress)
import qualified Ledger.Tx                    as Tx
import qualified Ledger.Validation            as Validation
import qualified Ledger.Value                 as Value

import           Ledger.Typed.TypeUtils

import qualified Language.PlutusCore          as PLC
import qualified Language.PlutusCore.Pretty   as PLC

import           Language.PlutusTx
import qualified Language.PlutusTx.Builtins   as PlutusTx
import           Language.PlutusTx.Lift       as Lift
import           Language.PlutusTx.Lift.Class as Lift

import qualified Language.PlutusIR.Compiler   as PIR

import           Data.Coerce
import           Data.Kind
import           Data.List                    (foldl')
import           Data.Proxy
import qualified Data.Set                     as Set

import           Control.Monad.Except

-- | A class that associates a type standing for a connection type with two types, the type of the redeemer
-- and the data script for that connection type.
class ScriptType (a :: Type) where
    -- | The type of the redeemers of this connection type.
    type RedeemerType a :: Type
    -- | The type of the data of this connection type.
    type DataType a :: Type

    -- Defaults
    type instance RedeemerType a = ()
    type instance DataType  a = ()

-- | The type of validators for the given connection type.
type ValidatorType (a :: Type) = DataType a -> RedeemerType a -> Validation.PendingTx -> Bool

-- | The type of a connection.
data ScriptInstance (a :: Type) where
    Validator :: ScriptType a => CompiledCode (ValidatorType a) -> ScriptInstance a

-- | Get the address for a script instance.
scriptAddress :: ScriptInstance a -> Address
scriptAddress = Tx.scriptAddress . validatorScript

-- | Get the validator script for a script instance.
validatorScript :: ScriptInstance a -> ValidatorScript
validatorScript (Validator vc) = ValidatorScript $ fromCompiledCode vc

-- | Defunctionalized symbol for use with 'Apply'.
data SealedDataTypeSym :: Type ~> Type
type instance Apply SealedDataTypeSym a = PlutusTx.Sealed (HashedDataScript (DataType a))
-- | Defunctionalized symbol for use with 'Apply'.
data DataTypeSym :: Type ~> Type
type instance Apply DataTypeSym a = DataType a

-- | The type of a redeemer function for the given output types and input type.
type RedeemerFunctionType (outs :: [Type]) (inn :: Type) = Uncurry (Map SealedDataTypeSym outs) (RedeemerType inn)

-- | Given code for a value of the simple redeemer type, constructs code of the redeemer function type by
-- ignoring all the data script arguments.
--
-- Requires a witness for the list of outputs. This should be automatically provided if it is a concrete list.
ignoreDataScripts
    :: forall (outs :: [Type]) (inn :: Type)
    . (All Typeable (Map SealedDataTypeSym outs), KnownSpine outs)
    => Proxy outs
    -> Proxy inn
    -> CompiledCode (RedeemerType inn)
    -> CompiledCode (RedeemerFunctionType outs inn)
ignoreDataScripts _ = ignoreDataScripts' (spine @outs)

-- | As 'ignoreDataScripts', but takes the witness explicitly.
ignoreDataScripts'
    :: forall (outs :: [Type]) (inn :: Type)
    . (All Typeable (Map SealedDataTypeSym outs))
    => Spine outs
    -> Proxy inn
    -> CompiledCode (RedeemerType inn)
    -> CompiledCode (RedeemerFunctionType outs inn)
ignoreDataScripts' wit _ =
    ignoreArgs
    (mapSpine (Proxy @SealedDataTypeSym) wit)
    (Proxy @(RedeemerType inn))

-- | Given code for a value of a result type, constructs code for a function that ignores
-- a list of arguments of the given types to produce the original code.
ignoreArgs
    :: forall (args :: [Type]) (r :: Type)
    . (All Typeable args)
    => Spine args
    -> Proxy r
    -> CompiledCode r
    -> CompiledCode (Uncurry args r)
ignoreArgs NilSpine _ c = c
ignoreArgs (ConsSpine tspine) p c = Lift.unsafeConstCode Proxy $ ignoreArgs tspine p c

-- | A 'TxIn' tagged by two phantom types: a list of the types of the data scripts in the transaction; and the connection type of the input.
newtype TypedScriptTxIn (outs :: [Type]) a = TypedScriptTxIn { unTypedScriptTxIn :: TxIn }
-- | Create a 'TypedScriptTxIn' from a correctly-typed validator, redeemer, and output ref.
makeTypedScriptTxIn
    :: forall inn (outs :: [Type])
    . ScriptInstance inn
    -> CompiledCode (RedeemerFunctionType outs inn)
    -> TypedScriptTxOutRef inn
    -> TypedScriptTxIn outs inn
makeTypedScriptTxIn si r (TypedScriptTxOutRef ref) =
    let vs = validatorScript si
        rs = RedeemerScript (fromCompiledCode r)
        txInType = ConsumeScriptAddress vs rs
    in TypedScriptTxIn @outs @inn $ TxInOf ref txInType

-- | A public-key 'TxIn'. We need this to be sure that it is not a script input.
newtype PubKeyTxIn = PubKeyTxIn { unPubKeyTxIn :: TxIn }
-- | Create a 'PubKeyTxIn'.
makePubKeyTxIn :: TxOutRef -> PubKey -> PubKeyTxIn
makePubKeyTxIn ref pubkey = PubKeyTxIn $ TxInOf ref $ ConsumePublicKeyAddress pubkey

-- | A 'TxOut' tagged by a phantom type: and the connection type of the output.
newtype TypedScriptTxOut a = TypedScriptTxOut { unTypedScriptTxOut :: TxOut }
-- | Create a 'TypedScriptTxOut' from a correctly-typed data script, an address, and a value.
makeTypedScriptTxOut
    :: forall out
    . ScriptInstance out
    -> CompiledCode (DataType out)
    -> Value.Value
    -> TypedScriptTxOut out
makeTypedScriptTxOut ct d value =
    let outTy = PayToScript (DataScript (fromCompiledCode d))
    in TypedScriptTxOut @out $ TxOutOf (scriptAddress ct) value outTy

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
    tyTxTypedTxIns   :: HListF (TypedScriptTxIn outs) ins,
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
    tyTxForge = Value.zero,
    tyTxValidRange = Interval.always
    }

-- | Adds a 'TypedScriptTxOut' to a 'TypedTx'.
--
-- Adding a new typed transaction output is only safe if there are no typed transaction
-- inputs yet. Otherwise those inputs would need to change to take the new data script as
-- an argument.
addTypedTxOut
    :: forall outs newOut
    . TypedScriptTxOut newOut
    -> TypedTx '[] outs
    -> TypedTx '[] (newOut ': outs)
-- We're changing the type so we can't use record update syntax :'(
addTypedTxOut out TypedTx {
    tyTxTypedTxOuts,
    tyTxPubKeyTxOuts,
    tyTxTypedTxIns=HNilF,
    tyTxPubKeyTxIns,
    tyTxForge,
    tyTxValidRange } = TypedTx {
      tyTxTypedTxOuts=HConsF out tyTxTypedTxOuts,
      tyTxPubKeyTxOuts,
      tyTxTypedTxIns=HNilF,
      tyTxPubKeyTxIns,
      tyTxForge,
      tyTxValidRange }

-- | Adds a 'TypedScriptTxIn' to a 'TypedTx'.
addTypedTxIn
    :: forall ins outs newIn
    . TypedScriptTxIn outs newIn
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
    . TypedScriptTxIn outs newIn
    -> TypedTxSomeIns outs
    -> TypedTxSomeIns outs
addSomeTypedTxIn inn (TypedTxSomeIns tx) = TypedTxSomeIns $ addTypedTxIn inn tx

-- | Adds many homogeneous 'TypedScriptTxIn' to a 'TypedTx'.
addManyTypedTxIns
    :: forall (ins :: [Type]) (outs :: [Type]) (newIn :: Type)
    . [TypedScriptTxIn outs newIn]
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
    txFee = Ada.zero,
    txValidRange = tyTxValidRange,
    txSignatures = mempty }

-- Checking
-- TODO: these could be in a separate module

-- | An error we can get while trying to type an existing transaction part.
data ConnectionError =
    WrongValidatorHash ValidatorHash ValidatorHash
    | WrongValidator ValidatorScript ValidatorScript
    | WrongOutType TxOutType
    | WrongInType TxInType
    | WrongValidatorType String
    | WrongRedeemerType String
    | WrongDataType String
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
    . ( Lift.Typeable (DataType a)
      , Lift.Typeable (RedeemerType a)
      , MonadError ConnectionError m)
    => ScriptInstance a
    -> ValidatorScript
    -> m (CompiledCode (ValidatorType a))
checkValidatorScript _ (ValidatorScript (Script prog)) =
    case PLC.runQuote $ runExceptT @(PIR.Error (PIR.Provenance ())) $ Lift.typeCode (Proxy @(ValidatorType a)) prog of
        Right code -> pure code
        Left e     -> throwError $ WrongValidatorType $ show $ PLC.prettyPlcDef e

-- | Checks that the given redeemer script has the right type.
checkRedeemerScript
    :: forall inn (outs :: [Type]) m
    . ( Lift.Typeable (RedeemerFunctionType outs inn)
      , MonadError ConnectionError m)
    => ScriptInstance inn
    -> Proxy outs
    -> RedeemerScript
    -> m (CompiledCode (RedeemerFunctionType outs inn))
checkRedeemerScript _ _ (RedeemerScript (Script prog)) =
    case PLC.runQuote $ runExceptT @(PIR.Error (PIR.Provenance ())) $ Lift.typeCode (Proxy @(RedeemerFunctionType outs inn)) prog of
        Right code -> pure code
        Left e     -> throwError $ WrongRedeemerType $ show $ PLC.prettyPlcDef e

-- | Checks that the given data script has the right type.
checkDataScript
    :: forall a m . (Lift.Typeable (DataType a), MonadError ConnectionError m)
    => ScriptInstance a
    -> DataScript
    -> m (CompiledCode (DataType a))
checkDataScript _ (DataScript (Script prog)) =
    case PLC.runQuote $ runExceptT @(PIR.Error (PIR.Provenance ())) $ Lift.typeCode (Proxy @(DataType a)) prog of
        Right code -> pure code
        Left e     -> throwError $ WrongDataType $ show $ PLC.prettyPlcDef e

-- | Create a 'TypedScriptTxIn' from an existing 'TxIn' by checking the types of its parts.
typeScriptTxIn
    :: forall inn (outs :: [Type]) m
    . ( Lift.Typeable (DataType inn)
      , Lift.Typeable (RedeemerType inn)
      , Lift.Typeable (RedeemerFunctionType outs inn)
      , MonadError ConnectionError m)
    => (TxOutRef -> Maybe TxOut)
    -> ScriptInstance inn
    -> TxIn
    -> m (TypedScriptTxIn outs inn)
typeScriptTxIn lookupRef si TxInOf{txInRef,txInType} = do
    (vs, rs) <- case txInType of
        ConsumeScriptAddress vs rs -> pure (vs, rs)
        x                          -> throwError $ WrongInType x
    _ <- checkValidatorScript si vs
    rsCode <- checkRedeemerScript si (Proxy @outs) rs
    -- If this succeeds we're okay
    typedOut <- typeScriptTxOutRef @inn lookupRef si txInRef
    pure $ makeTypedScriptTxIn si rsCode typedOut

-- | Create a 'PubKeyTxIn' from an existing 'TxIn' by checking that it has the right payment type.
typePubKeyTxIn
    :: forall m
    . (MonadError ConnectionError m)
    => TxIn
    -> m PubKeyTxIn
typePubKeyTxIn inn@TxInOf{txInType} = do
    case txInType of
        ConsumePublicKeyAddress _ -> pure ()
        x                         -> throwError $ WrongInType x
    pure $ PubKeyTxIn inn

-- | Create a 'TypedScriptTxOut' from an existing 'TxOut' by checking the types of its parts.
typeScriptTxOut
    :: forall out m
    . ( Lift.Typeable (DataType out)
      , MonadError ConnectionError m)
    => ScriptInstance out
    -> TxOut
    -> m (TypedScriptTxOut out)
typeScriptTxOut si TxOutOf{txOutAddress=AddressOf addrHash,txOutValue,txOutType} = do
    ds <- case txOutType of
        PayToScript ds -> pure ds
        x              -> throwError $ WrongOutType x
    checkValidatorHash si (plcValidatorDigest addrHash)
    dsCode <- checkDataScript si ds
    pure $ makeTypedScriptTxOut si dsCode txOutValue

-- | Create a 'TypedScriptTxOut' from an existing 'TxOut' by checking the types of its parts. To do this we
-- need to cross-reference against the validator script and be able to look up the 'TxOut' to which this
-- reference points.
typeScriptTxOutRef
    :: forall out m
    . ( Lift.Typeable (DataType out)
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
typePubKeyTxOut out@TxOutOf{txOutType} = do
    case txOutType of
        PayToPubKey _ -> pure ()
        x             -> throwError $ WrongOutType x
    pure $ PubKeyTxOut out
