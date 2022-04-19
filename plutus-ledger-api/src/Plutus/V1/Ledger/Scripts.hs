{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE DeriveAnyClass      #-}
{-# LANGUAGE DeriveGeneric       #-}
{-# LANGUAGE DerivingVia         #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE FlexibleInstances   #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE NoImplicitPrelude   #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE PatternSynonyms     #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell     #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeOperators       #-}
{-# LANGUAGE ViewPatterns        #-}

{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# OPTIONS_GHC -fno-specialise #-}
{-# OPTIONS_GHC -fno-warn-name-shadowing #-}

-- | Functions for working with scripts on the ledger.
module Plutus.V1.Ledger.Scripts(
    -- * Scripts
    Script (..),
    scriptSize,
    fromCompiledCode,
    ScriptError (..),
    evaluateScript,
    runScript,
    runMintingPolicyScript,
    runStakeValidatorScript,
    applyValidator,
    applyMintingPolicyScript,
    applyStakeValidatorScript,
    applyArguments,
    -- * Script wrappers
    mkValidatorScript,
    Validator (..),
    unValidatorScript,
    Redeemer(..),
    Datum(..),
    mkMintingPolicyScript,
    MintingPolicy (..),
    unMintingPolicyScript,
    mkStakeValidatorScript,
    StakeValidator (..),
    unStakeValidatorScript,
    Context(..),
    -- * Hashes
    DatumHash(..),
    RedeemerHash(..),
    ScriptHash(..),
    ValidatorHash(..),
    MintingPolicyHash (..),
    StakeValidatorHash (..),
    ) where

import Prelude qualified as Haskell

import Codec.CBOR.Extras (SerialiseViaFlat (..))
import Codec.Serialise (Serialise, serialise)
import Control.DeepSeq (NFData)
import Control.Lens hiding (Context)
import Control.Monad.Except (MonadError, throwError)
import Data.ByteString.Lazy qualified as BSL
import Data.String
import Data.Text (Text)
import GHC.Generics (Generic)
import Plutus.V1.Ledger.Bytes (LedgerBytes (..))
import PlutusCore qualified as PLC
import PlutusCore.Data qualified as PLC
import PlutusCore.Evaluation.Machine.ExBudget qualified as PLC
import PlutusCore.Evaluation.Machine.Exception (ErrorWithCause (..), EvaluationError (..))
import PlutusCore.MkPlc qualified as PLC
import PlutusTx (CompiledCode, FromData (..), ToData (..), UnsafeFromData (..), getPlc, makeLift)
import PlutusTx.Builtins as Builtins
import PlutusTx.Builtins.Internal as BI
import PlutusTx.Prelude
import Prettyprinter
import Prettyprinter.Extras
import UntypedPlutusCore qualified as UPLC
import UntypedPlutusCore.Check.Scope qualified as UPLC
import UntypedPlutusCore.Evaluation.Machine.Cek qualified as UPLC

-- | A script on the chain. This is an opaque type as far as the chain is concerned.
newtype Script = Script { unScript :: UPLC.Program UPLC.DeBruijn PLC.DefaultUni PLC.DefaultFun () }
  deriving stock (Generic)
  deriving anyclass (NFData)
  -- See Note [Using Flat inside CBOR instance of Script]
  -- Important to go via 'WithSizeLimits' to ensure we enforce the size limits for constants
  -- Currently, this is off because the old implementation didn't actually work, so we need to be careful
  -- about introducing a working version
  deriving Serialise via (SerialiseViaFlat (UPLC.Program UPLC.DeBruijn PLC.DefaultUni PLC.DefaultFun ()))

{-| Note [Using Flat inside CBOR instance of Script]
`plutus-ledger` uses CBOR for data serialisation and `plutus-core` uses Flat. The
choice to use Flat was made to have a more efficient (most wins are in uncompressed
size) data serialisation format and use less space on-chain.

To make `plutus-ledger` work with scripts serialised with Flat, and keep the CBOR
format otherwise we have defined a Serialise instance for Script, which is a wrapper
over Programs serialised with Flat. The instance will see programs as an opaque
ByteString, which is the result of encoding programs using Flat.

Because Flat is not self-describing and it gets used in the encoding of Programs,
data structures that include scripts (for example, transactions) no-longer benefit
for CBOR's ability to self-describe it's format.
-}

{- Note [Eq and Ord for Scripts]
We need `Eq` and `Ord` instances for `Script`s mostly so we can put them in `Set`s.
However, the `Eq` instance for `Program`s is *alpha-equivalence*, and we don't
have a compatible `Ord` instance, nor is it easy to derive one.

So we piggyback off a different representation. In this instance we have two
options:
- Use the serialized form
- Use a hash
The problem with the latter is that we don't want to add a derived `Hashable` instance
for `Program`s that's not compatible with the `Eq` instance. We *could* add a derived
instance for `Program`s with de Bruijn indices, since in that case the derived `Eq`
coincides with alpha-equivalence. However, this might be faster.

For the moment we use the serialized form. We used to store the serialized form directly
in `Script`, but that led to a lot of deserializing and reserializing in `applyProgram`.
Here we have to serialize when we do `Eq` or `Ord` operations, but this happens comparatively
infrequently (I believe).
-}
instance Haskell.Eq Script where
    a == b = Builtins.toBuiltin (BSL.toStrict (serialise a)) == Builtins.toBuiltin (BSL.toStrict (serialise b))

instance Haskell.Ord Script where
    a `compare` b = Builtins.toBuiltin (BSL.toStrict (serialise a)) `compare` Builtins.toBuiltin (BSL.toStrict (serialise b))

instance Haskell.Show Script where
    showsPrec _ _ = Haskell.showString "<Script>"

-- | The size of a 'Script'. No particular interpretation is given to this, other than that it is
-- proportional to the serialized size of the script.
scriptSize :: Script -> Integer
scriptSize (Script s) = UPLC.programSize s

-- | Turn a 'CompiledCode' (usually produced by 'compile') into a 'Script' for use with this package.
fromCompiledCode :: CompiledCode a -> Script
fromCompiledCode = Script . toNameless . getPlc
    where
      toNameless :: UPLC.Program UPLC.NamedDeBruijn PLC.DefaultUni PLC.DefaultFun ()
                 -> UPLC.Program UPLC.DeBruijn PLC.DefaultUni PLC.DefaultFun ()
      toNameless = over UPLC.progTerm $ UPLC.termMapNames UPLC.unNameDeBruijn

data ScriptError =
    EvaluationError [Text] Haskell.String -- ^ Expected behavior of the engine (e.g. user-provided error)
    | EvaluationException Haskell.String Haskell.String -- ^ Unexpected behavior of the engine (a bug)
    deriving stock (Haskell.Show, Haskell.Eq, Generic)
    deriving anyclass (NFData)

applyArguments :: Script -> [PLC.Data] -> Script
applyArguments (Script p) args =
    let termArgs = Haskell.fmap (PLC.mkConstant ()) args
        applied t = PLC.mkIterApp () t termArgs
    in Script $ over UPLC.progTerm applied p

-- | Evaluate a script, returning the trace log.
evaluateScript :: forall m . (MonadError ScriptError m) => Script -> m (PLC.ExBudget, [Text])
evaluateScript s =
    let namedT = UPLC.termMapNames UPLC.fakeNameDeBruijn $ UPLC._progTerm $ unScript s
    in case UPLC.checkScope @UPLC.FreeVariableError namedT of
        Left fvError -> throwError $ EvaluationError [] ("FreeVariableFailure of" ++ Haskell.show fvError)
        _ -> let (result, UPLC.TallyingSt _ budget, logOut) = UPLC.runCekDeBruijn PLC.defaultCekParameters UPLC.tallying UPLC.logEmitter namedT
            in case result of
                 Right _ -> Haskell.pure (budget, logOut)
                 Left errWithCause@(ErrorWithCause err cause) -> throwError $ case err of
                     InternalEvaluationError internalEvalError -> EvaluationException (Haskell.show errWithCause) (PLC.show internalEvalError)
                     UserEvaluationError evalError -> EvaluationError logOut (mkError evalError cause) -- TODO fix this error channel fuckery

-- | Create an error message from the contents of an ErrorWithCause.
-- If the cause of an error is a `Just t` where `t = b v0 v1 .. vn` for some builtin `b` then
-- the error will be a "BuiltinEvaluationFailure" otherwise it will be `PLC.show evalError`
mkError :: UPLC.CekUserError -> Maybe (UPLC.Term UPLC.NamedDeBruijn PLC.DefaultUni PLC.DefaultFun ()) -> String
mkError evalError Nothing = PLC.show evalError
mkError evalError (Just t) =
  case findBuiltin t of
    Just b  -> "BuiltinEvaluationFailure of " ++ Haskell.show b
    Nothing -> PLC.show evalError
  where
    findBuiltin :: UPLC.Term UPLC.NamedDeBruijn PLC.DefaultUni PLC.DefaultFun () -> Maybe PLC.DefaultFun
    findBuiltin t = case t of
       UPLC.Apply _ t _   -> findBuiltin t
       UPLC.Builtin _ fun -> Just fun
       -- These two *really shouldn't* appear but
       -- we are future proofing for a day when they do
       UPLC.Force _ t     -> findBuiltin t
       UPLC.Delay _ t     -> findBuiltin t
       -- Future proofing for eta-expanded builtins
       UPLC.LamAbs _ _ t  -> findBuiltin t
       UPLC.Var _ _       -> Nothing
       UPLC.Constant _ _  -> Nothing
       UPLC.Error _       -> Nothing

mkValidatorScript :: CompiledCode (BuiltinData -> BuiltinData -> BuiltinData -> ()) -> Validator
mkValidatorScript = Validator . fromCompiledCode

unValidatorScript :: Validator -> Script
unValidatorScript = getValidator

mkMintingPolicyScript :: CompiledCode (BuiltinData -> BuiltinData -> ()) -> MintingPolicy
mkMintingPolicyScript = MintingPolicy . fromCompiledCode

unMintingPolicyScript :: MintingPolicy -> Script
unMintingPolicyScript = getMintingPolicy

mkStakeValidatorScript :: CompiledCode (BuiltinData -> BuiltinData -> ()) -> StakeValidator
mkStakeValidatorScript = StakeValidator . fromCompiledCode

unStakeValidatorScript :: StakeValidator -> Script
unStakeValidatorScript = getStakeValidator

-- | 'Validator' is a wrapper around 'Script's which are used as validators in transaction outputs.
newtype Validator = Validator { getValidator :: Script }
  deriving stock (Generic)
  deriving newtype (Haskell.Eq, Haskell.Ord, Serialise)
  deriving anyclass (NFData)
  deriving Pretty via (PrettyShow Validator)

instance Haskell.Show Validator where
    show = const "Validator { <script> }"

-- | 'Datum' is a wrapper around 'Data' values which are used as data in transaction outputs.
newtype Datum = Datum { getDatum :: BuiltinData  }
  deriving stock (Generic, Haskell.Show)
  deriving newtype (Haskell.Eq, Haskell.Ord, Eq, ToData, FromData, UnsafeFromData, Pretty)
  deriving anyclass (NFData)

-- | 'Redeemer' is a wrapper around 'Data' values that are used as redeemers in transaction inputs.
newtype Redeemer = Redeemer { getRedeemer :: BuiltinData }
  deriving stock (Generic, Haskell.Show)
  deriving newtype (Haskell.Eq, Haskell.Ord, Eq, ToData, FromData, UnsafeFromData, Pretty)
  deriving anyclass (NFData)

-- | 'MintingPolicy' is a wrapper around 'Script's which are used as validators for minting constraints.
newtype MintingPolicy = MintingPolicy { getMintingPolicy :: Script }
  deriving stock (Generic)
  deriving newtype (Haskell.Eq, Haskell.Ord, Serialise)
  deriving anyclass (NFData)
  deriving Pretty via (PrettyShow MintingPolicy)

instance Haskell.Show MintingPolicy where
    show = const "MintingPolicy { <script> }"

-- | 'StakeValidator' is a wrapper around 'Script's which are used as validators for withdrawals and stake address certificates.
newtype StakeValidator = StakeValidator { getStakeValidator :: Script }
  deriving stock (Generic)
  deriving newtype (Haskell.Eq, Haskell.Ord, Serialise)
  deriving anyclass (NFData)
  deriving Pretty via (PrettyShow MintingPolicy)

instance Haskell.Show StakeValidator where
    show = const "StakeValidator { <script> }"

-- | Script runtime representation of a @Digest SHA256@.
newtype ScriptHash =
    ScriptHash { getScriptHash :: Builtins.BuiltinByteString }
    deriving (IsString, Haskell.Show, Pretty) via LedgerBytes
    deriving stock (Generic)
    deriving newtype (Haskell.Eq, Haskell.Ord, Eq, Ord, ToData, FromData, UnsafeFromData)
    deriving anyclass (NFData)

-- | Script runtime representation of a @Digest SHA256@.
newtype ValidatorHash =
    ValidatorHash Builtins.BuiltinByteString
    deriving (IsString, Haskell.Show, Pretty) via LedgerBytes
    deriving stock (Generic)
    deriving newtype (Haskell.Eq, Haskell.Ord, Eq, Ord, ToData, FromData, UnsafeFromData)
    deriving anyclass (NFData)

-- | Script runtime representation of a @Digest SHA256@.
newtype DatumHash =
    DatumHash Builtins.BuiltinByteString
    deriving (IsString, Haskell.Show, Pretty) via LedgerBytes
    deriving stock (Generic)
    deriving newtype (Haskell.Eq, Haskell.Ord, Eq, Ord, ToData, FromData, UnsafeFromData)
    deriving anyclass (NFData)

-- | Script runtime representation of a @Digest SHA256@.
newtype RedeemerHash =
    RedeemerHash Builtins.BuiltinByteString
    deriving (IsString, Haskell.Show, Pretty) via LedgerBytes
    deriving stock (Generic)
    deriving newtype (Haskell.Eq, Haskell.Ord, Eq, Ord, ToData, FromData, UnsafeFromData)
    deriving anyclass (NFData)

-- | Script runtime representation of a @Digest SHA256@.
newtype MintingPolicyHash =
    MintingPolicyHash Builtins.BuiltinByteString
    deriving (IsString, Haskell.Show, Pretty) via LedgerBytes
    deriving stock (Generic)
    deriving newtype (Haskell.Eq, Haskell.Ord, Eq, Ord, ToData, FromData, UnsafeFromData)
    deriving anyclass (NFData)

-- | Script runtime representation of a @Digest SHA256@.
newtype StakeValidatorHash =
    StakeValidatorHash Builtins.BuiltinByteString
    deriving (IsString, Haskell.Show, Pretty) via LedgerBytes
    deriving stock (Generic)
    deriving newtype (Haskell.Eq, Haskell.Ord, Eq, Ord, ToData, FromData, UnsafeFromData)
    deriving anyclass (NFData)

-- | Information about the state of the blockchain and about the transaction
--   that is currently being validated, represented as a value in 'Data'.
newtype Context = Context BuiltinData
    deriving newtype (Pretty, Haskell.Show)

-- | Apply a 'Validator' to its 'Context', 'Datum', and 'Redeemer'.
applyValidator
    :: Context
    -> Validator
    -> Datum
    -> Redeemer
    -> Script
applyValidator (Context (BuiltinData valData)) (Validator validator) (Datum (BuiltinData datum)) (Redeemer (BuiltinData redeemer)) =
    applyArguments validator [datum, redeemer, valData]

-- | Evaluate a 'Validator' with its 'Context', 'Datum', and 'Redeemer', returning the log.
runScript
    :: (MonadError ScriptError m)
    => Context
    -> Validator
    -> Datum
    -> Redeemer
    -> m (PLC.ExBudget, [Text])
runScript context validator datum redeemer =
    evaluateScript (applyValidator context validator datum redeemer)

-- | Apply 'MintingPolicy' to its 'Context' and 'Redeemer'.
applyMintingPolicyScript
    :: Context
    -> MintingPolicy
    -> Redeemer
    -> Script
applyMintingPolicyScript (Context (BuiltinData valData)) (MintingPolicy validator) (Redeemer (BuiltinData red)) =
    applyArguments validator [red, valData]

-- | Evaluate a 'MintingPolicy' with its 'Context' and 'Redeemer', returning the log.
runMintingPolicyScript
    :: (MonadError ScriptError m)
    => Context
    -> MintingPolicy
    -> Redeemer
    -> m (PLC.ExBudget, [Text])
runMintingPolicyScript context mps red =
    evaluateScript (applyMintingPolicyScript context mps red)

-- | Apply 'StakeValidator' to its 'Context' and 'Redeemer'.
applyStakeValidatorScript
    :: Context
    -> StakeValidator
    -> Redeemer
    -> Script
applyStakeValidatorScript (Context (BuiltinData valData)) (StakeValidator validator) (Redeemer (BuiltinData red)) =
    applyArguments validator [red, valData]

-- | Evaluate a 'StakeValidator' with its 'Context' and 'Redeemer', returning the log.
runStakeValidatorScript
    :: (MonadError ScriptError m)
    => Context
    -> StakeValidator
    -> Redeemer
    -> m (PLC.ExBudget, [Text])
runStakeValidatorScript context wps red =
    evaluateScript (applyStakeValidatorScript context wps red)

makeLift ''ScriptHash

makeLift ''ValidatorHash

makeLift ''MintingPolicyHash

makeLift ''StakeValidatorHash

makeLift ''DatumHash

makeLift ''RedeemerHash

makeLift ''Datum

makeLift ''Redeemer
