{-# LANGUAGE DataKinds          #-}
{-# LANGUAGE DeriveAnyClass     #-}
{-# LANGUAGE DeriveGeneric      #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleContexts   #-}
{-# LANGUAGE FlexibleInstances  #-}
{-# LANGUAGE LambdaCase         #-}
{-# LANGUAGE OverloadedStrings  #-}
{-# LANGUAGE TemplateHaskell    #-}
{-# LANGUAGE ViewPatterns       #-}
{-# LANGUAGE NoImplicitPrelude  #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# OPTIONS_GHC -fno-ignore-interface-pragmas #-}
-- | Functions for working with scripts on the ledger.
module Ledger.Scripts(
    -- * Scripts
    Script,
    scriptSize,
    fromCompiledCode,
    compileScript,
    lifted,
    applyScript,
    Checking (..),
    evaluateScript,
    runScript,
    -- * Script wrappers
    ValidatorScript(..),
    RedeemerScript(..),
    DataScript(..),
    ValidationData(..),
    -- * Example scripts
    unitRedeemer,
    unitData
    ) where

import qualified Prelude                                  as Haskell

import qualified Codec.CBOR.Write                         as Write
import           Codec.Serialise                          (serialise)
import           Codec.Serialise.Class                    (Serialise, encode)
import           Data.Aeson                               (FromJSON (parseJSON), ToJSON (toJSON))
import qualified Data.Aeson                               as JSON
import qualified Data.Aeson.Extras                        as JSON
import qualified Data.ByteArray                           as BA
import           GHC.Generics                             (Generic)
import qualified Language.Haskell.TH                      as TH
import qualified Language.PlutusCore                      as PLC
import qualified Language.PlutusCore.Constant.Dynamic     as PLC
import qualified Language.PlutusCore.Evaluation.Result    as PLC
import           Language.PlutusTx.Evaluation             (evaluateCekTrace)
import           Language.PlutusTx.Lift                   (unsafeLiftCode)
import           Language.PlutusTx.Lift.Class             (Lift)
import           Language.PlutusTx                        (CompiledCode, compile, getPlc)
import           Language.PlutusTx.Prelude

-- | A script on the chain. This is an opaque type as far as the chain is concerned.
--
-- Note: the program inside the 'Script' should have normalized types.
newtype Script = Script { unScript :: PLC.Program PLC.TyName PLC.Name () }
  deriving newtype (Serialise)

{- Note [Normalized types in Scripts]
The Plutus Tx plugin and lifting machinery does not necessarily produce programs
with normalized types, but we are supposed to put programs on the chain *with*
normalized types.

So we normalize types when we turn things into 'Script's. The only operation we
do after that is applying 'Script's together, which preserves type normalization.
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
instance Eq Script where
    {-# INLINABLE (==) #-}
    a == b = serialise a == serialise b

instance Haskell.Eq Script where
    a == b = serialise a == serialise b

instance Ord Script where
    {-# INLINABLE compare #-}
    a `compare` b = serialise a `compare` serialise b

instance Haskell.Ord Script where
    a `compare` b = serialise a `compare` serialise b

data Checking = Typecheck | DontCheck

-- | The size of a 'Script'. No particular interpretation is given to this, other than that it is
-- proportional to the serialized size of the script.
scriptSize :: Script -> Integer
scriptSize (Script s) = PLC.programSize s

-- See Note [Normalized types in Scripts]
-- | Turn a 'CompiledCode' (usually produced by 'compile') into a 'Script' for use with this package.
fromCompiledCode :: CompiledCode a -> Script
fromCompiledCode = Script . PLC.runQuote . PLC.normalizeTypesFullInProgram . getPlc

-- | Compile a quoted Haskell expression to a 'Script'.
compileScript :: TH.Q (TH.TExp a) -> TH.Q (TH.TExp Script)
compileScript a = [|| fromCompiledCode $$(compile a) ||]

-- | Given two 'Script's, compute the 'Script' that consists of applying the first to the second.
applyScript :: Script -> Script -> Script
applyScript (unScript -> s1) (unScript -> s2) = Script $ s1 `PLC.applyProgram` s2

-- | Evaluate a script, returning the trace log and a boolean indicating whether
-- evaluation was successful.
evaluateScript :: Checking -> Script -> ([String], Bool)
evaluateScript checking (unScript -> s) =
    let
        plcChecks :: PLC.Program PLC.TyName PLC.Name () -> Either (PLC.Error ()) (PLC.Type PLC.TyName ())
        plcChecks p = PLC.runQuoteT $ do
            types <- PLC.getStringBuiltinTypes ()
            -- We should be normalized, so we can use the on-chain config
            -- See Note [Normalized types in Scripts]
            let config = PLC.defOnChainConfig { PLC._tccDynamicBuiltinNameTypes = types }
            PLC.unNormalized Haskell.<$> PLC.typecheckPipeline config p
    in case checking of
        DontCheck -> PLC.isEvaluationSuccess Haskell.<$> evaluateCekTrace s
        Typecheck -> case plcChecks s of
            -- TODO: do something with the error
            Left _ -> ([], False)
            -- we don't care about the inferred type, we just care that type inference succeeded
            Right _ -> PLC.isEvaluationSuccess Haskell.<$> evaluateCekTrace s

instance ToJSON Script where
  toJSON = JSON.String . JSON.encodeSerialise

instance FromJSON Script where
  parseJSON = JSON.decodeSerialise

-- See Note [Normalized types in Scripts]
-- | Lift a Haskell value into the corresponding 'Script'. This allows you to create
-- 'Script's at runtime, whereas 'compileScript' allows you to do so at compile time.
lifted :: Lift a => a -> Script
lifted = fromCompiledCode . unsafeLiftCode

-- | 'ValidatorScript' is a wrapper around 'Script's which are used as validators in transaction outputs.
newtype ValidatorScript = ValidatorScript { getValidator :: Script }
  deriving stock (Generic)
  deriving newtype (Haskell.Eq, Haskell.Ord, Eq, Ord, Serialise)
  deriving anyclass (ToJSON, FromJSON)

instance Show ValidatorScript where
    show = const "ValidatorScript { <script> }"

instance BA.ByteArrayAccess ValidatorScript where
    length =
        BA.length . Write.toStrictByteString . encode
    withByteArray =
        BA.withByteArray . Write.toStrictByteString . encode

-- | 'DataScript' is a wrapper around 'Script's which are used as data scripts in transaction outputs.
newtype DataScript = DataScript { getDataScript :: Script  }
  deriving stock (Generic)
  deriving newtype (Haskell.Eq, Haskell.Ord, Eq, Ord, Serialise)
  deriving anyclass (ToJSON, FromJSON)

instance Show DataScript where
    show = const "DataScript { <script> }"

instance BA.ByteArrayAccess DataScript where
    length =
        BA.length . Write.toStrictByteString . encode
    withByteArray =
        BA.withByteArray . Write.toStrictByteString . encode

-- | 'RedeemerScript' is a wrapper around 'Script's that are used as redeemer scripts in transaction inputs.
newtype RedeemerScript = RedeemerScript { getRedeemer :: Script }
  deriving stock (Generic)
  deriving newtype (Haskell.Eq, Haskell.Ord, Eq, Ord, Serialise)
  deriving anyclass (ToJSON, FromJSON)

instance Show RedeemerScript where
    show = const "RedeemerScript { <script> }"

instance BA.ByteArrayAccess RedeemerScript where
    length =
        BA.length . Write.toStrictByteString . encode
    withByteArray =
        BA.withByteArray . Write.toStrictByteString . encode

-- | Information about the state of the blockchain and about the transaction
--   that is currently being validated, represented as a value in a 'Script'.
newtype ValidationData = ValidationData Script
    deriving stock (Generic)
    deriving anyclass (ToJSON, FromJSON)

instance Show ValidationData where
    show = const "ValidationData { <script> }"

-- | Evaluate a validator script with the given arguments, returning the log and a boolean indicating whether evaluation was successful.
runScript :: Checking -> ValidationData -> ValidatorScript -> DataScript -> RedeemerScript -> ([String], Bool)
runScript checking (ValidationData valData) (ValidatorScript validator) (DataScript dataScript) (RedeemerScript redeemer) =
    let
        -- See Note [Scripts returning Bool]
        applied = checker `applyScript` (((validator `applyScript` dataScript) `applyScript` redeemer) `applyScript` valData)
    in evaluateScript checking applied

{- Note [Scripts returning Bool]
It used to be that the signal for validation failure was a script being `error`. This is nice for the validator, since
you can determine whether the script evaluation is error-or-not without having to look at what the result actually
*is* if there is one.

However, from the script author's point of view, it would be nicer to return a Bool, since otherwise you end up doing a
lot of `if realCondition then () else error ()` which is rubbish.

So we changed the result type to be Bool. But now we have to answer the question of how the validator knows what the
result value is. All *sorts* of terms can be True or False in disguise. The easiest way to tell is by reducing it
to the previous problem: apply a function which does a pattern match and returns error in the case of False and ()
otherwise. Then, as before, we just check for error in the overall evaluation.
-}

-- | @()@ as a data script.
unitData :: DataScript
unitData = DataScript $ fromCompiledCode $$(compile [|| () ||])

-- | @()@ as a redeemer.
unitRedeemer :: RedeemerScript
unitRedeemer = RedeemerScript $ fromCompiledCode $$(compile [|| () ||])

-- | @()@ as a redeemer.
checker :: Script
checker = fromCompiledCode $$(compile [|| check ||])
