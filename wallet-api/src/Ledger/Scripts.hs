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
{-# OPTIONS_GHC -fno-warn-orphans #-}
-- | Functions for working with scripts on the ledger.
module Ledger.Scripts(
    -- * Scripts
    Script,
    scriptSize,
    fromCompiledCode,
    compileScript,
    lifted,
    applyScript,
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

import qualified Codec.CBOR.Write                         as Write
import           Codec.Serialise                          (deserialise, serialise)
import           Codec.Serialise.Class                    (Serialise, encode)
import           Data.Aeson                               (FromJSON (parseJSON), ToJSON (toJSON))
import qualified Data.Aeson                               as JSON
import qualified Data.Aeson.Extras                        as JSON
import qualified Data.ByteArray                           as BA
import           Data.Maybe                               (isJust)
import           GHC.Generics                             (Generic)
import qualified Language.Haskell.TH                      as TH
import qualified Language.PlutusCore                      as PLC
import           Language.PlutusTx.Evaluation             (evaluateCekTrace)
import           Language.PlutusTx.Lift                   (unsafeLiftProgram)
import           Language.PlutusTx.Lift.Class             (Lift)
import           Language.PlutusTx.TH                     (CompiledCode, compile, getSerializedPlc)
import           PlutusPrelude

-- | A script on the chain. This is an opaque type as far as the chain is concerned.
newtype Script = Script { getPlc :: PLC.Program PLC.TyName PLC.Name () }
  deriving newtype (Serialise)

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
    a == b = serialise a == serialise b

instance Ord Script where
    a `compare` b = serialise a `compare` serialise b

-- | The size of a 'Script'. No particular interpretation is given to this, other than that it is
-- proportional to the serialized size of the script.
scriptSize :: Script -> Integer
scriptSize (Script s) = PLC.programSize s

-- | Turn a 'CompiledCode' (usually produced by 'compile') into a 'Script' for use with this package.
fromCompiledCode :: CompiledCode a -> Script
fromCompiledCode = Script . deserialise . getSerializedPlc

-- | Compile a quoted Haskell expression to a 'Script'.
compileScript :: TH.Q (TH.TExp a) -> TH.Q (TH.TExp Script)
compileScript a = [|| fromCompiledCode $$(compile a) ||]

-- | Given two 'Script's, compute the 'Script' that consists of applying the first to the second.
applyScript :: Script -> Script -> Script
applyScript (getPlc -> s1) (getPlc -> s2) = Script $ s1 `PLC.applyProgram` s2

-- | Evaluate a script, returning the trace log and a boolean indicating whether
-- evaluation was successful.
evaluateScript :: Script -> ([String], Bool)
evaluateScript (getPlc -> s) = (isJust . reoption) <$> evaluateCekTrace s

instance ToJSON Script where
  toJSON = JSON.String . JSON.encodeSerialise

instance FromJSON Script where
  parseJSON = JSON.decodeSerialise

-- | Lift a Haskell value into the corresponding 'Script'. This allows you to create
-- 'Script's at runtime, whereas 'compileScript' allows you to do so at compile time.
lifted :: Lift a => a -> Script
lifted = Script . unsafeLiftProgram

-- | 'ValidatorScript' is a wrapper around 'Script's which are used as validators in transaction outputs.
newtype ValidatorScript = ValidatorScript { getValidator :: Script }
  deriving stock (Generic)
  deriving newtype (Serialise)
  deriving anyclass (ToJSON, FromJSON)

instance Show ValidatorScript where
    show = const "ValidatorScript { <script> }"

instance Eq ValidatorScript where
    (ValidatorScript l) == (ValidatorScript r) = -- TODO: Deriving via
        l == r

instance Ord ValidatorScript where
    compare (ValidatorScript l) (ValidatorScript r) = -- TODO: Deriving via
        l `compare` r

instance BA.ByteArrayAccess ValidatorScript where
    length =
        BA.length . Write.toStrictByteString . encode
    withByteArray =
        BA.withByteArray . Write.toStrictByteString . encode

-- | 'DataScript' is a wrapper around 'Script's which are used as data scripts in transaction outputs.
newtype DataScript = DataScript { getDataScript :: Script  }
  deriving stock (Generic)
  deriving newtype (Serialise)
  deriving anyclass (ToJSON, FromJSON)

instance Show DataScript where
    show = const "DataScript { <script> }"

instance Eq DataScript where
    (DataScript l) == (DataScript r) = -- TODO: Deriving via
        l == r

instance Ord DataScript where
    compare (DataScript l) (DataScript r) = -- TODO: Deriving via
        l `compare` r

instance BA.ByteArrayAccess DataScript where
    length =
        BA.length . Write.toStrictByteString . encode
    withByteArray =
        BA.withByteArray . Write.toStrictByteString . encode

-- | 'RedeemerScript' is a wrapper around 'Script's that are used as redeemer scripts in transaction inputs.
newtype RedeemerScript = RedeemerScript { getRedeemer :: Script }
  deriving stock (Generic)
  deriving newtype (Serialise)
  deriving anyclass (ToJSON, FromJSON)

instance Show RedeemerScript where
    show = const "RedeemerScript { <script> }"

instance Eq RedeemerScript where
    (RedeemerScript l) == (RedeemerScript r) = -- TODO: Deriving via
        l == r

instance Ord RedeemerScript where
    compare (RedeemerScript l) (RedeemerScript r) = -- TODO: Deriving via
        l `compare` r

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
runScript :: ValidationData -> ValidatorScript -> DataScript -> RedeemerScript -> ([String], Bool)
runScript (ValidationData valData) (ValidatorScript validator) (DataScript dataScript) (RedeemerScript redeemer) =
    let
        applied = ((validator `applyScript` dataScript) `applyScript` redeemer) `applyScript` valData
        -- TODO: do something with the error
    in evaluateScript applied
        -- TODO: Enable type checking of the program
        -- void typecheck

-- | @()@ as a data script.
unitData :: DataScript
unitData = DataScript $ fromCompiledCode $$(compile [|| () ||])

-- | @()@ as a redeemer.
unitRedeemer :: RedeemerScript
unitRedeemer = RedeemerScript $ fromCompiledCode $$(compile [|| () ||])
