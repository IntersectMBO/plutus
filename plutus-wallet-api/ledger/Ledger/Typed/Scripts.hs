{-# LANGUAGE GADTs                     #-}
{-# LANGUAGE TypeFamilies              #-}
{-# LANGUAGE ScopedTypeVariables       #-}
{-# LANGUAGE ViewPatterns              #-}
module Ledger.Typed.Scripts where

import           Language.PlutusTx

import           Ledger.Scripts
import           Ledger.Tx                    hiding (scriptAddress)
import qualified Ledger.Tx                    as Tx
import qualified Ledger.Validation            as Validation

import           Data.Kind

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

type WrappedValidatorType = Data -> Data -> Validation.PendingTx -> Bool

-- | The type of a connection.
data ScriptInstance (a :: Type) where
    Validator
        :: ScriptType a
        => CompiledCode (ValidatorType a)
        -> CompiledCode (ValidatorType a -> WrappedValidatorType)
        -> ScriptInstance a

-- | Get the address for a script instance.
scriptAddress :: ScriptInstance a -> Address
scriptAddress = Tx.scriptAddress . validatorScript

-- | Get the validator script for a script instance.
validatorScript :: ScriptInstance a -> ValidatorScript
validatorScript (Validator vc wrapper) = mkValidatorScript $ wrapper `applyCode` vc

{-# INLINABLE wrapValidator #-}
wrapValidator
    :: forall d r
    . (IsData d, IsData r)
    => (d -> r -> Validation.PendingTx -> Bool)
    -> (Data -> Data -> Validation.PendingTx -> Bool)
wrapValidator f (fromData -> Just d) (fromData -> Just r) p = f d r p
wrapValidator _ _ _ _ = False
