{-# LANGUAGE DataKinds          #-}
{-# LANGUAGE DeriveAnyClass     #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE KindSignatures     #-}
{-# LANGUAGE NamedFieldPuns     #-}
{-# LANGUAGE TemplateHaskell    #-}
{-# LANGUAGE TypeFamilies       #-}
{-# LANGUAGE ViewPatterns       #-}
{-# OPTIONS_GHC -fno-specialise #-}
{-# OPTIONS_GHC -fno-strictness #-}
{-# OPTIONS_GHC -Wno-simplifiable-class-constraints #-}
{-# OPTIONS_GHC -fno-omit-interface-pragmas #-}
module Ledger.Typed.Scripts.Validators where

import           Data.Aeson                            (FromJSON, ToJSON)
import           Data.Kind
import           Data.Void
import           GHC.Generics                          (Generic)

import           PlutusCore.Default                    (DefaultUni)
import           PlutusTx
import           PlutusTx.Prelude                      (check)

import           Plutus.V1.Ledger.Address              (Address (..), scriptHashAddress)
import qualified Plutus.V1.Ledger.Contexts             as Validation
import           Plutus.V1.Ledger.Scripts
import qualified Plutus.V1.Ledger.Scripts              as Scripts

import qualified Ledger.Typed.Scripts.MonetaryPolicies as MPS

-- | A class that associates a type standing for a connection type with two types, the type of the redeemer
-- and the data script for that connection type.
class ValidatorTypes (a :: Type) where
    -- | The type of the redeemers of this connection type.
    type RedeemerType a :: Type
    -- | The type of the data of this connection type.
    type DatumType a :: Type

    -- Defaults
    type instance RedeemerType a = ()
    type instance DatumType  a = ()

-- | The type of validators for the given connection type.
type ValidatorType (a :: Type) = DatumType a -> RedeemerType a -> Validation.ScriptContext -> Bool

instance ValidatorTypes Void where
    type RedeemerType Void = Void
    type DatumType Void = Void

data Any

instance ValidatorTypes Any where
    type RedeemerType Any = Data
    type DatumType Any = Data

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

type WrappedValidatorType = Data -> Data -> Data -> ()

{-# INLINABLE wrapValidator #-}
wrapValidator
    :: forall d r
    . (IsData d, IsData r)
    => (d -> r -> Validation.ScriptContext -> Bool)
    -> WrappedValidatorType
wrapValidator f (fromData -> Just d) (fromData -> Just r) (fromData -> Just p) = check $ f d r p
wrapValidator _ _ _ _                                                          = check False

-- | A typed validator script with its 'ValidatorScript' and 'Address'.
data TypedValidator (a :: Type) =
    TypedValidator
        { tvValidator         :: Validator
        , tvValidatorHash     :: ValidatorHash
        , tvForwardingMPS     :: MonetaryPolicy
        , tvForwardingMPSHash :: MonetaryPolicyHash
        -- ^ The hash of the monetary policy that checks whether the validator
        --   is run in this transaction
        }
    deriving stock (Show, Eq, Generic)
    deriving anyclass (ToJSON, FromJSON)

-- | Make a 'TypedValidator' from the 'CompiledCode' of a validator script and its wrapper.
mkTypedValidator ::
    CompiledCode (ValidatorType a)
    -- ^ Validator script (compiled)
    -> CompiledCode (ValidatorType a -> WrappedValidatorType)
    -- ^ A wrapper for the compiled validator
    -> TypedValidator a
mkTypedValidator vc wrapper =
    let val = mkValidatorScript $ wrapper `applyCode` vc
        hsh = Scripts.validatorHash val
        mps = MPS.mkForwardingMonetaryPolicy hsh
    in TypedValidator
        { tvValidator         = val
        , tvValidatorHash     = hsh
        , tvForwardingMPS     = mps
        , tvForwardingMPSHash = Scripts.monetaryPolicyHash mps
        }

-- | Make a 'TypedValidator' from the 'CompiledCode' of a paramaterized validator script and its wrapper.
mkTypedValidatorParam
    :: forall a param. Lift DefaultUni param
    => CompiledCode (param -> ValidatorType a)
    -- ^ Validator script (compiled)
    -> CompiledCode (ValidatorType a -> WrappedValidatorType)
    -- ^ A wrapper for the compiled validator
    -> param
    -- ^ The extra paramater for the validator script
    -> TypedValidator a
mkTypedValidatorParam vc wrapper param =
    mkTypedValidator (vc `PlutusTx.applyCode` PlutusTx.liftCode param) wrapper

-- | The hash of the validator.
validatorHash :: TypedValidator a -> ValidatorHash
validatorHash = tvValidatorHash

-- | The address of the validator.
validatorAddress :: TypedValidator a -> Address
validatorAddress = scriptHashAddress . tvValidatorHash

-- | The validator script itself.
validatorScript :: TypedValidator a -> Validator
validatorScript = tvValidator

-- | Make a 'TypedValidator' (with no type constraints) from an untyped 'Validator' script.
unsafeMkTypedValidator :: Validator -> TypedValidator Any
unsafeMkTypedValidator vl =
    let vh = Scripts.validatorHash vl
        mps = MPS.mkForwardingMonetaryPolicy vh
    in
    TypedValidator
        { tvValidator         = vl
        , tvValidatorHash     = vh
        , tvForwardingMPS     = mps
        , tvForwardingMPSHash = Scripts.monetaryPolicyHash mps
        }

-- | The monetary policy that forwards all checks to the instance's
--   validator
forwardingMonetaryPolicy :: TypedValidator a -> MonetaryPolicy
forwardingMonetaryPolicy = tvForwardingMPS

-- | Hash of the monetary policy that forwards all checks to the instance's
--   validator
forwardingMonetaryPolicyHash :: TypedValidator a -> MonetaryPolicyHash
forwardingMonetaryPolicyHash = tvForwardingMPSHash
