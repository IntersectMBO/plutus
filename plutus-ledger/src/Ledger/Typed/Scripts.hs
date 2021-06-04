{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE DeriveAnyClass      #-}
{-# LANGUAGE DeriveGeneric       #-}
{-# LANGUAGE DerivingStrategies  #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies        #-}
{-# OPTIONS_GHC -fno-specialise #-}
{-# OPTIONS_GHC -fno-omit-interface-pragmas #-}
module Ledger.Typed.Scripts(
    ValidatorTypes(..)
    , Validator
    , TypedValidator
    , MonetaryPolicy
    , mkTypedValidator
    , mkTypedValidatorParam
    , validatorHash
    , validatorAddress
    , validatorScript
    , wrapValidator
    , wrapMonetaryPolicy
    , forwardingMonetaryPolicy
    , forwardingMonetaryPolicyHash
    , ValidatorType
    , WrappedValidatorType
    , WrappedMonetaryPolicyType
    , unsafeMkTypedValidator
    , Any
    ) where

import           PlutusCore.Default              (DefaultUni)
import           PlutusTx

import qualified Plutus.V1.Ledger.Address        as Addr
import           Plutus.V1.Ledger.Scripts        hiding (monetaryPolicyHash, validatorHash)
import qualified Plutus.V1.Ledger.Scripts        as Scripts

import           Data.Aeson                      (FromJSON, ToJSON)
import           Data.Kind
import           GHC.Generics                    (Generic)
import           Ledger.Typed.Scripts.Validators

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
    deriving (Show, Eq, Generic, ToJSON, FromJSON)

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
        mps = forwardingMPS hsh
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
validatorAddress :: TypedValidator a -> Addr.Address
validatorAddress = Addr.scriptHashAddress . tvValidatorHash

-- | The validator script itself.
validatorScript :: TypedValidator a -> Validator
validatorScript = tvValidator

-- | Make a 'TypedValidator' (with no type constraints) from an untyped 'Validator' script.
unsafeMkTypedValidator :: Validator -> TypedValidator Any
unsafeMkTypedValidator vl =
    let vh = Scripts.validatorHash vl
        mps = forwardingMPS vh
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
