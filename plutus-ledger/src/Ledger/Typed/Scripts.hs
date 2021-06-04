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
    , validator
    , validatorParam
    , scriptHash
    , scriptAddress
    , validatorScript
    , wrapValidator
    , wrapMonetaryPolicy
    , monetaryPolicy
    , monetaryPolicyHash
    , ValidatorType
    , WrappedValidatorType
    , WrappedMonetaryPolicyType
    , fromValidator
    , Any
    ) where

import           PlutusCore.Default              (DefaultUni)
import           PlutusTx

import qualified Plutus.V1.Ledger.Address        as Addr
import           Plutus.V1.Ledger.Scripts        hiding (monetaryPolicyHash)
import qualified Plutus.V1.Ledger.Scripts        as Scripts

import           Data.Aeson                      (FromJSON, ToJSON)
import           Data.Kind
import           GHC.Generics                    (Generic)
import           Ledger.Typed.Scripts.Validators

-- | A typed validator script with its 'ValidatorScript' and 'Address'.
data TypedValidator (a :: Type) =
    TypedValidator
        { instanceScript  :: Validator
        , instanceHash    :: ValidatorHash
        , instanceMPSHash :: MonetaryPolicyHash
        -- ^ The hash of the monetary policy that checks whether the validator
        --   is run in this transaction
        , instanceMPS     :: MonetaryPolicy
        }
    deriving (Show, Eq, Generic, ToJSON, FromJSON)

-- | The 'TypedValidator' of a validator script and its wrapper.
validator ::
    CompiledCode (ValidatorType a)
    -- ^ Validator script (compiled)
    -> CompiledCode (ValidatorType a -> WrappedValidatorType)
    -- ^ A wrapper for the compiled validator
    -> TypedValidator a
validator vc wrapper =
    let val = mkValidatorScript $ wrapper `applyCode` vc
        hsh = validatorHash val
        mps = forwardingMPS hsh
    in ValidatorInstance
        { instanceScript  = val
        , instanceHash    = hsh
        , instanceMPS     = mps
        , instanceMPSHash = Scripts.monetaryPolicyHash mps
        }

-- | The 'TypedValidator' of a paramaterized validator script and its wrapper.
validatorParam
    :: forall a param. Lift DefaultUni param
    => CompiledCode (param -> ValidatorType a)
    -- ^ Validator script (compiled)
    -> CompiledCode (ValidatorType a -> WrappedValidatorType)
    -- ^ A wrapper for the compiled validator
    -> param
    -- ^ The extra paramater for the validator script
    -> TypedValidator a
validatorParam vc wrapper param =
    validator (vc `PlutusTx.applyCode` PlutusTx.liftCode param) wrapper

-- | The script's 'ValidatorHash'
scriptHash :: TypedValidator a -> ValidatorHash
scriptHash = instanceHash

-- | Get the address for a script instance.
scriptAddress :: TypedValidator a -> Addr.Address
scriptAddress = Addr.scriptHashAddress . scriptHash

-- | Get the validator script for a script instance.
validatorScript :: TypedValidator a -> Validator
validatorScript = instanceScript

-- | Script instance for a validator whose type is unknown
fromValidator :: Validator -> TypedValidator Any
fromValidator vl =
    let vh = validatorHash vl
        mps = forwardingMPS vh
    in
    ValidatorInstance
        { instanceScript  = vl
        , instanceHash    = vh
        , instanceMPS     = mps
        , instanceMPSHash = Scripts.monetaryPolicyHash mps
        }

-- | The monetary policy that forwards all checks to the instance's
--   validator
monetaryPolicy :: TypedValidator a -> MonetaryPolicy
monetaryPolicy = instanceMPS

-- | Hash of the monetary policy that forwards all checks to the instance's
--   validator
monetaryPolicyHash :: TypedValidator a -> MonetaryPolicyHash
monetaryPolicyHash = instanceMPSHash
