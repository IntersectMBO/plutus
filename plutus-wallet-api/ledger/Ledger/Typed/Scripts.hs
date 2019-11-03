{-# LANGUAGE GADTs               #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies        #-}
{-# LANGUAGE ViewPatterns        #-}
{-# OPTIONS_GHC -fno-specialise #-}
{-# OPTIONS_GHC -fno-omit-interface-pragmas #-}
module Ledger.Typed.Scripts where

import           Language.PlutusTx

import           Language.PlutusTx.Prelude (check)
import           Ledger.Scripts
import           Ledger.Tx                 hiding (scriptAddress)
import qualified Ledger.Tx                 as Tx
import qualified Ledger.Validation         as Validation

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

type WrappedValidatorType = Data -> Data -> Data -> ()

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

{-# INLINABLE wrapValidator #-}
wrapValidator
    :: forall d r
    . (IsData d, IsData r)
    => (d -> r -> Validation.PendingTx -> Bool)
    -> WrappedValidatorType
wrapValidator f (fromData -> Just d) (fromData -> Just r) (fromData -> Just p) = check $ f d r p
wrapValidator _ _ _ _                                                          = check False
