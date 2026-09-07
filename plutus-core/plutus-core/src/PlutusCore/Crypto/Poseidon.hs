-- editorconfig-checker-disable
{- | The Poseidon permutation over the BLS12-381 scalar field, backing the
'PlutusCore.Default.Builtins.Bls12_381_poseidonPermutation' builtin proposed
by the CIP /Poseidon Permutation Built-in for Plutus/.

This is a thin adapter around "Cardano.Crypto.Poseidon" in
cardano-crypto-class, which implements the permutation and the append-only
variant registry (index 0 = the midnight-zk instance, index 1 = the circom
BLS12-381 port's width-3 instance).  The builtin exposes the /permutation/,
never a hash: it maps a full input state of exactly the variant's width many
field elements to the full output state, and every hash framing (capacity
placement, absorption schedule, digest lane) is the calling script's
responsibility.  See the module header of "Cardano.Crypto.Poseidon" for the
full contract, including why the input is never padded.
-}
module PlutusCore.Crypto.Poseidon
  ( poseidonPermutation
  ) where

import Cardano.Crypto.Poseidon qualified as Poseidon
import PlutusCore.Builtin.Result (BuiltinResult)

{- | Apply the Poseidon permutation of the given registry variant to a full
input state.  Each input integer is reduced modulo the scalar field order r
(negative inputs land in [0, r)), matching the reduction the existing
BLS12-381 builtins apply to scalars; outputs are canonical representatives
in [0, r).  Fails on an unregistered variant index or on an input state
whose length differs from the variant's width -- the input is never padded.
-}
poseidonPermutation :: Integer -> [Integer] -> BuiltinResult [Integer]
poseidonPermutation variantIndex input =
  case Poseidon.poseidonPermutationInteger variantIndex input of
    Left err -> fail $ "Poseidon permutation failed: " ++ show err
    Right output -> pure output
{-# INLINE poseidonPermutation #-}
