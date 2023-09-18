-- editorconfig-checker-disable-file
{-# LANGUAGE DataKinds       #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies    #-}

module PlutusCore.Evaluation.Machine.ExBudgetingDefaults
    ( defaultBuiltinsRuntimeForSemanticsVariant
    , defaultBuiltinsRuntime
    , defaultCekCostModel
    , defaultCekMachineCosts
    , defaultCekParameters
    , defaultCostModelParams
    , defaultBuiltinCostModel
    , unitCekMachineCosts
    , unitCekParameters
    )

where

import PlutusCore.Builtin

import PlutusCore.DataFilePaths qualified as DFP
import PlutusCore.Default
import PlutusCore.Evaluation.Machine.BuiltinCostModel
import PlutusCore.Evaluation.Machine.CostModelInterface
import PlutusCore.Evaluation.Machine.MachineParameters

import UntypedPlutusCore.Evaluation.Machine.Cek.CekMachineCosts
import UntypedPlutusCore.Evaluation.Machine.Cek.Internal

import Data.Aeson.THReader
-- Not using 'noinline' from "GHC.Exts", because our CI was unable to find it there, somehow.
import GHC.Magic (noinline)
import PlutusPrelude

-- | The default cost model for built-in functions.
defaultBuiltinCostModel :: BuiltinCostModel
defaultBuiltinCostModel =
    $$(readJSONFromFile DFP.builtinCostModelFile)

{- Note [Modifying the cost model]
   When the Haskell representation of the cost model is changed, for example by
   adding a new builtin or changing the name of an existing one,
   readJSONFromFile will fail when it tries to read a JSON file generated using
   the previous version.  When this happens, uncomment the three lines below (and
   comment out the three above) then rerun

      cabal run plutus-core:generate-cost-model

   (You may also need to add 'data-default' to the 'build-depends' for the
   library in plutus-core.cabal). This will generate a new JSON file filled with
   default values.  After that, restore this file to its previous state and then
   run "generate-cost-model" again to fill in the JSON file with the correct
   values (assuming that suitable benchmarking data is in benching.csv and that
   models.R contains R code to generate cost models for any new functions).

   Alternatively, modify 'builtinCostModel.json' by hand so that it matches the new
   format.
 -}

-- import           Data.Default
-- defaultBuiltinCostModel :: BuiltinCostModel
-- defaultBuiltinCostModel = def

-- | Default costs for CEK machine instructions.
defaultCekMachineCosts :: CekMachineCosts
defaultCekMachineCosts =
  $$(readJSONFromFile DFP.cekMachineCostsFile)

{-| The default cost model, including both builtin costs and machine step costs.
    Note that this is not necessarily the cost model in use on the chain at any
    given time.  The definitive values used for calculating on-chain costs are
    protocol parameters which are part of the state of the chain; in practice
    these will usually have been obtained from the contents of the JSON files at
    some point in the past, but we do not guarantee this.  During on-chain
    evaluation the ledger passes a cost model to the Plutus Core evaluator using
    the `mkEvaluationContext` functions in PlutusLedgerApi.
-}
defaultCekCostModel :: CostModel CekMachineCosts BuiltinCostModel
defaultCekCostModel = CostModel defaultCekMachineCosts defaultBuiltinCostModel

-- | The default cost model data.  This is exposed to the ledger, so let's not
-- confuse anybody by mentioning the CEK machine
defaultCostModelParams :: Maybe CostModelParams
defaultCostModelParams = extractCostModelParams defaultCekCostModel

defaultCekParameters :: Typeable ann => MachineParameters CekMachineCosts DefaultFun (CekValue DefaultUni DefaultFun ann)
defaultCekParameters = mkMachineParameters def defaultCekCostModel

{- Note [noinline for saving on ticks]
We use 'noinline' purely for saving on simplifier ticks for definitions, whose performance doesn't
matter. Otherwise compilation for this module is slower and GHC may end up exhausting simplifier
ticks leading to a compilation error.
-}

unitCekParameters :: Typeable ann => MachineParameters CekMachineCosts DefaultFun (CekValue DefaultUni DefaultFun ann)
unitCekParameters =
    -- See Note [noinline for saving on ticks].
    noinline mkMachineParameters def $
        CostModel unitCekMachineCosts unitCostBuiltinCostModel

defaultBuiltinsRuntimeForSemanticsVariant
    :: HasMeaningIn DefaultUni term
    => BuiltinSemanticsVariant DefaultFun
    -> BuiltinsRuntime DefaultFun term
-- See Note [noinline for saving on ticks].
defaultBuiltinsRuntimeForSemanticsVariant semvar = noinline toBuiltinsRuntime semvar defaultBuiltinCostModel

defaultBuiltinsRuntime
    :: HasMeaningIn DefaultUni term
    => BuiltinsRuntime DefaultFun term
-- See Note [noinline for saving on ticks].
defaultBuiltinsRuntime = noinline toBuiltinsRuntime def defaultBuiltinCostModel


-- A cost model with unit costs, so we can count how often each builtin is called

unitCostOneArgument :: CostingFun ModelOneArgument
unitCostOneArgument =  CostingFun (ModelOneArgumentConstantCost 1) (ModelOneArgumentConstantCost 0)

unitCostTwoArguments :: CostingFun ModelTwoArguments
unitCostTwoArguments   =  CostingFun (ModelTwoArgumentsConstantCost 1) (ModelTwoArgumentsConstantCost 0)

unitCostThreeArguments :: CostingFun ModelThreeArguments
unitCostThreeArguments =  CostingFun (ModelThreeArgumentsConstantCost 1) (ModelThreeArgumentsConstantCost 0)

unitCostSixArguments :: CostingFun ModelSixArguments
unitCostSixArguments   =  CostingFun (ModelSixArgumentsConstantCost 1) (ModelSixArgumentsConstantCost 0)

unitCostBuiltinCostModel :: BuiltinCostModel
unitCostBuiltinCostModel = BuiltinCostModelBase
    {
     -- Integers
      paramAddInteger                      = unitCostTwoArguments
    , paramSubtractInteger                 = unitCostTwoArguments
    , paramMultiplyInteger                 = unitCostTwoArguments
    , paramDivideInteger                   = unitCostTwoArguments
    , paramQuotientInteger                 = unitCostTwoArguments
    , paramRemainderInteger                = unitCostTwoArguments
    , paramModInteger                      = unitCostTwoArguments
    , paramEqualsInteger                   = unitCostTwoArguments
    , paramLessThanInteger                 = unitCostTwoArguments
    , paramLessThanEqualsInteger           = unitCostTwoArguments
    -- Bytestrings
    , paramAppendByteString                = unitCostTwoArguments
    , paramConsByteString                  = unitCostTwoArguments
    , paramSliceByteString                 = unitCostThreeArguments
    , paramLengthOfByteString              = unitCostOneArgument
    , paramIndexByteString                 = unitCostTwoArguments
    , paramEqualsByteString                = unitCostTwoArguments
    , paramLessThanByteString              = unitCostTwoArguments
    , paramLessThanEqualsByteString        = unitCostTwoArguments
    -- Cryptography and hashes
    , paramSha2_256                        = unitCostOneArgument
    , paramSha3_256                        = unitCostOneArgument
    , paramBlake2b_256                     = unitCostOneArgument
    , paramVerifyEd25519Signature          = unitCostThreeArguments
    , paramVerifyEcdsaSecp256k1Signature   = unitCostThreeArguments
    , paramVerifySchnorrSecp256k1Signature = unitCostThreeArguments
    -- Strings
    , paramAppendString                    = unitCostTwoArguments
    , paramEqualsString                    = unitCostTwoArguments
    , paramEncodeUtf8                      = unitCostOneArgument
    , paramDecodeUtf8                      = unitCostOneArgument
    -- Bool
    , paramIfThenElse                      = unitCostThreeArguments
    -- Unit
    , paramChooseUnit                      = unitCostTwoArguments
    -- Tracing
    , paramTrace                           = unitCostTwoArguments
    -- Pairs
    , paramFstPair                         = unitCostOneArgument
    , paramSndPair                         = unitCostOneArgument
    -- Lists
    , paramChooseList                      = unitCostThreeArguments
    , paramMkCons                          = unitCostTwoArguments
    , paramHeadList                        = unitCostOneArgument
    , paramTailList                        = unitCostOneArgument
    , paramNullList                        = unitCostOneArgument
    -- Data
    , paramChooseData                      = unitCostSixArguments
    , paramConstrData                      = unitCostTwoArguments
    , paramMapData                         = unitCostOneArgument
    , paramListData                        = unitCostOneArgument
    , paramIData                           = unitCostOneArgument
    , paramBData                           = unitCostOneArgument
    , paramUnConstrData                    = unitCostOneArgument
    , paramUnMapData                       = unitCostOneArgument
    , paramUnListData                      = unitCostOneArgument
    , paramUnIData                         = unitCostOneArgument
    , paramUnBData                         = unitCostOneArgument
    , paramEqualsData                      = unitCostTwoArguments
    -- Misc constructors
    , paramMkPairData                      = unitCostTwoArguments
    , paramMkNilData                       = unitCostOneArgument
    , paramMkNilPairData                   = unitCostOneArgument
    , paramSerialiseData                   = unitCostOneArgument
    -- BLS12-381 operations
    , paramBls12_381_G1_add                = unitCostTwoArguments
    , paramBls12_381_G1_neg                = unitCostOneArgument
    , paramBls12_381_G1_scalarMul          = unitCostTwoArguments
    , paramBls12_381_G1_equal              = unitCostTwoArguments
    , paramBls12_381_G1_compress           = unitCostOneArgument
    , paramBls12_381_G1_uncompress         = unitCostOneArgument
    , paramBls12_381_G1_hashToGroup        = unitCostTwoArguments
    , paramBls12_381_G2_add                = unitCostTwoArguments
    , paramBls12_381_G2_neg                = unitCostOneArgument
    , paramBls12_381_G2_scalarMul          = unitCostTwoArguments
    , paramBls12_381_G2_equal              = unitCostTwoArguments
    , paramBls12_381_G2_compress           = unitCostOneArgument
    , paramBls12_381_G2_uncompress         = unitCostOneArgument
    , paramBls12_381_G2_hashToGroup        = unitCostTwoArguments
    , paramBls12_381_millerLoop            = unitCostTwoArguments
    , paramBls12_381_mulMlResult           = unitCostTwoArguments
    , paramBls12_381_finalVerify           = unitCostTwoArguments
    -- Keccak_256, Blake2b_224
    , paramKeccak_256                      = unitCostOneArgument
    , paramBlake2b_224                     = unitCostOneArgument
    }

