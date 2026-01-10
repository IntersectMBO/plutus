-- editorconfig-checker-disable-file
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}

module PlutusCore.Evaluation.Machine.ExBudgetingDefaults
  ( defaultBuiltinsRuntimeForSemanticsVariant
  , defaultCekParametersForVariant
  , defaultCostModelParamsForVariant
  , cekCostModelForVariant
  , defaultBuiltinsRuntimeForTesting
  , defaultCekParametersForTesting
  , defaultCekMachineCostsForTesting
  , defaultCostModelParamsForTesting
  , defaultBuiltinCostModelForTesting
  , defaultCekCostModelForTesting
  , defaultCekCostModelForTestingB
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

   Alternatively, modify the appropriate 'builtinCostModelX.json' by hand so
   that it matches the new format.
 -}

-- import           Data.Default
-- defaultBuiltinCostModel :: BuiltinCostModel
-- defaultBuiltinCostModel = def

-- | The default cost model for built-in functions (variant A)
builtinCostModelVariantA :: BuiltinCostModel
builtinCostModelVariantA =
  $$(readJSONFromFile DFP.builtinCostModelFileA)
-- This is a huge record, inlining it is wasteful.
{-# OPAQUE builtinCostModelVariantA #-}

{- Note [No inlining for CekMachineCosts]
We don't want this to get inlined, as otherwise the default 'CekMachineCosts'
appears faster than 'CekMachineCosts' that we get in production after applying
the costing parameters provided by the ledger. -}
-- | Default costs for CEK machine instructions (variant A)
cekMachineCostsVariantA :: CekMachineCosts
cekMachineCostsVariantA =
  $$(readJSONFromFile DFP.cekMachineCostsFileA)
{-# OPAQUE cekMachineCostsVariantA #-}

{-| The default cost model, including both builtin costs and machine step costs.
    Note that this is not necessarily the cost model in use on the chain at any
    given time.  The definitive values used for calculating on-chain costs are
    protocol parameters which are part of the state of the chain; in practice
    these will usually have been obtained from the contents of the JSON files at
    some point in the past, but we do not guarantee this.  During on-chain
    evaluation the ledger passes a cost model to the Plutus Core evaluator using
    the `mkEvaluationContext` functions in PlutusLedgerApi. -}
cekCostModelVariantA :: CostModel CekMachineCosts BuiltinCostModel
cekCostModelVariantA = CostModel cekMachineCostsVariantA builtinCostModelVariantA

builtinCostModelVariantB :: BuiltinCostModel
builtinCostModelVariantB =
  $$(readJSONFromFile DFP.builtinCostModelFileB)
{-# OPAQUE builtinCostModelVariantB #-}

-- See Note [No inlining for CekMachineCosts]
cekMachineCostsVariantB :: CekMachineCosts
cekMachineCostsVariantB =
  $$(readJSONFromFile DFP.cekMachineCostsFileB)
{-# OPAQUE cekMachineCostsVariantB #-}

cekCostModelVariantB :: CostModel CekMachineCosts BuiltinCostModel
cekCostModelVariantB = CostModel cekMachineCostsVariantB builtinCostModelVariantB

builtinCostModelVariantC :: BuiltinCostModel
builtinCostModelVariantC =
  $$(readJSONFromFile DFP.builtinCostModelFileC)
{-# OPAQUE builtinCostModelVariantC #-}

-- See Note [No inlining for CekMachineCosts]
cekMachineCostsVariantC :: CekMachineCosts
cekMachineCostsVariantC =
  $$(readJSONFromFile DFP.cekMachineCostsFileC)
{-# OPAQUE cekMachineCostsVariantC #-}

cekCostModelVariantC :: CostModel CekMachineCosts BuiltinCostModel
cekCostModelVariantC = CostModel cekMachineCostsVariantC builtinCostModelVariantC

{-| Return the 'CostModel' corresponding to the given semantics variant. The dependency on the
semantics variant is what makes cost models configurable. -}
cekCostModelForVariant :: BuiltinSemanticsVariant DefaultFun -> CostModel CekMachineCosts BuiltinCostModel
cekCostModelForVariant DefaultFunSemanticsVariantA = cekCostModelVariantA
cekCostModelForVariant DefaultFunSemanticsVariantB = cekCostModelVariantB
cekCostModelForVariant DefaultFunSemanticsVariantC = cekCostModelVariantC

{-| The default cost model data.  This is exposed to the ledger, so let's not
confuse anybody by mentioning the CEK machine -}
defaultCostModelParamsA :: Maybe CostModelParams
defaultCostModelParamsA = extractCostModelParams cekCostModelVariantA

defaultCostModelParamsB :: Maybe CostModelParams
defaultCostModelParamsB = extractCostModelParams cekCostModelVariantB

defaultCostModelParamsC :: Maybe CostModelParams
defaultCostModelParamsC = extractCostModelParams cekCostModelVariantC

defaultCostModelParamsForVariant :: BuiltinSemanticsVariant DefaultFun -> Maybe CostModelParams
defaultCostModelParamsForVariant = \case
  DefaultFunSemanticsVariantA -> defaultCostModelParamsA
  DefaultFunSemanticsVariantB -> defaultCostModelParamsB
  DefaultFunSemanticsVariantC -> defaultCostModelParamsC

{- Note [No inlining for MachineParameters]
We don't want this to get inlined in order for this definition not to appear
faster than the used in production. Also see Note [noinline for saving on
ticks]. -}
defaultCekParametersA :: Typeable ann => MachineParameters CekMachineCosts DefaultFun (CekValue DefaultUni DefaultFun ann)
defaultCekParametersA =
  MachineParameters def $
    noinline mkMachineVariantParameters DefaultFunSemanticsVariantA cekCostModelVariantA

-- See Note [No inlining for MachineParameters]
defaultCekParametersB :: Typeable ann => MachineParameters CekMachineCosts DefaultFun (CekValue DefaultUni DefaultFun ann)
defaultCekParametersB =
  MachineParameters def $
    noinline mkMachineVariantParameters DefaultFunSemanticsVariantB cekCostModelVariantB

-- See Note [No inlining for MachineParameters]
defaultCekParametersC :: Typeable ann => MachineParameters CekMachineCosts DefaultFun (CekValue DefaultUni DefaultFun ann)
defaultCekParametersC =
  MachineParameters def $
    noinline mkMachineVariantParameters DefaultFunSemanticsVariantC cekCostModelVariantC

{- Note [noinline for saving on ticks]
We use 'noinline' purely for saving on simplifier ticks for definitions, whose performance doesn't
matter. Otherwise compilation for this module is slower and GHC may end up exhausting simplifier
ticks leading to a compilation error.
-}
defaultBuiltinsRuntimeForSemanticsVariant
  :: HasMeaningIn DefaultUni term
  => BuiltinSemanticsVariant DefaultFun
  -> BuiltinsRuntime DefaultFun term
-- See Note [noinline for saving on ticks].
defaultBuiltinsRuntimeForSemanticsVariant semvar =
  noinline toBuiltinsRuntime semvar $ builtinCostModelFor semvar
  where
    builtinCostModelFor = \case
      DefaultFunSemanticsVariantA -> builtinCostModelVariantA
      DefaultFunSemanticsVariantB -> builtinCostModelVariantB
      DefaultFunSemanticsVariantC -> builtinCostModelVariantC

defaultCekParametersForVariant
  :: Typeable ann
  => BuiltinSemanticsVariant DefaultFun
  -> MachineParameters CekMachineCosts DefaultFun (CekValue DefaultUni DefaultFun ann)
defaultCekParametersForVariant = \case
  DefaultFunSemanticsVariantA -> defaultCekParametersA
  DefaultFunSemanticsVariantB -> defaultCekParametersB
  DefaultFunSemanticsVariantC -> defaultCekParametersC

-- *** THE FOLLOWING SHOULD ONLY BE USED FOR TESTING ***

{- We export a number of objects which are used in tests in a number of places in
   the codebase. For the time being we'll just use the most recent cost model
   for all of these.  In fact we may want tests for each variant in some cases
   TODO:
      * Maybe export fewer things and extract the required component at the use site.
      * Make the names more sensible: does "default" refer to the variant
        or the set of builtins?
      * Perhaps export functions like `defaultBuiltinCostModelForVariant
        and then apply those to `def` where they're used.
-}
defaultBuiltinsRuntimeForTesting
  :: HasMeaningIn DefaultUni term
  => BuiltinsRuntime DefaultFun term
-- See Note [noinline for saving on ticks].
defaultBuiltinsRuntimeForTesting = defaultBuiltinsRuntimeForSemanticsVariant DefaultFunSemanticsVariantC

defaultCekParametersForTesting :: Typeable ann => MachineParameters CekMachineCosts DefaultFun (CekValue DefaultUni DefaultFun ann)
defaultCekParametersForTesting = defaultCekParametersC

defaultCekMachineCostsForTesting :: CekMachineCosts
defaultCekMachineCostsForTesting = cekMachineCostsVariantC

defaultBuiltinCostModelForTesting :: BuiltinCostModel
defaultBuiltinCostModelForTesting = builtinCostModelVariantC

defaultCostModelParamsForTesting :: Maybe CostModelParams
defaultCostModelParamsForTesting = defaultCostModelParamsC

defaultCekCostModelForTesting :: CostModel CekMachineCosts BuiltinCostModel
defaultCekCostModelForTesting = cekCostModelVariantC

defaultCekCostModelForTestingB :: CostModel CekMachineCosts BuiltinCostModel
defaultCekCostModelForTestingB = cekCostModelVariantB

{- A cost model with unit costs, so we can count how often each builtin is called.
  This currently works for all semantics variants because to date we have only
  ever added new builtins and never removed any. -}
unitCostOneArgument :: CostingFun ModelOneArgument
unitCostOneArgument = CostingFun (ModelOneArgumentConstantCost 1) (ModelOneArgumentConstantCost 0)

unitCostTwoArguments :: CostingFun ModelTwoArguments
unitCostTwoArguments = CostingFun (ModelTwoArgumentsConstantCost 1) (ModelTwoArgumentsConstantCost 0)

unitCostThreeArguments :: CostingFun ModelThreeArguments
unitCostThreeArguments = CostingFun (ModelThreeArgumentsConstantCost 1) (ModelThreeArgumentsConstantCost 0)

unitCostFourArguments :: CostingFun ModelFourArguments
unitCostFourArguments = CostingFun (ModelFourArgumentsConstantCost 1) (ModelFourArgumentsConstantCost 0)

unitCostSixArguments :: CostingFun ModelSixArguments
unitCostSixArguments = CostingFun (ModelSixArgumentsConstantCost 1) (ModelSixArgumentsConstantCost 0)

unitCostBuiltinCostModel :: BuiltinCostModel
unitCostBuiltinCostModel =
  BuiltinCostModelBase
    { -- Integers
      paramAddInteger = unitCostTwoArguments
    , paramSubtractInteger = unitCostTwoArguments
    , paramMultiplyInteger = unitCostTwoArguments
    , paramDivideInteger = unitCostTwoArguments
    , paramQuotientInteger = unitCostTwoArguments
    , paramRemainderInteger = unitCostTwoArguments
    , paramModInteger = unitCostTwoArguments
    , paramEqualsInteger = unitCostTwoArguments
    , paramLessThanInteger = unitCostTwoArguments
    , paramLessThanEqualsInteger = unitCostTwoArguments
    , -- Bytestrings
      paramAppendByteString = unitCostTwoArguments
    , paramConsByteString = unitCostTwoArguments
    , paramSliceByteString = unitCostThreeArguments
    , paramLengthOfByteString = unitCostOneArgument
    , paramIndexByteString = unitCostTwoArguments
    , paramEqualsByteString = unitCostTwoArguments
    , paramLessThanByteString = unitCostTwoArguments
    , paramLessThanEqualsByteString = unitCostTwoArguments
    , -- Cryptography and hashes
      paramSha2_256 = unitCostOneArgument
    , paramSha3_256 = unitCostOneArgument
    , paramBlake2b_256 = unitCostOneArgument
    , paramVerifyEd25519Signature = unitCostThreeArguments
    , paramVerifyEcdsaSecp256k1Signature = unitCostThreeArguments
    , paramVerifySchnorrSecp256k1Signature = unitCostThreeArguments
    , -- Strings
      paramAppendString = unitCostTwoArguments
    , paramEqualsString = unitCostTwoArguments
    , paramEncodeUtf8 = unitCostOneArgument
    , paramDecodeUtf8 = unitCostOneArgument
    , -- Bool
      paramIfThenElse = unitCostThreeArguments
    , -- Unit
      paramChooseUnit = unitCostTwoArguments
    , -- Tracing
      paramTrace = unitCostTwoArguments
    , -- Pairs
      paramFstPair = unitCostOneArgument
    , paramSndPair = unitCostOneArgument
    , -- Lists
      paramChooseList = unitCostThreeArguments
    , paramMkCons = unitCostTwoArguments
    , paramHeadList = unitCostOneArgument
    , paramTailList = unitCostOneArgument
    , paramNullList = unitCostOneArgument
    , -- Data
      paramChooseData = unitCostSixArguments
    , paramConstrData = unitCostTwoArguments
    , paramMapData = unitCostOneArgument
    , paramListData = unitCostOneArgument
    , paramIData = unitCostOneArgument
    , paramBData = unitCostOneArgument
    , paramUnConstrData = unitCostOneArgument
    , paramUnMapData = unitCostOneArgument
    , paramUnListData = unitCostOneArgument
    , paramUnIData = unitCostOneArgument
    , paramUnBData = unitCostOneArgument
    , paramEqualsData = unitCostTwoArguments
    , -- Misc constructors
      paramMkPairData = unitCostTwoArguments
    , paramMkNilData = unitCostOneArgument
    , paramMkNilPairData = unitCostOneArgument
    , paramSerialiseData = unitCostOneArgument
    , -- BLS12-381 operations
      paramBls12_381_G1_add = unitCostTwoArguments
    , paramBls12_381_G1_neg = unitCostOneArgument
    , paramBls12_381_G1_scalarMul = unitCostTwoArguments
    , paramBls12_381_G1_multiScalarMul = unitCostTwoArguments
    , paramBls12_381_G1_equal = unitCostTwoArguments
    , paramBls12_381_G1_compress = unitCostOneArgument
    , paramBls12_381_G1_uncompress = unitCostOneArgument
    , paramBls12_381_G1_hashToGroup = unitCostTwoArguments
    , paramBls12_381_G2_add = unitCostTwoArguments
    , paramBls12_381_G2_neg = unitCostOneArgument
    , paramBls12_381_G2_scalarMul = unitCostTwoArguments
    , paramBls12_381_G2_multiScalarMul = unitCostTwoArguments
    , paramBls12_381_G2_equal = unitCostTwoArguments
    , paramBls12_381_G2_compress = unitCostOneArgument
    , paramBls12_381_G2_uncompress = unitCostOneArgument
    , paramBls12_381_G2_hashToGroup = unitCostTwoArguments
    , paramBls12_381_millerLoop = unitCostTwoArguments
    , paramBls12_381_mulMlResult = unitCostTwoArguments
    , paramBls12_381_finalVerify = unitCostTwoArguments
    , -- Keccak_256, Blake2b_224
      paramKeccak_256 = unitCostOneArgument
    , paramBlake2b_224 = unitCostOneArgument
    , -- Bitwise operations
      paramIntegerToByteString = unitCostThreeArguments
    , paramByteStringToInteger = unitCostTwoArguments
    , paramAndByteString = unitCostThreeArguments
    , paramOrByteString = unitCostThreeArguments
    , paramXorByteString = unitCostThreeArguments
    , paramComplementByteString = unitCostOneArgument
    , paramReadBit = unitCostTwoArguments
    , paramWriteBits = unitCostThreeArguments
    , paramReplicateByte = unitCostTwoArguments
    , paramShiftByteString = unitCostTwoArguments
    , paramRotateByteString = unitCostTwoArguments
    , paramCountSetBits = unitCostOneArgument
    , paramFindFirstSetBit = unitCostOneArgument
    , -- Ripemd_160
      paramRipemd_160 = unitCostOneArgument
    , -- Batch 6
      paramExpModInteger = unitCostThreeArguments
    , paramDropList = unitCostTwoArguments
    , -- Arrays
      paramLengthOfArray = unitCostOneArgument
    , paramListToArray = unitCostOneArgument
    , paramIndexArray = unitCostTwoArguments
    , -- Builtin values
      paramLookupCoin = unitCostThreeArguments
    , paramValueContains = unitCostTwoArguments
    , paramValueData = unitCostOneArgument
    , paramUnValueData = unitCostOneArgument
    , paramInsertCoin = unitCostFourArguments
    , paramUnionValue = unitCostTwoArguments
    , paramScaleValue = unitCostTwoArguments
    }

unitCekParameters :: Typeable ann => MachineParameters CekMachineCosts DefaultFun (CekValue DefaultUni DefaultFun ann)
unitCekParameters =
  -- See Note [noinline for saving on ticks].
  MachineParameters def $
    noinline mkMachineVariantParameters def $
      CostModel unitCekMachineCosts unitCostBuiltinCostModel
