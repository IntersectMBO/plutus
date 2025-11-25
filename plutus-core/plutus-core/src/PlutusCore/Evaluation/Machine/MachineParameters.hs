-- editorconfig-checker-disable-file
{-# LANGUAGE DeriveAnyClass  #-}
{-# LANGUAGE StrictData      #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies    #-}
{-# LANGUAGE TypeOperators   #-}

module PlutusCore.Evaluation.Machine.MachineParameters
where

import PlutusCore (UniOf)
import PlutusCore.Builtin

import Control.DeepSeq
import Control.Lens
import GHC.Exts (inline)
import GHC.Generics
import NoThunks.Class

{-| We need to account for the costs of evaluator steps and also built-in function
   evaluation.  The models for these have different structures and are used in
   different parts of the code, so inside the valuator we pass separate objects
   about most of the time .  It's convenient for clients of the evaluator to
   only have to worry about a single object, so the CostModel type bundles the
   two together.  We could conceivably have different evaluators with different
   internal costs, so we keep the machine costs abstract.  The model for Cek
   machine steps is in UntypedPlutusCore.Evaluation.Machine.Cek.CekMachineCosts.
-}
data CostModel machinecosts builtincosts =
    CostModel {
      _machineCostModel :: machinecosts
    , _builtinCostModel :: builtincosts
    } deriving stock (Eq, Show)
makeLenses ''CostModel

-- | The part of 'MachineParameters' that is individual for each semantics variant of 'DefaultFun'.
--
-- 'CaserBuiltin' isn't included, because it only explicitly depends on the protocol version and not
-- the language version (even though there's an implicit dependency on the language version: older
-- languages don't support 'Case' in general, but it's safe to ignore that, because support for
-- 'Case' is controlled by the AST version, which is a separate check during deserialisation).
data MachineVariantParameters machineCosts fun val =
    MachineVariantParameters {
      machineCosts    :: machineCosts
    , builtinsRuntime :: BuiltinsRuntime fun val
    }
    deriving stock Generic
    deriving anyclass (NFData)

{-| At execution time we need a 'BuiltinsRuntime' object which includes both the cost model for
builtins and their denotations. This bundles one of those together with the cost model for evaluator
steps and a 'CaserBuiltin' specifying how casing on values of built-in types works.
The @val@ type will be 'CekValue' when we're using this with the CEK machine.
-}
data MachineParameters machineCosts fun val =
    MachineParameters {
      machineCaserBuiltin      :: CaserBuiltin (UniOf val)
    , machineLeterBuiltin      :: LeterBuiltin (UniOf val)
    , machineVariantParameters :: MachineVariantParameters machineCosts fun val
    }
    deriving stock Generic
    deriving anyclass (NFData)

-- For some reason the generic instance gives incorrect nothunk errors,
-- see https://github.com/input-output-hk/nothunks/issues/24
instance (NoThunks machinecosts, Bounded fun, Enum fun) => NoThunks (MachineVariantParameters machinecosts fun val) where
  wNoThunks ctx (MachineVariantParameters costs runtime) =
      allNoThunks [ noThunks ctx costs, noThunks ctx runtime ]

instance (NoThunks machinecosts, Bounded fun, Enum fun) => NoThunks (MachineParameters machinecosts fun val) where
  wNoThunks ctx (MachineParameters caser leter varPars) =
      allNoThunks [ noThunks ctx caser, noThunks ctx leter, noThunks ctx varPars ]

{- Note [The CostingPart constraint in mkMachineVariantParameters]
Discharging the @CostingPart uni fun ~ builtincosts@ constraint in 'mkMachineParameters' causes GHC
to fail to inline the function at its call site regardless of the @INLINE@ pragma and an explicit
'inline' call.

We think that this is because discharging the @CostingPart uni fun ~ builtincosts@ constraint in the
type of 'mkMachineParameters' somehow causes it to be compiled into @expr `Cast@` co@ , where @co@'s
type is

    (CostingPart DefaultUni DefaultFun) ... ~R# ... BuiltinCostModel ...

and this fails to inline, because in order for @inline f@ to work, @f@ must be compiled into either
a @Var@, or an @App@ whose head is a @Var@, according to https://gitlab.haskell.org/ghc/ghc/-/blob/1f02b7430b2fbab403d7ffdde9cfd006e884678e/compiler/prelude/PrelRules.hs#L1442-1449
And if @f@ is compiled into a @Cast@ like 'mkMachineParameters' with the discharged constraint, then
inlining won't work. We don't know why it's implemented this way in GHC.

It seems fully applying @f@ helps, i.e.

    - inline mkMachineParameters unlMode <$> <...>
    + (\x -> inline (mkMachineParameters unlMode x)) <$> <...>

which makes sense: if @f@ receives all its type and term args then there's less reason to throw a
@Cast@ in there.
-}

-- See Note [Inlining meanings of builtins].
{-| This just uses 'toBuiltinsRuntime' function to convert a BuiltinCostModel to a BuiltinsRuntime. -}
mkMachineVariantParameters ::
    ( -- WARNING: do not discharge the equality constraint as that causes GHC to fail to inline the
      -- function at its call site, see Note [The CostingPart constraint in mkMachineParameters].
      CostingPart uni fun ~ builtincosts
    , HasMeaningIn uni val
    , ToBuiltinMeaning uni fun
    )
    => BuiltinSemanticsVariant fun
    -> CostModel machineCosts builtincosts
    -> MachineVariantParameters machineCosts fun val
mkMachineVariantParameters semvar (CostModel mchnCosts builtinCosts) =
    MachineVariantParameters mchnCosts $ inline toBuiltinsRuntime semvar builtinCosts
{-# INLINE mkMachineVariantParameters #-}
