-- editorconfig-checker-disable-file
{-# LANGUAGE ConstraintKinds   #-}
{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE Rank2Types        #-}
{-# LANGUAGE TypeFamilies      #-}
{-# LANGUAGE TypeOperators     #-}

module PlutusTx.Compiler.Types (
    module PlutusTx.Compiler.Types,
    module PlutusCore.Annotation
    ) where

import PlutusTx.Compiler.Error
import PlutusTx.Coverage
import PlutusTx.PLCTypes

import PlutusIR.Compiler.Definitions

import PlutusCore.Annotation
import PlutusCore.Builtin qualified as PLC
import PlutusCore.Default qualified as PLC
import PlutusCore.Quote

import GHC qualified
import GHC.Core.FamInstEnv qualified as GHC
import GHC.Plugins qualified as GHC

import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Writer

import Data.Map qualified as Map
import Data.Set (Set)
import Data.Set qualified as Set

import Language.Haskell.TH.Syntax qualified as TH
import Prettyprinter

type NameInfo = Map.Map TH.Name GHC.TyThing

-- | Compilation options.
data CompileOptions = CompileOptions {
      coProfile     :: ProfileOpts
    , coCoverage    :: CoverageOpts
    , coRemoveTrace :: Bool
    }

data CompileContext uni fun = CompileContext {
    ccOpts                    :: CompileOptions,
    ccFlags                   :: GHC.DynFlags,
    ccFamInstEnvs             :: GHC.FamInstEnvs,
    ccNameInfo                :: NameInfo,
    ccScope                   :: Scope uni,
    ccBlackholed              :: Set.Set GHC.Name,
    ccCurDef                  :: Maybe LexName,
    ccModBreaks               :: Maybe GHC.ModBreaks,
    ccBuiltinSemanticsVariant :: PLC.BuiltinSemanticsVariant fun,
    ccBuiltinCostModel        :: PLC.CostingPart uni fun,
    ccDebugTraceOn            :: Bool
    }

data CompileState = CompileState
    { -- | The ID of the next step to be taken by the PlutusTx compiler.
      -- This is used when generating debug traces.
      csNextStep      :: Int
      -- | The IDs of the previous steps taken by the PlutusTx compiler leading up to
      -- the current point. This is used when generating debug traces.
    , csPreviousSteps :: [Int]
    }

-- | Verbosity level of the Plutus Tx compiler.
data Verbosity =
    Quiet
    | Verbose
    | Debug
    deriving stock (Eq, Show)

instance Pretty Verbosity where
    pretty = viaShow

-- | Profiling options. @All@ profiles everything. @None@ is the default.
data ProfileOpts =
    All -- set this with -fplugin-opt PlutusTx.Plugin:profile-all
    | None
    deriving stock (Eq, Show)

instance Pretty ProfileOpts where
    pretty = viaShow

-- | Coverage options
-- See Note [Coverage annotations]
data CoverageOpts = CoverageOpts { unCoverageOpts :: Set CoverageType }

-- | Get the coverage types we are using
activeCoverageTypes :: CompileOptions -> Set CoverageType
activeCoverageTypes = unCoverageOpts . coCoverage

-- | Option `{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:coverage-all #-}` enables all these
-- See Note [Adding more coverage annotations].
-- See Note [Coverage order]
data CoverageType = LocationCoverage -- ^ Check that all source locations that we can identify in GHC Core have been covered.
                                     -- For this to work at all we need `{-# OPTIONS_GHC -g #-}`
                                     -- turn on with `{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:coverage-location #-}`
                  | BooleanCoverage -- ^ Check that every boolean valued expression that isn't `True` or `False` for which
                                    -- we know the source location have been covered. For this to work at all we need
                                    -- `{-# OPTIONS_GHC -g #-}` turn on with
                                    -- `{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:coverage-boolean #-}`
                    deriving stock (Ord, Eq, Show, Enum, Bounded)

{- Note [Coverage order]
   The order in which `CoverageType` constructors appear in the type determine the order in
   which their respective transformations in `coverageCompile` will be executed. The topmost `CoverageType`
   will be executed first, followed by the second from the top and so on. It is important to either:
   1. Never add coverage transformations that don't commute or
   2. BE VERY CAREFUL!
   Currently we are employing option (1). Please don't change that unless you know what you're doing
   and you've read the code of `coverageCompile` carefully.
-}

-- | A wrapper around 'GHC.Name' with a stable 'Ord' instance. Use this where the ordering
-- will affect the output of the compiler, i.e. when sorting or so on. It's  fine to use
-- 'GHC.Name' if we're just putting them in a 'Set.Set', for example.
--
-- The 'Eq' instance we derive - it's also not stable across builds, but I believe this is only
-- a problem if you compare things from different builds, which we don't do.
newtype LexName = LexName GHC.Name
    deriving stock (Eq)

instance Show LexName where
    show (LexName n) = GHC.occNameString $ GHC.occName n

instance Ord LexName where
    compare (LexName n1) (LexName n2) =
        case stableNameCmp n1 n2 of
            -- This case is not sound if the names are generated, so we have to
            -- fall back on the default sound comparison for names. This is
            -- non-deterministic! But we care even more about not mixing up things
            -- that are different than we do about determinism.
            EQ -> compare n1 n2
            o  -> o

{- Note [Stable name comparisons]
GHC defines `stableNameCmp` which does a good job of being a stable name
comparator across compiles. *However*, it includes, indirectly, the unit
id that a name comes from, including the hash. While this is stable across
compiles of exactly the same thing, it is *not* stable across compiles
in slightly different environments, e.g. with cabal new-build vs with nix.

This matters since that can eventually affect our test output.

We partially fix this by making the comparison less likely to consult the
unstable unit id. We do this by just flipping the order in which we consult
components: normally GHC looks at the unit id first, then the module name, then
the `OccName`. We do it in the opposite order.

While we can still get instability from this, it should now only happen
if we have a binding with the same name in the same module name but from
different units.

We would like to just copy GHC's implementation and tweak it, but it relies
on non-exported data constructors, so we have to write our own. This is mostly
the same, but e.g. we can't look directly at the "sort" of a `Name`.
-}

-- | Our own version of 'GHC.stableNameCmp'.
stableNameCmp :: GHC.Name -> GHC.Name -> Ordering
stableNameCmp n1 n2 =
    (GHC.occName n1 `compare` GHC.occName n2) <>
    -- See Note [Stable name comparisons]
    maybeCmp stableModuleCmp (GHC.nameModule_maybe n1) (GHC.nameModule_maybe n2)
    where
        maybeCmp :: (a -> a -> Ordering) -> Maybe a -> Maybe a -> Ordering
        maybeCmp cmp (Just l) (Just r) = l `cmp` r
        maybeCmp _ Nothing (Just _)    = LT
        maybeCmp _ (Just _) Nothing    = GT
        maybeCmp _ Nothing Nothing     = EQ

-- | Our own version of 'GHC.stableModuleCmp'.
stableModuleCmp :: GHC.Module -> GHC.Module -> Ordering
stableModuleCmp m1 m2 =
    (GHC.moduleName m1 `GHC.stableModuleNameCmp` GHC.moduleName m2) <>
    -- See Note [Stable name comparisons]
    (GHC.moduleUnit m1 `GHC.stableUnitCmp` GHC.moduleUnit m2)

-- See Note [Scopes]
type Compiling uni fun m ann =
    ( MonadError (CompileError uni fun ann) m
    , MonadQuote m
    , MonadReader (CompileContext uni fun) m
    , MonadState CompileState m
    , MonadDefs LexName uni fun Ann m
    , MonadWriter CoverageIndex m
    )

-- Packing up equality constraints gives us a nice way of writing type signatures as this way
-- we don't need to write 'PLC.DefaultUni' everywhere (in 'PIRTerm', 'PIRType' etc) and instead
-- can write the short @uni@ and know that it actually means 'PLC.DefaultUni'. Same regarding
-- 'DefaultFun'.
type CompilingDefault uni fun m ann =
    ( uni ~ PLC.DefaultUni
    , fun ~ PLC.DefaultFun
    , Compiling uni fun m ann
    )

blackhole :: MonadReader (CompileContext uni fun) m => GHC.Name -> m a -> m a
blackhole name = local (\cc -> cc {ccBlackholed=Set.insert name (ccBlackholed cc)})

blackholed :: MonadReader (CompileContext uni fun) m => GHC.Name -> m Bool
blackholed name = do
    CompileContext {ccBlackholed=bh} <- ask
    pure $ Set.member name bh

{- Note [Scopes]
We need a notion of scope, because we have to make sure that if we convert a GHC
Var into a variable, then we always convert it into the same variable, while also making
sure that if we encounter multiple things with the same name we produce fresh variables
appropriately.

We keep the scope in a `Reader` monad, so any modifications are only local.
-}

data Scope uni = Scope (Map.Map GHC.Name (PLCVar uni)) (Map.Map GHC.Name PLCTyVar)

initialScope :: Scope uni
initialScope = Scope Map.empty Map.empty

withCurDef :: Compiling uni fun m ann => LexName -> m a -> m a
withCurDef name = local (\cc -> cc {ccCurDef=Just name})

modifyCurDeps :: Compiling uni fun m ann => (Set.Set LexName -> Set.Set LexName) -> m ()
modifyCurDeps f = do
    cur <- asks ccCurDef
    case cur of
        Nothing -> pure ()
        Just n  -> modifyDeps n f
