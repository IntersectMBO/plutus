{-# LANGUAGE ConstraintKinds   #-}
{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE Rank2Types        #-}
{-# LANGUAGE TypeFamilies      #-}
{-# LANGUAGE TypeOperators     #-}

module PlutusTx.Compiler.Types where

import           PlutusTx.Compiler.Error
import           PlutusTx.PLCTypes

import           PlutusIR.Compiler.Definitions

import qualified PlutusCore.Constant           as PLC
import qualified PlutusCore.Default            as PLC
import           PlutusCore.Quote
import qualified PlutusCore.Universe           as PLC

import qualified FamInstEnv                    as GHC
import qualified GhcPlugins                    as GHC

import           Control.Monad.Except
import           Control.Monad.Reader

import qualified Data.List.NonEmpty            as NE
import qualified Data.Map                      as Map
import qualified Data.Set                      as Set

import qualified Language.Haskell.TH.Syntax    as TH

type BuiltinNameInfo = Map.Map TH.Name GHC.TyThing

-- | Compilation options. Empty currently.
data CompileOptions = CompileOptions {}

data CompileContext uni fun = CompileContext {
    ccOpts            :: CompileOptions,
    ccFlags           :: GHC.DynFlags,
    ccFamInstEnvs     :: GHC.FamInstEnvs,
    ccBuiltinNameInfo :: BuiltinNameInfo,
    ccScopes          :: ScopeStack uni fun,
    ccBlackholed      :: Set.Set GHC.Name
    }

-- | A wrapper around 'GHC.Name' with a stable 'Ord' instance. Use this where the ordering
-- will affect the output of the compiler, i.e. when sorting or so on. It's  fine to use
-- 'GHC.Name' if we're just putting them in a 'Set.Set', for example.
--
-- The 'Eq' instance we derive - it's also not stable across builds, but I believe this is only
-- a problem if you compare things from different builds, which we don't do.
newtype LexName = LexName GHC.Name
    deriving (Eq)

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
    (GHC.moduleUnitId m1 `GHC.stableUnitIdCmp` GHC.moduleUnitId m2)

-- See Note [Scopes]
type Compiling uni fun m =
    ( Monad m
    , MonadError (CompileError uni fun) m
    , MonadQuote m
    , MonadReader (CompileContext uni fun) m
    , MonadDefs LexName uni fun () m
    , PLC.GShow uni, PLC.GEq uni
    , PLC.ToBuiltinMeaning uni fun
    )

-- Packing up equality constraints gives us a nice way of writing type signatures as this way
-- we don't need to write 'PLC.DefaultUni' everywhere (in 'PIRTerm', 'PIRType' etc) and instead
-- can write the short @uni@ and know that it actually means 'PLC.DefaultUni'. Same regarding
-- 'DefaultFun'.
type CompilingDefault uni fun m =
    ( uni ~ PLC.DefaultUni
    , fun ~ PLC.DefaultFun
    , Compiling uni fun m
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

So we have the usual mechanism of carrying around a stack of scopes.
-}

data Scope uni fun = Scope (Map.Map GHC.Name (PLCVar uni fun)) (Map.Map GHC.Name PLCTyVar)
type ScopeStack uni fun = NE.NonEmpty (Scope uni fun)

initialScopeStack :: ScopeStack uni fun
initialScopeStack = pure $ Scope Map.empty Map.empty
