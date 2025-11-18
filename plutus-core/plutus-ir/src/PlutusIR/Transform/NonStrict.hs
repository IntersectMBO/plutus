-- editorconfig-checker-disable-file
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}

-- | Compile non-strict bindings into strict bindings.
module PlutusIR.Transform.NonStrict (compileNonStrictBindings, compileNonStrictBindingsPass, compileNonStrictBindingsPassSC) where

import PlutusIR
import PlutusIR.Subst
import PlutusIR.Transform.Rename ()

import PlutusCore.Quote
import PlutusCore.StdLib.Data.ScottUnit qualified as Unit

import Control.Lens hiding (Strict)
import Control.Monad.State

import Data.Map qualified as Map
import PlutusCore qualified as PLC
import PlutusIR.Pass
import PlutusIR.TypeCheck qualified as TC

{- Note [Compiling non-strict bindings]
Given `let x : ty = rhs in body`, we
- Replace `let x : ty = rhs in ...` with `let x : () -> ty = \arg : () -> rhs in ...`
- Replace all references to `x` in `body` with `x ()`

To avoid quadratic behaviour, we do the latter substitution in one go, by collecting
all the substitutions to do as we go, and then doing them in one go at the end.

Since we are constructing a global substitution, so we need globally unique
names to avoid clashes.
-}

{- Note [Using unit versus force/delay]
We don't have force/delay in PIR, but we can use trivial type-abstractions and instantiations,
which will erase to force and delay in UPLC. Not quite as nice, but it doesn't require an extension
to the language.

However, we retain the *option* to use unit-lambdas instead, since we rely on this pass to
handle recursive, non-function bindings and give them function types. `delayed x` is not a
function type but `() -> x` is!
-}

type Substs uni fun a = Map.Map Name (Term TyName Name uni fun a)

compileNonStrictBindingsPassSC
  :: (PLC.Typecheckable uni fun, PLC.GEq uni, MonadQuote m, Ord a)
  => TC.PirTCConfig uni fun
  -> Bool
  -> Pass m TyName Name uni fun a
compileNonStrictBindingsPassSC tcConfig useUnit =
  renamePass <> compileNonStrictBindingsPass tcConfig useUnit

compileNonStrictBindingsPass
  :: (PLC.Typecheckable uni fun, PLC.GEq uni, MonadQuote m)
  => TC.PirTCConfig uni fun
  -> Bool
  -> Pass m TyName Name uni fun a
compileNonStrictBindingsPass tcConfig useUnit =
  NamedPass "compile non-strict bindings" $
    Pass
      (compileNonStrictBindings useUnit)
      [Typechecks tcConfig]
      [ConstCondition (Typechecks tcConfig)]

{-| Compile all the non-strict bindings in a term into strict bindings. Note: requires globally
unique names. -}
compileNonStrictBindings :: MonadQuote m => Bool -> Term TyName Name uni fun a -> m (Term TyName Name uni fun a)
compileNonStrictBindings useUnit t = do
  (t', substs) <- liftQuote $ flip runStateT mempty $ strictifyTerm useUnit t
  -- See Note [Compiling non-strict bindings]
  pure $ termSubstNames (\n -> Map.lookup n substs) t'

strictifyTerm
  :: (MonadState (Substs uni fun a) m, MonadQuote m)
  => Bool -> Term TyName Name uni fun a -> m (Term TyName Name uni fun a)
strictifyTerm useUnit =
  -- See Note [Using unit versus force/delay]
  let transformation = if useUnit then strictifyBindingWithUnit else strictifyBinding
   in transformMOf termSubterms (traverseOf termBindings transformation)

strictifyBinding
  :: (MonadState (Substs uni fun a) m, MonadQuote m)
  => Binding TyName Name uni fun a -> m (Binding TyName Name uni fun a)
strictifyBinding = \case
  TermBind x NonStrict (VarDecl x' name ty) rhs -> do
    -- The annotation to use for new synthetic nodes
    let ann = x'

    a <- freshTyName "dead"
    -- See Note [Compiling non-strict bindings]
    modify $ Map.insert name $ TyInst ann (Var ann name) (TyForall ann a (Type ann) (TyVar ann a))

    pure $ TermBind x Strict (VarDecl x' name (TyForall ann a (Type ann) ty)) (TyAbs ann a (Type ann) rhs)
  x -> pure x

strictifyBindingWithUnit
  :: (MonadState (Substs uni fun a) m, MonadQuote m)
  => Binding TyName Name uni fun a -> m (Binding TyName Name uni fun a)
strictifyBindingWithUnit = \case
  TermBind x NonStrict (VarDecl x' name ty) rhs -> do
    -- The annotation to use for new synthetic nodes
    let ann = x'

    argName <- liftQuote $ freshName "arg"
    -- TODO: These are created at every use site, we should bind them globally
    let unit = ann <$ Unit.unit
        unitval = ann <$ Unit.unitval
        forced = Apply ann (Var ann name) unitval

    -- See Note [Compiling non-strict bindings]
    modify $ Map.insert name forced

    pure $ TermBind x Strict (VarDecl x' name (TyFun ann unit ty)) (LamAbs ann argName unit rhs)
  x -> pure x
