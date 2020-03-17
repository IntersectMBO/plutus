{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}
-- | Compile non-strict bindings into strict bindings.
module Language.PlutusIR.Transform.NonStrict (compileNonStrictBindings) where

import           Language.PlutusIR
import           Language.PlutusIR.Transform.Rename        ()
import           Language.PlutusIR.Transform.Substitute

import           Language.PlutusCore.Quote
import qualified Language.PlutusCore.StdLib.Data.ScottUnit as Unit

import           Control.Lens                              hiding (Strict)
import           Control.Monad.State

import qualified Data.Map                                  as Map

{- Note [Compiling non-strict bindings]
Given `let x : ty = rhs in body`, we
- Replace `let x : ty = rhs in ...` with `let x : () -> ty = \arg : () -> rhs in ...`
- Replace all references to `x` in `body` with `x ()`

To avoid quadratic behaviour, we do the latter substitution in one go, by collecting
all the substitutions to do as we go, and then doing them in one go at the end.

Since we are constructing a global substitution, so we need globally unique
names to avoid clashes.
-}

type Substs uni a = Map.Map (Name a) (Term TyName Name uni a)

-- | Compile all the non-strict bindings in a term into strict bindings. Note: requires globally
-- unique names.
compileNonStrictBindings :: MonadQuote m => Term TyName Name uni a -> m (Term TyName Name uni a)
compileNonStrictBindings t = do
    (t', substs) <- liftQuote $ flip runStateT mempty $ strictifyTerm t
    -- See Note [Compiling non-strict bindings]
    pure $ termSubstNames (\n -> Map.lookup n substs) t'

strictifyTerm
    :: (MonadState (Substs uni a) m, MonadQuote m)
    => Term TyName Name uni a -> m (Term TyName Name uni a)
strictifyTerm = transformMOf termSubterms (traverseOf termBindings strictifyBinding)

strictifyBinding
    :: (MonadState (Substs uni a) m, MonadQuote m)
    => Binding TyName Name uni a -> m (Binding TyName Name uni a)
strictifyBinding = \case
    TermBind x NonStrict (VarDecl x' name ty) rhs -> do
        let ann = x

        argName <- liftQuote $ freshName ann "arg"
        -- TODO: These are created at every use site, we should bind them globally
        let unit = ann <$ Unit.unit
            unitval = ann <$ Unit.unitval
            forced = Apply ann (Var ann name) unitval

        -- See Note [Compiling non-strict bindings]
        modify $ Map.insert name forced

        pure $ TermBind x Strict (VarDecl x' name (TyFun ann unit ty)) (LamAbs ann argName unit rhs)
    x -> pure x
