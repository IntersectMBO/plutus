-- editorconfig-checker-disable-file
{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}
-- | Functions for compiling PIR let terms.
module PlutusIR.Compiler.Let (compileLets, LetKind(..)) where

import PlutusIR
import PlutusIR.Compiler.Datatype
import PlutusIR.Compiler.Definitions
import PlutusIR.Compiler.Provenance
import PlutusIR.Compiler.Recursion
import PlutusIR.Compiler.Types
import PlutusIR.Error
import PlutusIR.MkPir qualified as PIR

import Control.Monad
import Control.Monad.Error.Lens
import Control.Monad.Trans

import Control.Lens hiding (Strict)

import Data.Foldable
import Data.List.NonEmpty hiding (partition, reverse)
import Data.List.NonEmpty qualified as NE
import PlutusCore.Pretty (display)

{- Note [Extra definitions while compiling let-bindings]
The let-compiling passes can generate some additional definitions, so we use the
support from 'Definitions' to ease this.

Specifically, only the recursive term pass should do this (it helps to share fixpoint combinators).
So putting in the definitions should mostly be a no-op, and we'll get errors if it's not.
It would be more elegant to somehow indicate that only one of the let-compiling passes needs
this, but this does the job.
Also we should pull out more stuff (e.g. see 'NonStrict' which uses unit).
-}

data LetKind = RecTerms | NonRecTerms | Types | DataTypes

-- | Compile the let terms out of a 'Term'. Note: the result does *not* have globally unique names.
compileLets :: Compiling m e uni fun a => LetKind -> PIRTerm uni fun a -> m (PIRTerm uni fun a)
compileLets kind t = getEnclosing >>= \p ->
    -- See Note [Extra definitions while compiling let-bindings]
    runDefT p $ transformMOf termSubterms (compileLet kind) t

compileLet :: Compiling m e uni fun a => LetKind -> PIRTerm uni fun a -> DefT SharedName uni fun (Provenance a) m (PIRTerm uni fun a)
compileLet kind = \case
    Let p r bs body -> withEnclosing (const $ LetBinding r p) $ case r of
            -- Right-associative fold because `let {b1;b2} in t` === `let {b1} in (let {b2} in t)`
            NonRec -> lift $ foldrM (compileNonRecBinding kind) body bs
            Rec    -> compileRecBindings kind body bs
    x -> pure x

compileRecBindings
    :: Compiling m e uni fun a
    => LetKind
    -> PIRTerm uni fun a
    -> NE.NonEmpty (Binding TyName Name uni fun (Provenance a))
    -> DefT SharedName uni fun (Provenance a) m (PIRTerm uni fun a)
compileRecBindings kind body bs =
  case grouped of
    singleGroup :| [] ->
      case NE.head singleGroup of
         TermBind {} -> compileRecTermBindings kind body singleGroup
         DatatypeBind {} ->  lift $ compileRecDataBindings kind body singleGroup
         tb@TypeBind {} ->
            lift $ getEnclosing >>= \p -> throwing _Error $
                CompilationError p
                    ("Type bindings cannot appear in recursive let, use datatypebind instead"
                    <> "The type binding is \n "
                    <> display tb)
    -- only one single group should appear, we do not allow mixing of bind styles
    _ -> lift $ getEnclosing >>= \p -> throwing _Error $ CompilationError p "Mixed term/type/data bindings in recursive let"
  where
        -- We group the bindings by their binding style, i.e.: term , data or type bindingstyle
        -- All bindings of a let should be of the same style; for that, we make use of the `groupWith1`
        -- and we expect to see exactly 1 group returned by it.
        -- The `NE.groupWith1` returns N>=1 of "adjacent" grouppings, compared to the similar `NE.groupAllWith1`
        -- which returns  at most 3 groups (1 => termbind, 2 -> typebind, 3 -> databind).
        -- `NE.groupAllWith1` is an overkill here, since we don't care about the minimal number of groups, just that there is exactly 1 group.
        grouped  = NE.groupWith1 (\case { TermBind {} -> 1 ::Int ; TypeBind {} -> 2; _ -> 3 }) bs

compileRecTermBindings
    :: Compiling m e uni fun a
    => LetKind
    -> PIRTerm uni fun a
    -> NE.NonEmpty (Binding TyName Name uni fun (Provenance a))
    -> DefT SharedName uni fun (Provenance a) m (PIRTerm uni fun a)
compileRecTermBindings RecTerms body bs = do
    binds <- forM bs $ \case
        TermBind _ Strict vd rhs -> pure $ PIR.Def vd rhs
        _ -> lift $ getEnclosing >>= \p -> throwing _Error $ CompilationError p "Internal error: type binding in term binding group"
    compileRecTerms body binds
compileRecTermBindings _ body bs = lift $ getEnclosing >>= \p -> pure $ Let p Rec bs body

compileRecDataBindings :: Compiling m e uni fun a => LetKind -> PIRTerm uni fun a -> NE.NonEmpty (Binding TyName Name uni fun (Provenance a)) -> m (PIRTerm uni fun a)
compileRecDataBindings DataTypes body bs = do
    binds <- forM bs $ \case
        DatatypeBind _ d -> pure d
        _ -> getEnclosing >>= \p -> throwing _Error $ CompilationError p "Internal error: term or type binding in datatype binding group"
    compileRecDatatypes body binds
compileRecDataBindings _ body bs = getEnclosing >>= \p -> pure $ Let p Rec bs body

compileNonRecBinding :: Compiling m e uni fun a => LetKind -> Binding TyName Name uni fun (Provenance a) -> PIRTerm uni fun a -> m (PIRTerm uni fun a)
compileNonRecBinding NonRecTerms (TermBind x Strict d rhs) body = withEnclosing (const $ TermBinding (varDeclNameString d) x) $
   PIR.mkImmediateLamAbs <$> getEnclosing <*> pure (PIR.Def d rhs) <*> pure body
compileNonRecBinding Types (TypeBind x d rhs) body = withEnclosing (const $ TypeBinding (tyVarDeclNameString d) x) $
   PIR.mkImmediateTyAbs <$> getEnclosing <*> pure (PIR.Def d rhs) <*> pure body
compileNonRecBinding DataTypes (DatatypeBind x d) body = withEnclosing (const $ TypeBinding (datatypeNameString d) x) $
   compileDatatype NonRec body d
compileNonRecBinding _ b body = getEnclosing >>= \p -> pure $ Let p NonRec (pure b) body
