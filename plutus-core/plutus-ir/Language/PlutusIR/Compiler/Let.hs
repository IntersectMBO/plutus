{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}
-- | Functions for compiling PIR let terms.
module Language.PlutusIR.Compiler.Let (compileLets, LetKind(..)) where

import           Language.PlutusIR
import           Language.PlutusIR.Compiler.Datatype
import           Language.PlutusIR.Compiler.Definitions
import           Language.PlutusIR.Compiler.Provenance
import           Language.PlutusIR.Compiler.Recursion
import           Language.PlutusIR.Compiler.Types
import           Language.PlutusIR.Error
import qualified Language.PlutusIR.MkPir                as PIR

import           Control.Monad
import           Control.Monad.Error.Lens
import           Control.Monad.Trans

import           Control.Lens                           hiding (Strict)

import           Data.List.NonEmpty                     hiding (partition, reverse)
import qualified Data.List.NonEmpty                     as NE

{- Note [Extra definitions while compiling let-bindings]
The let-compiling passes can generate some additional definitions, so we use the
support from 'Definitions' to ease this.

Specifically, only the recursive term pass should do this (it helps to share fixpoint combinators).
So putting in the definitions should mostly be a no-op, and we'll get errors if it's not.
It would be more elegant to somehow indicate that only one of the let-compiling passes needs
this, but this does the job.
Also we should pull out more stuff (e.g. see 'NonStrict' which uses unit).
-}

{- Note [Right-associative compilation of let-bindings for linear scoping]

The 'foldM' function for lists is left-associative, but we need right-associative for our case, i.e.
every right let must be wrapped/scoped by its left let

An pseudocode PIR example:
let b1 = rhs1;
    b2 = rhs2  (b1 is visible in rhs2);
in ...

must be treated the same as let b1 = rhs in (let b2 = rhs2 in ... )

Since there is no 'foldrM' in the stdlib, so we first reverse the bindings list,
and then apply the left-associative 'foldM' on them,
which yields the same results as doing a right-associative fold.
-}

data LetKind = RecTerms | NonRecTerms | Types

-- | Compile the let terms out of a 'Term'. Note: the result does *not* have globally unique names.
compileLets :: Compiling m e uni a => LetKind -> PIRTerm uni a -> m (PIRTerm uni a)
compileLets kind t = getEnclosing >>= \p ->
    -- See Note [Extra definitions while compiling let-bindings]
    runDefT p $ transformMOf termSubterms (compileLet kind) t

compileLet :: Compiling m e uni a => LetKind -> PIRTerm uni a -> DefT SharedName uni (Provenance a) m (PIRTerm uni a)
compileLet kind = \case
    Let p r bs body -> withEnclosing (const $ LetBinding r p) $ case r of
            -- See Note [Right-associative compilation of let-bindings for linear scoping]
            NonRec -> lift $ foldM (compileNonRecBinding kind) body (NE.reverse bs)
            Rec    -> compileRecBindings kind body bs
    x -> pure x

compileRecBindings
    :: Compiling m e uni a
    => LetKind
    -> PIRTerm uni a
    -> NE.NonEmpty (Binding TyName Name uni (Provenance a))
    -> DefT SharedName uni (Provenance a) m (PIRTerm uni a)
compileRecBindings kind body bs =
  case grouped of
    singleGroup :| [] ->
      case NE.head singleGroup of
         TermBind {} -> compileRecTermBindings kind body singleGroup
         DatatypeBind {} ->  lift $ compileRecDataBindings kind body singleGroup
         TypeBind {} -> lift $ getEnclosing >>= \p -> throwing _Error $ CompilationError p "Type bindings cannot appear in recursive let, use datatypebind instead"
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
    :: Compiling m e uni a
    => LetKind
    -> PIRTerm uni a
    -> NE.NonEmpty (Binding TyName Name uni (Provenance a))
    -> DefT SharedName uni (Provenance a) m (PIRTerm uni a)
compileRecTermBindings RecTerms body bs = do
    binds <- forM bs $ \case
        TermBind _ Strict vd rhs -> pure $ PIR.Def vd rhs
        _ -> lift $ getEnclosing >>= \p -> throwing _Error $ CompilationError p "Internal error: type binding in term binding group"
    compileRecTerms body binds
compileRecTermBindings _ body bs = lift $ getEnclosing >>= \p -> pure $ Let p Rec bs body

compileRecDataBindings :: Compiling m e uni a => LetKind -> PIRTerm uni a -> NE.NonEmpty (Binding TyName Name uni (Provenance a)) -> m (PIRTerm uni a)
compileRecDataBindings Types body bs = do
    binds <- forM bs $ \case
        DatatypeBind _ d -> pure d
        _ -> getEnclosing >>= \p -> throwing _Error $ CompilationError p "Internal error: term or type binding in datatype binding group"
    compileRecDatatypes body binds
compileRecDataBindings _ body bs = getEnclosing >>= \p -> pure $ Let p Rec bs body

compileNonRecBinding :: Compiling m e uni a => LetKind -> PIRTerm uni a -> Binding TyName Name uni (Provenance a) -> m (PIRTerm uni a)
compileNonRecBinding NonRecTerms body (TermBind x Strict d rhs) = withEnclosing (const $ TermBinding (varDeclNameString d) x) $
   PIR.mkImmediateLamAbs <$> getEnclosing <*> pure (PIR.Def d rhs) <*> pure body
compileNonRecBinding Types body (TypeBind x d rhs) = withEnclosing (const $ TypeBinding (tyVarDeclNameString d) x) $
   PIR.mkImmediateTyAbs <$> getEnclosing <*> pure (PIR.Def d rhs) <*> pure body
compileNonRecBinding Types body (DatatypeBind x d) = withEnclosing (const $ TypeBinding (datatypeNameString d) x) $
   compileDatatype NonRec body d
compileNonRecBinding _ body b = getEnclosing >>= \p -> pure $ Let p NonRec (pure b) body
