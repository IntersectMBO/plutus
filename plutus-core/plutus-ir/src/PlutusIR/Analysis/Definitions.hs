-- | Definition analysis for Plutus IR.
-- This mostly adapts term-related code from PlutusCore.Analysis.Definitions;
-- we just re-use the typed machinery to do the hard work here.
module PlutusIR.Analysis.Definitions
    ( UniqueInfos
    , termDefs
    , runTermDefs
    ) where

import PlutusCore.Error (UniqueError)
import PlutusCore.Name
import PlutusIR.Core

import Control.Lens (forMOf)
import Control.Monad.State
import Control.Monad.Writer

import PlutusCore.Analysis.Definitions hiding (runTermDefs, termDefs)

termDefs
    :: (Ord ann,
        HasUnique name TermUnique,
        HasUnique tyname TypeUnique,
        MonadState (UniqueInfos ann) m,
        MonadWriter [UniqueError ann] m, Ord tyname)
    => Term tyname name uni fun ann
    -> m (Term tyname name uni fun ann)
termDefs tm =
    let -- Add bindings to definition maps.
        addBindingDef :: Binding tyname name uni fun ann -> m ()
        addBindingDef (TermBind _tmAnn _tmStrict (VarDecl varAnn n varTy) rhs) = do
            addDef n varAnn TermScope -- FIXME add to a *local* map instead
            void $ typeDefs varTy
            void $ forMOf termSubterms rhs termDefs
        addBindingDef (TypeBind _tyBindingAnn (TyVarDecl tyN tyAnn _) ty) = do
            addDef tyN tyAnn TypeScope
            void $ typeDefs ty
        addBindingDef
            (DatatypeBind
                _a
                (Datatype dataAnn _ _ dataName _)) = do
            addDef dataName dataAnn TermScope
            void $ forMOf termSubterms tm termDefs
    in
    case tm of
        Let ann r bindings rhs -> do
            mapM_ addBindingDef bindings
            forMOf termSubterms rhs termDefs
        Var ann n         -> do
            addUsage n ann TermScope
            pure tm
        LamAbs ann n ty _t -> do
            addDef n ann TermScope
            void $ typeDefs ty
            forMOf termSubterms tm termDefs
        IWrap _ pat arg _t -> do
            void $ typeDefs pat
            void $ typeDefs arg
            forMOf termSubterms tm termDefs
        TyAbs ann tn _ _  -> do
            addDef tn ann TypeScope
            forMOf termSubterms tm termDefs
        TyInst _ _ ty     -> do
            void $ typeDefs ty
            forMOf termSubterms tm termDefs
        _                  -> forMOf termSubterms tm termDefs

runTermDefs
    :: (Ord ann,
        HasUnique name TermUnique,
        HasUnique tyname TypeUnique,
        Monad m, Ord tyname)
    => Term tyname name uni fun ann
    -> m (UniqueInfos ann, [UniqueError ann])
runTermDefs = runWriterT . flip execStateT mempty . termDefs
