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

import Control.Lens (forMOf, mapMOf)
import Control.Monad.State
import Control.Monad.Writer

import PlutusCore.Analysis.Definitions hiding (runTermDefs, termDefs)

-- | Add bindings to definition maps. The binding's subterms and subtypes are handled in another
-- traversal.
addBindingDef :: (Ord ann,
    HasUnique name TermUnique,
    HasUnique tyname TypeUnique,
    MonadState (UniqueInfos ann) m,
    MonadWriter [UniqueError ann] m)
    => Binding tyname name uni fun ann -> m ()
addBindingDef bd = case bd of
    TermBind _a _s (VarDecl varAnn n varTy) _ -> do
        addDef n varAnn TermScope
        void $ typeDefs varTy
    TypeBind _a (TyVarDecl tyAnn tyN  _) ty -> do
        addDef tyN tyAnn TypeScope
        void $ typeDefs ty
    DatatypeBind
        _a
        (Datatype
            dataAnn
            (TyVarDecl tyAnn tyN  _)
            tyVarDecls
            dataName
            varDecls
        ) -> do
        let addTyVarDecl :: (Ord ann,
                HasUnique tyname TypeUnique,
                MonadState (UniqueInfos ann) m,
                MonadWriter [UniqueError ann] m)
                => TyVarDecl tyname ann -> m ()
            addTyVarDecl (TyVarDecl tyVarAnn tyVarN  _) =
                addDef tyVarN tyVarAnn TypeScope
            addVarDecl :: (Ord ann,
                HasUnique name TermUnique,
                HasUnique tyname TypeUnique,
                MonadState (UniqueInfos ann) m,
                MonadWriter [UniqueError ann] m)
                => VarDecl tyname name uni ann -> m ()
            addVarDecl (VarDecl varAnn n varTy) = do
                addDef n varAnn TermScope
                void $ typeDefs varTy
        addDef dataName dataAnn TermScope
        addDef tyN tyAnn TypeScope
        forM_ tyVarDecls addTyVarDecl
        forM_ varDecls addVarDecl
        forM_ varDecls (typeDefs . _varDeclType)

-- | Given a PIR term, add all of its term and type definitions and usages, including its subterms
-- and subtypes, to a global map.
termDefs
    :: (Ord ann,
        HasUnique name TermUnique,
        HasUnique tyname TypeUnique,
        MonadState (UniqueInfos ann) m,
        MonadWriter [UniqueError ann] m)
    => Term tyname name uni fun ann
    -> m (Term tyname name uni fun ann)
termDefs tm =
    case tm of
        Let _ann _r bindings _rhs -> do
            forM_ bindings addBindingDef
            void $ forMOf termSubterms tm termDefs
            forMOf termSubtypes tm typeDefs
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
            void $ forMOf termSubterms tm termDefs
            forMOf termSubtypes tm typeDefs
        TyInst _ _ ty     -> do
            void $ typeDefs ty
            forMOf termSubterms tm termDefs
        _                  -> do
            void $ forMOf termSubterms tm termDefs
            forMOf termSubtypes tm typeDefs

runTermDefs
    :: (Ord ann,
        HasUnique name TermUnique,
        HasUnique tyname TypeUnique,
        Monad m)
    => Term tyname name uni fun ann
    -> m (UniqueInfos ann, [UniqueError ann])
runTermDefs = runWriterT . flip execStateT mempty . termDefs
