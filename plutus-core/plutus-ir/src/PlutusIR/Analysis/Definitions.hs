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

-- | Add bindings and their subterms and subtypes to definition maps.
addBindingDef :: (Ord ann,
    HasUnique name TermUnique,
    HasUnique tyname TypeUnique,
    MonadState (UniqueInfos ann) m,
    MonadWriter [UniqueError ann] m)
    => Binding tyname name uni fun ann -> m ()
addBindingDef bd = case bd of
    TermBind _a _s (VarDecl varAnn n _) rhs -> do
        addDef n varAnn TermScope
        void $ termDefs rhs
        void $ forMOf termSubtypes rhs typeDefs
    TypeBind _a (TyVarDecl tyAnn tyN  _) rhs -> do
        addDef tyN tyAnn TypeScope
        void $ typeDefs rhs
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
                MonadState (UniqueInfos ann) m,
                MonadWriter [UniqueError ann] m)
                => VarDecl tyname name uni ann -> m ()
            addVarDecl (VarDecl varAnn n _) = do
                addDef n varAnn TermScope
        addDef dataName dataAnn TermScope
        addDef tyN tyAnn TypeScope
        forM_ tyVarDecls addTyVarDecl
        forM_ varDecls addVarDecl

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
        Let _ann _r bindings rhs -> do
            forM_ bindings addBindingDef
            void $ termDefs rhs
            forMOf termSubtypes rhs typeDefs
        Var ann n         -> do
            addUsage n ann TermScope
            pure tm
        LamAbs ann n ty t -> do
            addDef n ann TermScope
            void $ typeDefs ty
            termDefs t
        IWrap _ pat arg t -> do
            void $ typeDefs pat
            void $ typeDefs arg
            termDefs t
        TyAbs ann tn _ t  -> do
            addDef tn ann TypeScope
            void $ termDefs t
            forMOf termSubtypes tm typeDefs
        TyInst _ t ty     -> do
            void $ typeDefs ty
            termDefs t
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
