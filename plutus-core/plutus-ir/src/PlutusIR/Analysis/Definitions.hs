{-# LANGUAGE LambdaCase #-}
-- | Definition analysis for Plutus IR.
-- This just adapts term-related code from PlutusCore.Analysis.Definitions;
-- we just re-use the typed machinery to do the hard work here.
module PlutusIR.Analysis.Definitions
    ( UniqueInfos
    , termDefs
    , runTermDefs
    ) where

import Data.Functor.Foldable
import PlutusCore.Error
import PlutusCore.Name
import PlutusIR.Core
import PlutusIR.Core.Instance.Recursive (TermF (IWrapF, LamAbsF, LetF, TyAbsF, TyInstF, VarF))

import Control.Monad.State
import Control.Monad.Writer

import PlutusCore.Analysis.Definitions hiding (runTermDefs, termDefs)

termDefs
    :: (Ord ann,
        HasUnique name TermUnique,
        HasUnique tyname TypeUnique,
        MonadState (UniqueInfos ann) m,
        MonadWriter [UniqueError ann] m)
    => Term tyname name uni fun ann
    -> m ()
termDefs =
    let -- Add bindings to definition maps.
        -- addBindingDef :: Binding tyname name uni fun ann -
        addBindingDef (TermBind _tmAnn _tmStrict (VarDecl varAnn n varTy) tm) =
            addDef n varAnn TermScope >> typeDefs varTy >> tm
        addBindingDef (TypeBind _tyBindingAnn (TyVarDecl tyN tyAnn _) ty) =
            addDef tyN tyAnn TypeScope >> typeDefs ty
        addBindingDef
            (DatatypeBind
                _a
                (Datatype dataAnn _ _ dataName _)) =
            addDef dataName dataAnn TermScope
    in
    cata $ \case
        LetF ann r bindings term -> do
            mapM_ addBindingDef bindings >> term
        VarF ann n         -> addUsage n ann TermScope
        LamAbsF ann n ty t -> addDef n ann TermScope >> typeDefs ty >> t
        IWrapF _ pat arg t -> typeDefs pat >> typeDefs arg >> t
        TyAbsF ann tn _ t  -> addDef tn ann TypeScope >> t
        TyInstF _ t ty     -> t >> typeDefs ty
        x                  -> sequence_ x

runTermDefs
    :: (Ord ann,
        HasUnique name TermUnique,
        HasUnique tyname TypeUnique,
        Monad m)
    => Term tyname name uni fun ann
    -> m (UniqueInfos ann, [UniqueError ann])
runTermDefs = runWriterT . flip execStateT mempty . termDefs
