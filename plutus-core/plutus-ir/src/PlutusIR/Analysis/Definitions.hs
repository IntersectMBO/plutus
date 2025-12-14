{-# LANGUAGE LambdaCase #-}

{-| Definition analysis for Plutus IR.
This mostly adapts term-related code from PlutusCore.Analysis.Definitions;
we just re-use the typed machinery to do the hard work here. -}
module PlutusIR.Analysis.Definitions
  ( UniqueInfos
  , termDefs
  , runTermDefs
  ) where

import Control.Lens (forMOf_)
import Control.Monad (forM_)
import Control.Monad.State (MonadState, execStateT)
import Control.Monad.Writer (MonadWriter, runWriterT)
import PlutusCore.Error (UniqueError)
import PlutusCore.Name.Unique
import PlutusIR.Core.Plated
import PlutusIR.Core.Type

import PlutusCore.Analysis.Definitions hiding (runTermDefs, termDefs)

-- | Add declarations to definition maps.
addBindingDef
  :: ( Ord ann
     , HasUnique name TermUnique
     , HasUnique tyname TypeUnique
     , MonadState (UniqueInfos ann) m
     , MonadWriter [UniqueError ann] m
     )
  => Binding tyname name uni fun ann -> m ()
addBindingDef bd = case bd of
  TermBind _a _s (VarDecl varAnn n _) _ -> do
    addDef n varAnn TermScope
  TypeBind _a (TyVarDecl tyAnn tyN _) _ -> do
    addDef tyN tyAnn TypeScope
  DatatypeBind
    _a
    ( Datatype
        dataAnn
        (TyVarDecl tyAnn tyN _)
        tyVarDecls
        dataName
        varDecls
      ) -> do
      let addTyVarDecl
            :: ( Ord ann
               , HasUnique tyname TypeUnique
               , MonadState (UniqueInfos ann) m
               , MonadWriter [UniqueError ann] m
               )
            => TyVarDecl tyname ann -> m ()
          addTyVarDecl (TyVarDecl tyVarAnn tyVarN _) =
            addDef tyVarN tyVarAnn TypeScope
          addVarDecl
            :: ( Ord ann
               , HasUnique name TermUnique
               , MonadState (UniqueInfos ann) m
               , MonadWriter [UniqueError ann] m
               )
            => VarDecl tyname name uni ann -> m ()
          addVarDecl (VarDecl varAnn n _) = do
            addDef n varAnn TermScope
      addDef dataName dataAnn TermScope
      addDef tyN tyAnn TypeScope
      forM_ tyVarDecls addTyVarDecl
      forM_ varDecls addVarDecl

{-| Given a PIR term, add all of its term and type definitions and usages, including its subterms
and subtypes, to a global map. -}
termDefs
  :: ( Ord ann
     , HasUnique name TermUnique
     , HasUnique tyname TypeUnique
     , MonadState (UniqueInfos ann) m
     , MonadWriter [UniqueError ann] m
     )
  => Term tyname name uni fun ann
  -> m ()
termDefs tm = do
  forMOf_ termSubtermsDeep tm handleTerm
  forMOf_ termSubtypesDeep tm handleType

handleTerm
  :: ( Ord ann
     , HasUnique name TermUnique
     , HasUnique tyname TypeUnique
     , MonadState (UniqueInfos ann) m
     , MonadWriter [UniqueError ann] m
     )
  => Term tyname name uni fun ann
  -> m ()
handleTerm = \case
  Let _ann _r bindings _ ->
    forM_ bindings addBindingDef
  Var ann n ->
    addUsage n ann TermScope
  LamAbs ann n _ _ ->
    addDef n ann TermScope
  TyAbs ann tn _ _ ->
    addDef tn ann TypeScope
  _ -> pure ()

runTermDefs
  :: ( Ord ann
     , HasUnique name TermUnique
     , HasUnique tyname TypeUnique
     , Monad m
     )
  => Term tyname name uni fun ann
  -> m (UniqueInfos ann, [UniqueError ann])
runTermDefs = runWriterT . flip execStateT mempty . termDefs
