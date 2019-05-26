{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase       #-}
module Language.PlutusIR.Analysis.Definitions where

import           Language.PlutusIR

import qualified Language.PlutusCore                      as PLC
import qualified Language.PlutusCore.Analysis.Definitions as PLC
import qualified Language.PlutusCore.Name                 as PLC

import           Control.Lens

import           Control.Monad.State
import           Control.Monad.Writer

termDefs
    :: (Ord a,
        PLC.HasUnique (name a) PLC.TermUnique,
        PLC.HasUnique (tyname a) PLC.TypeUnique,
        MonadState (PLC.UniqueInfos a) m,
        MonadWriter [PLC.UniqueError a] m)
    => Term tyname name a
    -> m ()
termDefs = \case
    Var a n         -> PLC.addUsage n a PLC.TermScope
    LamAbs a n ty t -> PLC.addDef n a PLC.TermScope >> PLC.typeDefs ty >> termDefs t
    TyAbs a tn _ t  -> PLC.addDef tn a PLC.TypeScope >> termDefs t
    Let a tn _ t    -> PLC.addDef tn a PLC.TypeScope >> termDefs t
    x               -> traverseOf_ termSubterms termDefs x >> traverseOf_ termSubtypes PLC.typeDefs x
