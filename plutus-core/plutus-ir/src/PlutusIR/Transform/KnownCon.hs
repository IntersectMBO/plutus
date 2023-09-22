{-# LANGUAGE NamedFieldPuns #-}

module PlutusIR.Transform.KnownCon (knownCon) where

import PlutusCore qualified as PLC
import PlutusCore.Name qualified as PLC
import PlutusIR
import PlutusIR.Contexts
import PlutusIR.Transform.Rename ()

import Control.Lens hiding (cons)
import Data.List.Extra qualified as List
import PlutusIR.Analysis.VarInfo

{- | Simplify destructor applications, if the scrutinee is a constructor application.

As an example, given

@
    Maybe_match
      {x_type}
      (Just {x_type} x)
      {result_type}
      (\a -> <just_case_body : result_type>)
      (<nothing_case_body : result_type>)
      additional_args
@

`knownCon` turns it into

@
    (\a -> <just_case_body>) x additional_args
@
-}
knownCon ::
    forall m tyname name uni fun a.
    ( PLC.HasUnique name PLC.TermUnique
    , PLC.HasUnique tyname PLC.TypeUnique
    , Eq name
    , PLC.MonadQuote m
    ) =>
    Term tyname name uni fun a ->
    m (Term tyname name uni fun a)
knownCon t0 = do
    -- We are going to record information about variables in a global map, so we
    -- need global uniqueness
    t <- PLC.rename t0
    let vinfo = termVarInfo t
    pure $ transformOf termSubterms (processTerm vinfo) t

processTerm ::
    forall tyname name uni fun a .
    (Eq name
    , PLC.HasUnique name PLC.TermUnique
    , PLC.HasUnique tyname PLC.TypeUnique) =>
    VarsInfo tyname name ->
    Term tyname name uni fun a ->
    Term tyname name uni fun a
processTerm vinfo t
    | (Var _ n, args) <- splitApplication t
    , Just (DatatypeMatcher _ parentName) <- lookupVarInfo n vinfo
    , Just (DatatypeTyVar numTyVars constructors ) <- lookupTyVarInfo parentName vinfo
    , (TermAppContext scrut _ (TypeAppContext _resTy _ branchArgs)) <-
        -- The datatype may have some type arguments, we
        -- aren't interested in them, so we drop them.
        dropAppContext numTyVars args
    , -- The scrutinee is itself an application
      (Var _ con, conArgs) <- splitApplication scrut
    , -- ... of one of the constructors from the same datatype as the destructor
      Just i <- List.findIndex (== con) constructors
    , -- ... and there is a  branch for that constructor in the destructor application
      (TermAppContext branch _ _) <- dropAppContext i branchArgs
    , -- This condition ensures the destructor is fully-applied
      -- (which should always be the case in programs that come from Plutus Tx,
      -- but not necessarily in arbitrary PIR programs).
      lengthContext branchArgs == length constructors =
        fillAppContext
            branch
            -- The arguments to the selected branch consists of the arguments
            -- to the constructor, without the leading type arguments - e.g.,
            -- if the scrutinee is `Just {integer} 1`, we only need the `1`).
            (dropAppContext numTyVars conArgs)
    | otherwise = t
