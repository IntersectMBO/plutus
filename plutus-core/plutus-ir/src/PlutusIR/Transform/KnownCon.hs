{-# LANGUAGE BangPatterns      #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell   #-}
{-# LANGUAGE TupleSections     #-}
{-# LANGUAGE TypeApplications  #-}
{-# LANGUAGE ViewPatterns      #-}

module PlutusIR.Transform.KnownCon (knownCon) where

import PlutusCore qualified as PLC
import PlutusCore.Name qualified as PLC
import PlutusIR
import PlutusIR.Core
import PlutusIR.Transform.Rename ()

import Control.Lens hiding (cons)
import Data.List.Extra qualified as List
import Data.Map (Map)
import Data.Map qualified as Map

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
    , Ord name
    , PLC.MonadQuote m
    ) =>
    Term tyname name uni fun a ->
    m (Term tyname name uni fun a)
knownCon t0 = do
    -- We are going to record information about variables in a global map, so we
    -- need global uniqueness
    t <- PLC.rename t0
    let ctxt =
            foldMapOf
                (termSubtermsDeep . termBindings)
                ( \case
                    DatatypeBind _ (Datatype _ _ tvs destr cons) ->
                        Map.singleton destr (_varDeclName <$> cons, length tvs)
                    _ -> mempty
                )
                t
    pure $ transformOf termSubterms (go ctxt) t

go ::
    forall tyname name uni fun a.
    (Ord name) =>
    -- | A map from destructor to (constructors, number of type variables)
    Map name ([name], Int) ->
    Term tyname name uni fun a ->
    Term tyname name uni fun a
go ctxt t
    | (Var _ n, args) <- collectArgs t
    , Just (cons, numTvs) <- Map.lookup n ctxt
    , ((TermArg scrut, _) : (TypeArg _resTy, _) : rest) <-
        -- The datatype may have some type arguments, we
        -- aren't interested in them, so we drop them.
        drop numTvs args
    , -- The scrutinee is itself an application
      (Var _ con, conArgs) <- collectArgs scrut
    , -- ... of one of the constructors from the same datatype as the destructor
      Just i <- List.findIndex (== con) cons
    , -- ... and there is a  branch for that constructor in the destructor application
      Just (TermArg branch, _) <- rest List.!? i
    , -- This condition ensures the destructor is fully-applied
      -- (which should always be the case in programs that come from Plutus Tx,
      -- but not necessarily in arbitrary PIR programs).
      length rest == length cons =
        mkTermApps
            branch
            -- The arguments to the selected branch consists of the arguments
            -- to the constructor, without the leading type arguments - e.g.,
            -- if the scrutinee is `Just {integer} 1`, we only need the `1`).
            (drop numTvs conArgs)
    | otherwise = t
