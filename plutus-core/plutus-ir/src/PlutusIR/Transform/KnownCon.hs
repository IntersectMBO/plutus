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
import Data.Bitraversable
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
    t <- PLC.rename t0
    let ctxt =
            foldMapOf
                (termSubtermsDeep . termBindings)
                ( \case
                    DatatypeBind _ (Datatype _ _ _ destr cons) ->
                        Map.singleton destr (_varDeclName <$> cons)
                    _ -> mempty
                )
                t
    go ctxt t

go ::
    forall m tyname name uni fun a.
    ( Ord name
    , PLC.MonadQuote m
    ) =>
    -- | A map from destructor to constructors
    Map name [name] ->
    Term tyname name uni fun a ->
    m (Term tyname name uni fun a)
go ctxt = go'
  where
    go' = \case
        t@Apply{} -> do
            let (fun, args) = collectArgs t
            case fun of
                Var _ n
                    -- it appears in our map, so it's a destructor
                    | Just cons <- Map.lookup n ctxt
                    , ((TermExpr scrut, _) : (TypeExpr _resTy, _) : rest) <-
                        -- The datatype may have some type arguments, we
                        -- aren't interested in them, so we drop them. We can
                        -- do this easily because we know that they are all type
                        -- arguments, and then we have a term argument for the
                        -- scrutinee
                        dropWhile (isTyArg . fst) args
                    -- The scrutinee is itself an application
                    , (Var _ con, conArgs) <- collectArgs scrut
                    -- ... of one of the constructors from the same datatype as the destructor
                    , Just i <- List.findIndex (== con) cons
                    -- ... and there is a  branch for that constructor in the destructor application
                    , Just (TermExpr branch, _) <- rest List.!? i
                    , -- This condition ensures the destructor is fully-applied
                      -- (which should always be the case).
                      length rest >= length cons -> do
                        pure $
                            mkTermApps
                                branch
                                -- The arguments to the selected branch consists of the arguments
                                -- to the constructor (without the leading type arguments - e.g.,
                                -- if the scrutinee is `Just {integer} 1`, we only need the `1`),
                                -- and the remaining arguments in `rest` (because the destructor
                                -- may be over-applied).
                                ((dropWhile (isTyArg . fst) conArgs) <> drop (length cons) rest)
                _ ->
                    -- This is more efficient than `forOf termSubterms t go'`.
                    -- The latter is quadratic in the length of `args`.
                    mkTermApps
                        <$> go' fun
                        <*> traverse
                            ( bitraverse
                                ( \case
                                    TermExpr term -> TermExpr <$> go' term
                                    expr          -> pure expr
                                )
                                pure
                            )
                            args
        t -> forOf termSubterms t go'

    isTyArg = \case TypeExpr{} -> True; _ -> False
