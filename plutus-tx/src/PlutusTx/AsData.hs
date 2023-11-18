-- editorconfig-checker-disable-file
{-# LANGUAGE BangPatterns       #-}
{-# LANGUAGE CPP                #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE LambdaCase         #-}
{-# LANGUAGE PatternSynonyms    #-}
{-# LANGUAGE TemplateHaskell    #-}
{-# LANGUAGE TypeApplications   #-}
{-# LANGUAGE ViewPatterns       #-}
module PlutusTx.AsData (asData, asDataFor) where

import Control.Lens (ifor)
import Control.Monad (unless)
import Data.Foldable
import Data.Traversable

import Language.Haskell.TH qualified as TH
import Language.Haskell.TH.Datatype qualified as TH
import Language.Haskell.TH.Datatype.TyVarBndr qualified as TH

import PlutusTx.Builtins as Builtins
import PlutusTx.Builtins.Internal as BI
import PlutusTx.IsData.Class
import PlutusTx.IsData.TH (mkConstrCreateExpr, mkUnsafeConstrMatchPattern)
import PlutusTx.Prelude qualified as PlutusTx

import Prelude

{- | 'asData' takes a datatype declaration and "backs it" by 'BuiltinData'. It does
this by replacing the datatype with a newtype around 'BuiltinData', and providing
pattern synonyms that match the behaviour of the original datatype.

Since 'BuiltinData' can only contain 'BuiltinData', the pattern synonyms
encode and decode all the fields using 'toBuiltinData' and 'unsafeFromBuiltinData'.
That means that these operations are called on every pattern match or construction.
This *can* be very efficient if, for example, the datatypes for the fields have
also been defined with 'asData', and so have trivial conversions to/from 'BuiltinData'
(or have very cheap conversions, like 'Integer' and 'ByteString').
But it can be very expensive otherwise, so take care.

Deriving clauses are transferred from the quoted declaration to the generated newtype
declaration. Note that you may therefore need to do strange things like use
@deriving newtype@ on a data declaration.

Example:
@
    $(asData
      [d|
        data Example a = Ex1 Integer | Ex2 a a
          deriving newtype (Eq)
      |]
@
becomes
@
    newtype Example a = Example BuiltinData
      deriving newtype (Eq)

    pattern Ex1 :: (ToData a, UnsafeFromData a) => Integer -> Example a
    pattern Ex1 i <- Example (unsafeDataAsConstr -> ((==) 0 -> True, [unsafeFromBuiltinData -> i]))
      where Ex1 i = Example (mkConstr 0 [toBuiltinData i])

    pattern Ex2 :: (ToData a, UnsafeFromData a) => a -> a -> Example a
    pattern Ex2 a1 a2 <- Example (unsafeDataAsConstr -> ((==) 1 -> True, [unsafeFromBuiltinData -> a1, unsafeFromBuiltinData -> a2]))
      where Ex2 a1 a2 = Example (mkConstr 1 [toBuiltinData a1, toBuiltinData a2])

    {-# COMPLETE Ex1, Ex2 #-}
@
-}
asData :: TH.Q [TH.Dec] -> TH.Q [TH.Dec]
asData decQ = do
  decs <- decQ
  outputDecs <- for decs asDataFor
  pure $ concat outputDecs

asDataFor :: TH.Dec -> TH.Q [TH.Dec]
asDataFor dec = do
  -- th-abstraction doesn't include deriving clauses, so we have to handle that here
  let derivs = case dec of
        TH.DataD _ _ _ _ _ deriv -> deriv
        _                        -> []

  di@(TH.DatatypeInfo{TH.datatypeVariant=dVariant, TH.datatypeCons=cons, TH.datatypeName=name, TH.datatypeVars=tTypeVars}) <- TH.normalizeDec dec

  -- Other stuff is data families and so on
  unless (dVariant == TH.Datatype) $ fail $ "asData: can't handle datatype variant " ++ show dVariant
  -- a fresh name for the new datatype, but same lexically as the old one
  cname <- TH.newName (show name)
  -- The newtype declaration
  let ntD =
        let con = TH.NormalC cname [(TH.Bang TH.NoSourceUnpackedness TH.NoSourceStrictness, TH.ConT ''BuiltinData)]
        in TH.NewtypeD [] name tTypeVars Nothing con derivs

  -- Generate field accessor functions, if applicable. This is more efficient than the
  -- field accessors obtained from record pattern synonyms (`RecordPatSyn`).
  fieldAccessors <- ifor cons $ \conIx (TH.ConstructorInfo{TH.constructorFields = fields, TH.constructorVariant = cVariant}) ->
    case cVariant of
      TH.RecordConstructor fieldNames ->
        ifor (fields `zip` fieldNames) $ \fieldIx (fieldTy, fieldName) -> do
          inp <- TH.newName "inp"
          tup <- TH.newName "tup"
          i <- TH.newName "idx"
          d <- TH.newName "d"
          ds <- TH.newName "ds"
          let body :: TH.Q TH.Exp
              body =
                [|
                  let $(TH.bangP $ TH.varP tup) = BI.unsafeDataAsConstr $(TH.varE inp)
                      $(TH.bangP $ TH.varP i) = BI.fst $(TH.varE tup)
                      $(TH.bangP $ TH.varP ds) = BI.snd $(TH.varE tup)
                      $(TH.bangP $ TH.varP d) =
                        BI.head
                          $(foldr (.) id (replicate fieldIx (\e -> [|BI.tail $e|])) (TH.varE ds))
                   in if $(TH.varE i) PlutusTx.== conIx
                        then unsafeFromBuiltinData $(TH.varE d)
                        else Builtins.error ()
                  |]
              fieldClause :: TH.Q TH.Clause
              fieldClause = TH.clause [TH.conP cname [TH.varP inp]] (TH.normalB body) mempty
              fieldAccessorCtx :: TH.Q TH.Cxt
              fieldAccessorCtx =
                sequenceA $
                  TH.appT (TH.conT ''UnsafeFromData) . TH.varT . TH.tvName
                    <$> TH.freeVariablesWellScoped [fieldTy]
              fieldAccessorTy :: TH.Q TH.Type
              fieldAccessorTy =
                TH.forallT
                  (TH.changeTVFlags TH.SpecifiedSpec tTypeVars)
                  fieldAccessorCtx
                  [t|
                    $(foldl' (\acc -> TH.appT acc . TH.varT . TH.tvName) (TH.conT name) tTypeVars) ->
                    $(pure fieldTy)
                    |]
              inlinable = TH.PragmaD (TH.InlineP fieldName TH.Inlinable TH.FunLike TH.AllPhases)
          sequenceA
            [ TH.sigD fieldName fieldAccessorTy
            , TH.funD fieldName [fieldClause]
            , pure inlinable
            ]
      _ -> pure mempty

  -- The pattern synonyms, one for each constructor
  pats <- ifor cons $ \conIx (TH.ConstructorInfo{TH.constructorName=conName, TH.constructorFields=fields, TH.constructorVariant=cVariant}) -> do
    -- If we have a record constructor, we need to reuse the names for the
    -- matching part of the pattern synonym
    fieldNames <- ifor fields $ \fieldIx _ -> TH.newName $ "arg" ++ show fieldIx
    createFieldNames <- for fieldNames (TH.newName . show)
    patSynArgs <- case cVariant of
      TH.NormalConstructor   -> pure $ TH.prefixPatSyn fieldNames
      -- Since field accessors are generated separately, here we use `PrefixPatSyn`
      -- rather than `RecordPatSyn`.
      TH.RecordConstructor _ -> pure $ TH.prefixPatSyn fieldNames
      TH.InfixConstructor    -> case fieldNames of
        [f1,f2] -> pure $ TH.infixPatSyn f1 f2
        _       -> fail "asData: infix data constructor with other than two fields"
    let

      pat = TH.conP cname [mkUnsafeConstrMatchPattern (fromIntegral conIx) fieldNames]

      createExpr = [| $(TH.conE cname) $(mkConstrCreateExpr (fromIntegral conIx) createFieldNames) |]
      clause = TH.clause (fmap TH.varP createFieldNames) (TH.normalB createExpr) []
      patSynD = TH.patSynD conName patSynArgs (TH.explBidir [clause]) pat

    let
      dataConstraints t = [TH.ConT ''ToData `TH.AppT` t, TH.ConT ''UnsafeFromData `TH.AppT` t]
      ctxFor vars = concatMap (dataConstraints . TH.VarT . TH.tvName) vars
      -- Try and be a little clever and only add constraints on the variables
      -- used in the arguments
      varsInArgs = TH.freeVariablesWellScoped fields
      ctxForArgs = ctxFor varsInArgs
      conTy = foldr (\ty acc -> TH.ArrowT `TH.AppT` ty `TH.AppT` acc) (TH.datatypeType di) fields
      allFreeVars = TH.freeVariablesWellScoped [conTy]
      fullTy = TH.ForallT (TH.changeTVFlags TH.SpecifiedSpec allFreeVars) ctxForArgs conTy
      patSynSigD = pure $ TH.PatSynSigD conName fullTy

    sequenceA [patSynSigD, patSynD]
  -- A complete pragma, to top it off
  let compl = TH.PragmaD (TH.CompleteP (fmap TH.constructorName cons) Nothing)
  pure $ [ntD] <> concat (concat fieldAccessors) <> [compl] <> concat pats
