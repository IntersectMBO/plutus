-- editorconfig-checker-disable-file
{-# LANGUAGE BangPatterns          #-}
{-# LANGUAGE CPP                   #-}
{-# LANGUAGE DerivingStrategies    #-}
{-# LANGUAGE PatternSynonyms       #-}
{-# LANGUAGE TemplateHaskellQuotes #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE ViewPatterns          #-}
module PlutusTx.AsData (asData, asDataFor) where

import Control.Lens (ifor)
import Control.Monad (unless)
import Data.Foldable
import Data.Traversable

import Language.Haskell.TH qualified as TH
import Language.Haskell.TH.Datatype qualified as TH
import Language.Haskell.TH.Datatype.TyVarBndr qualified as TH

import PlutusTx.Eq qualified as PlutusTx

import PlutusTx.Builtins as Builtins
import PlutusTx.IsData.Class

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

Instances can be derived using standalone deriving, and should mostly
use the newtype strategy (e.g. in order to benefit from the fast 'Eq' instance for
the underlying 'BuiltinData').

Example:
@
    $(asData
      [d|
        data Example a = Ex1 Integer | Ex2 a a
      |]
@
becomes
@
    newtype Example a = Example BuiltinData
      deriving newtype (ToData, FromData, UnsafeFromBuiltinData)

    pattern Ex1 :: (ToData a, UnsafeFromData a) => Integer -> Example a
    pattern Ex1 i = Example (unsafeDataAsConstr -> ((==) 0 -> True, [unsafeFromBuiltinData -> i]))
      where Ex1 i = Example (mkConstr 0 [toBuiltinData i])

    pattern Ex2 :: (ToData a, UnsafeFromData a) => a -> a -> Example a
    pattern Ex2 a1 a2 = Example (unsafeDataAsConstr -> ((==) 1 -> True, [unsafeFromBuiltinData -> a1, unsafeFromBuiltinData -> a2]))
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
  -- th-abstraction doesn't include deriving clauses, so we have to handle that hereth-abstraction doesn't include deriving clauses, so we have to handle that here
  case dec of
    TH.DataD _ _ _ _ _ deriv | not (null deriv) -> fail "asData: can't handle deriving clauses"
    _                                           -> pure ()

  di@(TH.DatatypeInfo{TH.datatypeVariant=dVariant, TH.datatypeCons=cons, TH.datatypeName=name, TH.datatypeVars=tTypeVars}) <- TH.normalizeDec dec

  -- Other stuff is data families and so on
  unless (dVariant == TH.Datatype) $ fail $ "asData: can't handle datatype variant " ++ show dVariant
  -- a fresh name for the new datatype, but same lexically as the old one
  cname <- TH.newName (show name)
  -- The newtype declaration
  let ntD =
        let con = TH.NormalC cname [(TH.Bang TH.NoSourceUnpackedness TH.NoSourceStrictness, TH.ConT ''BuiltinData)]
        in TH.NewtypeD [] name tTypeVars Nothing con []

  -- The pattern synonyms, one for each constructor
  pats <- ifor cons $ \conIx (TH.ConstructorInfo{TH.constructorName=conName, TH.constructorFields=fields, TH.constructorVariant=cVariant}) -> do
    -- If we have a record constructor, we need to reuse the names for the
    -- matching part of the pattern synonym
    fieldNames <- case cVariant of
      TH.RecordConstructor names -> pure names
      -- otherwise whatever
      _                          -> ifor fields $ \fieldIx _ -> TH.newName $ "arg" ++ show fieldIx
    let extractFieldNames = fieldNames
    createFieldNames <- for fieldNames (TH.newName . show)
    patSynArgs <- case cVariant of
      TH.NormalConstructor   -> pure $ TH.PrefixPatSyn extractFieldNames
      TH.RecordConstructor _ -> pure $ TH.RecordPatSyn extractFieldNames
      TH.InfixConstructor    -> case extractFieldNames of
        [f1,f2] -> pure $ TH.InfixPatSyn f1 f2
        _       -> fail "asData: infix data constructor with other than two fields"
    let
      dataConstraints t = [TH.ConT ''ToData `TH.AppT` t, TH.ConT ''UnsafeFromData `TH.AppT` t]
      ixLit = TH.IntegerL (fromIntegral conIx)
      -- (==) i -> True
      ixMatchPat = TH.ViewP (TH.VarE '(PlutusTx.==) `TH.AppE` TH.LitE ixLit) (ConP' 'True [])
      -- [unsafeFromBuiltinData -> arg1, ...]
      extractArgPats = (flip fmap) (zip fields extractFieldNames) $ \(ty, n) ->
        TH.ViewP (TH.VarE 'unsafeFromBuiltinData `TH.AppTypeE` ty) (TH.VarP n)
      -- unsafeDataAsConstr -> ((==) i -> True, [unsafeFromBuiltinData -> arg1, ...])
      pat = ConP' cname [TH.ViewP (TH.VarE 'Builtins.unsafeDataAsConstr) (TH.TupP [ixMatchPat, TH.ListP extractArgPats])]
      -- [toBuiltinData arg1, ...]
      createArgExprs = (flip fmap) (zip fields createFieldNames) $ \(ty, n) ->
        TH.VarE 'toBuiltinData `TH.AppTypeE` ty `TH.AppE` (TH.VarE n)
      -- mkConstr i [toBuiltinData arg1, ...]
      createExpr = TH.ConE cname `TH.AppE` (TH.VarE 'Builtins.mkConstr `TH.AppE` TH.LitE ixLit `TH.AppE` TH.ListE createArgExprs)
      -- arg1 ... = mkConstr i [toBuiltinData arg1, ...]
      clause = TH.Clause (fmap TH.VarP createFieldNames) (TH.NormalB createExpr) []

      ctxFor vars = concatMap (dataConstraints . TH.VarT . TH.tvName) vars
      -- Try and be a little clever and only add constraints on the variables
      -- used in the arguments
      varsInArgs = TH.freeVariablesWellScoped fields
      ctxForArgs = ctxFor varsInArgs

      conTy = foldr (\ty acc -> TH.ArrowT `TH.AppT` ty `TH.AppT` acc) (TH.datatypeType di) fields
      allFreeVars = TH.freeVariablesWellScoped [conTy]
      fullTy = TH.ForallT (TH.changeTVFlags TH.SpecifiedSpec allFreeVars) ctxForArgs conTy
    let
      patSynSigD = TH.PatSynSigD conName fullTy
      patSynD = TH.PatSynD conName patSynArgs (TH.ExplBidir [clause]) pat
    pure [patSynSigD, patSynD]
  -- A complete pragma, to top it off
  let compl = TH.PragmaD (TH.CompleteP (fmap TH.constructorName cons) Nothing)
  pure $ ntD : compl : concat pats

-- compat for different signature of ConP in old TH
pattern ConP' :: TH.Name -> [TH.Pat] -> TH.Pat
#if MIN_VERSION_template_haskell(2,18,0)
pattern ConP' name pats = TH.ConP name [] pats
#else
pattern ConP' name pats = TH.ConP name pats
#endif
