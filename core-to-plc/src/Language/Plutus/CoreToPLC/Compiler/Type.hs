{-# LANGUAGE ConstraintKinds   #-}
{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ViewPatterns      #-}

-- | Functions for compiling GHC types into PlutusCore types, as well as compiling constructors,
-- matchers, and pattern match alternatives.
module Language.Plutus.CoreToPLC.Compiler.Type (
    convType,
    convKind,
    getDataCons,
    getConstructors,
    getConstructorsInstantiated,
    getMatch,
    getMatchInstantiated,
    convAlt,
    NewtypeCoercion (..),
    splitNewtypeCoercion) where

import           Language.Plutus.CoreToPLC.Compiler.Binders
import           Language.Plutus.CoreToPLC.Compiler.Builtins
import           Language.Plutus.CoreToPLC.Compiler.Definitions
import {-# SOURCE #-} Language.Plutus.CoreToPLC.Compiler.Expr
import           Language.Plutus.CoreToPLC.Compiler.Kind
import           Language.Plutus.CoreToPLC.Compiler.Names
import           Language.Plutus.CoreToPLC.Compiler.Types
import           Language.Plutus.CoreToPLC.Compiler.Utils
import           Language.Plutus.CoreToPLC.Error
import           Language.Plutus.CoreToPLC.Laziness
import           Language.Plutus.CoreToPLC.PIRTypes

import qualified GhcPlugins                                     as GHC
import qualified Pair                                           as GHC
import qualified PrelNames                                      as GHC
import qualified TysPrim                                        as GHC

import qualified Language.PlutusIR                              as PIR
import qualified Language.PlutusIR.MkPir                        as PIR

import qualified Language.PlutusCore                            as PLC
import qualified Language.PlutusCore.MkPlc                      as PLC

import           Control.Monad.Reader

import qualified Data.List.NonEmpty                             as NE
import           Data.Traversable

import           Data.List                                      (reverse, sortBy)

-- Types

convType :: Converting m => GHC.Type -> m PIRType
convType t = withContextM (sdToTxt $ "Converting type:" GHC.<+> GHC.ppr t) $ do
    -- See Note [Scopes]
    ConvertingContext {ccScopes=stack} <- ask
    let top = NE.head stack
    case t of
        -- in scope type name
        (GHC.getTyVar_maybe -> Just (lookupTyName top . GHC.getName -> Just (PLC.TyVarDecl _ name _))) -> pure $ PLC.TyVar () name
        (GHC.getTyVar_maybe -> Just v) -> throwSd FreeVariableError $ "Type variable:" GHC.<+> GHC.ppr v
        (GHC.splitFunTy_maybe -> Just (i, o)) -> PLC.TyFun () <$> convType i <*> convType o
        (GHC.splitTyConApp_maybe -> Just (tc, ts)) -> convTyConApp tc ts
        (GHC.splitForAllTy_maybe -> Just (tv, tpe)) -> mkTyForallScoped tv (convType tpe)
        -- I think it's safe to ignore the coercion here
        (GHC.splitCastTy_maybe -> Just (tpe, _)) -> convType tpe
        _ -> throwSd UnsupportedError $ "Type" GHC.<+> GHC.ppr t

convTyConApp :: (Converting m) => GHC.TyCon -> [GHC.Type] -> m PIRType
convTyConApp tc ts
    -- this is Int#, convert as Int
    | tc == GHC.intPrimTyCon = convTyCon GHC.intTyCon
    -- we don't support Integer
    | GHC.getName tc == GHC.integerTyConName = throwPlain $ UnsupportedError "Integer: use Int instead"
    -- this is Void#, see Note [Value restriction]
    | tc == GHC.voidPrimTyCon = errorTy
    | otherwise = do
        tc' <- convTyCon tc
        args' <- mapM convType ts
        pure $ PLC.mkIterTyApp () tc' args'

convTyCon :: (Converting m) => GHC.TyCon -> m PIRType
convTyCon tc = do
    let tcName = GHC.getName tc
    maybeDef <- lookupTypeDef tcName
    case maybeDef of
        Just ty -> pure ty
        Nothing -> do
            dcs <- getDataCons tc
            usedTcs <- getUsedTcs tc
            let deps = fmap GHC.getName usedTcs ++ fmap GHC.getName dcs

            tvd <- convTcTyVarFresh tc

            defineType tcName (PIR.TypeBind () tvd (PIR.mkTyVar () tvd)) []

            -- type variables are in scope for the rest of the definition
            withTyVarsScoped (GHC.tyConTyVars tc) $ \tvs -> do
                constructors <- for dcs $ \dc -> do
                    name <- convNameFresh (GHC.getName dc)
                    ty <- mkConstructorType dc
                    pure $ PIR.VarDecl () name ty

                matchName <- safeFreshName $ (GHC.getOccString $ GHC.getName tc) ++ "_match"

                let datatype = PIR.Datatype () tvd tvs matchName constructors

                defineType tcName (PIR.DatatypeBind () datatype) deps

            pure $ PIR.mkTyVar () tvd

-- Newtypes

-- | Wrapper for a pair of types with a direction of wrapping or unwrapping.
data NewtypeCoercion = Wrap GHC.Type GHC.Type
                     | Unwrap GHC.Type GHC.Type

-- | View a 'GHC.Coercion' as possibly a newtype coercion.
splitNewtypeCoercion :: GHC.Coercion -> Maybe NewtypeCoercion
splitNewtypeCoercion coerce = case GHC.coercionKind coerce of
    (GHC.Pair lhs@(GHC.splitTyConApp_maybe -> Just (GHC.unwrapNewTyCon_maybe -> Just (_, inner, _), _)) rhs) | GHC.eqType rhs inner -> Just $ Unwrap lhs rhs
    (GHC.Pair lhs rhs@(GHC.splitTyConApp_maybe -> Just (GHC.unwrapNewTyCon_maybe -> Just (_, inner, _), _))) | GHC.eqType lhs inner -> Just $ Wrap lhs rhs
    _ -> Nothing

getUsedTcs :: (Converting m) => GHC.TyCon -> m [GHC.TyCon]
getUsedTcs tc = do
    dcs <- getDataCons tc
    let usedTcs = GHC.unionManyUniqSets $ (\dc -> GHC.unionManyUniqSets $ GHC.tyConsOfType <$> GHC.dataConRepArgTys dc) <$> dcs
    pure $ GHC.nonDetEltsUniqSet usedTcs

{- Note [Case expressions and laziness]
PLC is strict, but users *do* expect that, e.g. they can write an if expression and have it be
lazy. This only *matters* because we have 'error', so it's important that 'if false error else ...'
does not evaluate to 'error'!

More generally, we can compile case expressions (of which an if expression is one) lazily, i.e. we add
a unit argument and apply it at the end.

However, we apply an important optimization: we only need to do this if it is not the case that
all the case expressions are values. In the common case they *will* be, so this gives us
significantly better codegen a lot of the time.

The check we do is:
- Alternatives with arguments will be turned into lambdas by us, so will be values.
- Otherwise, we convert the expression (we can do this easily since it doesn't need any variables in scope),
  and check whether it is a value.

This is somewhat wasteful, since we may convert the expression twice, but it's difficult to avoid, and
it's hard to tell if a GHC core expression will be a PLC value or not. Easiest to just try it.
-}

{- Note [Ordering of constructors]
It is very important that we convert types and constructors consistently, especially between
lifting at runtime and compilation via the plugin. The main place we can get bitten is ordering.

GHC is under no obligation to give us any particular ordering of constructors, so we impose
an alphabetical one (with a few exceptions, see [Ensuring compatibility with spec and stdlib types]).

The other place where ordering matters is arguments to constructors, but here there is a
clear natural ordering which we will assume GHC respects.
-}

{- Note [Ensuring compatibility with spec and stdlib types]
Haskell's Bool has its constructors ordered with False before True, which results in the
normal case expression having the oppposite sense to the one in the spec, where
the true branch comes first (which is more logical).

Our options are:
- Reverse the branches in the spec.
    - This is ugly, the plugin details shouldn't influence the spec.
- Rewrite the primitive functions that produce booleans to produce spec booleans.
    - This is pretty bad codegen.
- Special case Bool to swap the order of the cases.

We take the least bad option, option 3.

The same problem arises for List. It's not in the spec, but the stdlib order (and the natural one)
is nil first and then cons, but ":" is less than "[]", so we end up with the wrong order. Again,
we just special case this.
-}

-- See Note [Ordering of constructors]
sortConstructors :: GHC.TyCon -> [GHC.DataCon] -> [GHC.DataCon]
sortConstructors tc cs =
    -- note we compare on the OccName *not* the Name, as the latter compares on uniques, not the string name
    let sorted = sortBy (\dc1 dc2 -> compare (GHC.getOccName dc1) (GHC.getOccName dc2)) cs
    in if tc == GHC.boolTyCon || tc == GHC.listTyCon then reverse sorted else sorted

getDataCons :: (Converting m) =>  GHC.TyCon -> m [GHC.DataCon]
getDataCons tc' = sortConstructors tc' <$> extractDcs tc'
    where
        extractDcs tc
          | GHC.isAlgTyCon tc || GHC.isTupleTyCon tc = case GHC.algTyConRhs tc of
              GHC.AbstractTyCon                -> throwSd UnsupportedError $ "Abstract type:" GHC.<+> GHC.ppr tc
              GHC.DataTyCon{GHC.data_cons=dcs} -> pure dcs
              GHC.TupleTyCon{GHC.data_con=dc}  -> pure [dc]
              GHC.SumTyCon{GHC.data_cons=dcs}  -> pure dcs
              GHC.NewTyCon{GHC.data_con=dc}    -> pure [dc]
          | otherwise = throwSd UnsupportedError $ "Type constructor:" GHC.<+> GHC.ppr tc

-- | Makes the type of the constructor corresponding to the given 'DataCon', with the type variables free.
mkConstructorType :: Converting m => GHC.DataCon -> m PIRType
mkConstructorType dc =
    let argTys = GHC.dataConRepArgTys dc
    in
        -- See Note [Scott encoding of datatypes]
        withContextM (sdToTxt $ "Converting data constructor type:" GHC.<+> GHC.ppr dc) $ do
            args <- mapM convType argTys
            resultType <- convType (GHC.dataConOrigResTy dc)
            -- t_c_i_1 -> ... -> t_c_i_j -> resultType
            pure $ PLC.mkIterTyFun () args resultType

-- | Get the constructors of the given 'TyCon' as PLC terms.
getConstructors :: Converting m => GHC.TyCon -> m [PIRTerm]
getConstructors tc = do
    -- make sure the constructors have been created
    _ <- convTyCon tc
    maybeConstrs <- lookupConstructors (GHC.getName tc)
    case maybeConstrs of
        Just constrs -> pure constrs
        Nothing      -> throwPlain $ ConversionError "Constructors have not been converted"

-- | Get the constructors of the given 'Type' (which must be equal to a type constructor application) as PLC terms instantiated for
    -- the type constructor argument types.
getConstructorsInstantiated :: Converting m => GHC.Type -> m [PIRTerm]
getConstructorsInstantiated = \case
    (GHC.splitTyConApp_maybe -> Just (tc, args)) -> do
        constrs <- getConstructors tc

        forM constrs $ \c -> do
            args' <- mapM convType args
            pure $ PIR.mkIterInst () c args'
    -- must be a TC app
    _ -> throwPlain $ ConversionError "Type was not a type constructor application"

-- | Get the matcher of the given 'TyCon' as a PLC term
getMatch :: Converting m => GHC.TyCon -> m PIRTerm
getMatch tc = do
    -- ensure the tycon has been converted, which will create the matcher
    _ <- convTyCon tc
    maybeMatch <- lookupMatch (GHC.getName tc)
    case maybeMatch of
        Just match -> pure match
        Nothing    -> throwPlain $ ConversionError "Match has not been converted"

-- | Get the matcher of the given 'Type' (which must be equal to a type constructor application) as a PLC term instantiated for
-- the type constructor argument types.
getMatchInstantiated :: Converting m => GHC.Type -> m PIRTerm
getMatchInstantiated = \case
    (GHC.splitTyConApp_maybe -> Just (tc, args)) -> do
        match <- getMatch tc

        args' <- mapM convType args
        pure $ PIR.mkIterInst () match args'
    -- must be a TC app
    _ -> throwPlain $ ConversionError "Type was not a type constructor application"

-- | Make the alternative for a given 'CoreAlt'.
convAlt
    :: Converting m
    => Bool -- ^ Whether we must delay the alternative.
    -> GHC.DataCon -- ^ The 'DataCon' for the current alternative.
    -> GHC.CoreAlt -- ^ The 'CoreAlt' representing the branch itself.
    -> m PIRTerm
convAlt mustDelay dc (alt, vars, body) = case alt of
    GHC.LitAlt _  -> throwPlain $ UnsupportedError "Literal case"
    GHC.DEFAULT   -> do
        body' <- convExpr body >>= maybeDelay mustDelay
        -- need to consume the args
        argTypes <- mapM convType $ GHC.dataConRepArgTys dc
        argNames <- forM [0..(length argTypes -1)] (\i -> safeFreshName $ "default_arg" ++ show i)
        pure $ PIR.mkIterLamAbs () (zipWith (PIR.VarDecl ()) argNames argTypes) body'
    -- We just package it up as a lambda bringing all the
    -- vars into scope whose body is the body of the case alternative.
    -- See Note [Iterated abstraction and application]
    -- See Note [Case expressions and laziness]
    GHC.DataAlt _ -> mkIterLamAbsScoped vars (convExpr body >>= maybeDelay mustDelay)
