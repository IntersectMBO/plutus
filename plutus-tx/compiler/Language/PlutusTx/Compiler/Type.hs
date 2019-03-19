{-# LANGUAGE ConstraintKinds   #-}
{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications  #-}
{-# LANGUAGE ViewPatterns      #-}

-- | Functions for compiling GHC types into PlutusCore types, as well as compiling constructors,
-- matchers, and pattern match alternatives.
module Language.PlutusTx.Compiler.Type (
    convType,
    convKind,
    getDataCons,
    getConstructors,
    getConstructorsInstantiated,
    getMatch,
    getMatchInstantiated,
    convAlt) where

import           Language.PlutusTx.Compiler.Binders
import           Language.PlutusTx.Compiler.Builtins
import           Language.PlutusTx.Compiler.Error
import {-# SOURCE #-} Language.PlutusTx.Compiler.Expr
import           Language.PlutusTx.Compiler.Kind
import           Language.PlutusTx.Compiler.Laziness
import           Language.PlutusTx.Compiler.Names
import           Language.PlutusTx.Compiler.Types
import           Language.PlutusTx.Compiler.Utils
import           Language.PlutusTx.PIRTypes

import qualified GhcPlugins                             as GHC
import qualified TysPrim                                as GHC

import qualified Language.PlutusIR                      as PIR
import qualified Language.PlutusIR.Compiler.Definitions as PIR
import           Language.PlutusIR.Compiler.Names
import qualified Language.PlutusIR.MkPir                as PIR

import           Control.Monad.Extra
import           Control.Monad.Reader

import           Data.List                              (reverse, sortBy)
import qualified Data.List.NonEmpty                     as NE
import qualified Data.Set                               as Set
import qualified Data.Text                              as T
import           Data.Traversable

-- Types

convType :: Converting m => GHC.Type -> m PIRType
convType t = withContextM 2 (sdToTxt $ "Converting type:" GHC.<+> GHC.ppr t) $ do
    -- See Note [Scopes]
    ConvertingContext {ccScopes=stack} <- ask
    let top = NE.head stack
    case t of
        -- in scope type name
        (GHC.getTyVar_maybe -> Just (lookupTyName top . GHC.getName -> Just (PIR.TyVarDecl _ name _))) -> pure $ PIR.TyVar () name
        (GHC.getTyVar_maybe -> Just v) -> throwSd FreeVariableError $ "Type variable:" GHC.<+> GHC.ppr v
        (GHC.splitFunTy_maybe -> Just (i, o)) -> PIR.TyFun () <$> convType i <*> convType o
        (GHC.splitTyConApp_maybe -> Just (tc, ts)) -> convTyConApp tc ts
        (GHC.splitForAllTy_maybe -> Just (tv, tpe)) -> mkTyForallScoped tv (convType tpe)
        -- I think it's safe to ignore the coercion here
        (GHC.splitCastTy_maybe -> Just (tpe, _)) -> convType tpe
        _ -> throwSd UnsupportedError $ "Type" GHC.<+> GHC.ppr t

-- TODO: fold the special cases into convTyCon as aliases?
convTyConApp :: (Converting m) => GHC.TyCon -> [GHC.Type] -> m PIRType
convTyConApp tc ts
    -- we don't support Int or Int#
    | GHC.getName tc == GHC.intTyConName = throwPlain $ UnsupportedError "Int: use Integer instead"
    | tc == GHC.intPrimTyCon = throwPlain $ UnsupportedError "Int#: unboxed integers are not supported"
    -- this is Void#, see Note [Value restriction]
    | tc == GHC.voidPrimTyCon = errorTy
    | otherwise = do
        tc' <- convTyCon tc
        args' <- mapM convType ts
        pure $ PIR.mkIterTyApp () tc' args'

{- Note [Occurrences of recursive names]
When we compile recursive types/terms, we need to process their definitions before we can produce
the final definition that we will use going forward.

But the thing that makes them *recursive* is that they appear in their own definitions! So
what do we do when we see those occurrences?

For cases where we are introducing a new variable for the definition (terms and datatypes), we
simply add that variable as a "fake" definition before we process the definition of the main entity.
That will be enough to ensure that we can make references to it normally, without making us loop.
Then we fix it up at the end.

For newtypes, we can't do this because the final value we will use is precisely the definition. So
we just have to ban recursive newtypes, and we do this by blackholing the name while we process the
definition, and dying if we see it again.
-}

convTyCon :: (Converting m) => GHC.TyCon -> m PIRType
convTyCon tc = do
    let tcName = GHC.getName tc
    whenM (blackholed tcName) $ throwSd UnsupportedError $ "Recursive newtypes, use data:" GHC.<+> GHC.ppr tcName
    maybeDef <- PIR.lookupType () tcName
    case maybeDef of
        Just ty -> pure ty
        Nothing -> do
            dcs <- getDataCons tc
            usedTcs <- getUsedTcs tc
            let deps = fmap GHC.getName usedTcs ++ fmap GHC.getName dcs

            tvd <- convTcTyVarFresh tc

            case GHC.unwrapNewTyCon_maybe tc of
                Just (_, underlying, _) -> do
                    -- See Note [Coercions and newtypes]
                    -- See Note [Occurrences of recursive names]
                    -- Type variables are in scope for the rhs of the alias
                    alias <- mkIterTyLamScoped (GHC.tyConTyVars tc) $ blackhole (GHC.getName tc) $ convType underlying
                    PIR.defineType tcName (PIR.Def tvd alias) (Set.fromList deps)
                    PIR.recordAlias @GHC.Name @() tcName
                    pure alias
                Nothing -> do
                    matchName <- safeFreshName () $ (T.pack $ GHC.getOccString $ GHC.getName tc) <> "_match"

                    -- See Note [Occurrences of recursive names]
                    let fakeDatatype = PIR.Datatype () tvd [] matchName []
                    PIR.defineDatatype tcName (PIR.Def tvd fakeDatatype) Set.empty

                    -- Type variables are in scope for the rest of the definition
                    withTyVarsScoped (GHC.tyConTyVars tc) $ \tvs -> do
                        constructors <- for dcs $ \dc -> do
                            name <- convNameFresh (GHC.getName dc)
                            ty <- mkConstructorType dc
                            pure $ PIR.VarDecl () name ty

                        let datatype = PIR.Datatype () tvd tvs matchName constructors

                        PIR.defineDatatype tcName (PIR.Def tvd datatype) (Set.fromList deps)
                    pure $ PIR.mkTyVar () tvd

getUsedTcs :: (Converting m) => GHC.TyCon -> m [GHC.TyCon]
getUsedTcs tc = do
    dcs <- getDataCons tc
    let usedTcs = GHC.unionManyUniqSets $ (\dc -> GHC.unionManyUniqSets $ GHC.tyConsOfType <$> GHC.dataConOrigArgTys dc) <$> dcs
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
    let argTys = GHC.dataConOrigArgTys dc
    in
        -- See Note [Scott encoding of datatypes]
        withContextM 3 (sdToTxt $ "Converting data constructor type:" GHC.<+> GHC.ppr dc) $ do
            args <- mapM convType argTys
            resultType <- convType (GHC.dataConOrigResTy dc)
            -- t_c_i_1 -> ... -> t_c_i_j -> resultType
            pure $ PIR.mkIterTyFun () args resultType

-- | Get the constructors of the given 'TyCon' as PLC terms.
getConstructors :: Converting m => GHC.TyCon -> m [PIRTerm]
getConstructors tc = do
    -- make sure the constructors have been created
    _ <- convTyCon tc
    maybeConstrs <- PIR.lookupConstructors () (GHC.getName tc)
    case maybeConstrs of
        Just constrs -> pure constrs
        Nothing      -> throwSd CompilationError $ "Constructors have not been compiled for:" GHC.<+> GHC.ppr tc

-- | Get the constructors of the given 'Type' (which must be equal to a type constructor application) as PLC terms instantiated for
-- the type constructor argument types.
getConstructorsInstantiated :: Converting m => GHC.Type -> m [PIRTerm]
getConstructorsInstantiated t = withContextM 3 (sdToTxt $ "Creating instantiated constructors for type:" GHC.<+> GHC.ppr t) $ case t of
    (GHC.splitTyConApp_maybe -> Just (tc, args)) -> do
        constrs <- getConstructors tc

        forM constrs $ \c -> do
            args' <- mapM convType args
            pure $ PIR.mkIterInst () c args'
    -- must be a TC app
    _ -> throwSd CompilationError $ "Type was not a type constructor application:" GHC.<+> GHC.ppr t

-- | Get the matcher of the given 'TyCon' as a PLC term
getMatch :: Converting m => GHC.TyCon -> m PIRTerm
getMatch tc = do
    -- ensure the tycon has been compiled, which will create the matcher
    _ <- convTyCon tc
    maybeMatch <- PIR.lookupDestructor () (GHC.getName tc)
    case maybeMatch of
        Just match -> pure match
        Nothing    -> throwSd CompilationError $ "Match has not been compiled for:" GHC.<+> GHC.ppr tc

-- | Get the matcher of the given 'Type' (which must be equal to a type constructor application) as a PLC term instantiated for
-- the type constructor argument types.
getMatchInstantiated :: Converting m => GHC.Type -> m PIRTerm
getMatchInstantiated t = withContextM 3 (sdToTxt $ "Creating instantiated matcher for type:" GHC.<+> GHC.ppr t) $ case t of
    (GHC.splitTyConApp_maybe -> Just (tc, args)) -> do
        match <- getMatch tc

        args' <- mapM convType args
        pure $ PIR.mkIterInst () match args'
    -- must be a TC app
    _ -> throwSd CompilationError $ "Type was not a type constructor application:" GHC.<+> GHC.ppr t

-- | Make the alternative for a given 'CoreAlt'.
convAlt
    :: Converting m
    => Bool -- ^ Whether we must delay the alternative.
    -> [GHC.Type] -- ^ The instantiated type arguments for the data constructor.
    -> GHC.CoreAlt -- ^ The 'CoreAlt' representing the branch itself.
    -> m PIRTerm
convAlt mustDelay instArgTys (alt, vars, body) = withContextM 3 (sdToTxt $ "Creating alternative:" GHC.<+> GHC.ppr alt) $ case alt of
    GHC.LitAlt _  -> throwPlain $ UnsupportedError "Literal case"
    GHC.DEFAULT   -> do
        body' <- convExpr body >>= maybeDelay mustDelay
        -- need to consume the args
        argTypes <- mapM convType instArgTys
        argNames <- forM [0..(length argTypes -1)] (\i -> safeFreshName () $ "default_arg" <> (T.pack $ show i))
        pure $ PIR.mkIterLamAbs (zipWith (PIR.VarDecl ()) argNames argTypes) body'
    -- We just package it up as a lambda bringing all the
    -- vars into scope whose body is the body of the case alternative.
    -- See Note [Iterated abstraction and application]
    -- See Note [Case expressions and laziness]
    GHC.DataAlt _ -> mkIterLamAbsScoped vars (convExpr body >>= maybeDelay mustDelay)
