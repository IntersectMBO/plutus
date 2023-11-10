-- editorconfig-checker-disable-file
{-# LANGUAGE CPP                   #-}
{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE DefaultSignatures     #-}
{-# LANGUAGE DeriveAnyClass        #-}
{-# LANGUAGE DerivingStrategies    #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE PolyKinds             #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE ViewPatterns          #-}
-- It is complex to mix TH with polymorphisms. Core lint can sometimes catch problems
-- caused by using polymorphisms the wrong way, e.g., accidentally using impredicative types.
{-# OPTIONS_GHC -dcore-lint #-}
module PlutusTx.Lift.TH (
    makeTypeable
    , makeLift
    , LiftError (..)
    ) where

import PlutusTx.Lift.Class
import PlutusTx.Lift.THUtils

import PlutusIR
import PlutusIR.Compiler.Definitions
import PlutusIR.Compiler.Names
import PlutusIR.MkPir hiding (constr)

import PlutusCore.Default qualified as PLC
import PlutusCore.MkPlc qualified as PLC

import Control.Monad ((<=<))
import Control.Monad.Except (ExceptT, runExceptT, throwError)
import Control.Monad.Reader (MonadReader, ReaderT, ask, asks, local, runReaderT)
import Control.Monad.State (StateT, gets, modify, runStateT)
import Control.Monad.Trans qualified as Trans

import Language.Haskell.TH qualified as TH hiding (newName)
import Language.Haskell.TH.Datatype qualified as TH
import Language.Haskell.TH.Syntax qualified as TH hiding (newName)
import Language.Haskell.TH.Syntax.Compat qualified as TH

import Data.Map qualified as Map
import Data.Set qualified as Set

import Control.Exception qualified as Prelude (Exception, throw)
import Data.Foldable
import Data.List (sortBy)
import Data.Maybe
import Data.Proxy
import Data.Text qualified as T
import Data.Traversable
import Prettyprinter qualified as PP

-- We do not use qualified import because the whole module contains off-chain code
import Prelude as Haskell

type RTCompileScope uni fun = ReaderT (LocalVars uni) (RTCompile uni fun)
type THCompile = StateT Deps (ReaderT THLocalVars (ExceptT LiftError TH.Q))

data LiftError = UnsupportedLiftKind !TH.Kind
               | UnsupportedLiftType !TH.Type
               | UserLiftError !T.Text
               | LiftMissingDataCons !TH.Name
               | LiftMissingVar !TH.Name
               deriving anyclass (Prelude.Exception)

instance PP.Pretty LiftError where
    pretty (UnsupportedLiftType t) = "Unsupported lift type: " PP.<+> PP.viaShow t
    pretty (UnsupportedLiftKind t) = "Unsupported lift kind: " PP.<+> PP.viaShow t
    pretty (UserLiftError t)       = PP.pretty t
    pretty (LiftMissingDataCons n) = "Constructors not created for type: " PP.<+> PP.viaShow n
    pretty (LiftMissingVar n)      = "Unknown local variable: " PP.<+> PP.viaShow n

instance Show LiftError where
    show = show . PP.pretty -- for Control.Exception

{- Note [Impredicative function universe wrappers]
We are completely independent of the function universe. We generate constants (so we care about the type universe),
but we never generate builtin functions.

This is indicated in the fact that e.g. 'typeRep' has type 'forall fun . ...'. Note what this says: the
*caller* of 'typeRep` can decide on 'fun'.

So how do we deal with this? A wrong way is to parameterize our (TH) functions by 'fun'. This is wrong, because
this 'fun' is a type variable at TH-generation time, and we want a type variable in the generated code.
Sometimes this will even appear to work, and I don't know what kind of awful magic is going on in trying to persist
type variables into the quote, but I'm pretty sure it's wrong.

We could use 'InstanceSigs', bind 'fun', and then pass it down and use it in our signatures. But you can't splice
types into signatures in typed TH, you need to go to untyped TH and 'unsafeCoerceTExp' back again, which is pretty ugly.

Alternatively, we can *generate* functions which are parameterized over 'fun', and instantiate them at the top-level.
This is totally fine... except that the representation of expressions in typed TH has a type parameter for the type of
the expression, so we would need to write 'TExp (forall fun . ...)'... which is an impredicative type.

The usual solution is to make a datatype that wraps up the quantification, so you write 'newtype X = X (forall a . ...)',
and then you can write 'TExp X' just fine.

We do this, but annoyingly due to the fact that 'fun' appears inside the *value* of our monadic types (e.g. when we compile
to a term we need to have 'fun' in there) we can't do this generically, and instead we end up with a set of repetitive wrappers
for different variants of this impredicative type. Which is annoying, but does work.
-}

-- See Note [Impredicative function universe wrappers]
newtype CompileTerm = CompileTerm
  { unCompileTerm ::
      forall fun.
      RTCompile PLC.DefaultUni fun (Term TyName Name PLC.DefaultUni fun ())
  }
newtype CompileType = CompileType
  { unCompileType ::
      forall fun.
      RTCompile PLC.DefaultUni fun (Type TyName PLC.DefaultUni ())
  }
newtype CompileTypeScope = CompileTypeScope
  { unCompileTypeScope ::
      forall fun.
      RTCompileScope PLC.DefaultUni fun (Type TyName PLC.DefaultUni ())
  }
newtype CompileDeclFun = CompileDeclFun
  { unCompileDeclFun ::
      forall fun.
      Type TyName PLC.DefaultUni () ->
      RTCompileScope PLC.DefaultUni fun (VarDecl TyName Name PLC.DefaultUni ())
  }

{- Note [Type variables]
We handle types in almost exactly the same way when we are constructing Typeable
instances and when we are constructing Lift instances. However, there is one key difference
in how we handle type variables.

In the Typeable case, the type variables we see will be the type variables of the
datatype, which we want to map into the variable declarations that we construct. This requires
us to do some mapping between them at *runtime*, and keep a scope around to map between the TH names
and the PLC types.

In the Lift case, type variables will be free type variables in the instance, and should be handled
by appropriate Typeable constraints for those variables. We get the PLC types by just calling
typeRep.

However, for simplicity we always act as though we have a local scope, and fall back to Typeable,
but in the Lift case we will never populate the local scope.
-}

-- | A scope for type variables. See note [Type variables].
type LocalVars uni = Map.Map TH.Name (Type TyName uni ())
type THLocalVars = Set.Set TH.Name

{- Note [Lifting newtypes]
Newtypes are handled differently in the compiler, in that we identify them with their underlying type.
See Note [Coercions and newtypes] for details.

So we need to do the same here. This means two things:
- For Typeable, we look for the unique field of the unique constructor, and then make a type lambda
  binding the type variables whose body is that type.
- For Lift, we assert that all constructors must have precisely one argument (as newtypes do), and we
  simply call lift on that.

Since we don't "compile" all the way, rather relying on the typeclass system, lifting recursive
newtypes will hang a runtime. Don't do that. (This is worse than what we do in the compiler, see
Note [Occurrences of recursive names])
-}

-- Dependencies at TH time

{- Note [Tracking dependencies]
While running at TH time, we track the requirements that we need in order to be able to compile
the given type/term, which are things like "must be able to type the constructor argument types".

These are then cashed out into constraints on the instance.
-}

data Dep = TypeableDep TH.Type | LiftDep TH.Type deriving stock (Show, Eq, Ord)
type Deps = Set.Set Dep

withTyVars :: (MonadReader (LocalVars uni) m) => [(TH.Name, TyVarDecl TyName ())] -> m a -> m a
withTyVars mappings = local (\scope -> foldl' (\acc (n, tvd) -> Map.insert n (mkTyVar () tvd) acc) scope mappings)

thWithTyVars :: (MonadReader THLocalVars m) => [TH.Name] -> m a -> m a
thWithTyVars names = local (\scope -> foldr Set.insert scope names)

-- | Get all the named types which we depend on to define the current type.
-- Note that this relies on dependencies having been added with type synonyms
-- resolved!
getTyConDeps :: Deps -> Set.Set TH.Name
getTyConDeps deps = Set.fromList $ mapMaybe typeableDep $ Set.toList deps
    where
        typeableDep (TypeableDep (TH.ConT n)) = Just n
        typeableDep _                         = Nothing

addTypeableDep :: TH.Type -> THCompile ()
addTypeableDep ty = do
    ty' <- normalizeAndResolve ty
    modify $ Set.insert $ TypeableDep ty'

addLiftDep :: TH.Type -> THCompile ()
addLiftDep ty = do
    ty' <- normalizeAndResolve ty
    modify $ Set.insert $ LiftDep ty'

-- Constraints

-- | Make a 'Typeable' constraint.
typeablePir :: TH.Type -> TH.Type -> TH.Type
typeablePir uni ty = TH.classPred ''Typeable [uni, ty]

-- | Make a 'Lift' constraint.
liftPir :: TH.Type -> TH.Type -> TH.Type
liftPir uni ty = TH.classPred ''Lift [uni, ty]

toConstraint :: TH.Type -> Dep -> TH.Pred
toConstraint uni = \case
    TypeableDep n -> typeablePir uni n
    LiftDep ty    -> liftPir uni ty

{- Note [Closed constraints]
There is no point adding constraints that are "closed", i.e. don't mention any of the
instance type variables. These will either be satisfied by other instances in scope
(in which case GHC will complain at you), or be unsatisfied in which case the user will
get a useful error anyway.
-}

isClosedConstraint :: TH.Pred -> Bool
isClosedConstraint = null . TH.freeVariables

-- | Convenience wrapper around 'normalizeType' and 'TH.resolveTypeSynonyms'.
normalizeAndResolve :: TH.Type -> THCompile TH.Type
normalizeAndResolve ty = normalizeType <$> (Trans.lift $ Trans.lift $ Trans.lift $ TH.resolveTypeSynonyms ty)

-- See Note [Ordering of constructors]
sortedCons :: TH.DatatypeInfo -> [TH.ConstructorInfo]
sortedCons TH.DatatypeInfo{TH.datatypeName=tyName, TH.datatypeCons=cons} =
    -- We need to compare 'TH.Name's on their string name *not* on the unique
    let sorted = sortBy (\(TH.constructorName -> (TH.Name o1 _)) (TH.constructorName -> (TH.Name o2 _)) -> compare o1 o2) cons
    in if tyName == ''Bool || tyName == ''[] then reverse sorted else sorted

#if MIN_VERSION_template_haskell(2,17,0)
tvNameAndKind :: TH.TyVarBndrUnit -> THCompile (TH.Name, Kind ())
tvNameAndKind = \case
    TH.KindedTV name _ kind -> do
        kind' <- (compileKind <=< normalizeAndResolve) kind
        pure (name, kind')
    -- TODO: is this what PlainTV actually means? That it's of kind Type?
    TH.PlainTV name _ -> pure (name, Type ())
#else
tvNameAndKind :: TH.TyVarBndr -> THCompile (TH.Name, Kind ())
tvNameAndKind = \case
    TH.KindedTV name kind -> do
        kind' <- (compileKind <=< normalizeAndResolve) kind
        pure (name, kind')
    -- TODO: is this what PlainTV actually means? That it's of kind Type?
    TH.PlainTV name -> pure (name, Type ())
#endif

------------------
-- Types and kinds
------------------

-- Note: we can actually do this entirely at TH-time, which is nice
compileKind :: TH.Kind -> THCompile (Kind ())
compileKind = \case
    TH.StarT                          -> pure $ Type ()
    TH.AppT (TH.AppT TH.ArrowT k1) k2 -> KindArrow () <$> compileKind k1 <*> compileKind k2
    k                                 -> throwError $ UnsupportedLiftKind k

compileType :: TH.Type -> THCompile (TH.TExpQ CompileTypeScope)
compileType = \case
    TH.AppT t1 t2 -> do
        t1' <- compileType t1
        t2' <- compileType t2
        pure . TH.examineSplice $ [|| CompileTypeScope (TyApp () <$> unCompileTypeScope ($$(TH.liftSplice t1')) <*> unCompileTypeScope ($$(TH.liftSplice t2'))) ||]
    t@(TH.ConT name) -> compileTypeableType t name
    -- See note [Type variables]
    t@(TH.VarT name) -> do
        isLocal <- asks (Set.member name)
        if isLocal
        then pure . TH.examineSplice $ [||
              CompileTypeScope $ do
                  vars <- ask
                  case Map.lookup name vars of
                      Just ty -> pure ty
                      Nothing -> Prelude.throw $ LiftMissingVar name
             ||]
        else compileTypeableType t name
    t -> throwError $ UnsupportedLiftType t

-- | Compile a type with the given name using 'typeRep' and incurring a corresponding 'Typeable' dependency.
compileTypeableType :: TH.Type -> TH.Name -> THCompile (TH.TExpQ CompileTypeScope)
compileTypeableType ty name = do
    addTypeableDep ty
    -- We need the `unsafeTExpCoerce` since this will necessarily involve
    -- types we don't know now: the type which this instance is for (which
    -- appears in the proxy argument). However, since we know the type of
    -- `typeRep` we can get back into typed land quickly.
    let trep :: TH.TExpQ CompileType
        trep = TH.unsafeTExpCoerce [| CompileType (typeRep (Proxy :: Proxy $(pure ty))) |]
    pure . TH.examineSplice $ [||
          let trep' :: forall fun . RTCompileScope PLC.DefaultUni fun (Type TyName PLC.DefaultUni ())
              trep' = Trans.lift $ unCompileType ($$(TH.liftSplice trep))
          in CompileTypeScope $ do
              maybeType <- lookupType () name
              case maybeType of
                  Just t  -> pure t
                  -- this will need some additional constraints in scope
                  Nothing -> trep'
          ||]

-- Just here so we can pin down the type variables without using TypeApplications in the generated code
recordAlias' :: TH.Name -> RTCompileScope PLC.DefaultUni fun ()
recordAlias' = recordAlias

-- Just here so we can pin down the type variables without using TypeApplications in the generated code
defineDatatype' :: TH.Name -> DatatypeDef TyName Name PLC.DefaultUni () -> Set.Set TH.Name -> RTCompileScope PLC.DefaultUni fun ()
defineDatatype' = defineDatatype

-- TODO: there is an unpleasant amount of duplication between this and the main compiler, but
-- I'm not sure how to unify them better
compileTypeRep :: TH.DatatypeInfo -> THCompile (TH.TExpQ CompileType)
compileTypeRep dt@TH.DatatypeInfo{TH.datatypeName=tyName, TH.datatypeVars=tvs} = do
    tvNamesAndKinds <- traverse tvNameAndKind tvs
    -- annoyingly th-abstraction doesn't give us a kind we can compile here
    let typeKind = foldr (\(_, k) acc -> KindArrow () k acc) (Type ()) tvNamesAndKinds
    let cons = sortedCons dt

    thWithTyVars (fmap fst tvNamesAndKinds) $ if isNewtype dt
    then do
        -- Extract the unique field of the unique constructor
        argTy <- case cons of
            [ TH.ConstructorInfo {TH.constructorFields=[argTy]} ] -> (compileType <=< normalizeAndResolve) argTy
            _ -> throwError $ UserLiftError "Newtypes must have a single constructor with a single argument"
        deps <- gets getTyConDeps
        pure . TH.examineSplice $ [||
            let
                argTy' :: forall fun . RTCompileScope PLC.DefaultUni fun (Type TyName PLC.DefaultUni ())
                argTy' = unCompileTypeScope $$(TH.liftSplice argTy)
                act :: forall fun . RTCompileScope PLC.DefaultUni fun (Type TyName PLC.DefaultUni ())
                act = do
                    maybeDefined <- lookupType () tyName
                    case maybeDefined of
                        Just ty -> pure ty
                        Nothing -> do
                            (_, dtvd) <- mkTyVarDecl tyName typeKind
                            tvds <- traverse (uncurry mkTyVarDecl) tvNamesAndKinds

                            alias <- withTyVars tvds $ mkIterTyLam (fmap snd tvds) <$> argTy'
                            defineType tyName (PLC.Def dtvd alias) deps
                            recordAlias' tyName
                            pure alias
            in CompileType $ runReaderT act mempty
         ||]
    else do
        constrExprs <- traverse compileConstructorDecl cons
        deps <- gets getTyConDeps
        pure . TH.examineSplice $ [||
          let
              constrExprs' :: [CompileDeclFun]
              constrExprs' = $$(TH.liftSplice $ tyListE constrExprs)
              act :: forall fun . RTCompileScope PLC.DefaultUni fun (Type TyName PLC.DefaultUni ())
              act = do
                maybeDefined <- lookupType () tyName
                case maybeDefined of
                    Just ty -> pure ty
                    Nothing -> do
                        (_, dtvd) <- mkTyVarDecl tyName typeKind
                        tvds <- traverse (uncurry mkTyVarDecl) tvNamesAndKinds

                        let resultType = mkIterTyAppNoAnn (mkTyVar () dtvd) (fmap (mkTyVar () . snd) tvds)
                        matchName <- safeFreshName (T.pack "match_" <> showName tyName)

                        -- See Note [Occurrences of recursive names]
                        let fakeDatatype = Datatype () dtvd [] matchName []

                        defineDatatype' tyName (PLC.Def dtvd fakeDatatype) Set.empty

                        withTyVars tvds $ do
                            -- The TH expressions are in fact all functions that take the result type, so
                            -- we need to apply them
                            let constrActs :: RTCompileScope PLC.DefaultUni fun [VarDecl TyName Name PLC.DefaultUni ()]
                                constrActs = sequence $ fmap (\x -> unCompileDeclFun x) constrExprs' <*> [resultType]
                            constrs <- constrActs

                            let datatype = Datatype () dtvd (fmap snd tvds) matchName constrs

                            defineDatatype tyName (PLC.Def dtvd datatype) deps
                        pure $ mkTyVar () dtvd
          in CompileType $ runReaderT act mempty
          ||]

compileConstructorDecl
    :: TH.ConstructorInfo
    -> THCompile (TH.TExpQ CompileDeclFun)
compileConstructorDecl TH.ConstructorInfo{TH.constructorName=name, TH.constructorFields=argTys} = do
    tyExprs <- traverse (compileType <=< normalizeAndResolve) argTys
    pure . TH.examineSplice $ [||
         let
             tyExprs' :: forall fun . [RTCompileScope PLC.DefaultUni fun (Type TyName PLC.DefaultUni ())]
             tyExprs' = fmap (\x -> unCompileTypeScope x) $$(TH.liftSplice $ tyListE tyExprs)
          -- we won't know the result type until runtime, so take it as an argument
          in CompileDeclFun $ \resultType -> do
              tys' <- sequence tyExprs'
              let constrTy = mkIterTyFun () tys' resultType
              constrName <- safeFreshName $ showName name
              pure $ VarDecl () constrName constrTy
          ||]

makeTypeable :: TH.Type -> TH.Name -> TH.Q [TH.Dec]
makeTypeable uni name = do
    requireExtension TH.ScopedTypeVariables

    info <- TH.reifyDatatype name
    (rhs, deps) <- runTHCompile $ compileTypeRep info

    -- See Note [Closed constraints]
    let constraints = filter (not . isClosedConstraint) $ toConstraint uni <$> Set.toList deps
    -- We need to unwrap the wrapper at the last minute, see Note [Impredicative function universe wrappers]
    let unwrappedRhs = [| unCompileType |] `TH.appE` TH.unTypeQ rhs

    decl <- TH.funD 'typeRep [TH.clause [TH.wildP] (TH.normalB unwrappedRhs) []]
    pure [TH.InstanceD Nothing constraints (typeablePir uni (TH.ConT name)) [decl]]

compileLift :: TH.DatatypeInfo -> THCompile [TH.Q TH.Clause]
compileLift dt = traverse (uncurry (compileConstructorClause dt)) (zip [0..] (sortedCons dt))

compileConstructorClause
    :: TH.DatatypeInfo -> Int -> TH.ConstructorInfo -> THCompile (TH.Q TH.Clause)
compileConstructorClause dt@TH.DatatypeInfo{TH.datatypeName=tyName, TH.datatypeVars=tvs} index TH.ConstructorInfo{TH.constructorName=name, TH.constructorFields=argTys} = do
    -- need to be able to lift the argument types
    traverse_ addLiftDep argTys

    -- We need the actual type parameters for the non-newtype case, and we have to do
    -- it out here, but it will give us redundant constraints in the newtype case,
    -- so we fudge it.
    tyExprs <- if isNewtype dt then pure [] else for tvs $ \tv -> do
      (n, _) <- tvNameAndKind tv
      compileType (TH.VarT n)

    -- Build the patter for the clause definition. All the argument will be called "arg".
    patNames <- Trans.lift $ Trans.lift $ Trans.lift $ for argTys $ \_ -> TH.newName "arg"
    let pat = TH.conP name (fmap TH.varP patNames)

    -- `lift arg` for each arg we bind in the pattern. We need the `unsafeTExpCoerce` since this will
    -- necessarily involve types we don't know now: the types of each argument. However, since we
    -- know the type of `lift arg` we can get back into typed land quickly.
    let liftExprs :: [TH.TExpQ CompileTerm]
        liftExprs = fmap (\pn -> TH.unsafeTExpCoerce $ [| CompileTerm $(TH.varE 'lift `TH.appE` TH.varE pn) |]) patNames

    rhsExpr <- if isNewtype dt
            then case liftExprs of
                    [argExpr] -> pure argExpr
                    _         -> throwError $ UserLiftError "Newtypes must have a single constructor with a single argument"
            else
                pure . TH.examineSplice $ [||
                    -- We bind all the splices with explicit signatures to ensure we
                    -- get type errors as soon as possible, and to aid debugging.
                    let
                        liftExprs' :: [CompileTerm]
                        liftExprs' = $$(TH.liftSplice $ tyListE liftExprs)
                        -- We need the `unsafeTExpCoerce` since this will necessarily involve
                        -- types we don't know now: the type which this instance is for (which
                        -- appears in the proxy argument). However, since we know the type of
                        -- `typeRep` we can get back into typed land quickly.
                        trep :: CompileType
                        trep = $$(TH.unsafeSpliceCoerce [| CompileType (typeRep (Proxy :: Proxy $(TH.conT tyName))) |])
                    in CompileTerm $ do
                        -- force creation of datatype
                        _ <- unCompileType trep

                        -- get the right constructor
                        maybeConstructors <- lookupConstructors () tyName
                        constrs <- case maybeConstructors of
                            Nothing -> Prelude.throw $ LiftMissingDataCons tyName
                            Just cs -> pure cs
                        let constr = constrs !! index

                        lifts :: [Term TyName Name PLC.DefaultUni fun ()] <- sequence (unCompileTerm <$> liftExprs')
                        -- The 'fun' that is referenced here is the 'fun' that we bind the line above.
                        -- If it was forall-bound instead, 'typeExprs\'' wouldn't type check,
                        -- because 'Type' does not determine 'fun' (unlike 'Term' in 'liftExprs\''
                        -- above).
                        let tyExprs' :: [RTCompileScope PLC.DefaultUni fun (Type TyName PLC.DefaultUni ())]
                            tyExprs' = fmap (\x -> unCompileTypeScope x) $$(TH.liftSplice $ tyListE tyExprs)
                        -- The types are compiled in an (empty) local scope.
                        types <- flip runReaderT mempty $ sequence tyExprs'

                        pure $ mkIterAppNoAnn (mkIterInstNoAnn constr types) lifts
                  ||]
    pure $ TH.clause [pat] (TH.normalB $ [| unCompileTerm $(TH.unTypeQ rhsExpr) |]) []

makeLift :: TH.Name -> TH.Q [TH.Dec]
makeLift name = do
    requireExtension TH.ScopedTypeVariables

    let uni = TH.ConT ''PLC.DefaultUni
    -- we need this too if we're lifting
    typeableDecs <- makeTypeable uni name
    info <- TH.reifyDatatype name

    let datatypeType = TH.datatypeType info

    (clauses, deps) <- runTHCompile $ compileLift info

    {-
    Here we *do* need to add some constraints, because we're going to generate things like
    `instance Lift a => Lift (Maybe a)`. We can't just leave these open because they refer to type variables.

    We *could* put in a Typeable constraint for the type itself. This is somewhat more correct,
    but GHC warns us if we do this because we always also define the instance alongside. So we just
    leave it out.

    We also need to remove any Lift constraints we get for the type we're defining. This can happen if
    we're recursive, since we'll probably end up with constructor arguments of the current type.
    We don't want `instance Lift [a] => Lift [a]`!
    -}
    let prunedDeps = Set.delete (LiftDep datatypeType) deps
    -- See Note [Closed constraints]
    let constraints = filter (not . isClosedConstraint) $ toConstraint uni <$> Set.toList prunedDeps

    decl <- TH.funD 'lift clauses
    let liftDecs = [TH.InstanceD Nothing constraints (liftPir uni datatypeType) [decl]]
    pure $ typeableDecs ++ liftDecs

-- | In case of exception, it will call `fail` in TemplateHaskell
runTHCompile :: THCompile a -> TH.Q (a, Deps)
runTHCompile m = do
    res <- runExceptT .
          flip runReaderT mempty $
          flip runStateT mempty m
    case res of
        Left a  -> fail $ "Generating Lift instances: " ++ show (PP.pretty a)
        Right b -> pure b
