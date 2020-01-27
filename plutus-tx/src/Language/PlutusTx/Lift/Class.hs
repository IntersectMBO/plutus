{-# LANGUAGE ConstraintKinds   #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PolyKinds         #-}
{-# LANGUAGE TemplateHaskell   #-}
{-# LANGUAGE TypeApplications  #-}
{-# LANGUAGE ViewPatterns      #-}
module Language.PlutusTx.Lift.Class (Typeable (..),  Lift (..), makeTypeable, makeLift, withTyVars)where

import           Language.PlutusTx.Lift.THUtils

import           Language.PlutusIR
import           Language.PlutusIR.Compiler.Definitions
import           Language.PlutusIR.Compiler.Names
import           Language.PlutusIR.MkPir

import qualified Language.PlutusCore.MkPlc              as PLC
import           Language.PlutusCore.Quote

import           Control.Monad.Reader                   hiding (lift)
import           Control.Monad.State                    hiding (lift)
import qualified Control.Monad.Trans                    as Trans

import qualified Language.Haskell.TH                    as TH
import qualified Language.Haskell.TH.Datatype           as TH
import qualified Language.Haskell.TH.Syntax             as TH

import qualified Data.Map                               as Map
import qualified Data.Set                               as Set

import           Data.Foldable
import           Data.List                              (sortBy)
import           Data.Maybe
import           Data.Proxy
import qualified Data.Text                              as T
import           Data.Traversable

-- Apparently this is how you're supposed to fail at TH time.
dieTH :: Monad m => String -> m a
dieTH message = fail $ "Generating Lift instances: " ++ message

{- Note [Compiling at TH time and runtime]
We want to reuse PIR's machinery for defining datatypes. However, one cannot
get a PLC Type consisting of the compiled PIR type, because the compilation of the
definitions is done by making a *term*.

So we use the abstract support for handling definitions in PIR, MonadDefs. Typeable
then has `typeRep :: Proxy a -> RTCompile (Type TyName Name ())`,
which says that you can get the type in some compilation monad (which
you will later have to discharge yourself).

This means that the TH expressions we are generating are not for `Type`s directly, but rather
for monadic expressions that will, at runtime, compute types. We are effectively generating
a specialized compiler.

We thus have two pieces of compilation going on here:
- At TH time, we reify information about datatypes, and construct specialized compilation expressions
  for the various parts.
- At runtime, we actually run these and create definitions etc.

The interplay between the parts happening at TH time and the parts happening at runtime is somewhat
awkward, but I couldn't think of a better way of doing it.

A particularly awkward feature is that the typeclass constriants required by the code in each
instance are going to be different, and so we can't use reusable functions, instead we need to
inline all the definitions so that the overall expression can have the right constraints inferred.
-}

type RTCompile = DefT TH.Name () Quote
type RTCompileScope = ReaderT LocalVars RTCompile
type THCompile = StateT Deps (ReaderT THLocalVars TH.Q)

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
type LocalVars = Map.Map TH.Name (Type TyName ())
type THLocalVars = Set.Set TH.Name

withTyVars :: (MonadReader LocalVars m) => [(TH.Name, TyVarDecl TyName ())] -> m a -> m a
withTyVars mappings = local (\scope -> foldl' (\acc (n, tvd) -> Map.insert n (mkTyVar () tvd) acc) scope mappings)

thWithTyVars :: (MonadReader THLocalVars m) => [TH.Name] -> m a -> m a
thWithTyVars names = local (\scope -> foldr Set.insert scope names)

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

data Dep = TypeableDep TH.Type | LiftDep TH.Type deriving (Show, Eq, Ord)
type Deps = Set.Set Dep

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
typeablePir :: TH.Type -> TH.Type
typeablePir ty = TH.classPred ''Typeable [ty]

-- | Make a 'Lift' constraint.
liftPir :: TH.Type -> TH.Type
liftPir ty = TH.classPred ''Lift [ty]

toConstraint :: Dep -> TH.Pred
toConstraint = \case
    TypeableDep n -> typeablePir n
    LiftDep ty -> liftPir ty

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
normalizeAndResolve ty = normalizeType <$> (Trans.lift $ Trans.lift $ TH.resolveTypeSynonyms ty)

-- See Note [Ordering of constructors]
sortedCons :: TH.DatatypeInfo -> [TH.ConstructorInfo]
sortedCons TH.DatatypeInfo{TH.datatypeName=tyName, TH.datatypeCons=cons} =
    -- We need to compare 'TH.Name's on their string name *not* on the unique
    let sorted = sortBy (\(TH.constructorName -> (TH.Name o1 _)) (TH.constructorName -> (TH.Name o2 _)) -> compare o1 o2) cons
    in if tyName == ''Bool || tyName == ''[] then reverse sorted else sorted

tvNameAndKind :: TH.Type -> THCompile (TH.Name, Kind ())
tvNameAndKind = \case
    TH.SigT (TH.VarT name) kind -> do
        kind' <- (compileKind <=< normalizeAndResolve) kind
        pure (name, kind')
    _ -> dieTH "Unknown sort of type variable"

------------------
-- Types and kinds
------------------

-- Note: we can actually do this entirely at TH-time, which is nice
compileKind :: TH.Kind -> THCompile (Kind ())
compileKind = \case
    TH.StarT -> pure $ Type ()
    TH.AppT (TH.AppT TH.ArrowT k1) k2 -> KindArrow () <$> compileKind k1 <*> compileKind k2
    k -> dieTH $ "Unsupported kind: " ++ show k

compileType :: TH.Type -> THCompile (TH.TExpQ (RTCompileScope (Type TyName ())))
compileType = \case
    TH.AppT t1 t2 -> do
        t1' <- compileType t1
        t2' <- compileType t2
        pure [|| TyApp () <$> $$t1' <*> $$t2' ||]
    t@(TH.ConT name) -> compileTypeableType t name
    -- See note [Type variables]
    t@(TH.VarT name) -> do
        isLocal <- asks (Set.member name)
        if isLocal
        then pure [||
              do
                  vars <- ask
                  case Map.lookup name vars of
                      Just ty -> pure ty
                      -- TODO: better runtime failures
                      Nothing -> fail $ "Unknown local variable: " ++ show name
             ||]
        else compileTypeableType t name
    t -> dieTH $ "Unsupported type: " ++ show t

-- | Compile a type with the given name using 'typeRep' and incurring a corresponding 'Typeable' dependency.
compileTypeableType :: TH.Type -> TH.Name -> THCompile (TH.TExpQ (RTCompileScope (Type TyName ())))
compileTypeableType ty name = do
    addTypeableDep ty
    -- We need the `unsafeTExpCoerce` since this will necessarily involve
    -- types we don't know now: the type which this instance is for (which
    -- appears in the proxy argument). However, since we know the type of
    -- `typeRep` we can get back into typed land quickly.
    let trep :: TH.TExpQ (RTCompile (Type TyName ()))
        trep = TH.unsafeTExpCoerce [| typeRep (undefined :: Proxy $(pure ty)) |]
    pure [||
          let trep' :: RTCompile (Type TyName ())
              trep' = $$trep
          in do
              maybeType <- lookupType () name
              case maybeType of
                  Just t  -> pure t
                  -- this will need some additional constraints in scope
                  Nothing -> Trans.lift trep'
          ||]

-----------
-- Typeable
-----------

-- TODO: try and make this work with type applications
-- | Class for types which have a corresponding Plutus IR type. Instances should always be derived, do not write
-- your own instance!
class Typeable (a :: k) where
    -- | Get the Plutus IR type corresponding to this type.
    typeRep :: Proxy a -> RTCompile (Type TyName ())

-- TODO: there is an unpleasant amount of duplication between this and the main compiler, but
-- I'm not sure how to unify them better
compileTypeRep :: TH.DatatypeInfo -> THCompile (TH.TExpQ (RTCompile (Type TyName ())))
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
            _ -> dieTH "Newtypes must have a single constructor with a single argument"
        deps <- gets getTyConDeps
        pure [||
            let
                argTy' :: RTCompileScope (Type TyName ())
                argTy' = $$argTy
            in flip runReaderT mempty $ do
                maybeDefined <- lookupType () tyName
                case maybeDefined of
                    Just ty -> pure ty
                    Nothing -> do
                        (_, dtvd) <- mkTyVarDecl tyName typeKind
                        tvds <- traverse (uncurry mkTyVarDecl) tvNamesAndKinds

                        alias <- withTyVars tvds $ mkIterTyLam (fmap snd tvds) <$> argTy'
                        defineType tyName (PLC.Def dtvd alias) deps
                        recordAlias @TH.Name @() tyName
                        pure alias
            ||]
    else do
        constrExprs <- traverse compileConstructorDecl cons
        deps <- gets getTyConDeps
        pure [||
          let
              constrExprs' :: [Type TyName () -> RTCompileScope (VarDecl TyName Name ())]
              constrExprs' = $$(tyListE constrExprs)
          in flip runReaderT mempty $ do
              maybeDefined <- lookupType () tyName
              case maybeDefined of
                  Just ty -> pure ty
                  Nothing -> do
                      (_, dtvd) <- mkTyVarDecl tyName typeKind
                      tvds <- traverse (uncurry mkTyVarDecl) tvNamesAndKinds

                      let resultType = mkIterTyApp () (mkTyVar () dtvd) (fmap (mkTyVar () . snd) tvds)
                      matchName <- safeFreshName () (T.pack "match_" <> showName tyName)

                      -- See Note [Occurrences of recursive names]
                      let fakeDatatype = Datatype () dtvd [] matchName []

                      defineDatatype tyName (PLC.Def dtvd fakeDatatype) Set.empty

                      withTyVars tvds $ do
                          -- The TH expressions are in fact all functions that take the result type, so
                          -- we need to apply them
                          let constrActs :: RTCompileScope [VarDecl TyName Name ()]
                              constrActs = sequence $ constrExprs' <*> [resultType]
                          constrs <- constrActs

                          let datatype = Datatype () dtvd (fmap snd tvds) matchName constrs

                          defineDatatype tyName (PLC.Def dtvd datatype) deps
                      pure $ mkTyVar () dtvd
          ||]

compileConstructorDecl
    :: TH.ConstructorInfo
    -> THCompile (TH.TExpQ (Type TyName () -> RTCompileScope (VarDecl TyName Name ())))
compileConstructorDecl TH.ConstructorInfo{TH.constructorName=name, TH.constructorFields=argTys} = do
    tyExprs <- traverse (compileType <=< normalizeAndResolve) argTys
    pure [||
         let
             tyExprs' :: [RTCompileScope (Type TyName ())]
             tyExprs' = $$(tyListE tyExprs)
          -- we won't know the result type until runtime, so take it as an argument
          in \resultType -> do
              tys' <- sequence tyExprs'
              let constrTy = mkIterTyFun () tys' resultType
              constrName <- safeFreshName () $ showName name
              pure $ VarDecl () constrName constrTy
          ||]

makeTypeable :: TH.Name -> TH.Q [TH.Dec]
makeTypeable name = do
    requireExtension TH.ScopedTypeVariables

    info <- TH.reifyDatatype name
    (rhs, deps) <- flip runReaderT mempty $ flip runStateT mempty $ (compileTypeRep info)

    -- See Note [Closed constraints]
    let constraints = filter (not . isClosedConstraint) $ toConstraint <$> Set.toList deps

    decl <- TH.funD 'typeRep [TH.clause [TH.wildP] (TH.normalB (TH.unTypeQ rhs)) []]
    pure [TH.InstanceD Nothing constraints (typeablePir (TH.ConT name)) [decl]]

-------
-- Lift
-------

-- | Class for types which can be lifted into Plutus IR. Instances should be derived, do not write your
-- own instance!
class Lift a where
    -- | Get a Plutus IR term corresponding to the given value.
    lift :: a -> RTCompile (Term TyName Name ())

compileLift :: TH.DatatypeInfo -> THCompile [TH.Q TH.Clause]
compileLift dt = traverse (uncurry (compileConstructorClause dt)) (zip [0..] (sortedCons dt))

compileConstructorClause :: TH.DatatypeInfo -> Int -> TH.ConstructorInfo -> THCompile (TH.Q TH.Clause)
compileConstructorClause dt@TH.DatatypeInfo{TH.datatypeName=tyName, TH.datatypeVars=tvs} index TH.ConstructorInfo{TH.constructorName=name, TH.constructorFields=argTys} = do
    -- need to be able to lift the argument types
    traverse_ addLiftDep argTys

    -- We need the actual type parameters for the non-newtype case, and we have to do
    -- it out here, but it will give us redundant constraints in the newtype case,
    -- so we fudge it.
    typeExprs <- if isNewtype dt then pure [] else traverse (compileType <=< normalizeAndResolve) tvs
    pure $ do
        -- Build the patter for the clause definition. All the argument will be called "arg".
        patNames <- for argTys $ \_ -> TH.newName "arg"
        let pat = TH.conP name (fmap TH.varP patNames)

        -- `lift arg` for each arg we bind in the pattern. We need the `unsafeTExpCoerce` since this will
        -- necessarily involve types we don't know now: the types of each argument. However, since we
        -- know the type of `lift arg` we can get back into typed land quickly.
        let liftExprs :: [TH.TExpQ (RTCompile (Term TyName Name ()))]
            liftExprs = fmap (\pn -> TH.unsafeTExpCoerce $ TH.varE 'lift `TH.appE` TH.varE pn) patNames
        rhsExpr <- if isNewtype dt
            then case liftExprs of
                    [argExpr] -> pure argExpr
                    _     -> dieTH "Newtypes must have a single constructor with a single argument"
            else
                pure [||
                    -- We bind all the splices with explicit signatures to ensure we
                    -- get type errors as soon as possible, and to aid debugging.
                    let
                        typeExprs' :: [RTCompileScope (Type TyName ())]
                        typeExprs' = $$(tyListE typeExprs)
                        liftExprs' :: [RTCompile (Term TyName Name ())]
                        liftExprs' = $$(tyListE liftExprs)
                        -- We need the `unsafeTExpCoerce` since this will necessarily involve
                        -- types we don't know now: the type which this instance is for (which
                        -- appears in the proxy argument). However, since we know the type of
                        -- `typeRep` we can get back into typed land quickly.
                        trep :: RTCompile (Type TyName ())
                        trep = $$(TH.unsafeTExpCoerce [| typeRep (undefined :: Proxy $(TH.conT tyName)) |])
                    in do
                        -- force creation of datatype
                        _ <- trep

                        -- get the right constructor
                        maybeConstructors <- lookupConstructors () tyName
                        constrs <- case maybeConstructors of
                            -- TODO: better runtime failures
                            Nothing -> fail $ "Constructors not created for " ++ show tyName
                            Just cs -> pure cs
                        let constr = constrs !! index

                        -- The types are compiled in an (empty) local scope.
                        types <- flip runReaderT mempty $ sequence typeExprs'
                        lifts <- sequence liftExprs'

                        pure $ mkIterApp () (mkIterInst () constr types) lifts
                  ||]
        TH.clause [pat] (TH.normalB $ TH.unTypeQ rhsExpr) []

makeLift :: TH.Name -> TH.Q [TH.Dec]
makeLift name = do
    requireExtension TH.ScopedTypeVariables

    -- we need this too if we're lifting
    typeableDecs <- makeTypeable name
    info <- TH.reifyDatatype name

    let datatypeType = TH.datatypeType info

    (clauses, deps) <-
        flip runReaderT mempty $
        flip runStateT mempty $
        (compileLift info)

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
    let constraints = filter (not . isClosedConstraint) $ toConstraint <$> Set.toList prunedDeps

    decl <- TH.funD 'lift clauses
    let liftDecs = [TH.InstanceD Nothing constraints (liftPir datatypeType) [decl]]
    pure $ typeableDecs ++ liftDecs
