{-# LANGUAGE ConstraintKinds   #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE KindSignatures    #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PolyKinds         #-}
{-# LANGUAGE TemplateHaskell   #-}
{-# LANGUAGE ViewPatterns      #-}
module Language.PlutusTx.Lift.Class (Typeable (..),  Lift (..), makeTypeable, makeLift)where

import           Language.PlutusTx.Lift.THUtils

import           Language.PlutusIR
import           Language.PlutusIR.Compiler.Definitions
import           Language.PlutusIR.Compiler.Names
import           Language.PlutusIR.MkPir

import qualified Language.PlutusCore.MkPlc              as PLC
import           Language.PlutusCore.Quote

import           Control.Monad.Reader                   hiding (lift)
import           Control.Monad.State                    hiding (lift)

import qualified Language.Haskell.TH                    as TH
import qualified Language.Haskell.TH.Datatype           as TH
import qualified Language.Haskell.TH.Syntax             as TH

import qualified Data.Map                               as Map
import qualified Data.Set                               as Set

import           Data.Foldable
import           Data.List                              (sortBy)
import           Data.Maybe
import           Data.Proxy
import           Data.Traversable

-- Apparently this is how you're supposed to fail at TH time.
die :: Monad m => String -> m a
die message = fail $ "Generating Lift instances: " ++ message

{- Note [Compiling at TH time and runtime]
We want to reuse PIR's machinery for defining datatypes. However, one cannot
get a PLC Type consisting of the compiled PIR type, because the compilation of the
definitions is done by making a *term*.

So we use the abstract support for handling definitions in PIR, MonadDefs. Typeable
then has `typeRep :: (MonadDefs m, MonadQuote m) => Proxy a -> m (Type TyName Name ())`,
which says that you can get the type in some context where you can make definitions (which
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

-- Constraints

-- | Make a 'Typeable' constraint.
typeablePir :: TH.Type -> TH.Type
typeablePir ty = TH.classPred ''Typeable [ty]

-- | Make a 'Lift' constraint.
liftPir :: TH.Type -> TH.Type
liftPir ty = TH.classPred ''Lift [ty]

{- Note [Closed constraints]
There is no point adding constraints that are "closed", i.e. don't mention any of the
instance type variables. These will either be satisfied by other instances in scope
(in which case GHC will complain at you), or be unsatisfied in which case the user will
get a useful error anyway.
-}

isClosedConstraint :: TH.Pred -> Bool
isClosedConstraint = null . TH.freeVariables

-- Dependencies at TH time

{- Note [Tracking dependencies]
While running at TH time, we track the requirements that we need in order to be able to compile
the given type/term, which are things like "must be able to type the constructor argument types".

These are then cashed out into constraints on the instance.
-}

data Dep = TypeableDep TH.Type | LiftDep TH.Type deriving (Show, Eq, Ord)
type Deps = Set.Set Dep

toConstraint :: Dep -> TH.Pred
toConstraint = \case
    TypeableDep n -> typeablePir n
    LiftDep ty -> liftPir ty

getTyConDeps :: Deps -> Set.Set TH.Name
getTyConDeps deps = Set.fromList $ mapMaybe typeableDep $ Set.toList deps
    where
        typeableDep (TypeableDep (TH.ConT n)) = Just n
        typeableDep _                         = Nothing

addTypeableDep :: (THCompiling m) => TH.Type -> m ()
addTypeableDep ty = modify $ Set.insert $ TypeableDep $ normalizeType ty

addLiftDep :: (THCompiling m) => TH.Type -> m ()
addLiftDep ty = modify $ Set.insert $ LiftDep $ normalizeType ty

-- | The constraints when we are compiling at runtime. See note [Compiling at TH time and runtime].
type RTCompiling m = (MonadDefs TH.Name () m, MonadQuote m)
-- | The constraints when we are compiling at TH time. See note [Compiling at TH time and runtime].
type THCompiling m = (MonadState Deps m)

-- See Note [Ordering of constructors]
sortedCons :: TH.DatatypeInfo -> [TH.ConstructorInfo]
sortedCons TH.DatatypeInfo{TH.datatypeName=tyName, TH.datatypeCons=cons} =
    -- We need to compare 'TH.Name's on their string name *not* on the unique
    let sorted = sortBy (\(TH.constructorName -> (TH.Name o1 _)) (TH.constructorName -> (TH.Name o2 _)) -> compare o1 o2) cons
    in if tyName == ''Bool || tyName == ''[] then reverse sorted else sorted

tvNameAndKind :: (Monad m) => TH.Type -> m (TH.Name, Kind ())
tvNameAndKind = \case
    TH.SigT (TH.VarT name) kind -> do
        kind' <- compileKind kind
        pure (name, kind')
    _ -> die "Unknown sort of type variable"

-- Types and kinds

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
-}

-- | A switch to indicate how to handle type variables. See note [Type variables].
data VarsAs = Local | Typeable

-- | A scope for type variables. See note [Type variables].
type LocalVars = Map.Map TH.Name (Type TyName ())

getLocalName :: MonadReader LocalVars m => TH.Name -> m (Type TyName ())
getLocalName name = do
    vars <- ask
    case Map.lookup name vars of
        Just ty -> pure ty
        Nothing -> die $ "Free type variable: " ++ show name

withTyVars :: (MonadReader LocalVars m) => [(TH.Name, TyVarDecl TyName ())] -> m a -> m a
withTyVars mappings = local (\scope -> foldl' (\acc (n, tvd) -> Map.insert n (mkTyVar () tvd) acc) scope mappings)

compileKind :: (Monad m) => TH.Kind -> m (Kind ())
compileKind = \case
    TH.StarT -> pure $ Type ()
    TH.AppT (TH.AppT TH.ArrowT k1) k2 -> KindArrow () <$> compileKind k1 <*> compileKind k2
    k -> die $ "Unsupported kind: " ++ show k

-- see note [Compiling at TH time and runtime]
compileType :: THCompiling m => VarsAs -> TH.Type -> m (TH.Q TH.Exp)
compileType vars = \case
    TH.AppT t1 t2 -> do
        t1' <- compileType vars t1
        t2' <- compileType vars t2
        pure [| TyApp () <$> $(t1') <*> $(t2') |]
    t@(TH.ConT name) -> compileTypeableType t name
    -- See note [Type variables]
    t@(TH.VarT name) -> case vars of
        Typeable -> compileTypeableType t name
        Local    -> pure [| getLocalName name |]
    t -> die $ "Unsupported type: " ++ show t

-- | Compile a type with the given name using 'typeRep' and incurring a corresponding 'Typeable' dependency.
compileTypeableType :: (THCompiling m) => TH.Type -> TH.Name -> m (TH.Q TH.Exp)
compileTypeableType ty name = do
    addTypeableDep ty
    pure [|
          do
              maybeType <- lookupType () name
              case maybeType of
                  Just t  -> pure t
                  -- this will need some additional constraints in scope
                  Nothing -> typeRep (undefined :: Proxy $(pure ty))
          |]

-- Typeable

-- TODO: try and make this work with type applications
-- | Class for types which have a corresponding Plutus IR type. Instances should usually be declared
-- for type constructors, instances for applied types will be derived.
class Typeable (a :: k) where
    -- | Get the Plutus IR type corresponding to this type.
    typeRep :: (RTCompiling m) => Proxy a -> m (Type TyName ())

compileTypeRep :: (THCompiling m) => TH.DatatypeInfo -> m (TH.Q TH.Exp)
compileTypeRep dt@TH.DatatypeInfo{TH.datatypeName=tyName, TH.datatypeVars=tvs}= do
    tvNamesAndKinds <- traverse tvNameAndKind tvs
    -- annoyingly th-abstraction doesn't give us a kind we can compile here
    let datatypeKind = foldr (\(_, k) acc -> KindArrow () k acc) (Type ()) tvNamesAndKinds

    constrExprs <- traverse compileConstructorDecl (sortedCons dt)
    deps <- gets getTyConDeps
    -- see note [Compiling at TH time and runtime]
    pure [|
          flip runReaderT mempty $ do
              -- TODO: this is essentially the same as the code in Type.hs, really unify them
              maybeDefined <- lookupType () tyName
              case maybeDefined of
                  Just ty -> pure ty
                  Nothing -> do
                      (_, dtvd) <- mkTyVarDecl tyName datatypeKind
                      tvds <- traverse (uncurry mkTyVarDecl) tvNamesAndKinds

                      let resultType = mkIterTyApp () (mkTyVar () dtvd) (fmap (mkTyVar () . snd) tvds)
                      matchName <- safeFreshName () ("match_" ++ showName tyName)

                      -- Define it so we get something for recursive uses
                      let fakeDatatype = Datatype () dtvd [] matchName []

                      defineDatatype tyName (PLC.Def dtvd fakeDatatype) Set.empty

                      withTyVars tvds $ do
                          -- The TH expressions are in fact all functions that take the result type, so
                          -- we need to apply them
                          let constrActs = $(TH.listE constrExprs) <*> [resultType]
                          constrs <- sequence constrActs

                          let datatype = Datatype () dtvd (fmap snd tvds) matchName constrs

                          defineDatatype tyName (PLC.Def dtvd datatype) deps

                      pure $ mkTyVar () dtvd
          |]

compileConstructorDecl :: THCompiling m => TH.ConstructorInfo -> m (TH.Q TH.Exp)
compileConstructorDecl TH.ConstructorInfo{TH.constructorName=name, TH.constructorFields=argTys} = do
    tyExprs <- traverse (compileType Local . normalizeType) argTys
    -- see note [Compiling at TH time and runtime]
    pure [|
          -- we won't know the result type until runtime, so take it as an argument
          \resultType -> do
              tys' <- sequence $(TH.listE tyExprs)
              let constrTy = mkIterTyFun () tys' resultType
              constrName <- safeFreshName () $ showName name
              pure $ VarDecl () constrName constrTy
          |]

makeTypeable :: TH.Name -> TH.Q [TH.Dec]
makeTypeable name = do
    requireExtension TH.ScopedTypeVariables

    info <- TH.reifyDatatype name
    let (rhs, deps) = runState (compileTypeRep info) mempty

    -- See Note [Closed constraints]
    let constraints = filter (not . isClosedConstraint) $ toConstraint <$> Set.toList deps

    decl <- TH.funD 'typeRep [TH.clause [TH.wildP] (TH.normalB rhs) []]
    pure [TH.InstanceD Nothing constraints (typeablePir (TH.ConT name)) [decl]]

-- Lift

-- | Class for types which can be lifted into Plutus IR.
class Lift a where
    -- | Get a Plutus IR term corresponding to the given value.
    lift :: (RTCompiling m) => a -> m (Term TyName Name ())

compileLift :: THCompiling m => TH.DatatypeInfo -> m [TH.Q TH.Clause]
compileLift dt = traverse (uncurry (compileConstructorClause dt)) (zip [0..] (sortedCons dt))

compileConstructorClause :: (THCompiling m) => TH.DatatypeInfo -> Int -> TH.ConstructorInfo -> m (TH.Q TH.Clause)
compileConstructorClause TH.DatatypeInfo{TH.datatypeName=tyName, TH.datatypeVars=tvs} index TH.ConstructorInfo{TH.constructorName=name, TH.constructorFields=argTys} = do
    -- need to be able to lift the argument types
    traverse_ addLiftDep argTys

    -- need the actual type parameters
    typeExprs <- traverse (compileType Typeable . normalizeType) tvs
    pure $ do
        patNames <- for argTys $ \_ -> TH.newName "arg"
        let pats = fmap TH.varP patNames
        let pat = TH.conP name pats
        let liftExprs = fmap (\pn -> TH.varE 'lift `TH.appE` TH.varE pn) patNames
        -- see note [Compiling at TH time and runtime]
        expr <-
            [|
              do
                  -- force creation of datatype
                  _ <- typeRep (undefined :: Proxy $(TH.conT tyName))

                  -- get the right constructor
                  maybeConstructors <- lookupConstructors () tyName
                  constrs <- case maybeConstructors of
                      Nothing -> die $ "Constructors not created for " ++ show tyName
                      Just cs -> pure cs
                  let constr = constrs !! index

                  -- need to instantiate it to the right types and then lift all the arguments and apply it to them
                  types <- sequence $(TH.listE typeExprs)
                  lifts <- sequence $(TH.listE liftExprs)

                  pure $ mkIterApp () (mkIterInst () constr types) lifts
            |]
        TH.clause [pat] (TH.normalB $ pure expr) []

makeLift :: TH.Name -> TH.Q [TH.Dec]
makeLift name = do
    requireExtension TH.ScopedTypeVariables

    -- we need this too if we're lifting
    typeableDecs <- makeTypeable name
    info <- TH.reifyDatatype name

    let datatypeType = TH.datatypeType info

    let (clauses, deps) = runState (compileLift info) mempty

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
