{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE OverloadedStrings #-}
-- | Functions for compiling let-bound PIR datatypes into PLC.
module Language.PlutusIR.Compiler.Datatype (compileDatatype) where

import           Language.PlutusIR
import           Language.PlutusIR.Compiler.Types

import           PlutusPrelude                    (strToBs)

import           Control.Monad

import qualified Language.PlutusCore              as PLC
import           Language.PlutusCore.MkPlc
import           Language.PlutusCore.Quote

import           Data.List
import           Data.Maybe

-- Utilities

-- | @replaceFunTyTarget "X" "A->..->Z" = "A->..->X"@
replaceFunTyTarget :: PLC.Type tyname a -> PLC.Type tyname a -> PLC.Type tyname a
replaceFunTyTarget newTarget t = case t of
    PLC.TyFun a t1 t2 -> PLC.TyFun a t1 $ replaceFunTyTarget newTarget t2
    _                 -> newTarget

-- | Given the type of a constructor, get the type of the "case" type with the given result type.
-- @constructorCaseType "R" "A->Maybe A" = "A -> R"@
constructorCaseType :: PLC.Type tyname a -> VarDecl tyname name a -> PLC.Type tyname a
constructorCaseType resultType = replaceFunTyTarget resultType . varDeclTy

-- | Get the argument types of a function type.
-- @funTyArgs "A->B->C" = ["A", "B"]@
funTyArgs :: PLC.Type tyname a -> [PLC.Type tyname a]
funTyArgs t = case t of
    PLC.TyFun _ t1 t2 -> t1 : funTyArgs t2
    _                 -> []

-- | Given the type of a constructor, get its argument types.
-- @constructorArgTypes "A->Maybe A" = ["A"]
constructorArgTypes :: VarDecl tyname name a -> [PLC.Type tyname a]
constructorArgTypes = funTyArgs . varDeclTy

-- Datatypes

{- Note [Scott encoding of datatypes]
(This describes the conceptual scheme for converting data types - in fact we translate
them as abstract, so see also Note [Abstract data types].)

We translate our datatypes using the Scott encoding. The fundamental idea is that there is one thing
you can do with a datatype value: pattern match on it. A datatype value is therefore represented by
precisely the thing you need to do a pattern match. Namely, a function that takes functions implementing
each arm of the match, and then gives you a result.

For example, 'Just ' and 'Nothing' are encoded as
\arg1 . \justBranch nothingBranch . justBranch arg1
\justBranch nothingBranch . nothingBranch

We also need to think about the types. In general, we need:
- The type of the datatype
- The type of each constructor
- The value of each constructor

Consider a datatype T with type parameters t_i, constructors c_j with arguments a_c_j_k of types
t_c_j_k. Then:

The polymorphic type of the datatype is:
\t_1 :: (type) .. t_i :: (type) .
  forall r :: (type) .
    (t_1 -> .. -> t_c_1_k -> r) -> .. -> (t_1 -> .. -> t_c_j_k -> r) ->
      r

The polymorphic type of the constructor c_j is:
\t_1 :: (type) .. t_i :: (type) .
  t1 -> .. -> t_c_j_k ->
    T t_1 .. t_i
We never actually use this, since we don't put these as arguments to lambdas.

The value of the constructor c_j applied to arguments t_i is:
\a_1 : t1 .. a_c_j_k : t_c_j_k .
  abs r :: (type) .
    \c_1 : (t_1 -> .. -> t_c_1_k -> r) .. c_j : (t_1 -> .. -> t_c_j_k -> r) .
      c_j a_1 .. a_c_j_k

Pattern matching is very simple:
- We take each alternative, turn it into a function of its bound variables.
- We instantiate the scrutinee (which is polymorphic in the result type) at the
type of the overall case expression.
- We apply the instantiated scrutinee to the functions for each alternative.
-}

{- Note [Abstract data types]
While the Scott encoding makes it easy to simply convert all types inline, it
is convenient for a number of reasons to instead abstract out data types. Namely:
- The resulting code is much more readable, since we have named types instead
of (potentially big) inlined types.
- We generate less code because we're not repeating the definition at every use site.

The basic idea is to "let-bind" types using type abstractions, and values using
lambda abstractions. There are a few considerations that make this tricky, however:
1. When types are inlined, the Scott encoding allows us to construct values by
constructing the matching function inline. When they are abstract, we need to provide
(suitably polymorphic) constructors abstractly.
2. When types are inlined, the Scott encoding allows us to match against a type by
simply using it as a function. When they are abstract, we need to provide a
(suitably polymorphic) matching function abstractly.
3. The definition of a type must be abstract in the binding for the constructors and destructors
(so they can be used alongside the abstract type), but it must *not* be abstract in the
*body* of the constructors or destructors, because they depend on knowing the real structure
of the type.

Consequently, for a single type we end up with something like the following:

(abs ty :: (type) .
  \c1 : forall t_1 :: (type) .. t_i :: (type) . t_1 -> .. -> t_c_1_k -> ty .. c_j : t_1 -> t_c_j_k -> ty
    \match : forall t_1 :: (type) .. t_i :: (type) . forall r :: (type) b. (t_1 -> .. -> t_c_1_k -> r) -> .. -> (t_1 -> t_c_j_k -> r) -> r
      <user term>
)
<defn of t>
<defn of c1>
..
<defn of c_n>
<defn of match>
(see Note [Scott-encoding of datatypes] for how the actual definitions are constructed)

We also have to convert data constructors and case expressions into suitably instantiated
calls to the constructors/destructors instead of converting them directly as described in
Note [Scott encoding of data types].
-}

-- See note [Scott encoding of datatypes]
-- | Make the "Scott-encoded" type for a 'Datatype', with type variables free.
-- @mkScottTy "Maybe" = "forall r. r -> (a -> r) -> r"@
mkScottTy :: MonadQuote m => Datatype TyName Name () -> m (PLC.Type TyName ())
mkScottTy (Datatype _ _ _ _ constrs) = do
    -- TODO: include type name
    resultType <- liftQuote $ freshTyName () "r"
    let caseTys = fmap (constructorCaseType (PLC.TyVar () resultType)) constrs
        match = mkIterTyFun caseTys (PLC.TyVar () resultType)
        universal = PLC.TyForall () resultType (PLC.Type ()) match
    pure universal

-- | Make the "pattern functor" of a 'Datatype'. This is just the normal type, but with the
-- type variable for the type itself free. In the case of non-recursive datatypes this is just the
-- datatype.
-- @mkDatatypePatternFunctor "List" = "\a :: * -> forall r . r -> (a -> list a -> r) -> r"@
mkDatatypePatternFunctor :: MonadQuote m => Datatype TyName Name () -> m (PLC.Type TyName ())
mkDatatypePatternFunctor d@(Datatype _ _ tvs _ _) = do
    scottTy <- mkScottTy d
    let tyVars = fmap splitTyVarDecl tvs
        lambda = mkIterTyLam tyVars scottTy
    pure lambda

-- | Make the real PLC type corresponding to a 'Datatype' with the given pattern functor.
mkDatatypeType :: MonadQuote m => Recursivity -> Type TyName () -> Datatype TyName Name () -> m (PLC.Type TyName ())
mkDatatypeType r pf (Datatype _ tn _ _ _) = pure $ case r of
    NonRec -> pf
    -- We are reusing the same type name for the fixpoint variable. This is fine
    -- so long as we do renaming later, since we only reuse the name inside an inner binder
    Rec    -> PLC.TyFix () (tyVarDeclName tn) pf

-- | Make a 'Def' for the given 'Datatype' and pattern functor.
mkDatatypeTypeDef :: MonadQuote m => Recursivity -> Type TyName () -> Datatype TyName Name () -> m (Def (TyVarDecl TyName ()) (PLC.Type TyName ()))
mkDatatypeTypeDef r pf d@(Datatype _ tn _ _ _) = Def tn <$> mkDatatypeType r pf d

-- Constructors

-- | Make the 'Def's for the constructors of a 'Datatype' with the given pattern functor.
mkConstructorDefs :: forall m . MonadQuote m => Recursivity -> Type TyName () -> Datatype TyName Name () -> m [Def (VarDecl TyName Name ()) (PLC.Term TyName Name ())]
mkConstructorDefs r pf (Datatype _ tn tvs _ constrs) =
    forM constrs $ \c -> Def c <$> mkConstructor c
        where
            -- See note [Scott encoding of datatypes]
            mkConstructor :: VarDecl TyName Name () -> m (PLC.Term TyName Name ())
            mkConstructor constr = do
                -- TODO: include type name
                resultType <- liftQuote $ freshTyName () "r"

                -- case arguments and their types
                let caseTypes = fmap (constructorCaseType (PLC.TyVar () resultType)) constrs
                caseArgNames <- forM [0..(length constrs -1)] (\i -> liftQuote $ freshName () $ strToBs $ "case" ++ show i)

                -- TODO: this is inelegant, but it should never fail
                let index = fromJust $ elemIndex constr constrs
                let thisCase = caseArgNames !! index

                -- constructor args and their types
                let argTypes = constructorArgTypes constr
                argNames <- forM [0..(length argTypes -1)] (\i -> liftQuote $ freshName () $ strToBs $ "arg" ++ show i)

                let scottBody = mkScottConstructorBody r resultType (zip caseArgNames caseTypes) (zip argNames argTypes) thisCase (tyVarDeclName tn, pf)
                pure $ mkIterTyAbs (fmap splitTyVarDecl tvs) scottBody

-- See note [Scott encoding of datatypes]
-- | Make the body of a constructor.
mkScottConstructorBody
    :: Recursivity
    -> TyName () -- ^ Name of the result type
    -> [(Name (), PLC.Type TyName () )] -- ^ Names of the case arguments and their types
    -> [(Name (), PLC.Type TyName () )] -- ^ Names of the constructor arguments and their types
    -> Name () -- ^ Name of the current constructor
    -> (TyName (), PLC.Type TyName ()) -- ^ A bound name and pattern functor
    -> PLC.Term TyName Name ()
mkScottConstructorBody r resultTypeName caseNamesAndTypes argNamesAndTypes thisConstructor (n, pf) =
    let
        -- data types are always in kind Type
        resultKind = PLC.Type ()
        -- See Note [Iterated abstraction and application]
        -- c_i a_1 .. a_m
        applied = foldl' (\acc a -> PLC.Apply () acc (PLC.Var () a)) (PLC.Var () thisConstructor) (fmap fst argNamesAndTypes)
        -- \c_1 .. c_n . applied
        cfuncs = mkIterLamAbs caseNamesAndTypes applied
        -- no need for a body value check here, we know it's a lambda (see Note [Value restriction])
        -- forall r . cfuncs
        resAbstracted = PLC.TyAbs () resultTypeName resultKind cfuncs
        -- wrap resAbstracted
        fixed = case r of
            Rec    -> PLC.Wrap () n pf resAbstracted
            NonRec -> resAbstracted
        -- \a_1 .. a_m . fixed
        afuncs = mkIterLamAbs argNamesAndTypes fixed
    in afuncs

-- Destructors

-- See note [Scott encoding of datatypes]
-- See note [Abstract data types]
-- | Make the destructor for a 'Datatype'.
mkDestructor :: MonadQuote m => Recursivity -> Datatype TyName Name () -> m (PLC.Term TyName Name ())
mkDestructor r (Datatype _ tn tvs _ _) =
    let
        tyVars = fmap splitTyVarDecl tvs
    in do
        -- t t_1 .. t_n
        let applied = mkIterTyApp (PLC.TyVar () $ tyVarDeclName tn) (fmap (PLC.TyVar () . fst) tyVars)

        -- this is basically the identity! but we do need to unwrap it
        x <- liftQuote $ freshName () "x"
        let body = PLC.Var () x
            unwrapped = case r of
                Rec    -> PLC.Unwrap () body
                NonRec -> body
            lambda = PLC.LamAbs () x applied unwrapped
            -- /\ t_1 .. t_n
            abstracted = mkIterTyAbs tyVars lambda

        pure abstracted

-- | Make the type of a destructor for a 'Datatype'.
mkDestructorTy :: MonadQuote m => PLC.Type TyName () -> Datatype TyName Name () -> m (PLC.Type TyName ())
mkDestructorTy datatypeTy (Datatype _ tn tvs _ _) =
    let
        tyVars = fmap splitTyVarDecl tvs
        -- we essentially "unveil" the abstract type, so this
        -- is a function from the (instantiated, unwrapped) abstract type
        -- to the "real" Scott-encoded type that we can use as
        -- a destructor

        -- t t_1 .. t_n
        appliedAbstract = mkIterTyApp (PLC.TyVar () $ tyVarDeclName tn) (fmap (PLC.TyVar () . fst) tyVars)
        -- <actual datatype> t_1 .. t_n
        appliedConcrete = mkIterTyApp datatypeTy (fmap (PLC.TyVar () . fst) tyVars)
        converter = PLC.TyFun () appliedAbstract appliedConcrete

        -- forall t_1 .. t_n
        abstracted = mkIterTyForall tyVars converter
    in pure abstracted

-- | Make a 'Def' for the destructor of a 'Datatype'.
mkDestructorDef :: MonadQuote m => Recursivity -> PLC.Type TyName () -> Datatype TyName Name () -> m (Def (VarDecl TyName Name ()) (PLC.Term TyName Name ()))
mkDestructorDef r datatypeTy d@(Datatype _ _ _ destr _) = do
    destrFun <- mkDestructor r d
    -- we need this because we don't make the user declare the type when they give the name
    destTy <- mkDestructorTy datatypeTy d
    pure $ Def (VarDecl () destr destTy) destrFun

-- The main function

-- | Compile a 'Datatype' bound with the given body.
compileDatatype :: MonadQuote m => Recursivity -> PLC.Term TyName Name () -> Datatype TyName Name () -> m (PLC.Term TyName Name ())
compileDatatype r body d = do
    -- we compute the pattern functor and pass it around to avoid recomputing it
    pf <- mkDatatypePatternFunctor d
    ty <- mkDatatypeTypeDef r pf d
    constrs <- mkConstructorDefs r pf d
    destr <- mkDestructorDef r (defVal ty) d
    let
        tyVars = splitTyVarDecl <$> [defVar ty]
        tys = [defVal ty]
        vars = splitVarDecl <$> fmap defVar constrs ++ [defVar destr]
        vals = fmap defVal constrs ++ [defVal destr]
    -- See note [Abstract data types]
    pure $ mkIterApp (mkIterInst (mkIterTyAbs tyVars (mkIterLamAbs vars body)) tys) vals
