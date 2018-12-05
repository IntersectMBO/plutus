{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE OverloadedStrings #-}
-- | Functions for compiling let-bound PIR datatypes into PLC.
module Language.PlutusIR.Compiler.Datatype (compileDatatype) where

import           Language.PlutusIR
import           Language.PlutusIR.Compiler.Names
import           Language.PlutusIR.Compiler.Provenance
import           Language.PlutusIR.Compiler.Types

import           PlutusPrelude                         (bsToStr)

import qualified Language.PlutusCore                   as PLC
import qualified Language.PlutusCore.MkPlc             as PLC
import           Language.PlutusCore.Quote
import qualified Language.PlutusCore.Subst             as PLC

import           Control.Monad.Reader

import           Data.Traversable

-- Utilities

-- | @replaceFunTyTarget X (A->..->Z) = (A->..->X)@
replaceFunTyTarget :: PLC.Type tyname a -> PLC.Type tyname a -> PLC.Type tyname a
replaceFunTyTarget newTarget t = case t of
    PLC.TyFun a t1 t2 -> PLC.TyFun a t1 $ replaceFunTyTarget newTarget t2
    _                 -> newTarget

-- | Given the type of a constructor, get the type of the "case" type with the given result type.
-- @constructorCaseType R (A->Maybe A) = (A -> R)@
constructorCaseType :: PLC.Type tyname a -> VarDecl tyname name a -> PLC.Type tyname a
constructorCaseType resultType = replaceFunTyTarget resultType . varDeclType

-- | Get the argument types of a function type.
-- @funTyArgs (A->B->C) = [A, B]@
funTyArgs :: PLC.Type tyname a -> [PLC.Type tyname a]
funTyArgs t = case t of
    PLC.TyFun _ t1 t2 -> t1 : funTyArgs t2
    _                 -> []

-- | Given the type of a constructor, get its argument types.
-- @constructorArgTypes (A->Maybe A) = [A]
constructorArgTypes :: VarDecl tyname name a -> [PLC.Type tyname a]
constructorArgTypes = funTyArgs . varDeclType

-- | "Unveil" a datatype definition in a type, by replacing uses of the name as a type variable with the concrete definition.
unveilDatatype :: Eq (tyname a) => Type tyname a -> Datatype tyname name a -> Type tyname a -> Type tyname a
unveilDatatype dty (Datatype _ tn _ _ _) = PLC.substTy (\n -> if n == tyVarDeclName tn then Just dty else Nothing)

resultTypeName :: Compiling m e a => Datatype TyName Name (Provenance a) -> m (TyName (Provenance a))
resultTypeName (Datatype _ tn _ _ _) = ask >>= \p -> liftQuote $ freshTyName p $ "out_" <> (nameString $ unTyName $ tyVarDeclName tn)

-- Datatypes

{- Note [Scott encoding of datatypes]
(This describes the conceptual scheme for converting data types - in fact we translate
them as abstract, so see also Note [Abstract data types].)

We translate our datatypes using the Scott encoding. The fundamental idea is that there is one thing
you can do with a datatype value: pattern match on it. A datatype value is therefore represented by
precisely the thing you need to do a pattern match. Namely, a function that takes functions implementing
each arm of the match, and then gives you a result.

We also need to think about the types. In general, we need:
- The encoded type corresponding to the datatype itself
- The encoded type of each constructor
- The encoded term for each constructor
- The encoded type of the destructor
- The encoded term for the destructor

-- Basic example

For example, consider 'Maybe a'. Then:
- The type corresponding to the datatype is:
  Maybe = \(a :: *) -> forall out_Maybe . out_maybe -> (a -> out_Maybe) -> out_Maybe
- The type of the constructors are:
  Just : forall (a :: *) . a -> Maybe a
  Nothing : forall (a :: *) . Maybe a
- The terms for the constructors are:
  Just = \(arg1 : a). /\ (out_Maybe :: *) . \(case_Nothing : out_Maybe) (case_Just : a -> out_Maybe) . case_Just arg1
  Nothing = /\ (out_Maybe :: *) . \(case_Nothing : out_Maybe) (caseJust : a -> out_Maybe) . caseNothing
- The type of the destructor is:
  match_Maybe : forall (a :: *) . Maybe a -> forall (out_Maybe :: *) . out_maybe -> (a -> out_maybe) -> out_maybe
- The term for the destructor is:
  match_Maybe = /\(a :: *) -> \(x : Maybe a) -> x

(Constructors and destructors are much more necessary when we define the datatype as abstract,
rather than inlining it, see Note [Abstract data types]. However, it is easier to present them here
as a slightly unnecessary generality.)

-- General case

Consider a datatype as defined in Plutus IR:
(datatype
  (tyvardecl T (type))
  (tyvardecl a_1 t_1)
  ..
  (tyvardecl a_n t_n)
  match_T
  (vardecl c_1 (fun t_c_1_1 .. (fun t_c_1_(c_1_k)) [T t1 .. tn]))
  ..
  (vardecl c_j (fun t_c_j_1 .. (fun t_c_j_(c_j_k)) [T t1 .. tn]))
)

That is, it has:
- Name T
- Kind *
- n type parameters of type t_1 to t_n
- Destructor match_t
_ j constructors with c_i_k arguments each of types t_c_i_1 to t_c_i_(c_i_k)

The type corresponding to the datatype is:
\(t_1 :: *) .. (t_n :: *) .
  forall out_T :: * .
    (t_c_1_1 -> .. -> t_c_1_(c_1_k) -> out_T) -> .. -> (t_c_j_1 -> .. -> t_c_j_(c_j_k) -> out_T) ->
      out_T

The type of the constructor c_i is:
forall (t_1 :: *) .. (t_n :: *) .
  t_c_i_1 -> .. -> t_c_i_(c_i_k) ->
    (T t_1 .. t_n)
This is actually declared for us in the datatype declaration, but without the type
variables being abstracted out. We use this to get the argument types of the constructor.

The term for the constructor c_i is:
/\(t_1 :: *) .. (t_n :: *) .
  \(a_1 : t_c_j_1) .. (a_c_i_(c_i_k) : t_c_i_(c_i_k)) .
    abs out_T :: * .
      \(case_c_1 : (t_c_1_1 -> .. -> t_c_1_(c_1_k) -> out_T)) .. (case_c_j : (t_c_j_1 -> .. -> t_c_j_(c_j_k) -> out_T)) .
        case_c_i a_1 .. a_c_i_(c_i_k)

The type of the destructor is:
forall (t_1 :: *) .. (t_n :: *) .
  (T t_1 .. t_n) ->
    forall out_T :: * .
      (t_c_1_1 -> .. -> t_c_1_(c_1_k) -> out_T) -> .. -> (t_c_j_1 -> .. -> t_c_j_(c_j_k) -> out_T) ->
        out_T

The term for the destructor is:
/\(t_1 :: *) .. (t_n :: *) .
  \(x :: (T t_1 .. t_n)) ->
    x

-- Compiling uses of datatypes

We turn constructor invocations into calls to the constructor functions.

Pattern matching is slightly more complex as we need to turn it into an invocation of the destructor:
- We take each alternative, turn it into a function of its bound variables.
- We apply the destructor to the scrutinee, and then instantiate that (which will be polymorphic
  in the result type) at the type of the overall match expression.
    - This does indicate one wrinkle: we need to know the overall type, we can't infer it.
- We apply the instantiated value to the functions for each alternative.
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
3. The definition of a type must be abstract in the binding types of the constructors and destructors
  (so they can be used alongside the abstract type), but it must *not* be abstract in the
  *definition* of the constructors or destructors, because they depend on knowing the real structure
  of the type.
    1. In fact we can do slightly better than this: in the constructors of a recursive datatype we can use the type
       as a name inside the 'wrap'.

Consequently, for a single type we end up with something like the following:

(forall ty :: * .
  -- ty abstract in these types
  \(c_1 : <constructor type i>) .. (c_j : <constructor type j>) .
    -- ty abstract in this type
    \match : <destructor type> .
      <user term>
)
<defn of ty>
-- ty concrete in these terms, except maybe inside a 'wrap'
<defn of c_1>
..
<defn of c_j>
-- ty concrete in this term
<defn of match>

(see Note [Scott encoding of datatypes] for how the actual definitions are constructed)
-}

{- Note [Recursive data types]
Recursive data types make the scheme described in [Scott encoding of datatypes] a bit more
complex. At the moment we only support self-recursive datatypes.

For a (self-)recursive datatype we have to change three things:
- The type of the datatype itself must have an enclosing fix over the type variable for
  the type itself.
- Constructors must include a wrap.
- Destructors must include an unwrap.
-}

-- See note [Scott encoding of datatypes]
-- | Make the "Scott-encoded" type for a 'Datatype', with type variables free.
-- @mkScottTy Maybe = forall out_Maybe. out_Maybe -> (a -> out_Maybe) -> out_Maybe@
mkScottTy :: forall m e a . Compiling m e a => Datatype TyName Name (Provenance a) -> m (PLCType a)
mkScottTy d@(Datatype _ _ _ _ constrs) = do
    p <- ask
    resultType <- resultTypeName d
    let caseTys = fmap (constructorCaseType (PLC.TyVar p resultType)) constrs
    pure $
        -- forall resultType
        PLC.TyForall p resultType (PLC.Type p) $
        -- c_1 -> .. -> c_n -> resultType
        PLC.mkIterTyFun p caseTys (PLC.TyVar p resultType)

-- | Make the "pattern functor" of a 'Datatype'. This is just the normal type, but with the
-- type variable for the type itself free. In the case of non-recursive datatypes this is just the
-- datatype.
-- @mkDatatypePatternFunctor List = \(a :: *) -> forall (r :: *) . r -> (a -> List a -> r) -> r@
mkDatatypePatternFunctor :: Compiling m e a => Datatype TyName Name (Provenance a) -> m (PLCType a)
mkDatatypePatternFunctor d@(Datatype _ _ tvs _ _) = local (DatatypeComponent PatternFunctor) $ PLC.mkIterTyLam <$> ask <*> pure tvs <*> mkScottTy d

-- | Make the real PLC type corresponding to a 'Datatype' with the given pattern functor.
-- @
--     mkDatatypeType List <pattern functor of List>
--         = fix list . <pattern functor of List>
--         = fix list . \(a :: *) -> forall (r :: *) . r -> (a -> List a -> r) -> r
-- @
mkDatatypeType :: Compiling m e a => Recursivity -> PLCType a -> Datatype TyName Name (Provenance a) -> m (PLCRecType a)
mkDatatypeType r pf (Datatype _ tn _ _ _) = local (DatatypeComponent DatatypeType) $ case r of
    NonRec -> pure $ PlainType pf
    -- See note [Recursive datatypes]
    -- We are reusing the same type name for the fixpoint variable. This is fine
    -- so long as we do renaming later, since we only reuse the name inside an inner binder
    Rec    -> ask >>= \p -> RecursiveType <$> (liftQuote $ mkRecursiveType p (tyVarDeclName tn) pf)

-- Constructors

-- | Make the type of a constructor of a 'Datatype'. This is not quite the same as the declared type because the declared type has the
-- type variables free.
-- @
--     mkConstructorType List Cons = forall (a :: *) . a -> List a -> List a
-- @
mkConstructorType :: Compiling m e a => Datatype TyName Name (Provenance a) -> VarDecl TyName Name (Provenance a) -> m (PLCType a)
-- this type appears *inside* the scope of the abstraction for the datatype so we can just reference the name and
-- we don't need to do anything to the declared type
-- see note [Abstract data types]
mkConstructorType (Datatype _ _ tvs _ _) constr = local (DatatypeComponent ConstructorType) $ PLC.mkIterTyForall <$> ask <*> pure tvs <*> pure (varDeclType constr)

-- See note [Scott encoding of datatypes]
-- | Make a constructor of a 'Datatype' with the given pattern functor. The constructor argument mostly serves to identify the constructor
-- that we are interested in in the list of constructors.
-- @
--     mkConstructor <definition of List> <pattern functor of List> List Cons
--         = /\(a :: *) . \(arg1 : a) (arg2 : <definition of List> a) .
--             wrap <pattern functor of List> /\(out_List :: *) .
--                 \(case_Nil : out_List) (case_Cons : a -> List a -> out_List) . case_Cons arg1 arg2
-- @
mkConstructor :: Compiling m e a => PLCRecType a -> Datatype TyName Name (Provenance a) -> Int -> m (PLCTerm a)
mkConstructor dty d@(Datatype _ _ tvs _ constrs) index = local (DatatypeComponent Constructor) $ do
    p <- ask
    resultType <- resultTypeName d

    -- case arguments and their types
    casesAndTypes <- do
          -- these types appear *outside* the scope of the abstraction for the datatype, *but* the name of the datatype will be in
          -- scope from the wrap, so we can still use it, and we don't need to do anything to the declared types
          -- see note [Abstract data types]
          let caseTypes = fmap (constructorCaseType (PLC.TyVar p resultType)) constrs
          caseArgNames <- for constrs (\c -> safeFreshName p $ "case_" ++ bsToStr (nameString $ varDeclName c))
          pure $ zipWith (VarDecl p) caseArgNames caseTypes

    -- This is inelegant, but it should never fail
    let constr = constrs !! index
    let thisCase = PLC.mkVar p $ casesAndTypes !! index

    -- constructor args and their types
    argsAndTypes <- do
          -- these types appear *outside* the scope of the abstraction for the datatype, *and* they are outside the wrap, so
          -- we need to use the concrete datatype here
          -- see note [Abstract data types]
        let argTypes = unveilDatatype (getType dty) d <$> constructorArgTypes constr
        -- we don't have any names for these things, we just had the type, so we call them "arg_i
        argNames <- for [0..(length argTypes -1)] (\i -> safeFreshName p $ "arg_" ++ show i)
        pure $ zipWith (VarDecl p) argNames argTypes


    pure $
        -- /\t_1 .. t_n
        PLC.mkIterTyAbs p tvs $
        -- \arg_1 .. arg_m
        PLC.mkIterLamAbs p argsAndTypes $
        -- See Note [Recursive datatypes]
        -- wrap
        wrap p dty $
        -- no need for a body value check here, we know it's a lambda (see Note [Value restriction])
        -- forall out
        PLC.TyAbs p resultType (PLC.Type p) $
        -- \case_1 .. case_j
        PLC.mkIterLamAbs p casesAndTypes $
        -- c_i arg_1 .. arg_m
        PLC.mkIterApp p thisCase (fmap (PLC.mkVar p) argsAndTypes)

-- Destructors

-- See note [Scott encoding of datatypes]
-- | Make the destructor for a 'Datatype'.
-- @
--     mkDestructor <definition of List> List
--        = /\(a :: *) -> \(x : (<definition of List> a)) -> unwrap x
--        = /\(a :: *) -> \(x : (fix List . \(a :: *) -> forall (r :: *) . r -> (a -> List a -> r) -> r) a) -> unwrap x
-- @
mkDestructor :: Compiling m e a => PLCRecType a -> Datatype TyName Name (Provenance a) -> m (PLCTerm a)
mkDestructor dty (Datatype _ _ tvs _ _) = local (DatatypeComponent Destructor) $ do
    p <- ask

    -- This term appears *outside* the scope of the abstraction for the datatype, so we need to put in the Scott-encoded type here
    -- see note [Abstract data types]
    -- dty t_1 .. t_n
    let appliedReal = PLC.mkIterTyApp p (getType dty) (fmap (PLC.mkTyVar p) tvs)

    xn <- safeFreshName p "x"
    pure $
        -- /\t_1 .. t_n
        PLC.mkIterTyAbs p tvs $
        -- \x
        PLC.LamAbs p xn appliedReal $
        -- See note [Recursive datatypes]
        -- unwrap
        unwrap p dty $
        PLC.Var p xn

-- See note [Scott encoding of datatypes]
-- | Make the type of a destructor for a 'Datatype'.
-- @
--     mkDestructorTy <pattern functor of List> List
--         = forall (a :: *) . (List a) -> ((<pattern functor of List>) a)
--         = forall (a :: *) . (List a) -> ((\(a :: *) -> forall (out_List :: *) . (out_List -> (a -> List a -> out_List) -> out_List)) a)
-- @
mkDestructorTy :: Compiling m e a => PLCType a -> Datatype TyName Name (Provenance a) -> m (PLCType a)
mkDestructorTy pf (Datatype _ tn tvs _ _) = local (DatatypeComponent DestructorType) $ do
    p <- ask

    -- we essentially "unveil" the abstract type, so this
    -- is a function from the (instantiated) abstract type
    -- to the (unwrapped, i.e. the pattern functor of the) "real" Scott-encoded type that we can use as
    -- a destructor

    -- these types appears *inside* the scope of the abstraction for the datatype, so we can use a references to the name
    -- and we don't need to do anything to the pattern functor
    -- see note [Abstract data types]
    -- t t_1 .. t_n
    let appliedAbstract = PLC.mkIterTyApp p (PLC.mkTyVar p tn) (fmap (PLC.mkTyVar p) tvs)
    -- pf t_1 .. t_n
    let appliedPattern = PLC.mkIterTyApp p pf (fmap (PLC.mkTyVar p) tvs)
    -- forall t_1 .. t_n
    pure $
        PLC.mkIterTyForall p tvs $
        PLC.TyFun p appliedAbstract appliedPattern

-- The main function

-- | Compile a 'Datatype' bound with the given body.
compileDatatype :: Compiling m e a => Recursivity -> PLCTerm a -> Datatype TyName Name (Provenance a) -> m (PLCTerm a)
compileDatatype r body d@(Datatype _ tn _ destr constrs) = do
    p <- ask

    -- we compute the pattern functor and pass it around to avoid recomputing it
    pf <- mkDatatypePatternFunctor d
    concreteTyDef <- PLC.Def tn <$> mkDatatypeType r pf d

    constrDefs <- for (zip constrs [0..]) $ \(c, i) -> do
        constrTy <- mkConstructorType d c
        PLC.Def (VarDecl p (varDeclName c) constrTy) <$> mkConstructor (PLC.defVal concreteTyDef) d i

    destrDef <- do
        destTy <- mkDestructorTy pf d
        PLC.Def (VarDecl p destr destTy) <$> mkDestructor (PLC.defVal concreteTyDef) d

    let
        tyVars = [PLC.defVar concreteTyDef]
        tys = [getType $ PLC.defVal concreteTyDef]
        vars = fmap PLC.defVar constrDefs ++ [PLC.defVar destrDef]
        vals = fmap PLC.defVal constrDefs ++ [PLC.defVal destrDef]
    -- See note [Abstract data types]
    pure $ PLC.mkIterApp p (PLC.mkIterInst p (PLC.mkIterTyAbs p tyVars (PLC.mkIterLamAbs p vars body)) tys) vals
