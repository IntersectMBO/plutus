{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications  #-}
{-# LANGUAGE TypeOperators     #-}
-- | Functions for compiling let-bound PIR datatypes into PLC.
module Language.PlutusIR.Compiler.Datatype
    ( compileDatatype
    , compileDatatypeDefs
    , compileRecDatatypes
    , funTyArgs
    , funResultType
    , mkDatatypeValueType
    , mkDestructorTy
    , replaceFunTyTarget
    , resultTypeName
    ) where

import           PlutusPrelude                          (showText)

import           Language.PlutusIR
import           Language.PlutusIR.Compiler.Names
import           Language.PlutusIR.Compiler.Provenance
import           Language.PlutusIR.Compiler.Types
import           Language.PlutusIR.Error
import qualified Language.PlutusIR.MkPir                as PIR
import           Language.PlutusIR.Transform.Substitute

import qualified Language.PlutusCore.MkPlc              as PLC
import           Language.PlutusCore.Quote
import qualified Language.PlutusCore.StdLib.Type        as Types

import           Control.Monad.Error.Lens

import qualified Data.Text                              as T
import           Data.Traversable

import qualified Data.List.NonEmpty                     as NE

{- NOTE [Normalization of data-constructors' types]

Currently the typechecking and compilation of dataconstructors/destructor
assume that the data-constructors' types (of the parsed PIR input) are in normalized form.
If these types are not normalized, the compilation will generate failing plc code.

There are no checks in place to enforce this normalization, and while
plutus-tx plugin is unlikely to generate PIR code with unnormalized types inside
these dataconstructor locations, it may still need to be taken into account in
the unlikely case that a user has manually modified the PIR input.

Future solutions:

1) disallow unnormalized types in dataconstructors, by adding a "isNormalized" check  prior to compilation.
2) allow unnormalized types in dataconstructors and normalize them prior to compilation.
-}

-- Utilities

-- | @replaceFunTyTarget X (A->..->Z) = (A->..->X)@
replaceFunTyTarget :: Type tyname uni a -> Type tyname uni a -> Type tyname uni a
replaceFunTyTarget newTarget t = case t of
    TyFun a t1 t2 -> TyFun a t1 $ replaceFunTyTarget newTarget t2
    _             -> newTarget

-- | Given the type of a constructor, get the type of the "case" type with the given result type.
-- @constructorCaseType R (A->Maybe A) = (A -> R)@
constructorCaseType :: Type tyname uni a -> VarDecl tyname name uni fun a -> Type tyname uni a
constructorCaseType resultType = replaceFunTyTarget resultType . varDeclType

-- | Get recursively all the domains and codomains of a type.
-- @funTySections (A->B->C) = [A, B, C]@
-- @funTySections (X) = [X]@
funTySections :: Type tyname uni a -> NE.NonEmpty (Type tyname uni a)
funTySections = \case
    TyFun _ t1 t2 -> t1 NE.<| funTySections t2
    t             -> pure t

-- | Get the argument types of a function type.
-- @funTyArgs (A->B->C) = [A, B]@
funTyArgs :: Type tyname uni a ->  [Type tyname uni a]
funTyArgs = NE.init . funTySections

-- | Get the result type of a function.
-- If not a function, then is the same as `id`
-- @funResultType (A->B->C) = C@
-- @funResultType (X) = X@
funResultType :: Type tyname uni a ->  Type tyname uni a
funResultType = NE.last . funTySections

-- | Given the type of a constructor, get its argument types.
-- @constructorArgTypes (A->Maybe A) = [A]
constructorArgTypes :: VarDecl tyname name uni fun a -> [Type tyname uni a]
constructorArgTypes = funTyArgs . varDeclType

-- | "Unveil" a datatype definition in a type, by replacing uses of the name as a type variable with the concrete definition.
unveilDatatype :: Eq tyname => Type tyname uni a -> Datatype tyname name uni fun a -> Type tyname uni a -> Type tyname uni a
unveilDatatype dty (Datatype _ tn _ _ _) = typeSubstTyNames (\n -> if n == tyVarDeclName tn then Just dty else Nothing)

resultTypeName :: MonadQuote m => Datatype TyName Name uni fun a -> m TyName
resultTypeName (Datatype _ tn _ _ _) = liftQuote $ freshTyName $ "out_" <> (nameString $ unTyName $ tyVarDeclName tn)

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
mkScottTy :: MonadQuote m => ann -> Datatype TyName Name uni fun ann -> m (Type TyName uni ann)
mkScottTy ann d@(Datatype _ _ _ _ constrs) = do
    resultType <- resultTypeName d
     -- FIXME: normalize datacons' types also here
    let caseTys = fmap (constructorCaseType (TyVar ann resultType)) constrs
    pure $
        -- forall resultType
        TyForall ann resultType (Type ann) $
        -- c_1 -> .. -> c_n -> resultType
        PIR.mkIterTyFun ann caseTys (TyVar ann resultType)

-- | Make the "pattern functor" of a 'Datatype'. This is just the normal type, but with the
-- type variable for the type itself free and its type variables free.
-- @mkDatatypePatternFunctor List = forall (r :: *) . r -> (a -> List a -> r) -> r@
-- FIXME: inline this
mkDatatypePatternFunctor :: MonadQuote m => ann -> Datatype TyName Name uni fun ann -> m (Type TyName uni ann)
mkDatatypePatternFunctor ann d = mkScottTy ann d

-- | Make the real PLC type corresponding to a 'Datatype' with the given pattern functor.
-- @
--     mkDatatypeType List <pattern functor of List>
--         = fix list . <pattern functor of List>
--         = fix list . \(a :: *) -> forall (r :: *) . r -> (a -> List a -> r) -> r
-- @
mkDatatypeType :: forall m uni fun a. MonadQuote m => Recursivity -> PIRType uni a -> Datatype TyName Name uni fun (Provenance a) -> m (PLCRecType uni fun a)
mkDatatypeType r pf (Datatype ann tn tvs _ _) = case r of
    NonRec -> PlainType <$> (PLC.mkIterTyLam <$> pure tvs <*> pure pf)
    -- See note [Recursive datatypes]
    -- We are reusing the same type name for the fixpoint variable. This is fine
    -- so long as we do renaming later, since we only reuse the name inside an inner binder
    Rec    -> do
        RecursiveType <$> (liftQuote $ Types.makeRecursiveType @uni @(Provenance a) ann (tyVarDeclName tn) tvs pf)

-- | The type of a datatype-value is of the form `[TyCon tyarg1 tyarg2 ... tyargn]`
mkDatatypeValueType :: a -> Datatype TyName Name uni fun a -> Type TyName uni a
mkDatatypeValueType ann (Datatype _ tn tvs _ _)  = PIR.mkIterTyApp ann (PIR.mkTyVar ann tn) $ PIR.mkTyVar ann <$> tvs

-- Constructors

-- | Make the type of a constructor of a 'Datatype'. This is not quite the same as the declared type because the declared type has the
-- type variables free.
-- @
--     mkConstructorType List Cons = forall (a :: *) . a -> List a -> List a
-- @
mkConstructorType :: Datatype TyName Name uni fun (Provenance a) -> VarDecl TyName Name uni fun (Provenance a) -> PIRType uni a
-- this type appears *inside* the scope of the abstraction for the datatype so we can just reference the name and
-- we don't need to do anything to the declared type
-- see note [Abstract data types]
-- FIXME: normalize constructors also here
mkConstructorType (Datatype _ _ tvs _ _) constr = PIR.mkIterTyForall  tvs $ varDeclType constr

-- See note [Scott encoding of datatypes]
-- | Make a constructor of a 'Datatype' with the given pattern functor. The constructor argument mostly serves to identify the constructor
-- that we are interested in in the list of constructors.
-- @
--     mkConstructor <definition of List> <pattern functor of List> List Cons
--         = /\(a :: *) . \(arg1 : a) (arg2 : <definition of List> a) .
--             wrap <pattern functor of List> /\(out_List :: *) .
--                 \(case_Nil : out_List) (case_Cons : a -> List a -> out_List) . case_Cons arg1 arg2
-- @
mkConstructor :: MonadQuote m => PLCRecType uni fun a -> Datatype TyName Name uni fun (Provenance a) -> Int -> m (PIRTerm uni fun a)
mkConstructor dty d@(Datatype ann _ tvs _ constrs) index = do
    resultType <- resultTypeName d

    -- case arguments and their types
    casesAndTypes <- do
          -- these types appear *outside* the scope of the abstraction for the datatype, so we need to use the concrete datatype here
          -- see note [Abstract data types]
          -- FIXME: normalize datacons' types also here
          let caseTypes = unveilDatatype (getType dty) d <$> fmap (constructorCaseType (TyVar ann resultType)) constrs
          caseArgNames <- for constrs (\c -> safeFreshName $ "case_" <> T.pack (varDeclNameString c))
          pure $ zipWith (VarDecl ann) caseArgNames caseTypes

    -- This is inelegant, but it should never fail
    let constr = constrs !! index
    let thisCase = PIR.mkVar ann $ casesAndTypes !! index

    -- constructor args and their types
    argsAndTypes <- do
        -- these types appear *outside* the scope of the abstraction for the datatype, so we need to use the concrete datatype here
        -- see note [Abstract data types]
        -- FIXME: normalize datacons' types also here
        let argTypes = unveilDatatype (getType dty) d <$> constructorArgTypes constr
        -- we don't have any names for these things, we just had the type, so we call them "arg_i
        argNames <- for [0..(length argTypes -1)] (\i -> safeFreshName $ "arg_" <> showText i)
        pure $ zipWith (VarDecl ann) argNames argTypes


    pure $
        -- /\t_1 .. t_n
        PIR.mkIterTyAbs tvs $
        -- \arg_1 .. arg_m
        PIR.mkIterLamAbs argsAndTypes $
        -- See Note [Recursive datatypes]
        -- wrap
        wrap ann dty (fmap (PIR.mkTyVar ann) tvs)$
        -- forall out
        TyAbs ann resultType (Type ann) $
        -- \case_1 .. case_j
        PIR.mkIterLamAbs casesAndTypes $
        -- c_i arg_1 .. arg_m
        PIR.mkIterApp ann thisCase (fmap (PIR.mkVar ann) argsAndTypes)

-- Destructors

-- See note [Scott encoding of datatypes]
-- | Make the destructor for a 'Datatype'.
-- @
--     mkDestructor <definition of List> List
--        = /\(a :: *) -> \(x : (<definition of List> a)) -> unwrap x
--        = /\(a :: *) -> \(x : (fix List . \(a :: *) -> forall (r :: *) . r -> (a -> List a -> r) -> r) a) -> unwrap x
-- @
mkDestructor :: MonadQuote m => PLCRecType uni fun a -> Datatype TyName Name uni fun (Provenance a) -> m (PIRTerm uni fun a)
mkDestructor dty (Datatype ann _ tvs _ _) = do
    -- This term appears *outside* the scope of the abstraction for the datatype, so we need to put in the Scott-encoded type here
    -- see note [Abstract data types]
    -- dty t_1 .. t_n
    let appliedReal = PIR.mkIterTyApp ann (getType dty) (fmap (PIR.mkTyVar ann) tvs)

    xn <- safeFreshName "x"
    pure $
        -- /\t_1 .. t_n
        PIR.mkIterTyAbs tvs $
        -- \x
        LamAbs ann xn appliedReal $
        -- See note [Recursive datatypes]
        -- unwrap
        unwrap ann dty $
        Var ann xn

-- See note [Scott encoding of datatypes]
-- | Make the type of a destructor for a 'Datatype'.
-- @
--     mkDestructorTy <pattern functor of List> List
--         = forall (a :: *) . (List a) -> (<pattern functor of List>)
--         = forall (a :: *) . (List a) -> (forall (out_List :: *) . (out_List -> (a -> List a -> out_List) -> out_List))
-- @
mkDestructorTy :: ann -> Type TyName uni ann -> Datatype TyName Name uni fun ann -> Type TyName uni ann
mkDestructorTy ann pf dt@(Datatype _ _ tvs _ _) =
    -- we essentially "unveil" the abstract type, so this
    -- is a function from the (instantiated) abstract type
    -- to the (unwrapped, i.e. the pattern functor of the) "real" Scott-encoded type that we can use as
    -- a destructor

    -- these types appears *inside* the scope of the abstraction for the datatype, so we can use a references to the name
    -- and we don't need to do anything to the pattern functor
    -- see note [Abstract data types]
    -- t t_1 .. t_n
    let appliedAbstract = mkDatatypeValueType ann dt
    -- forall t_1 .. t_n
    in
        PIR.mkIterTyForall tvs $
        TyFun ann appliedAbstract pf

-- The main function

-- | Compile a 'Datatype' bound with the given body.
compileDatatype :: Compiling m e uni fun a => Recursivity -> PIRTerm uni fun a -> Datatype TyName Name uni fun (Provenance a) -> m (PIRTerm uni fun a)
compileDatatype r body d = do
    p <- getEnclosing

    (concreteTyDef, constrDefs, destrDef) <- compileDatatypeDefs r d

    let
        tyVars = [PIR.defVar concreteTyDef]
        tys = [getType $ PIR.defVal concreteTyDef]
        vars = fmap PIR.defVar constrDefs ++ [PIR.defVar destrDef]
        vals = fmap PIR.defVal constrDefs ++ [PIR.defVal destrDef]
    -- See note [Abstract data types]
    pure $ PIR.mkIterApp p (PIR.mkIterInst p (PIR.mkIterTyAbs tyVars (PIR.mkIterLamAbs vars body)) tys) vals

-- | Compile a 'Datatype' to a triple of type-constructor, data-constructors, destructor definitions.
compileDatatypeDefs  :: MonadQuote m => Recursivity
                     -> Datatype TyName Name uni fun (Provenance a)
                     -> m (PLC.Def (TyVarDecl TyName (Provenance a)) (PLCRecType uni fun a),
                          [PLC.Def (VarDecl TyName Name uni fun (Provenance a)) (PIRTerm uni fun a)],
                          PLC.Def (VarDecl TyName Name uni fun (Provenance a)) (PIRTerm uni fun a))
compileDatatypeDefs r d@(Datatype ann tn _ destr constrs) = do
    -- we compute the pattern functor and pass it around to avoid recomputing it
    pf <- mkDatatypePatternFunctor ann d
    concreteTyDef <- PIR.Def tn <$> mkDatatypeType r pf d

    constrDefs <- for (zip constrs [0..]) $ \(c, i) -> do
        let constrTy = mkConstructorType d c
        PIR.Def (VarDecl ann (varDeclName c) constrTy) <$> mkConstructor (PIR.defVal concreteTyDef) d i

    destrDef <- do
        let destTy = mkDestructorTy ann pf d
        PIR.Def (VarDecl ann destr destTy) <$> mkDestructor (PIR.defVal concreteTyDef) d

    pure (concreteTyDef, constrDefs, destrDef)

compileRecDatatypes :: Compiling m e uni fun a => PIRTerm uni fun a -> NE.NonEmpty (Datatype TyName Name uni fun (Provenance a)) -> m (PIRTerm uni fun a)
compileRecDatatypes body ds = case ds of
    d NE.:| [] -> compileDatatype Rec body d
    _          -> getEnclosing >>= \p -> throwing _Error $ UnsupportedError p "Mutually recursive datatypes"
