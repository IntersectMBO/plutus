-- editorconfig-checker-disable-file
{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TupleSections     #-}
{-# LANGUAGE TypeApplications  #-}
-- | Functions for compiling let-bound PIR datatypes into PLC.
module PlutusIR.Compiler.Datatype
    ( compileDatatype
    , compileDatatypeDefs
    , compileRecDatatypes
    , mkDatatypeValueType
    , mkDestructorTy
    , mkScottTy
    , resultTypeName
    ) where

import PlutusPrelude (showText)

import PlutusIR
import PlutusIR.Compiler.Names
import PlutusIR.Compiler.Provenance
import PlutusIR.Compiler.Types
import PlutusIR.Error
import PlutusIR.MkPir qualified as PIR
import PlutusIR.Transform.Substitute

import PlutusCore.Core qualified as PLC
import PlutusCore.MkPlc qualified as PLC
import PlutusCore.Quote
import PlutusCore.StdLib.Type qualified as Types

import Control.Monad.Error.Lens

import Data.Text qualified as T
import Data.Traversable

import Control.Lens hiding (index)
import Data.List.NonEmpty qualified as NE
import Data.Word (Word64)

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

-- | Given the type of a constructor, get the type of the "case" type with the given result type.
-- @constructorCaseType R (A->Maybe A) = (A -> R)@
constructorCaseType :: a -> Type tyname uni a -> VarDecl tyname name uni a -> Type tyname uni a
constructorCaseType ann resultType vd = PLC.mkIterTyFun ann (PLC.funTyArgs (_varDeclType vd)) resultType

-- | Given the type of a constructor, get its argument types.
-- @constructorArgTypes (A->Maybe A) = [A]
constructorArgTypes :: VarDecl tyname name uni a -> [Type tyname uni a]
constructorArgTypes = PLC.funTyArgs . _varDeclType

-- | "Unveil" a datatype definition in a type, by replacing uses of the name as a type variable with the concrete definition.
unveilDatatype :: Eq tyname => Type tyname uni a -> Datatype tyname name uni a -> Type tyname uni a -> Type tyname uni a
unveilDatatype dty (Datatype _ tn _ _ _) = typeSubstTyNames (\n -> if n == _tyVarDeclName tn then Just dty else Nothing)

resultTypeName :: MonadQuote m => Datatype TyName Name uni a -> m TyName
resultTypeName (Datatype _ tn _ _ _) = liftQuote $ freshTyName $ "out_" <> (_nameText $ unTyName $ _tyVarDeclName tn)

-- Datatypes

{- Note [Encoding of datatypes]
PIR datatypes must be encoded into PLC. We support two schemes for doing this:
- Scott encoding (see Note [Scott encoding of datatypes] for details)
- Sums-of-products (SOPs) (See Note [SOP encoding of datatypes] for details)

Scott encoding is what we used originally, before we had SOPs. We still support both
modes, because users targeting older versions of the language can't use the SOP
encoding. Otherwise, the SOP encoding is superior (faster, simpler).
-}

{- Note [Scott encoding of datatypes]
We can translate our datatypes using the Scott encoding. The fundamental idea is that there is one thing
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

For example, consider 'data Maybe a = Nothing | Just a'. Then:
- The type corresponding to the datatype is:
  Maybe = \(t :: *) . forall (out_Maybe :: *) . out_Maybe -> (t -> out_Maybe) -> out_Maybe
- The type of the constructors are:
  Just : forall (t :: *) . t -> Maybe t
  Nothing : forall (t :: *) . Maybe t
- The terms for the constructors are:
  Just = /\ (t :: *) \(x : t) /\ (out_Maybe :: *) \(case_Nothing : out_Maybe) (case_Just : t -> out_Maybe) . case_Just x
  Nothing = /\ (t :: *) /\ (out_Maybe :: *) \(case_Nothing : out_Maybe) (case_Just : t -> out_Maybe) . case_Nothing
- The type of the destructor is:
  match_Maybe : forall (t :: *) . Maybe t -> forall (out_Maybe :: *) . out_Maybe -> (t -> out_Maybe) -> out_Maybe
- The term for the destructor is:
  match_Maybe = /\(t :: *) \(x : Maybe t) . x

-- General case

Consider a datatype as defined in Plutus IR:
(datatype
  (tyvardecl T (type))
  (tyvardecl t_0 k_0)
  ..
  (tyvardecl t_n k_n)
  match_T
  (vardecl c_0 (fun t_c_0_0 .. (fun t_c_0_(c_0_k)) [T t0 .. tn]))
  ..
  (vardecl c_j (fun t_c_j_0 .. (fun t_c_j_(c_j_k)) [T t0 .. tn]))
)

That is, it has:
- Name T
- Type parameters t_0 to t_n of kind k_0 to k_n
- Kind * -> ... n times ... -> *
- Destructor match_t
_ Constructors c_0 to c_j with the arguments of c_i having types t_c_i_1 to t_c_i_(c_i_k)

The type corresponding to the datatype is:
\(t_0 :: k_0) .. (t_n :: k_n) .
  forall out_T :: * .
    (t_c_0_0 -> .. -> t_c_0_(c_0_k) -> out_T) -> .. -> (t_c_j_0 -> .. -> t_c_j_(c_j_k) -> out_T) ->
      out_T

The type of the constructor c_i (0 <= i <= j) is:
forall (t_0 :: k_0) .. (t_n :: k_n) .
  t_c_i_0 -> .. -> t_c_i_(c_i_k) ->
    (T t_0 .. t_n)
This is actually declared for us in the datatype declaration, but without the type
variables being abstracted out. We use this to get the argument types of the constructor.

The term for the constructor c_i (0 <= i <= j) is (slightly fudged types, see Note [Abstract data types]):
/\(t_0 :: k_0) .. (t_n :: k_n) .
  \(x_0 : t_c_i_0) .. (x_(c_i_k) : t_c_i_(c_i_k)) .
    /\(out_T :: *) .
      \(case_c_0 : (t_c_0_0 -> .. -> t_c_0_(c_0_k) -> out_T)) .. (case_c_j : (t_c_j_0 -> .. -> t_c_j_(c_j_k) -> out_T)) .
        case_c_i x_0 .. x_(c_i_k)

The type of the destructor is:
forall (t_0 :: k_0) .. (t_n :: k_n) .
  (T t_0 .. t_n) ->
    forall out_T :: * .
      (t_c_0_0 -> .. -> t_c_0_(c_0_k) -> out_T) -> .. -> (t_c_j_0 -> .. -> t_c_j_(c_j_k) -> out_T) ->
        out_T

The term for the destructor is (slightly fudged types, see Note [Abstract data types]):
/\(t_0 :: k_0) .. (t_n :: k_n) .
  \(x :: (T t_0 .. t_n)) .
    x
-}

{- Note [SOP encoding of datatypes]
We can translate our datatypes using SOPs. This is much more direct than Scott encoding, since
we have terms in the language for construction and destruction themselves.

We still need to think about the types. In general, we need:
- The encoded type corresponding to the datatype itself
- The encoded type of each constructor
- The encoded term for each constructor
- The encoded type of the destructor
- The encoded term for the destructor

-- Basic example

For example, consider 'data Maybe a = Nothing | Just a'. Then:
- The type corresponding to the datatype is:
  Maybe = \(t :: *) . sop [] [a]
- The type of the constructors are:
  Just : forall (t :: *) . a -> Maybe a
  Nothing : forall (t :: *) . Maybe a
- The terms for the constructors are:
  Just = /\(t :: *) \(x :: t) . constr (Maybe t) 1 x
  Nothing = /\(t :: *) . constr 0 (Maybe t)
- The type of the destructor is:
  match_Maybe :: forall (t :: *) . Maybe t -> forall (out_Maybe :: *) . out_Maybe -> (t -> out_Maybe) -> out_Maybe
- The term for the destructor is:
  match_Maybe = /\(t :: *) \(x : Maybe t) /\(out_Maybe :: *) \(case_Nothing :: out_Maybe) (case_Just :: t -> out_Maybe) .
    case out_Maybe x case_Nothing case_Just

-- General case

Consider a datatype as defined in Plutus IR:
(datatype
  (tyvardecl T (type))
  (tyvardecl t_0 k_0)
  ..
  (tyvardecl t_n k_n)
  match_T
  (vardecl c_0 (fun t_c_0_0 .. (fun t_c_0_(c_0_k)) [T t0 .. tn]))
  ..
  (vardecl c_j (fun t_c_j_0 .. (fun t_c_j_(c_j_k)) [T t0 .. tn]))
)

That is, it has:
- Name T
- Type parameters t_0 to t_n of kind k_0 to k_n
- Kind * -> ... n times .. -> *
- Destructor match_T
_ Constructors c_0 to c_j with the arguments of c_i having types t_c_i_0 to t_c_i_(c_i_k)

The type corresponding to the datatype is:
\(t_0 :: k_0) .. (t_n :: k_n) . sop [t_c_0_0 .. t_c_0_(c_0_k)] .. [t_c_j_0 .. t_c_j_(c_j_k)]

The type of the constructor c_i (0 <= i <= j) is:
forall (t_0 :: t_0) .. (t_n :: k_n) .
  t_c_i_0 -> .. -> t_c_i_(c_i_k) ->
    (T t_0 .. t_n)
This is actually declared for us in the datatype declaration, but without the type
variables being abstracted out. We use this to get the argument types of the constructor.

The term for the constructor c_i (0 <= i <= j) is (slightly fudged types, see Note [Abstract data types]):
/\(t_0 :: t_0) .. (t_n :: k_n) .
  \(x_0 : t_c_i_0) .. (x_(c_i_k) : t_c_i_(c_i_k)) .
    constr (T t_0 .. t_n) i (T t_0 .. t_n) x_0 .. x_(c_i_k)

The type of the destructor is:
forall (t_0 :: k_0) .. (t_n :: k_n) .
  (T t_0 .. t_n) ->
    forall out_T :: * .
      (t_c_0_1 -> .. -> t_c_0_(c_0_k) -> out_T) -> .. -> (t_c_j_0 -> .. -> t_c_j_(c_j_k) -> out_T) ->
        out_T

The term for the destructor is (slightly fudged types, see Note [Abstract data types]):
/\(t_0 :: k_0) .. (t_n :: k_n) .
  \(x :: (T t_0 .. t_n)) .
    /\(out_T :: *) .
      \(case_c_0 : (t_c_0_0 -> .. -> t_c_0_(c_0_k) -> out_T)) .. (case_c_j : (t_c_j_0 -> .. -> t_c_j_(c_j_k) -> out_T)) .
        case out_T x case_c_0 .. case_c_j
-}

{- Note [Compiling uses of datatypes]

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

(/\ ty :: * .
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

(see Note [Encoding of datatypes] for how the actual definitions are constructed)
-}

{- Note [Recursive data types]
Recursive data types make the scheme described in [Encoding of datatypes] a bit more
complex. At the moment we only support self-recursive datatypes.

For a (self-)recursive datatype we have to change three things:
- The type of the datatype itself must have an enclosing fix over the type variable for
  the type itself.
- Constructors must include a wrap.
- Destructors must include an unwrap.
-}

-- See note [Encoding of datatypes]
-- | Make the "Scott-encoded" type for a 'Datatype', with type variables free.
-- This is exactly the type of an eliminator function for the datatype.
--
-- @mkScottTy Maybe = forall out_Maybe. out_Maybe -> (a -> out_Maybe) -> out_Maybe@
mkScottTy :: MonadQuote m => ann -> Datatype TyName Name uni ann -> m (Type TyName uni ann)
mkScottTy ann d@(Datatype _ _ _ _ constrs) = do
   res <- resultTypeName d
   -- FIXME: normalize datacons' types also here
   let caseTys = fmap (constructorCaseType ann (TyVar ann res)) constrs
   pure $
      -- forall res.
      TyForall ann res (Type ann) $
      -- c_1 -> .. -> c_n -> res
      PIR.mkIterTyFun ann caseTys (TyVar ann res)

mkDatatypeSOPTy :: ann -> Datatype TyName Name uni ann -> Type TyName uni ann
mkDatatypeSOPTy ann (Datatype _ _ _ _ constrs) = TySOP ann (fmap constructorArgTypes constrs)

{- | Make the body of the "pattern functor" of a 'Datatype'. This is just the non-abstract datatype type,
but with the type variable for the type itself free and its type variables free.

Scott: @mkPatternFunctorBody List = forall (out_List :: *) . out_List -> (a -> List a -> out_List) -> out_List@
SOPs: @mkPatternFunctorBody List = sop [] [a, List a]@
-}
mkPatternFunctorBody :: MonadQuote m => DatatypeCompilationOpts -> ann -> Datatype TyName Name uni ann -> m (Type TyName uni ann)
mkPatternFunctorBody opts ann d = case _dcoStyle opts of
  ScottEncoding  -> mkScottTy ann d
  SumsOfProducts -> pure $ mkDatatypeSOPTy ann d

{- | Make the real PLC type corresponding to a 'Datatype' with the given pattern functor body.

Scott:
@
    mkDatatypeType List <pattern functor body of List>
        = fix (\(List :: * -> *) (a :: *) -> <pattern functor body of List>)
        = fix (\(List :: * -> *) (a :: *) -> forall (r :: *) . r -> (a -> List a -> r) -> r)
@

SOPs:
@
    mkDatatypeType List <pattern functor of List>
        = fix (\(List :: * -> *) (a :: *) -> <pattern functor body of List>)
        = fix (\(List :: * -> *) (a :: *) -> \(a :: *) -> sop [] [a, List a])
@
-}
mkDatatypeType :: forall m uni fun a. MonadQuote m => DatatypeCompilationOpts -> Recursivity -> Datatype TyName Name uni (Provenance a) -> m (PLCRecType uni fun a)
mkDatatypeType opts r d@(Datatype ann tn tvs _ _) = do
  pf <- mkPatternFunctorBody opts ann d
  case r of
    NonRec -> pure $ PlainType $ PLC.mkIterTyLam tvs pf
    -- See note [Recursive datatypes]
    -- We are reusing the same type name for the fixpoint variable. This is fine
    -- so long as we do renaming later, since we only reuse the name inside an inner binder
    Rec    -> do
        RecursiveType <$> (liftQuote $ Types.makeRecursiveType @uni @(Provenance a) ann (_tyVarDeclName tn) tvs pf)

-- | The type of a datatype-value is of the form `[TyCon tyarg1 tyarg2 ... tyargn]`
mkDatatypeValueType :: a -> Datatype TyName Name uni a -> Type TyName uni a
mkDatatypeValueType ann (Datatype _ tn tvs _ _)  = PIR.mkIterTyApp (PIR.mkTyVar ann tn) $ (ann,) . PIR.mkTyVar ann <$> tvs

-- Constructors

{- | Make the type of a constructor of a 'Datatype'. This is not quite the same as the declared type because the declared type has the
type variables free.
@
    mkConstructorType List Cons = forall (a :: *) . a -> List a -> List a
@
-}
mkConstructorType :: Datatype TyName Name uni (Provenance a) -> VarDecl TyName Name uni (Provenance a) -> PIRType uni a
-- this type appears *inside* the scope of the abstraction for the datatype so we can just reference the name and
-- we don't need to do anything to the declared type
-- see note [Abstract data types]
-- FIXME: normalize constructors also here
mkConstructorType (Datatype _ _ tvs _ _) constr = PIR.mkIterTyForall tvs $ _varDeclType constr

-- See note [Encoding of datatypes]
{- | Make a constructor of a 'Datatype' with the given pattern functor. The constructor argument mostly serves to identify the constructor
that we are interested in in the list of constructors.

Scott:
@
    mkConstructor <definition of List> List Cons
        = /\(a :: *) . \(x : a) (xs : <definition of List> a) .
            wrap <pattern functor of List> /\(out_List :: *) .
                \(case_Nil : out_List) (case_Cons : a -> List a -> out_List) . case_Cons arg1 arg2
@

SOPs:
@
    mkConstructor <definition of List> List Cons
        = /\(a :: *) . \(x : a) (xs : <definition of List> a) .
            wrap <pattern functor of List>
                constr ((\(List :: * -> *) . <pattern functor of List>) <definition of List>) arg1 arg2
@
-}
mkConstructor :: MonadQuote m => DatatypeCompilationOpts -> PLCRecType uni fun a -> Datatype TyName Name uni (Provenance a) -> Word64 -> m (PIRTerm uni fun a)
mkConstructor opts dty d@(Datatype ann _ tvs _ constrs) index = do
    -- This is inelegant, but it should never fail
    let thisConstr = constrs !! fromIntegral index

    -- constructor args and their types
    argsAndTypes <- do
        -- these types appear *outside* the scope of the abstraction for the datatype, so we need to use the concrete datatype here
        -- see note [Abstract data types]
        -- FIXME: normalize datacons' types also here
        let argTypes = unveilDatatype (getType dty) d <$> constructorArgTypes thisConstr
        -- we don't have any names for these things, we just had the type, so we call them "arg_i
        argNames <- for [0..(length argTypes -1)] (\i -> safeFreshName $ "arg_" <> showText i)
        pure $ zipWith (VarDecl ann) argNames argTypes

    constrBody <- case _dcoStyle opts of
          SumsOfProducts -> do
            -- We have to be a bit careful annotating the type of the constr. It is inside the 'wrap' so it
            -- needs to be one level "unrolled".

            -- The pattern functor with a hole in it
            pf <- mkPatternFunctorBody opts ann d
            -- ... and with the hole filled in with the datatype type
            let unrolled = unveilDatatype (getType dty) d pf

            pure $ Constr ann unrolled index (fmap (PIR.mkVar ann) argsAndTypes)
          ScottEncoding -> do
            resultType <- resultTypeName d

            -- case arguments and their types
            casesAndTypes <- do
                  -- these types appear *outside* the scope of the abstraction for the datatype, so we need to use the concrete datatype here
                  -- see note [Abstract data types]
                  -- FIXME: normalize datacons' types also here
                  let caseTypes = unveilDatatype (getType dty) d <$> fmap (constructorCaseType ann (TyVar ann resultType)) constrs
                  caseArgNames <- for constrs (\c -> safeFreshName $ "case_" <> T.pack (varDeclNameString c))
                  pure $ zipWith (VarDecl ann) caseArgNames caseTypes

            -- This is inelegant, but it should never fail
            let thisCase = PIR.mkVar ann $ casesAndTypes !! fromIntegral index

            pure $
                -- forall out
                TyAbs ann resultType (Type ann) $
                -- \case_1 .. case_j
                PIR.mkIterLamAbs casesAndTypes $
                -- c_i arg_1 .. arg_m
                PIR.mkIterApp thisCase (fmap ((ann,) . PIR.mkVar ann) argsAndTypes)

    let constr =
            -- /\t_1 .. t_n
            PIR.mkIterTyAbs tvs $
            -- \arg_1 .. arg_m
            PIR.mkIterLamAbs argsAndTypes $
            -- See Note [Recursive datatypes]
            -- wrap
            wrap ann dty (fmap (PIR.mkTyVar ann) tvs) constrBody
    pure $ fmap (\a -> DatatypeComponent Constructor a) constr

-- Destructors

-- See note [Encoding of datatypes]
{- | Make the destructor for a 'Datatype'.

Scott:
@
    mkDestructor <definition of List> List
       = /\(a :: *) -> \(x : (<definition of List> a)) -> unwrap x
@

SOPs:
@
    mkDestructor <definition of List> List
       = /\(a :: *) -> \(x : (<definition of List> a)) ->
         /\(r :: *) ->
         \(case_Nil :: r) (case_Cons :: a -> (<definition of List> a) -> r) -> case r (unwrap x) case_Nil case_Cons
@
-}
mkDestructor :: MonadQuote m => DatatypeCompilationOpts -> PLCRecType uni fun a -> Datatype TyName Name uni (Provenance a) -> m (PIRTerm uni fun a)
mkDestructor opts dty d@(Datatype ann _ tvs _ constrs) = do
    -- This term appears *outside* the scope of the abstraction for the datatype, so we need to put in the Scott-encoded type here
    -- see note [Abstract data types]
    -- dty t_1 .. t_n
    let appliedReal = PIR.mkIterTyApp (getType dty) (fmap ((ann,) . PIR.mkTyVar ann) tvs)

    xn <- safeFreshName "x"

    destrBody <- case _dcoStyle opts of
        SumsOfProducts -> do
            resultType <- resultTypeName d
            -- Variables for case arguments, and the bodies to be used as the actual cases
            caseVars <- for constrs $ \c -> do
                -- these types appear *outside* the scope of the abstraction for the datatype, so we need to use the concrete datatype here
                -- see note [Abstract data types]
                -- FIXME: normalize datacons' types also here
                let caseType = constructorCaseType ann (TyVar ann resultType) c
                    unveiledCaseType = unveilDatatype (getType dty) d caseType
                caseArgName <- safeFreshName $ "case_" <> T.pack (varDeclNameString c)
                pure $ VarDecl ann caseArgName unveiledCaseType
            pure $
                -- forall out
                TyAbs ann resultType (Type ann) $
                -- \case_1 .. case_j
                PIR.mkIterLamAbs caseVars $
                -- See note [Recursive datatypes]
                -- case (unwrap x) case_1 .. case_j
                Case ann (TyVar ann resultType) (unwrap ann dty $ Var ann xn) (fmap (PIR.mkVar ann) caseVars)
        ScottEncoding ->
            pure $
                -- See note [Recursive datatypes]
                -- unwrap
                unwrap ann dty $
                Var ann xn

    let destr =
            -- /\t_1 .. t_n
            PIR.mkIterTyAbs tvs $
            -- \x
            LamAbs ann xn appliedReal destrBody
    pure $ DatatypeComponent Destructor <$> destr

-- See note [Encoding of datatypes]
-- | Make the type of a destructor for a 'Datatype'.
-- @
--     mkDestructorTy List
--         = forall (a :: *) . List a -> forall (out_List :: *) . (out_List -> (a -> List a -> out_List) -> out_List)
-- @
mkDestructorTy :: MonadQuote m => Datatype TyName Name uni a -> m (Type TyName uni a)
mkDestructorTy dt@(Datatype ann _ tvs _ _) = do
    -- The scott type is exactly the eliminator type, which is what we want here regardless of the compilation style
    st <- mkScottTy ann dt
    -- these types appear *inside* the scope of the abstraction for the datatype, so we can just directly use
    -- references to the name
    -- see note [Abstract data types]
    -- t t_1 .. t_n
    let valueType = mkDatatypeValueType ann dt
    -- forall t_1 .. t_n
    pure $ PIR.mkIterTyForall tvs $ TyFun ann valueType st

-- The main function

-- | Compile a 'Datatype' bound with the given body.
compileDatatype
    :: Compiling m e uni fun a
    => Recursivity
    -> PIRTerm uni fun a
    -> Datatype TyName Name uni (Provenance a)
    -> m (PIRTerm uni fun a)
compileDatatype r body d = do
    opts <- view (ccOpts . coDatatypes)
    p <- getEnclosing

    (concreteTyDef, constrDefs, destrDef) <- compileDatatypeDefs opts r d

    let
        tyVars = [PIR.defVar concreteTyDef]
        tys = [getType $ PIR.defVal concreteTyDef]
        vars = fmap PIR.defVar constrDefs ++ [ PIR.defVar destrDef ]
        vals = fmap PIR.defVal constrDefs ++ [ PIR.defVal destrDef ]
    -- See note [Abstract data types]
    pure $
      PIR.mkIterApp
        (PIR.mkIterInst (PIR.mkIterTyAbs tyVars (PIR.mkIterLamAbs vars body)) ((p,) <$> tys))
        ((p,) <$> vals)

-- | Compile a 'Datatype' to a triple of type-constructor, data-constructors, destructor definitions.
compileDatatypeDefs
    :: MonadQuote m
    => DatatypeCompilationOpts
    -> Recursivity
    -> Datatype TyName Name uni (Provenance a)
    -> m (PLC.Def (TyVarDecl TyName (Provenance a)) (PLCRecType uni fun a),
          [PLC.Def (VarDecl TyName Name uni (Provenance a)) (PIRTerm uni fun a)],
          PLC.Def (VarDecl TyName Name uni (Provenance a)) (PIRTerm uni fun a))
compileDatatypeDefs opts r d@(Datatype ann tn _ destr constrs) = do
    concreteTyDef <- PIR.Def tn <$> mkDatatypeType opts r d

    constrDefs <- for (zip constrs [0..]) $ \(constr, i) -> do
        let constrTy = DatatypeComponent ConstructorType <$> mkConstructorType d constr
        c <- mkConstructor opts (PIR.defVal concreteTyDef) d i
        pure $ PIR.Def (VarDecl (DatatypeComponent Constructor ann) (_varDeclName constr) constrTy) c

    destrDef <- do
        destTy <- fmap (DatatypeComponent DestructorType) <$> mkDestructorTy d
        t <- mkDestructor opts (PIR.defVal concreteTyDef) d
        pure $ PIR.Def (VarDecl (DatatypeComponent Destructor ann) destr destTy) t

    pure (concreteTyDef, constrDefs, destrDef)

compileRecDatatypes
    :: Compiling m e uni fun a
    => PIRTerm uni fun a
    -> NE.NonEmpty (Datatype TyName Name uni (Provenance a))
    -> m (PIRTerm uni fun a)
compileRecDatatypes body ds = case ds of
    d NE.:| [] -> compileDatatype Rec body d
    _          -> do
      p <- getEnclosing
      throwing _Error $ UnsupportedError p "Mutually recursive datatypes"
