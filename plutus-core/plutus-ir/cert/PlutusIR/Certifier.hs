{-# LANGUAGE GADTs      #-}
{-# LANGUAGE LambdaCase #-}

-- Still some stuff that isn't used yet
{-# OPTIONS_GHC -Wno-unused-top-binds #-}

-- | Interface to automatically extracted code from plutus-cert (Coq):
-- - Conversion functions for PIR's AST to the representation in Coq.
-- - Boolean decision procedures for translation relations
module PlutusIR.Certifier (is_dead_code, is_unique) where

import PlutusCore qualified as P (DefaultFun (..), DefaultUni (..), Some (..), SomeTypeIn (..),
                                  ValueOf (..))
import PlutusIR qualified as P
import PlutusIR.Certifier.Extracted qualified as E

import Data.Char
import Data.List.NonEmpty

type EString = E.String

type Term a = P.Term P.TyName P.Name P.DefaultUni P.DefaultFun a
type ETerm = E.Term EString EString EString EString

type Binding a = P.Binding P.TyName P.Name P.DefaultUni P.DefaultFun a
type EBinding = E.Binding EString EString EString EString

type PDatatype a = P.Datatype P.TyName P.Name P.DefaultUni a
type EDatatype = E.Dtdecl EString EString EString

type Type a = P.Type P.TyName P.DefaultUni a
type EType = E.Ty EString EString

type Kind a = P.Kind a
type EKind = E.Kind

type PVarDecl a = P.VarDecl P.TyName P.Name P.DefaultUni a
type EVarDecl = E.Vdecl EString EString EString

type PTyVarDecl a = P.TyVarDecl P.TyName a
type ETyVarDecl = E.Tvdecl EString
type EConstr = E.Constr EString EString EString

glueString :: String -> EString
glueString = Prelude.foldr (E.String0 . glueChar) E.EmptyString

intToNat :: Int -> E.Nat
intToNat 0 = E.O
intToNat n
  | n < 0 = error "intToNat: negative Int"
  | otherwise = E.S (intToNat (n - 1))

glueChar :: Char -> E.Ascii0
glueChar = E.ascii_of_nat . intToNat . ord

glueNonEmpty :: NonEmpty a -> E.List a
glueNonEmpty (x :| xs) = E.Cons x (glueList xs)

glueList :: [a] -> E.List a
glueList []       = E.Nil
glueList (x : xs) = E.Cons x (glueList xs)

glueTerm :: Term a -> ETerm
glueTerm = \case
  P.Let _ r bs t       -> E.Let
                            (glueRecursivity r)
                            (glueNonEmpty (fmap glueBinding bs))
                            (glueTerm t)
  P.Var _ name         -> E.Var (glueName name)
  P.TyAbs _ tyname k t -> E.TyAbs (glueTyName tyname) (glueKind k) (glueTerm t)
  P.LamAbs _ name ty t -> E.LamAbs (glueName name) (glueType ty) (glueTerm t)
  P.Apply _ t t'       -> E.Apply (glueTerm t) (glueTerm t')
  P.Constant _ c       -> E.Constant (glueConstant c)
  P.Builtin _ fun      -> E.Builtin (glueDefaultFun fun)
  P.TyInst _ t ty      -> E.TyInst (glueTerm t) (glueType ty)
  P.Unwrap _ t         -> E.Unwrap (glueTerm t)
  P.IWrap _ ty1 ty2 t  -> E.IWrap (glueType ty1) (glueType ty2) (glueTerm t)
  P.Error _ ty         -> E.Error (glueType ty)
  P.Case _ _ _ _       -> error "glueTerm: Case not supported"
  P.Constr _ _ _ _     -> error "glueTerm: Constr not supported"

glueRecursivity :: P.Recursivity -> E.Recursivity
glueRecursivity P.Rec    = E.Rec
glueRecursivity P.NonRec = E.NonRec



glueDefaultFun :: P.DefaultFun -> E.DefaultFun
glueDefaultFun = \case
  P.AddInteger             -> E.AddInteger
  P.SubtractInteger        -> E.SubtractInteger
  P.MultiplyInteger        -> E.MultiplyInteger
  P.DivideInteger          -> E.DivideInteger
  P.QuotientInteger        -> E.QuotientInteger
  P.RemainderInteger       -> E.RemainderInteger
  P.ModInteger             -> E.ModInteger
  P.LessThanInteger        -> E.LessThanInteger
  P.LessThanEqualsInteger  -> E.LessThanEqInteger
  -- P.GreaterThanInteger   -> E.GreaterThanInteger
  -- P.GreaterThanEqInteger -> E.GreaterThanEqInteger
  P.EqualsInteger          -> E.EqInteger
  -- P.Concatenate          -> E.Concatenate
  -- P.TakeByteString       -> E.TakeByteString
  -- P.DropByteString       -> E.DropByteString
  P.Sha2_256               -> E.SHA2
  P.Sha3_256               -> E.SHA3
  P.VerifyEd25519Signature -> E.VerifySignature
  P.EqualsByteString       -> E.EqByteString
  P.LessThanByteString     -> E.LtByteString
  -- P.GtByteString         -> E.GtByteString
  P.IfThenElse             -> E.IfThenElse
  -- P.CharToString         -> E.CharToString
  P.AppendString           -> E.Append
  P.Trace                  -> E.Trace

  -- TODO: support current set of builtin functions
  _                        -> E.Trace

glueConstant :: P.Some (P.ValueOf P.DefaultUni) -> E.Some0 E.ValueOf
glueConstant (P.Some (P.ValueOf u _x)) =
  let anyU = case u of
        _ -> E.unsafeCoerce ()
        -- P.DefaultUniInteger    -> E.unsafeCoerce (glueInteger x)
        -- P.DefaultUniChar       -> E.unsafeCoerce (glueChar x)
        -- P.DefaultUniUnit       -> E.unsafeCoerce x -- same rep ()
        -- P.DefaultUniBool       -> E.unsafeCoerce (glueBool x)
        -- P.DefaultUniString     -> E.unsafeCoerce (glueString x)
        -- P.DefaultUniByteString -> E.unsafeCoerce (glueString (show x))
  in E.Some' (glueDefaultUni u) (E.unsafeCoerce anyU)

glueInteger :: Integer -> E.Z
glueInteger x
  | x == 0 = E.Z0
  | x > 0  = E.Zpos (gluePositive x)
  | otherwise = E.Zneg (gluePositive (-1 * x))



-- Coq's representation of Positive: https://coq.inria.fr/library/Coq.Numbers.BinNums.html
gluePositive :: Integer -> E.Positive
gluePositive n
  | n <= 0    = error "gluePositive: non-positive number provided"
  | otherwise = bitsToPos (go n)
  where
    go 0 = []
    go m = case divMod m 2 of
      (r, 0) -> False : go r
      (r, 1) -> True : go r
      _      -> error "gluePositive: impossible"

    bitsToPos :: [Bool] -> E.Positive
    bitsToPos [True]       = E.XH
    bitsToPos (True : xs)  = E.XI (bitsToPos xs)
    bitsToPos (False : xs) = E.XO (bitsToPos xs)
    bitsToPos []           =
      error "bitsToPos: positive number should have a most significant (leading) 1 bit"


glueBool :: Bool -> E.Bool
glueBool True  = E.True
glueBool False = E.False

glueStrictness :: P.Strictness -> E.Strictness
glueStrictness P.Strict    = E.Strict
glueStrictness P.NonStrict = E.NonStrict


glueVarDecl :: PVarDecl a -> EVarDecl
glueVarDecl (P.VarDecl _ name ty) = E.VarDecl (glueName name) (glueType ty)

glueTyVarDecl :: PTyVarDecl a -> ETyVarDecl
glueTyVarDecl (P.TyVarDecl _ tyname k) = E.TyVarDecl (glueTyName tyname) (glueKind k)


glueConstructor :: PVarDecl a -> EConstr
glueConstructor (P.VarDecl _ name ty) =
  E.Constructor
    (E.VarDecl (glueName name)
    (glueType ty))
    (arity ty)
  where
    arity :: P.Type tyname uni a -> E.Nat
    arity (P.TyFun _ _a b) = E.S (arity b)
    arity _                = E.O

glueDatatype :: PDatatype a -> EDatatype
glueDatatype (P.Datatype _ tvd tvs elim cs) =
  E.Datatype
    (glueTyVarDecl tvd)
    (glueList (fmap glueTyVarDecl tvs))
    (glueName elim)
    (glueList (fmap glueConstructor cs))

glueBinding :: Binding a -> EBinding
glueBinding = \case
  P.TermBind _ s vd t  -> E.TermBind (glueStrictness s) (glueVarDecl vd) (glueTerm t)
  P.TypeBind _ tvd ty  -> E.TypeBind (glueTyVarDecl tvd) (glueType ty)
  P.DatatypeBind _ dtd -> E.DatatypeBind (glueDatatype dtd)

-- This is hacky: we use (unique) strings for variable names in Coq,
-- so we just `show` the Unique
glueName :: P.Name -> EString
glueName (P.Name _str uniq) = glueString (show uniq)

glueTyName :: P.TyName -> EString
glueTyName (P.TyName n) = glueName n

glueDefaultUni :: P.DefaultUni a -> E.DefaultUni
glueDefaultUni u = case u of
  -- TODO: implement current constructors of DefaultUni
  -- _                      -> E.DefaultUniInteger
  P.DefaultUniInteger    -> E.DefaultUniInteger
  P.DefaultUniByteString -> E.DefaultUniByteString
  P.DefaultUniString     -> E.DefaultUniString
  -- P.DefaultUniChar       -> E.DefaultUniChar
  P.DefaultUniUnit       -> E.DefaultUniUnit
  P.DefaultUniBool       -> E.DefaultUniBool
  _                      -> E.DefaultUniInteger

glueBuiltinType :: P.SomeTypeIn P.DefaultUni -> E.Some0 ()
glueBuiltinType (P.SomeTypeIn u) = E.Some' (glueDefaultUni u) ()

glueType :: Type a -> EType
glueType (P.TyVar _ tyname)        = E.Ty_Var (glueTyName tyname)
glueType (P.TyFun _ t t')          = E.Ty_Fun (glueType t) (glueType t')
glueType (P.TyIFix _ t t')         = E.Ty_IFix (glueType t) (glueType t')
glueType (P.TyForall _ tyname k t) = E.Ty_Forall (glueTyName tyname) (glueKind k) (glueType t)
glueType (P.TyBuiltin _ b)         = E.Ty_Builtin (glueBuiltinType b)
glueType (P.TyLam _ tyname k t)    = E.Ty_Lam (glueTyName tyname) (glueKind k) (glueType t)
glueType (P.TyApp _ t t')          = E.Ty_App (glueType t) (glueType t')
-- TODO: Support TySOP
glueType (P.TySOP _ _)             = error "glueType: TySOP not supported"

glueKind :: Kind a -> EKind
glueKind (P.Type _)            = E.Kind_Base
glueKind (P.KindArrow _ k1 k2) = E.Kind_Arrow (glueKind k1) (glueKind k2)


-- * Decision procedures for translation relations

toBool :: E.Bool -> Bool
toBool E.True  = True
toBool E.False = False

-- | Check if only pure let bindings were eliminated
is_dead_code :: Term a -> Term a -> Bool
is_dead_code t1 t2 = toBool $ E.dec_Term (glueTerm t1) (glueTerm t2)

-- | Check if a term has unique binders
is_unique :: Term a -> Bool
is_unique t = case E.dec_unique (glueTerm t) infinity of
  E.Some b -> toBool b
  _        -> False
  where
    infinity :: E.Nat
    infinity = E.S infinity
