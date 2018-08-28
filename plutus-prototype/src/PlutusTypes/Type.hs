{-# OPTIONS -Wall #-}
{-# LANGUAGE DeriveFoldable       #-}
{-# LANGUAGE DeriveFunctor        #-}
{-# LANGUAGE DeriveGeneric        #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE TypeSynonymInstances #-}







-- | The types of the simply typed lambda calculus w/ non-parametric user
-- defined types (eg Bool, Nat).

module PlutusTypes.Type where

import           Utils.ABT
import           Utils.Pretty
import           Utils.Vars

import           GHC.Generics






-- | A type constructor's signature consists of just the number of parameters
-- the constructor has.

newtype TyConSig = TyConSig Int
  deriving (Generic)

instance Show TyConSig where
  show (TyConSig n) = "*^" ++ show n







-- | Types can be type constructors, functions, foralls.

data TypeF r
  = TyCon String [r]
  | Fun r r
  | Forall r
  | Comp r
  | PlutusInt
  | PlutusFloat
  | PlutusByteString
  deriving (Show,Eq,Functor,Foldable,Generic)


type Type = ABT TypeF





tyConH :: String -> [Type] -> Type
tyConH c as = In (TyCon c (map (scope []) as))

funH :: Type -> Type -> Type
funH a b = In (Fun (scope [] a) (scope [] b))

forallH :: String -> Type -> Type
forallH x b = In (Forall (scope [x] b))

compH :: Type -> Type
compH a = In (Comp (scope [] a))

intH :: Type
intH = In PlutusInt

floatH :: Type
floatH = In PlutusFloat

byteStringH :: Type
byteStringH = In PlutusByteString





-- | There are two possible recursive locations within a type, so there are
-- two 'TypeParenLoc's for the parenthesizer to use.

data TypeParenLoc = TyConArg | FunLeft | FunRight | ForallBody
  deriving (Eq,Generic)


-- | Everything can be de-parenthesized everywhere, except for functions.
-- A function can only be de-parenthesized on the right of a function arrow.

instance Parens Type where
  type Loc Type = TypeParenLoc

  parenLoc (Var _) =
    [TyConArg,FunLeft,FunRight,ForallBody]
  parenLoc (In (TyCon _ [])) =
    [TyConArg,FunLeft,FunRight,ForallBody]
  parenLoc (In (TyCon _ _)) =
    [FunRight,ForallBody]
  parenLoc (In (Fun _ _)) =
    [FunRight,ForallBody]
  parenLoc (In (Forall _)) =
    [FunRight,ForallBody]
  parenLoc (In (Comp _)) =
    [FunRight,ForallBody]
  parenLoc (In PlutusInt) =
    [TyConArg,FunLeft,FunRight,ForallBody]
  parenLoc (In PlutusFloat) =
    [TyConArg,FunLeft,FunRight,ForallBody]
  parenLoc (In PlutusByteString) =
    [TyConArg,FunLeft,FunRight,ForallBody]

  parenRec (Var v) = name v
  parenRec (In (TyCon c [])) = c
  parenRec (In (TyCon c as)) =
    c ++ " "
      ++ unwords
           (map (parenthesize (Just TyConArg) . instantiate0) as)
  parenRec (In (Fun a b)) =
    parenthesize (Just FunLeft) (instantiate0 a)
      ++ " -> "
      ++ parenthesize (Just FunRight) (instantiate0 b)
  parenRec (In (Forall sc)) =
    "forall " ++ unwords (names sc) ++ ". "
    ++ parenthesize (Just ForallBody) (body sc)
  parenRec (In (Comp a)) =
    "Comp " ++ parenthesize (Just TyConArg) (instantiate0 a)
  parenRec (In PlutusInt) =
    "Int"
  parenRec (In PlutusFloat) =
    "Float"
  parenRec (In PlutusByteString) =
    "ByteString"
