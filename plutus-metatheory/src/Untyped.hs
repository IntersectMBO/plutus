{-# LANGUAGE GADTs          #-}
{-# LANGUAGE KindSignatures #-}

module Untyped where

import PlutusCore.Data
import PlutusCore.Default
import UntypedPlutusCore

import Data.ByteString as BS
import Data.Text as T
import Universe

data SomeStarIn uni = forall (a :: *). SomeStarIn !(uni (Esc a))

data TyTag = TagInt | TagBS | TagStr | TagBool | TagUnit | TagData
            | TagPair TyTag TyTag
            | TagList TyTag
            deriving Show

convTyTag :: SomeStarIn DefaultUni -> TyTag
convTyTag (SomeStarIn DefaultUniInteger) = TagInt
convTyTag (SomeStarIn DefaultUniByteString) = TagBS
convTyTag (SomeStarIn DefaultUniString) = TagStr
convTyTag (SomeStarIn DefaultUniBool) = TagBool
convTyTag (SomeStarIn DefaultUniUnit) = TagUnit
convTyTag (SomeStarIn DefaultUniData) = TagData
convTyTag (SomeStarIn (DefaultUniPair a b)) =
   TagPair (convTyTag (SomeStarIn a)) (convTyTag (SomeStarIn b))
convTyTag (SomeStarIn (DefaultUniList a)) = TagList (convTyTag (SomeStarIn a))
convTyTag _  = error "Cannot handle applications other than pair and lists"

uconvTyTag :: TyTag -> SomeStarIn DefaultUni
uconvTyTag TagInt = SomeStarIn DefaultUniInteger
uconvTyTag TagBS = SomeStarIn DefaultUniByteString
uconvTyTag TagStr = SomeStarIn DefaultUniString
uconvTyTag TagBool = SomeStarIn DefaultUniBool
uconvTyTag TagUnit = SomeStarIn DefaultUniUnit
uconvTyTag TagData = SomeStarIn DefaultUniData
uconvTyTag (TagPair x y) = case (uconvTyTag x, uconvTyTag y) of
                (SomeStarIn x', SomeStarIn y') -> SomeStarIn (DefaultUniPair x' y')
uconvTyTag (TagList x) = case uconvTyTag x of
                           (SomeStarIn x') ->  SomeStarIn (DefaultUniList x')

data TermCon = TmInteger Integer
             | TmByteString ByteString
             | TmString Text
             | TmBool Bool
             | TmUnit
             | TmData Data
             | TmPair TyTag TyTag TermCon TermCon
             | TmList TyTag [TermCon]
            deriving Show

convTermCon :: Some (ValueOf DefaultUni) -> TermCon
convTermCon (Some (ValueOf DefaultUniInteger i)) = TmInteger i
convTermCon (Some (ValueOf DefaultUniByteString b)) = TmByteString b
convTermCon (Some (ValueOf DefaultUniString s)) = TmString s
convTermCon (Some (ValueOf DefaultUniBool b)) = TmBool b
convTermCon (Some (ValueOf DefaultUniUnit _)) = TmUnit
convTermCon (Some (ValueOf DefaultUniData d)) = TmData d
convTermCon (Some (ValueOf (DefaultUniPair ta tb) (a,b))) =
     TmPair (convTyTag (SomeStarIn ta))
            (convTyTag (SomeStarIn tb))
            (convTermCon (Some (ValueOf ta a)))
            (convTermCon (Some (ValueOf tb b)))
convTermCon (Some (ValueOf (DefaultUniList ta) xs)) =
     TmList (convTyTag (SomeStarIn ta))
            (Prelude.map (\a -> convTermCon (Some (ValueOf ta a))) xs)
convTermCon _ = error "Cannot handle applications other than pair and lists"

uconvTermCon :: TermCon -> Some (ValueOf DefaultUni)
uconvTermCon (TmInteger i)    = someValueOf DefaultUniInteger i
uconvTermCon (TmByteString b) = someValueOf DefaultUniByteString b
uconvTermCon (TmString s)     = someValueOf DefaultUniString s
uconvTermCon (TmBool b)       = someValueOf DefaultUniBool b
uconvTermCon TmUnit           = someValueOf DefaultUniUnit ()
uconvTermCon (TmData d)       = someValueOf DefaultUniData d
uconvTermCon (TmPair _ _ a b) = case (uconvTermCon a , uconvTermCon b) of
          (Some (ValueOf t a) , Some (ValueOf u b )) -> someValueOf (DefaultUniPair t u) (a , b)
uconvTermCon (TmList t [])     = case uconvTyTag t of
      (SomeStarIn t') -> someValueOf (DefaultUniList t') []
uconvTermCon (TmList t (x:xs)) =
   case (uconvTermCon x , uconvTermCon (TmList t xs)) of
     (Some (ValueOf tx x') , Some (ValueOf (DefaultUniList ts) xs')) -> undefined
     _                                                               -> error "gg"
-- Untyped (Raw) syntax

data UTerm = UVar Integer
           | ULambda UTerm
           | UApp UTerm UTerm
           | UCon TermCon
           | UError
           | UBuiltin DefaultFun
           | UDelay UTerm
           | UForce UTerm
           deriving Show

unIndex :: Index -> Integer
unIndex (Index n) = toInteger n

convP :: Program NamedDeBruijn DefaultUni DefaultFun a -> UTerm
convP (Program _ _ t) = conv t

conv :: Term NamedDeBruijn DefaultUni DefaultFun a -> UTerm
conv (Var _ x)      = UVar (unIndex (ndbnIndex x) - 1)
conv (LamAbs _ _ t) = ULambda (conv t)
conv (Apply _ t u)  = UApp (conv t) (conv u)
conv (Builtin _ b)  = UBuiltin b
conv (Constant _ c) = UCon (convTermCon c)
conv (Error _)      = UError
conv (Delay _ t)    = UDelay (conv t)
conv (Force _ t)    = UForce (conv t)

tmnames = ['a' .. 'z']

uconv ::  Int -> UTerm -> Term NamedDeBruijn DefaultUni DefaultFun ()
uconv i (UVar x)     = Var
  ()
  (NamedDeBruijn (T.pack [tmnames !! (i - 1 - fromInteger x)])
                -- PLC's debruijn starts counting from 1, while in the metatheory it starts from 0.
                 (Index (fromInteger x + 1)))
uconv i (ULambda t)  = LamAbs
  ()
  (NamedDeBruijn (T.pack [tmnames !! i]) deBruijnInitIndex)
  (uconv (i+1) t)
uconv i (UApp t u)   = Apply () (uconv i t) (uconv i u)
uconv i (UCon c)     = Constant () (uconvTermCon c)
uconv i UError       = Error ()
uconv i (UBuiltin b) = Builtin () b
uconv i (UDelay t)   = Delay () (uconv i t)
uconv i (UForce t)   = Force () (uconv i t)

