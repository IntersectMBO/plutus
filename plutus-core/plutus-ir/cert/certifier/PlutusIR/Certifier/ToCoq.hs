{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE UndecidableInstances  #-}

-- | Pretty printing of PIR types suitable for parsing in the Coq certifier.
-- This basically implements a Show-like representation without record syntax so it
-- easy to parse on the Coq side. It also does not print annotations which are
-- not needed.
module PlutusIR.Certifier.ToCoq where

import PlutusCore qualified as PLC
import PlutusIR qualified as PIR
import PlutusIR.Compiler.Types qualified as PIR

import Data.ByteString qualified as BS
import Data.List (intercalate)
import Data.List.NonEmpty (NonEmpty (..))
import Data.Proxy
import Data.Text qualified as T
import GHC.Word (Word64)
import PlutusCore.Crypto.BLS12_381.G1 qualified as BLS12_381.G1
import PlutusCore.Crypto.BLS12_381.G2 qualified as BLS12_381.G2
import PlutusCore.Crypto.BLS12_381.Pairing qualified as BLS12_381.Pairing
import PlutusCore.Data qualified as Data

class ToCoq a where
  toCoq :: a -> String

apps :: String -> [String] -> String
apps f xs = intercalate " " (f : fmap parens xs)

parens :: String -> String
parens x = "(" ++ x ++ ")"

instance
  ( ToCoq name
  , ToCoq tyname
  , ToCoq fun
  , forall b. ToCoq (uni b)
  , PLC.Closed uni
  , PLC.Everywhere uni ToCoq
  ) =>
  ToCoq (PIR.Term name tyname uni fun a) where
  toCoq = \case
    PIR.Let _ rec bindings t  -> apps "Let"    [toCoq rec, toCoq bindings, toCoq t]
    PIR.Var _ name            -> apps "Var"    [toCoq name]
    PIR.TyAbs _ tyname kind t -> apps "TyAbs"  [toCoq tyname, toCoq kind, toCoq t]
    PIR.LamAbs _ name ty t    -> apps "LamAbs" [toCoq name, toCoq ty, toCoq t]
    PIR.Apply _ t1 t2         -> apps "Apply"  [toCoq t1, toCoq t2]
    PIR.Constant _ val        -> apps "Constant" [toCoq val]
    PIR.Builtin _ fun         -> apps "Builtin" [toCoq fun]
    PIR.TyInst _ term ty      -> apps "TyInst" [toCoq term, toCoq ty]
    PIR.Error _ ty            -> apps "Error" [toCoq ty]
    PIR.IWrap _ ty1 ty2 t     -> apps "IWrap" [toCoq ty1, toCoq ty2, toCoq t]
    PIR.Unwrap _ t            -> apps "Unwrap" [toCoq t]
    PIR.Constr _ ty tag args  -> apps "Constr" [toCoq ty, toCoq tag, toCoq args]
    PIR.Case _ ty t bs        -> apps "Case" [toCoq ty, toCoq t, toCoq bs]

instance (forall a. ToCoq (f a)) => ToCoq (PLC.Some f) where
  toCoq (PLC.Some x) = apps "Some" [toCoq x]

instance (forall a. ToCoq (f a)) => ToCoq (PLC.SomeTypeIn f) where
  toCoq (PLC.SomeTypeIn x) = apps "SomeTypeIn" [toCoq x]

instance
  (forall t. ToCoq (uni t), PLC.Closed uni, PLC.Everywhere uni ToCoq) =>
  ToCoq (PLC.ValueOf uni a) where
  toCoq (PLC.ValueOf uni x) = PLC.bring (Proxy @ToCoq) uni $ apps "ValueOf" [toCoq uni, toCoq x]

instance ToCoq (PLC.DefaultUni a) where
  toCoq = show

instance ToCoq Bool where
  toCoq True  = "true"
  toCoq False = "false"

instance ToCoq GHC.Word.Word64 where
  toCoq = show

instance ToCoq () where toCoq () = "tt"
instance ToCoq T.Text where toCoq = show
instance ToCoq Int where toCoq = show
instance ToCoq Integer where toCoq = show
instance ToCoq Char where toCoq = show
instance ToCoq BS.ByteString where toCoq = show
instance ToCoq BLS12_381.Pairing.MlResult where toCoq = show
instance ToCoq BLS12_381.G2.Element where toCoq = show
instance ToCoq BLS12_381.G1.Element where toCoq = show

instance
  ( ToCoq tyname
  , ToCoq name
  , ToCoq fun
  , PLC.Closed uni
  , PLC.Everywhere uni ToCoq
  , forall b. ToCoq (uni b)
  ) => ToCoq (PIR.Binding tyname name uni fun a) where
  toCoq (PIR.TermBind _ strictness vdecl t)
    = apps "TermBind" [toCoq strictness, toCoq vdecl, toCoq t]
  toCoq (PIR.TypeBind _ tvdecl ty)
    = apps "TypeBind" [toCoq tvdecl, toCoq ty]
  toCoq (PIR.DatatypeBind _ dt)
    = apps "DatatypeBind" [toCoq dt]

instance
  (ToCoq name
  , ToCoq tyname
  , PLC.Closed uni
  , PLC.Everywhere uni ToCoq
  , forall b. ToCoq (uni b)
  ) => ToCoq (PIR.VarDecl tyname name uni a) where
  toCoq (PIR.VarDecl _ name ty) = apps "VarDecl" [toCoq name, toCoq ty]
instance (ToCoq tyname) => ToCoq (PIR.TyVarDecl tyname a) where
  toCoq (PIR.TyVarDecl _ name kind) = apps "TyVarDecl" [toCoq name, toCoq kind]

instance
  ( ToCoq name
  , ToCoq tyname
  , forall b. ToCoq (uni b)
  , PLC.Closed uni
  , PLC.Everywhere uni ToCoq
  ) => ToCoq (PIR.Datatype tyname name uni a) where
  toCoq (PIR.Datatype _ tvdecl tvdecls name constructors)
    = apps "Datatype" [toCoq tvdecl, toCoq tvdecls, toCoq name, toCoq constructors]

instance ToCoq (PLC.TyName) where toCoq (PLC.TyName name) = apps "TyName" [toCoq name]


instance ToCoq a => ToCoq (NonEmpty a) where
  toCoq (x :| xs) = apps "cons" [toCoq x, toCoq xs]

instance ToCoq a => ToCoq [a] where
  toCoq []     = "nil"
  toCoq (x:xs) = apps "cons" [toCoq x, toCoq xs]

instance (ToCoq a, ToCoq b) => ToCoq (a, b) where
  toCoq (a, b) = "(" ++ toCoq a ++ "," ++ toCoq b ++ ")"

instance ToCoq PLC.Name where toCoq (PLC.Name str uniq) = apps "Name" [toCoq str, toCoq uniq]
instance ToCoq PLC.Unique where toCoq (PLC.Unique n) = apps "Unique" [toCoq n]
instance ToCoq PLC.DefaultFun where toCoq = show
instance ToCoq PIR.Strictness where toCoq = show
instance ToCoq PIR.Recursivity where toCoq = show

instance ToCoq (PIR.Kind ann) where
  toCoq (PIR.Type _)            = "Kind_Base"
  toCoq (PIR.KindArrow _ k1 k2) = apps "Kind_Arrow" [toCoq k1, toCoq k2]

instance (ToCoq tyname, PLC.Closed uni, PLC.Everywhere uni ToCoq, forall a. ToCoq (uni a))
  => ToCoq (PIR.Type tyname uni ann) where
  toCoq (PIR.TyVar _ tyname)         = apps "Ty_Var" [toCoq tyname]
  toCoq (PIR.TyFun _ ty1 ty2)        = apps "Ty_Fun" [toCoq ty1, toCoq ty2]
  toCoq (PIR.TyIFix _ ty1 ty2)       = apps "Ty_IFix" [toCoq ty1, toCoq ty2]
  toCoq (PIR.TyForall _ tyname k ty) = apps "Ty_Forall" [toCoq tyname, toCoq k, toCoq ty]
  toCoq (PIR.TyBuiltin _ b)          = apps "Ty_Builtin" [toCoq b]
  toCoq (PIR.TyLam _ tyname k ty)    = apps "Ty_Lam" [toCoq tyname, toCoq k , toCoq ty]
  toCoq (PIR.TyApp _ ty1 ty2)        = apps "Ty_App" [toCoq ty1, toCoq ty2]
  toCoq (PIR.TySOP _ sop)            = apps "Ty_SOP" [toCoq sop]

instance ToCoq Data.Data where
  toCoq = show

instance ToCoq PIR.PassMeta where
  toCoq (PIR.PassInline names tyNames) = apps "PassInline" [toCoq names, toCoq tyNames]
  toCoq pm                             = show pm


instance
  ( PLC.Everywhere uni ToCoq
  , PLC.Closed uni
  , ToCoq fun
  , forall b. ToCoq (uni b)
  )
  => ToCoq (PIR.CompilationTrace uni fun a) where
  toCoq (PIR.CompilationTrace t0 passes) = apps "CompilationTrace" [toCoq t0, toCoq passes]

