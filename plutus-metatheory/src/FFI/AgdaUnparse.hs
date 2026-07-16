{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -Wall #-}

module FFI.AgdaUnparse where

import Data.ByteString (ByteString)
import Data.List.NonEmptySep
import Data.Proxy
import Data.Text (Text)
import Data.Text qualified as T
import Data.Vector.Strict (Vector)
import FFI.Untyped qualified as AgdaFFI
import PlutusCore qualified as PLC
import PlutusCore.Crypto.BLS12_381.G1 qualified as BLS12_381.G1
import PlutusCore.Crypto.BLS12_381.G2 qualified as BLS12_381.G2
import PlutusCore.Crypto.BLS12_381.Pairing qualified as BLS12_381.Pairing
import PlutusCore.Data (Data)
import PlutusCore.Data qualified as Data
import PlutusCore.Value (Value)
import PlutusPrelude
import Prettyprinter
import Prettyprinter.Render.String (renderString)
import UntypedPlutusCore qualified as UPLC
import UntypedPlutusCore.Transform.Certify.Hints qualified as Hints
import UntypedPlutusCore.Transform.Certify.Trace

usToHyphen :: String -> String
usToHyphen = map (\c -> if c == '_' then '-' else c)

-- | A class for types that can be unparsed to Agda code.
class AgdaUnparse a where
  agdaUnparse :: a -> Doc ann

-- | Render an 'AgdaUnparse' value to a 'String'.
renderAgdaUnparse :: AgdaUnparse a => a -> String
renderAgdaUnparse = renderString . layoutPretty (LayoutOptions Unbounded) . agdaUnparse

instance (AgdaUnparse a, AgdaUnparse b) => AgdaUnparse (NonEmptySep a b) where
  agdaUnparse (Singleton x) = parens ("singleton" <+> agdaUnparse x)
  agdaUnparse (Cons x y xs) =
    parens $
      "cons"
        <+> agdaUnparse x
        <+> agdaUnparse y
        <+> agdaUnparse xs

instance AgdaUnparse AgdaFFI.UTerm where
  agdaUnparse =
    \case
      AgdaFFI.UVar n -> parens ("UVar" <+> agdaUnparse (fromInteger n :: Natural))
      AgdaFFI.ULambda term -> parens ("ULambda" <+> agdaUnparse term)
      AgdaFFI.UApp t u -> parens ("UApp" <+> agdaUnparse t <+> agdaUnparse u)
      AgdaFFI.UCon someValue -> parens ("UCon" <+> agdaUnparse someValue)
      AgdaFFI.UError -> "UError"
      AgdaFFI.UBuiltin fun -> parens ("UBuiltin" <+> agdaUnparse fun)
      AgdaFFI.UDelay term -> parens ("UDelay" <+> agdaUnparse term)
      AgdaFFI.UForce term -> parens ("UForce" <+> agdaUnparse term)
      AgdaFFI.UConstr i terms ->
        parens ("UConstr" <+> agdaUnparse (fromInteger i :: Natural) <+> agdaUnparse terms)
      AgdaFFI.UCase term cases -> parens ("UCase" <+> agdaUnparse term <+> agdaUnparse cases)

instance AgdaUnparse UPLC.DefaultFun where
  agdaUnparse = pretty . usToHyphen . lowerInitialChar . show

instance AgdaUnparse CertifiedOptStage where
  agdaUnparse FloatDelay = "floatDelayT"
  agdaUnparse ForceDelay = "forceDelayT"
  agdaUnparse ForceCaseDelay = "forceCaseDelayT"
  agdaUnparse Inline = "inlineT"
  agdaUnparse CSE = "cseT"
  agdaUnparse ApplyToCase = "applyToCaseT"
  agdaUnparse CaseReduce = "caseReduceT"
  agdaUnparse LetFloatOut = "letFloatOutT"

instance AgdaUnparse UncertifiedOptStage where
  agdaUnparse CaseOfCase = "caseOfCaseT"
  agdaUnparse ConstantFolding = "constantFoldingT"
  agdaUnparse PolyBuiltin = "polyBuiltinT"

instance AgdaUnparse Hints.Hints where
  agdaUnparse = \case
    Hints.NoHints -> "none"
    Hints.Inline x -> parens ("inline" <+> agdaUnparse x)

instance AgdaUnparse Hints.Inline where
  agdaUnparse = \case
    Hints.InlVar -> "var"
    Hints.InlLam t -> parens ("ƛ" <+> agdaUnparse t)
    Hints.InlApply f x -> parens (agdaUnparse f <+> "·" <+> agdaUnparse x)
    Hints.InlForce t -> parens ("force" <+> agdaUnparse t)
    Hints.InlDelay t -> parens ("delay" <+> agdaUnparse t)
    Hints.InlCon -> "con"
    Hints.InlBuiltin -> "builtin"
    Hints.InlError -> "error"
    Hints.InlConstr ts -> parens ("constr" <+> agdaUnparse ts)
    Hints.InlCase t ts -> parens ("case" <+> agdaUnparse t <+> agdaUnparse ts)
    Hints.InlMatch _ _ -> error "UPLC 1.2 'match' hints are not yet supported by the Agda certifier"
    Hints.InlExpand t -> parens ("expand" <+> agdaUnparse t)
    Hints.InlDrop t -> parens (agdaUnparse t <+> "·↓")

instance AgdaUnparse Natural where
  agdaUnparse = viaShow

instance AgdaUnparse Integer where
  agdaUnparse x
    | x < 0 = parens ("ℤ.negsuc" <+> viaShow (abs x - 1))
    | otherwise = parens ("ℤ.pos" <+> viaShow x)

instance AgdaUnparse Bool where
  agdaUnparse True = "true"
  agdaUnparse False = "false"

instance AgdaUnparse Char where
  agdaUnparse = viaShow
instance AgdaUnparse Text where
  agdaUnparse = viaShow . T.unpack

instance AgdaUnparse ByteString where
  agdaUnparse bs = parens ("mkByteString" <+> viaShow bs)

instance AgdaUnparse () where
  agdaUnparse _ = "tt"

agdaUnfold :: (AgdaUnparse a, Foldable f) => f a -> Doc ann
agdaUnfold l = parens $ foldr (\x xs -> agdaUnparse x <+> "∷" <+> xs) "[]" l

instance AgdaUnparse a => AgdaUnparse [a] where
  agdaUnparse = agdaUnfold

instance (AgdaUnparse a, AgdaUnparse b) => AgdaUnparse (a, b) where
  agdaUnparse (x, y) = parens (agdaUnparse x <+> "," <+> agdaUnparse y)

instance AgdaUnparse a => AgdaUnparse (Vector a) where
  agdaUnparse v = parens ("mkArray" <+> parens (agdaUnfold v))

instance (AgdaUnparse a, AgdaUnparse b) => AgdaUnparse (Either a b) where
  agdaUnparse (Left a) = parens ("inj₁" <+> agdaUnparse a)
  agdaUnparse (Right b) = parens ("inj₂" <+> agdaUnparse b)
instance AgdaUnparse Data where
  agdaUnparse (Data.Constr i args) =
    parens ("ConstrDATA" <+> agdaUnparse i <+> agdaUnparse args)
  agdaUnparse (Data.Map assocList) =
    parens ("MapDATA" <+> agdaUnparse assocList)
  agdaUnparse (Data.List xs) =
    parens ("ListDATA" <+> agdaUnparse xs)
  agdaUnparse (Data.I i) =
    parens ("iDATA" <+> agdaUnparse i)
  agdaUnparse (Data.B b) =
    parens ("bDATA" <+> agdaUnparse b)

-- FIXME (https://github.com/IntersectMBO/plutus-private/issues/1796)
instance AgdaUnparse Value where
  agdaUnparse _ = "Not Implemented: AgdaUnprase Value"

instance AgdaUnparse BLS12_381.G1.Element where
  agdaUnparse = viaShow

instance AgdaUnparse BLS12_381.G2.Element where
  agdaUnparse = viaShow

instance AgdaUnparse BLS12_381.Pairing.MlResult where
  agdaUnparse = viaShow

instance AgdaUnparse (UPLC.DefaultUni (PLC.Esc a)) where
  agdaUnparse PLC.DefaultUniInteger = "integer"
  agdaUnparse PLC.DefaultUniByteString = "bytestring"
  agdaUnparse PLC.DefaultUniString = "string"
  agdaUnparse PLC.DefaultUniBool = "bool"
  agdaUnparse PLC.DefaultUniUnit = "unit"
  agdaUnparse PLC.DefaultUniData = "pdata"
  agdaUnparse PLC.DefaultUniValue = "value"
  agdaUnparse (PLC.DefaultUniList t) =
    parens ("list" <+> agdaUnparse t)
  agdaUnparse (PLC.DefaultUniPair t1 t2) =
    parens ("pair" <+> agdaUnparse t1 <+> agdaUnparse t2)
  agdaUnparse PLC.DefaultUniBLS12_381_G1_Element = "bls12-381-g1-element"
  agdaUnparse PLC.DefaultUniBLS12_381_G2_Element = "bls12-381-g2-element"
  agdaUnparse PLC.DefaultUniBLS12_381_MlResult = "bls12-381-mlresult"
  agdaUnparse (PLC.DefaultUniArray t) =
    parens ("array" <+> agdaUnparse t)
  agdaUnparse (PLC.DefaultUniApply _ _) = error "Application of an unknown type is not supported."

instance AgdaUnparse (PLC.Some (PLC.ValueOf UPLC.DefaultUni)) where
  agdaUnparse (PLC.Some (PLC.ValueOf univ val)) =
    parens $
      "tagCon"
        <+> agdaUnparse univ
        <+> PLC.bring (Proxy @AgdaUnparse) univ (agdaUnparse val)
