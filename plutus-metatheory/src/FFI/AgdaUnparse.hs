{-# LANGUAGE FlexibleInstances #-}
{-# OPTIONS_GHC -Wall #-}

module FFI.AgdaUnparse where

import Data.ByteString (ByteString)
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
import PlutusPrelude
import UntypedPlutusCore qualified as UPLC
import UntypedPlutusCore.Transform.Simplifier

usToHyphen :: String -> String
usToHyphen = map (\c -> if c == '_' then '-' else c)

-- | A class for types that can be unparsed to Agda code.
class AgdaUnparse a where
  agdaUnparse :: a -> String

instance AgdaUnparse AgdaFFI.UTerm where
  agdaUnparse =
    \case
      AgdaFFI.UVar n -> "(UVar " ++ agdaUnparse (fromInteger n :: Natural) ++ ")"
      AgdaFFI.ULambda term -> "(ULambda " ++ agdaUnparse term ++ ")"
      AgdaFFI.UApp t u -> "(UApp " ++ agdaUnparse t ++ " " ++ agdaUnparse u ++ ")"
      AgdaFFI.UCon someValue -> "(UCon " ++ agdaUnparse someValue ++ ")"
      AgdaFFI.UError -> "UError"
      AgdaFFI.UBuiltin fun -> "(UBuiltin " ++ agdaUnparse fun ++ ")"
      AgdaFFI.UDelay term -> "(UDelay " ++ agdaUnparse term ++ ")"
      AgdaFFI.UForce term -> "(UForce " ++ agdaUnparse term ++ ")"
      AgdaFFI.UConstr i terms -> "(UConstr " ++ agdaUnparse (fromInteger i :: Natural)
                                      ++ " " ++ agdaUnparse terms ++ ")"
      AgdaFFI.UCase term cases -> "(UCase " ++ agdaUnparse term ++ " " ++ agdaUnparse cases ++ ")"

instance AgdaUnparse UPLC.DefaultFun where
  agdaUnparse = usToHyphen . lowerInitialChar . show

instance AgdaUnparse SimplifierStage where
  agdaUnparse FloatDelay     = "floatDelayT"
  agdaUnparse ForceDelay     = "forceDelayT"
  agdaUnparse ForceCaseDelay = "forceCaseDelayT"
  agdaUnparse CaseOfCase     = "caseOfCaseT"
  agdaUnparse CaseReduce     = "caseReduceT"
  agdaUnparse Inline         = "inlineT"
  agdaUnparse CSE            = "cseT"

instance AgdaUnparse Natural where
  agdaUnparse = show

instance AgdaUnparse Integer where
  agdaUnparse x =
    case (x < 0) of
      True  -> "(ℤ.negsuc " ++ show (x - 1) ++ ")"
      False ->  "(ℤ.pos " ++ show x ++ ")"

instance AgdaUnparse Bool where
  agdaUnparse True  = "true"
  agdaUnparse False = "false"

instance AgdaUnparse Char where
  agdaUnparse c = show c
instance AgdaUnparse Text where
  agdaUnparse = show . T.unpack

instance AgdaUnparse ByteString where
  agdaUnparse bs = "(mkByteString " <> show bs <> ")"

instance AgdaUnparse () where
  agdaUnparse _ = "tt"

agdaUnfold :: (AgdaUnparse a , Foldable f) => f a -> String
agdaUnfold l = "(" ++ foldr (\x xs -> agdaUnparse x ++ " ∷ " ++ xs) "[]" l ++ ")"

instance AgdaUnparse a => AgdaUnparse [a] where
  agdaUnparse = agdaUnfold

instance (AgdaUnparse a, AgdaUnparse b) => AgdaUnparse (a, b) where
  agdaUnparse (x, y) = "(" ++ agdaUnparse x ++ " , " ++ agdaUnparse y ++ ")"

instance (AgdaUnparse a) => AgdaUnparse (Vector a) where
  agdaUnparse v = "(mkArray (" ++ agdaUnfold v ++ "))"

instance AgdaUnparse Data where
  agdaUnparse (Data.Constr i args) =
    "(ConstrDATA " ++ agdaUnparse i ++ " " ++ agdaUnparse args ++ ")"
  agdaUnparse (Data.Map assocList) =
    "(MapDATA " ++ agdaUnparse assocList ++ ")"
  agdaUnparse (Data.List xs) =
    "(ListDATA " ++ agdaUnparse xs ++ ")"
  agdaUnparse (Data.I i) =
    "(iDATA " ++ agdaUnparse i ++ ")"
  agdaUnparse (Data.B b) =
    "(bDATA " ++ agdaUnparse b ++ ")"

instance AgdaUnparse BLS12_381.G1.Element where
  agdaUnparse = show

instance AgdaUnparse BLS12_381.G2.Element where
  agdaUnparse = show

instance AgdaUnparse BLS12_381.Pairing.MlResult where
  agdaUnparse = show

instance AgdaUnparse (UPLC.DefaultUni (PLC.Esc a)) where
  agdaUnparse PLC.DefaultUniInteger = "integer"
  agdaUnparse PLC.DefaultUniByteString = "bytestring"
  agdaUnparse PLC.DefaultUniString = "string"
  agdaUnparse PLC.DefaultUniBool = "bool"
  agdaUnparse PLC.DefaultUniUnit = "unit"
  agdaUnparse PLC.DefaultUniData = "pdata"
  agdaUnparse (PLC.DefaultUniList t) =
    "(list " ++ agdaUnparse t ++ ")"
  agdaUnparse (PLC.DefaultUniPair t1 t2) =
    "(pair " ++ agdaUnparse t1 ++ " " ++ agdaUnparse t2 ++ ")"
  agdaUnparse PLC.DefaultUniBLS12_381_G1_Element = "bls12-381-g1-element"
  agdaUnparse PLC.DefaultUniBLS12_381_G2_Element = "bls12-381-g2-element"
  agdaUnparse PLC.DefaultUniBLS12_381_MlResult = "bls12-381-mlresult"
  agdaUnparse (PLC.DefaultUniArray t) =
    "(array " ++ agdaUnparse t ++ ")"
  agdaUnparse (PLC.DefaultUniApply _ _) = error "Application of an unknown type is not supported."

instance AgdaUnparse (PLC.Some (PLC.ValueOf UPLC.DefaultUni)) where
  agdaUnparse (PLC.Some valOf) =
    "(tagCon " ++
      case valOf of
        PLC.ValueOf PLC.DefaultUniInteger val ->
          "integer " ++ agdaUnparse val
        PLC.ValueOf PLC.DefaultUniByteString val ->
          "bytestring " ++ agdaUnparse val
        PLC.ValueOf PLC.DefaultUniString val ->
          "string " ++ agdaUnparse val
        PLC.ValueOf PLC.DefaultUniBool val ->
          "bool " ++ agdaUnparse val
        PLC.ValueOf PLC.DefaultUniUnit _ ->
          "unit " ++ agdaUnparse ()
        PLC.ValueOf PLC.DefaultUniData val ->
          "pdata " ++ agdaUnparse val
        PLC.ValueOf univ@(PLC.DefaultUniList elemType) val ->
          agdaUnparse univ
          ++ " "
          ++
            ( PLC.bring (Proxy @AgdaUnparse) elemType
            $ agdaUnparse val
            )
        PLC.ValueOf univ@(PLC.DefaultUniPair type1 type2) val ->
          agdaUnparse univ
          ++ " "
          ++
            ( PLC.bring (Proxy @AgdaUnparse) type1
            $ PLC.bring (Proxy @AgdaUnparse) type2
            $ agdaUnparse val
            )
        PLC.ValueOf PLC.DefaultUniBLS12_381_G1_Element val ->
          "bls12-381-g1-element " ++  agdaUnparse val
        PLC.ValueOf PLC.DefaultUniBLS12_381_G2_Element val ->
          "bls12-381-g2-element " ++  agdaUnparse val
        PLC.ValueOf PLC.DefaultUniBLS12_381_MlResult val ->
          "bls12-381-mlresult " ++ agdaUnparse val
        PLC.ValueOf univ@(PLC.DefaultUniArray elemType)  val ->
          agdaUnparse univ
          ++ " "
          ++
            ( PLC.bring (Proxy @AgdaUnparse) elemType
            $ agdaUnparse val
            )
        PLC.ValueOf (PLC.DefaultUniApply _ _) _ ->
          error "Application of an unknown type is not supported."
    ++ ")"
