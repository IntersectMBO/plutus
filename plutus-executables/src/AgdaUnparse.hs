module AgdaUnparse where

import Data.ByteString (ByteString)
import Data.Functor.Identity
import Data.Text (Text)
import Data.Text qualified as T
import PlutusCore qualified as PLC
import PlutusCore.Crypto.BLS12_381.G1 qualified as BLS12_381.G1
import PlutusCore.Crypto.BLS12_381.G2 qualified as BLS12_381.G2
import PlutusCore.Crypto.BLS12_381.Pairing qualified as BLS12_381.Pairing
import PlutusCore.Data (Data)
import PlutusCore.Data qualified as Data
import PlutusCore.Default (DSum (..))
import PlutusPrelude
import Untyped qualified as AgdaFFI
import UntypedPlutusCore qualified as UPLC
import UntypedPlutusCore.Transform.Simplifier

-- | A class for types that can be unparsed to Agda code.
class AgdaUnparse a where
  agdaUnparse :: a -> String

instance AgdaUnparse AgdaFFI.UTerm where
  agdaUnparse =
    \case
      AgdaFFI.UVar n -> "(UVar " ++ agdaUnparse (fromInteger n :: Natural) ++ ")"
      AgdaFFI.ULambda term -> "(ULambda " ++ agdaUnparse term ++ ")"
      AgdaFFI.UApp t u -> "(UApp " ++ agdaUnparse t ++ " " ++ agdaUnparse u ++ ")"
      AgdaFFI.UCon someValue -> "(UCon " ++ (agdaUnparseValue . mkValueDSum) someValue ++ ")"
      AgdaFFI.UError -> "UError"
      AgdaFFI.UBuiltin fun -> "(UBuiltin " ++ agdaUnparse fun ++ ")"
      AgdaFFI.UDelay term -> "(UDelay " ++ agdaUnparse term ++ ")"
      AgdaFFI.UForce term -> "(UForce " ++ agdaUnparse term ++ ")"
      AgdaFFI.UConstr i terms -> "(UConstr " ++ agdaUnparse i ++ " " ++ agdaUnparse terms ++ ")"
      AgdaFFI.UCase term cases -> "(UCase " ++ agdaUnparse term ++ " " ++ agdaUnparse cases ++ ")"

instance AgdaUnparse UPLC.DefaultFun where
  agdaUnparse = lowerInitialChar . show

instance AgdaUnparse SimplifierStage where
  agdaUnparse FloatDelay = "floatDelayT"
  agdaUnparse ForceDelay = "forceDelayT"
  agdaUnparse CaseOfCase = "caseOfCaseT"
  agdaUnparse CaseReduce = "caseReduceT"
  agdaUnparse Inline     = "inlineT"
  agdaUnparse CSE        = "cseT"

instance AgdaUnparse Natural where
  agdaUnparse = show

instance AgdaUnparse Integer where
  agdaUnparse x = "(ℤ.pos " ++ show x ++ ")"

instance AgdaUnparse Bool where
  agdaUnparse True  = "true"
  agdaUnparse False = "false"

instance AgdaUnparse Char where
  agdaUnparse c = [c]
instance AgdaUnparse Text where
  agdaUnparse = T.unpack

instance AgdaUnparse ByteString where
  agdaUnparse = show  -- TODO: maybe this should be encoded some other way

instance AgdaUnparse () where
  agdaUnparse _ = "tt"

instance AgdaUnparse a => AgdaUnparse [a] where
  agdaUnparse l = "(" ++ foldr (\x xs -> agdaUnparse x ++ " ∷ " ++ xs) "[]" l ++ ")"

instance (AgdaUnparse a, AgdaUnparse b) => AgdaUnparse (a, b) where
  agdaUnparse (x, y) = "(" ++ agdaUnparse x ++ " , " ++ agdaUnparse y ++ ")"

instance AgdaUnparse Data where
  agdaUnparse (Data.Constr i args) =
    "(ConstrDATA" ++ " " ++ agdaUnparse i ++ " " ++ agdaUnparse args ++ ")"
  agdaUnparse (Data.Map assocList) =
    "(MapDATA" ++ " " ++ agdaUnparse assocList ++ ")"
  agdaUnparse (Data.List xs) =
    "(ListDATA" ++ " " ++ agdaUnparse xs ++ ")"
  agdaUnparse (Data.I i) =
    "(iDATA" ++ " " ++ agdaUnparse i ++ ")"
  agdaUnparse (Data.B b) =
    "(bDATA" ++ " " ++ agdaUnparse b ++ ")"

instance AgdaUnparse BLS12_381.G1.Element where
  agdaUnparse = show

instance AgdaUnparse BLS12_381.G2.Element where
  agdaUnparse = show

instance AgdaUnparse BLS12_381.Pairing.MlResult where
  agdaUnparse = show

agdaUnparseValue :: DSum (PLC.ValueOf UPLC.DefaultUni) Identity -> String
agdaUnparseValue dSum =
  "(tagCon " ++
    case dSum of
      PLC.ValueOf PLC.DefaultUniInteger _ :=> Identity val ->
        "integer " ++ agdaUnparse val
      PLC.ValueOf PLC.DefaultUniByteString _ :=> Identity val ->
        "bytestring " ++ agdaUnparse val
      PLC.ValueOf PLC.DefaultUniString _ :=> Identity val ->
        "string " ++ agdaUnparse val
      PLC.ValueOf PLC.DefaultUniBool _ :=> Identity val ->
        "bool " ++ agdaUnparse val
      PLC.ValueOf PLC.DefaultUniUnit _ :=> Identity _ ->
        "unit " ++ agdaUnparse ()
      PLC.ValueOf PLC.DefaultUniData _ :=> Identity val ->
        "pdata " ++ agdaUnparse val
      PLC.ValueOf (PLC.DefaultUniList elemType) _ :=> Identity val ->
        "list " ++ agdaUnparseDList elemType val
      PLC.ValueOf (PLC.DefaultUniPair type1 type2) _ :=> Identity val ->
        "pair " ++ agdaUnparseDPair type1 type2 val
      PLC.ValueOf PLC.DefaultUniBLS12_381_G1_Element _ :=> Identity val ->
        "bls12-381-g1-element " ++  agdaUnparse val
      PLC.ValueOf PLC.DefaultUniBLS12_381_G2_Element _ :=> Identity val ->
        "bls12-381-g2-element " ++  agdaUnparse val
      PLC.ValueOf PLC.DefaultUniBLS12_381_MlResult _ :=> Identity val ->
        "bls12-381-mlresult " ++ agdaUnparse val
      _ -> error "agdaUnparseValue: unexpected value"
  ++ ")"
  where
    agdaUnparseDList elemType xs =
      let xs' :: [DSum (PLC.ValueOf PLC.DefaultUni) Identity]
          xs' = mkValueDSum . PLC.Some . PLC.ValueOf elemType <$> xs
        in agdaUnparse $ agdaUnparseValue <$> xs'
    agdaUnparseDPair type1 type2 (x, y) =
      let x' = mkValueDSum $ PLC.Some $ PLC.ValueOf type1 x
          y' = mkValueDSum $ PLC.Some $ PLC.ValueOf type2 y
        in agdaUnparse (agdaUnparseValue x', agdaUnparseValue y')

mkValueDSum :: PLC.Some (PLC.ValueOf UPLC.DefaultUni) -> DSum (PLC.ValueOf UPLC.DefaultUni) Identity
mkValueDSum (PLC.Some valueOf@(PLC.ValueOf _ a)) = valueOf :=> Identity a
