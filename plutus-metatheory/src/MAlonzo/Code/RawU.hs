{-# LANGUAGE BangPatterns              #-}
{-# LANGUAGE EmptyCase                 #-}
{-# LANGUAGE EmptyDataDecls            #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE OverloadedStrings         #-}
{-# LANGUAGE PatternSynonyms           #-}
{-# LANGUAGE RankNTypes                #-}
{-# LANGUAGE ScopedTypeVariables       #-}

{-# OPTIONS_GHC -Wno-overlapping-patterns #-}
{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
{-# LANGUAGE GADTs                     #-}

module MAlonzo.Code.RawU where

import Data.Text qualified
import MAlonzo.Code.Agda.Builtin.Bool qualified
import MAlonzo.Code.Agda.Builtin.Equality qualified
import MAlonzo.Code.Agda.Builtin.Sigma qualified
import MAlonzo.Code.Agda.Builtin.String qualified
import MAlonzo.Code.Agda.Builtin.Unit qualified
import MAlonzo.Code.Builtin qualified
import MAlonzo.Code.Builtin.Constant.AtomicType qualified
import MAlonzo.Code.Builtin.Signature qualified
import MAlonzo.Code.Data.Bool.Base qualified
import MAlonzo.Code.Data.Bool.Properties qualified
import MAlonzo.Code.Data.Integer.Properties qualified
import MAlonzo.Code.Data.String.Properties qualified
import MAlonzo.Code.Relation.Nullary.Decidable.Core qualified
import MAlonzo.Code.Relation.Nullary.Reflects qualified
import MAlonzo.Code.Type qualified
import MAlonzo.Code.Type.BetaNormal qualified
import MAlonzo.Code.Utils qualified
import MAlonzo.Code.Utils.Decidable qualified
import MAlonzo.RTE (AgdaAny, add64, addInt, coe, eq64, eqInt, erased, geqInt, lt64, ltInt, mul64,
                    mulInt, quot64, quotInt, rem64, remInt, sub64, subInt, word64FromNat,
                    word64ToNat)
import MAlonzo.RTE qualified

import FFI.Untyped
import PlutusCore
import Raw
type Tag = DefaultUni
pattern TagInt                  = DefaultUniInteger
pattern TagBS                   = DefaultUniByteString
pattern TagStr                  = DefaultUniString
pattern TagBool                 = DefaultUniBool
pattern TagUnit                 = DefaultUniUnit
pattern TagData                 = DefaultUniData
pattern TagPair ta tb           = DefaultUniPair ta tb
pattern TagList ta              = DefaultUniList ta
pattern TagBLS12_381_G1_Element = DefaultUniBLS12_381_G1_Element
pattern TagBLS12_381_G2_Element = DefaultUniBLS12_381_G2_Element
pattern TagBLS12_381_MlResult   = DefaultUniBLS12_381_MlResult
type TagCon = Some (ValueOf DefaultUni)
pattern TagCon t x = Some (ValueOf t x)
-- RawU._.SigTy
d_SigTy_4 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 = ()
-- RawU._.convSigTy
d_convSigTy_6 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Utils.T__'8724'_'8803'__120 ->
  MAlonzo.Code.Utils.T__'8724'_'8803'__120 ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Utils.T__'8724'_'8803'__120 ->
  MAlonzo.Code.Utils.T__'8724'_'8803'__120 ->
  Integer ->
  Integer ->
  MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
  MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Builtin.Signature.T_SigTy_260 ->
  MAlonzo.Code.Builtin.Signature.T_SigTy_260
d_convSigTy_6 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11
              ~v12 ~v13 ~v14 v15
  = du_convSigTy_6 v15
du_convSigTy_6 ::
  MAlonzo.Code.Builtin.Signature.T_SigTy_260 ->
  MAlonzo.Code.Builtin.Signature.T_SigTy_260
du_convSigTy_6 v0 = coe v0
-- RawU._.sig2type
d_sig2type_8 ::
  MAlonzo.Code.Builtin.Signature.T_Sig_68 ->
  MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4
d_sig2type_8
  = coe
      MAlonzo.Code.Builtin.Signature.du_sig2type_236
      (\ v0 v1 v2 -> coe MAlonzo.Code.Type.BetaNormal.C_ne_20 v2)
      (coe
         (\ v0 v1 v2 v3 -> coe MAlonzo.Code.Type.BetaNormal.C_'96'_8 v3))
      (\ v0 v1 v2 v3 v4 ->
         coe MAlonzo.Code.Type.BetaNormal.C__'183'__10 v1 v3 v4)
      (coe (\ v0 v1 -> coe MAlonzo.Code.Type.BetaNormal.C_'94'_12))
      (\ v0 v1 -> coe MAlonzo.Code.Type.BetaNormal.C_con_22 v1)
      (\ v0 v1 v2 ->
         coe MAlonzo.Code.Type.BetaNormal.C__'8658'__16 v1 v2)
      (\ v0 v1 v2 -> coe MAlonzo.Code.Type.BetaNormal.C_Π_14 v1 v2)
-- RawU._.sigTy2type
d_sigTy2type_10 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
  MAlonzo.Code.Utils.T__'8724'_'8803'__120 ->
  MAlonzo.Code.Utils.T__'8724'_'8803'__120 ->
  MAlonzo.Code.Builtin.Signature.T_SigTy_260 ->
  MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4
d_sigTy2type_10 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 ~v8 ~v9 ~v10
  = du_sigTy2type_10 v7
du_sigTy2type_10 ::
  MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
  MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4
du_sigTy2type_10 v0 = coe v0
-- RawU._.⊢♯2TyNe♯
d_'8866''9839'2TyNe'9839'_12 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Builtin.Signature.T__'8866''9839'_4 ->
  MAlonzo.Code.Type.BetaNormal.T__'8866'Ne'8902'__6
d_'8866''9839'2TyNe'9839'_12
  = coe
      MAlonzo.Code.Builtin.Signature.du_'8866''9839'2TyNe'9839'_182
      (\ v0 v1 v2 -> coe MAlonzo.Code.Type.BetaNormal.C_ne_20 v2)
      (coe
         (\ v0 v1 v2 v3 -> coe MAlonzo.Code.Type.BetaNormal.C_'96'_8 v3))
      (\ v0 v1 v2 v3 v4 ->
         coe MAlonzo.Code.Type.BetaNormal.C__'183'__10 v1 v3 v4)
      (coe (\ v0 v1 -> coe MAlonzo.Code.Type.BetaNormal.C_'94'_12))
-- RawU.Esc
d_Esc_24 a0 = ()
type T_Esc_24 a0 = Esc a0
cover_Esc_24 :: Esc a1 -> ()
cover_Esc_24 x = case x of
-- RawU.Tag
d_Tag_28 a0 = ()
type T_Tag_28 = Tag
pattern C_integer_30 = TagInt
pattern C_bytestring_32 = TagBS
pattern C_string_34 = TagStr
pattern C_bool_36 = TagBool
pattern C_unit_38 = TagUnit
pattern C_pdata_40 = TagData
pattern C_pair_46 a0 a1 = TagPair a0 a1
pattern C_list_50 a0 = TagList a0
pattern C_bls12'45'381'45'g1'45'element_52 = TagBLS12_381_G1_Element
pattern C_bls12'45'381'45'g2'45'element_54 = TagBLS12_381_G2_Element
pattern C_bls12'45'381'45'mlresult_56 = TagBLS12_381_MlResult
check_integer_30 :: T_Tag_28 (T_Esc_24 Integer)
check_integer_30 = TagInt
check_bytestring_32 ::
  T_Tag_28 (T_Esc_24 MAlonzo.Code.Utils.T_ByteString_356)
check_bytestring_32 = TagBS
check_string_34 ::
  T_Tag_28 (T_Esc_24 MAlonzo.Code.Agda.Builtin.String.T_String_6)
check_string_34 = TagStr
check_bool_36 :: T_Tag_28 (T_Esc_24 Bool)
check_bool_36 = TagBool
check_unit_38 ::
  T_Tag_28 (T_Esc_24 MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6)
check_unit_38 = TagUnit
check_pdata_40 :: T_Tag_28 (T_Esc_24 MAlonzo.Code.Utils.T_DATA_478)
check_pdata_40 = TagData
check_pair_46 ::
  forall xA.
    forall xB.
      T_Tag_28 (T_Esc_24 xA) ->
      T_Tag_28 (T_Esc_24 xB) ->
      T_Tag_28 (T_Esc_24 (MAlonzo.Code.Utils.T__'215'__366 xA xB))
check_pair_46 = TagPair
check_list_50 ::
  forall xA.
    T_Tag_28 (T_Esc_24 xA) ->
    T_Tag_28 (T_Esc_24 (MAlonzo.Code.Utils.T_List_384 xA))
check_list_50 = TagList
check_bls12'45'381'45'g1'45'element_52 ::
  T_Tag_28
    (T_Esc_24 MAlonzo.Code.Utils.T_Bls12'45'381'45'G1'45'Element_624)
check_bls12'45'381'45'g1'45'element_52 = TagBLS12_381_G1_Element
check_bls12'45'381'45'g2'45'element_54 ::
  T_Tag_28
    (T_Esc_24 MAlonzo.Code.Utils.T_Bls12'45'381'45'G2'45'Element_628)
check_bls12'45'381'45'g2'45'element_54 = TagBLS12_381_G2_Element
check_bls12'45'381'45'mlresult_56 ::
  T_Tag_28
    (T_Esc_24 MAlonzo.Code.Utils.T_Bls12'45'381'45'MlResult_632)
check_bls12'45'381'45'mlresult_56 = TagBLS12_381_MlResult
cover_Tag_28 :: Tag a1 -> ()
cover_Tag_28 x
  = case x of
      TagInt                  -> ()
      TagBS                   -> ()
      TagStr                  -> ()
      TagBool                 -> ()
      TagUnit                 -> ()
      TagData                 -> ()
      TagPair _ _             -> ()
      TagList _               -> ()
      TagBLS12_381_G1_Element -> ()
      TagBLS12_381_G2_Element -> ()
      TagBLS12_381_MlResult   -> ()
-- RawU.TagCon
d_TagCon_58 = ()
type T_TagCon_58 = TagCon
pattern C_tagCon_62 a0 a1 = TagCon a0 a1
check_tagCon_62 ::
  forall xA. T_Tag_28 (T_Esc_24 xA) -> xA -> T_TagCon_58
check_tagCon_62 = TagCon
cover_TagCon_58 :: TagCon -> ()
cover_TagCon_58 x
  = case x of
      TagCon _ _ -> ()
-- RawU.decTagCon'
d_decTagCon''_76 ::
  () ->
  () ->
  T_Tag_28 (T_Esc_24 AgdaAny) ->
  AgdaAny -> T_Tag_28 (T_Esc_24 AgdaAny) -> AgdaAny -> Bool
d_decTagCon''_76 ~v0 ~v1 v2 v3 v4 v5
  = du_decTagCon''_76 v2 v3 v4 v5
du_decTagCon''_76 ::
  T_Tag_28 (T_Esc_24 AgdaAny) ->
  AgdaAny -> T_Tag_28 (T_Esc_24 AgdaAny) -> AgdaAny -> Bool
du_decTagCon''_76 v0 v1 v2 v3
  = let v4 = coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8 in
    coe
      (case coe v0 of
         C_integer_30
           -> case coe v2 of
                C_integer_30
                  -> coe
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
                       (coe
                          MAlonzo.Code.Data.Integer.Properties.d__'8799'__2692 (coe v1)
                          (coe v3))
                _ -> coe v4
         C_bytestring_32
           -> case coe v2 of
                C_bytestring_32 -> coe MAlonzo.Code.Builtin.d_equals_328 v1 v3
                _               -> coe v4
         C_string_34
           -> case coe v2 of
                C_string_34
                  -> coe
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
                       (coe
                          MAlonzo.Code.Data.String.Properties.d__'8799'__54 (coe v1)
                          (coe v3))
                _ -> coe v4
         C_bool_36
           -> case coe v2 of
                C_bool_36
                  -> coe
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
                       (coe
                          MAlonzo.Code.Data.Bool.Properties.d__'8799'__3082 (coe v1)
                          (coe v3))
                _ -> coe v4
         C_unit_38
           -> case coe v2 of
                C_unit_38 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
                _         -> coe v4
         C_pdata_40
           -> case coe v2 of
                C_pdata_40 -> coe MAlonzo.Code.Utils.d_eqDATA_490 (coe v1) (coe v3)
                _          -> coe v4
         C_pair_46 v7 v8
           -> case coe v1 of
                MAlonzo.Code.Utils.C__'44'__380 v9 v10
                  -> case coe v2 of
                       C_pair_46 v13 v14
                         -> case coe v3 of
                              MAlonzo.Code.Utils.C__'44'__380 v15 v16
                                -> coe
                                     MAlonzo.Code.Data.Bool.Base.d__'8743'__24
                                     (coe du_decTagCon''_76 (coe v7) (coe v9) (coe v13) (coe v15))
                                     (coe du_decTagCon''_76 (coe v8) (coe v10) (coe v14) (coe v16))
                              _ -> MAlonzo.RTE.mazUnreachableError
                       _ -> coe v4
                _ -> MAlonzo.RTE.mazUnreachableError
         C_list_50 v6
           -> case coe v1 of
                MAlonzo.Code.Utils.C_'91''93'_388
                  -> case coe v2 of
                       C_list_50 v8
                         -> case coe v3 of
                              MAlonzo.Code.Utils.C_'91''93'_388
                                -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
                              _ -> coe v4
                       _ -> coe v4
                MAlonzo.Code.Utils.C__'8759'__390 v7 v8
                  -> case coe v2 of
                       C_list_50 v10
                         -> case coe v3 of
                              MAlonzo.Code.Utils.C__'8759'__390 v11 v12
                                -> coe
                                     MAlonzo.Code.Data.Bool.Base.d__'8743'__24
                                     (coe du_decTagCon''_76 (coe v6) (coe v7) (coe v10) (coe v11))
                                     (coe
                                        du_decTagCon''_76 (coe C_list_50 v6) (coe v8)
                                        (coe C_list_50 v10) (coe v12))
                              _ -> coe v4
                       _ -> coe v4
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> coe v4)
-- RawU.decTagCon
d_decTagCon_136 :: T_TagCon_58 -> T_TagCon_58 -> Bool
d_decTagCon_136 v0 v1
  = case coe v0 of
      C_tagCon_62 v3 v4
        -> case coe v1 of
             C_tagCon_62 v6 v7
               -> coe du_decTagCon''_76 (coe v3) (coe v4) (coe v6) (coe v7)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- RawU.Untyped
d_Untyped_146 = ()
type T_Untyped_146 = UTerm
pattern C_UVar_148 a0 = UVar a0
pattern C_ULambda_150 a0 = ULambda a0
pattern C_UApp_152 a0 a1 = UApp a0 a1
pattern C_UCon_154 a0 = UCon a0
pattern C_UError_156 = UError
pattern C_UBuiltin_158 a0 = UBuiltin a0
pattern C_UDelay_160 a0 = UDelay a0
pattern C_UForce_162 a0 = UForce a0
pattern C_UConstr_164 a0 a1 = UConstr a0 a1
pattern C_UCase_166 a0 a1 = UCase a0 a1
check_UVar_148 :: Integer -> T_Untyped_146
check_UVar_148 = UVar
check_ULambda_150 :: T_Untyped_146 -> T_Untyped_146
check_ULambda_150 = ULambda
check_UApp_152 :: T_Untyped_146 -> T_Untyped_146 -> T_Untyped_146
check_UApp_152 = UApp
check_UCon_154 :: T_TagCon_58 -> T_Untyped_146
check_UCon_154 = UCon
check_UError_156 :: T_Untyped_146
check_UError_156 = UError
check_UBuiltin_158 ::
  MAlonzo.Code.Builtin.T_Builtin_2 -> T_Untyped_146
check_UBuiltin_158 = UBuiltin
check_UDelay_160 :: T_Untyped_146 -> T_Untyped_146
check_UDelay_160 = UDelay
check_UForce_162 :: T_Untyped_146 -> T_Untyped_146
check_UForce_162 = UForce
check_UConstr_164 ::
  Integer ->
  MAlonzo.Code.Utils.T_List_384 T_Untyped_146 -> T_Untyped_146
check_UConstr_164 = UConstr
check_UCase_166 ::
  T_Untyped_146 ->
  MAlonzo.Code.Utils.T_List_384 T_Untyped_146 -> T_Untyped_146
check_UCase_166 = UCase
cover_Untyped_146 :: UTerm -> ()
cover_Untyped_146 x
  = case x of
      UVar _      -> ()
      ULambda _   -> ()
      UApp _ _    -> ()
      UCon _      -> ()
      UError      -> ()
      UBuiltin _  -> ()
      UDelay _    -> ()
      UForce _    -> ()
      UConstr _ _ -> ()
      UCase _ _   -> ()
-- RawU.TyTag
d_TyTag_168 :: ()
d_TyTag_168 = erased
-- RawU.⟦_⟧tag
d_'10214'_'10215'tag_170 ::
  MAlonzo.Code.Builtin.Signature.T__'8866''9839'_4 -> ()
d_'10214'_'10215'tag_170 = erased
-- RawU.decTag
d_decTag_174 ::
  MAlonzo.Code.Builtin.Signature.T__'8866''9839'_4 ->
  MAlonzo.Code.Builtin.Signature.T__'8866''9839'_4 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_decTag_174 v0 v1
  = case coe v0 of
      MAlonzo.Code.Builtin.Signature.C_atomic_12 v3
        -> case coe v1 of
             MAlonzo.Code.Builtin.Signature.C_atomic_12 v5
               -> coe
                    MAlonzo.Code.Utils.Decidable.du_dcong_40
                    (MAlonzo.Code.Builtin.Constant.AtomicType.d_decAtomicTyCon_26
                       (coe v3) (coe v5))
             MAlonzo.Code.Builtin.Signature.C_list_16 v5
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Builtin.Signature.C_pair_20 v5 v6
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Builtin.Signature.C_list_16 v3
        -> case coe v1 of
             MAlonzo.Code.Builtin.Signature.C_atomic_12 v5
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Builtin.Signature.C_list_16 v5
               -> coe
                    MAlonzo.Code.Utils.Decidable.du_dcong_40
                    (d_decTag_174 (coe v3) (coe v5))
             MAlonzo.Code.Builtin.Signature.C_pair_20 v5 v6
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Builtin.Signature.C_pair_20 v3 v4
        -> case coe v1 of
             MAlonzo.Code.Builtin.Signature.C_atomic_12 v6
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Builtin.Signature.C_list_16 v6
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Builtin.Signature.C_pair_20 v6 v7
               -> coe
                    MAlonzo.Code.Utils.Decidable.du_dcong'8322'_70
                    (coe d_decTag_174 (coe v3) (coe v6))
                    (coe d_decTag_174 (coe v4) (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- RawU.TmCon
d_TmCon_198 = ()
data T_TmCon_198
  = C_tmCon_202 MAlonzo.Code.Builtin.Signature.T__'8866''9839'_4
                AgdaAny
-- RawU.tag2TyTag
d_tag2TyTag_206 ::
  () ->
  T_Tag_28 AgdaAny ->
  MAlonzo.Code.Builtin.Signature.T__'8866''9839'_4
d_tag2TyTag_206 ~v0 v1 = du_tag2TyTag_206 v1
du_tag2TyTag_206 ::
  T_Tag_28 AgdaAny ->
  MAlonzo.Code.Builtin.Signature.T__'8866''9839'_4
du_tag2TyTag_206 v0
  = case coe v0 of
      C_integer_30
        -> coe
             MAlonzo.Code.Builtin.Signature.C_atomic_12
             (coe MAlonzo.Code.Builtin.Constant.AtomicType.C_aInteger_8)
      C_bytestring_32
        -> coe
             MAlonzo.Code.Builtin.Signature.C_atomic_12
             (coe MAlonzo.Code.Builtin.Constant.AtomicType.C_aBytestring_10)
      C_string_34
        -> coe
             MAlonzo.Code.Builtin.Signature.C_atomic_12
             (coe MAlonzo.Code.Builtin.Constant.AtomicType.C_aString_12)
      C_bool_36
        -> coe
             MAlonzo.Code.Builtin.Signature.C_atomic_12
             (coe MAlonzo.Code.Builtin.Constant.AtomicType.C_aBool_16)
      C_unit_38
        -> coe
             MAlonzo.Code.Builtin.Signature.C_atomic_12
             (coe MAlonzo.Code.Builtin.Constant.AtomicType.C_aUnit_14)
      C_pdata_40
        -> coe
             MAlonzo.Code.Builtin.Signature.C_atomic_12
             (coe MAlonzo.Code.Builtin.Constant.AtomicType.C_aData_18)
      C_pair_46 v3 v4
        -> coe
             MAlonzo.Code.Builtin.Signature.C_pair_20
             (coe du_tag2TyTag_206 (coe v3)) (coe du_tag2TyTag_206 (coe v4))
      C_list_50 v2
        -> coe
             MAlonzo.Code.Builtin.Signature.C_list_16
             (coe du_tag2TyTag_206 (coe v2))
      C_bls12'45'381'45'g1'45'element_52
        -> coe
             MAlonzo.Code.Builtin.Signature.C_atomic_12
             (coe
                MAlonzo.Code.Builtin.Constant.AtomicType.C_aBls12'45'381'45'g1'45'element_20)
      C_bls12'45'381'45'g2'45'element_54
        -> coe
             MAlonzo.Code.Builtin.Signature.C_atomic_12
             (coe
                MAlonzo.Code.Builtin.Constant.AtomicType.C_aBls12'45'381'45'g2'45'element_22)
      C_bls12'45'381'45'mlresult_56
        -> coe
             MAlonzo.Code.Builtin.Signature.C_atomic_12
             (coe
                MAlonzo.Code.Builtin.Constant.AtomicType.C_aBls12'45'381'45'mlresult_24)
      _ -> MAlonzo.RTE.mazUnreachableError
-- RawU.tagLemma
d_tagLemma_218 ::
  () ->
  T_Tag_28 (T_Esc_24 AgdaAny) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_tagLemma_218 = erased
-- RawU.tagCon2TmCon
d_tagCon2TmCon_226 :: T_TagCon_58 -> T_TmCon_198
d_tagCon2TmCon_226 v0
  = case coe v0 of
      C_tagCon_62 v2 v3
        -> case coe v2 of
             C_integer_30
               -> coe
                    C_tmCon_202
                    (coe
                       MAlonzo.Code.Builtin.Signature.C_atomic_12
                       (coe MAlonzo.Code.Builtin.Constant.AtomicType.C_aInteger_8))
                    (coe v3)
             C_bytestring_32
               -> coe
                    C_tmCon_202
                    (coe
                       MAlonzo.Code.Builtin.Signature.C_atomic_12
                       (coe MAlonzo.Code.Builtin.Constant.AtomicType.C_aBytestring_10))
                    (coe v3)
             C_string_34
               -> coe
                    C_tmCon_202
                    (coe
                       MAlonzo.Code.Builtin.Signature.C_atomic_12
                       (coe MAlonzo.Code.Builtin.Constant.AtomicType.C_aString_12))
                    (coe v3)
             C_bool_36
               -> coe
                    C_tmCon_202
                    (coe
                       MAlonzo.Code.Builtin.Signature.C_atomic_12
                       (coe MAlonzo.Code.Builtin.Constant.AtomicType.C_aBool_16))
                    (coe v3)
             C_unit_38
               -> coe
                    C_tmCon_202
                    (coe
                       MAlonzo.Code.Builtin.Signature.C_atomic_12
                       (coe MAlonzo.Code.Builtin.Constant.AtomicType.C_aUnit_14))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             C_pdata_40
               -> coe
                    C_tmCon_202
                    (coe
                       MAlonzo.Code.Builtin.Signature.C_atomic_12
                       (coe MAlonzo.Code.Builtin.Constant.AtomicType.C_aData_18))
                    (coe v3)
             C_pair_46 v6 v7
               -> coe
                    seq (coe v3)
                    (coe
                       C_tmCon_202
                       (coe
                          MAlonzo.Code.Builtin.Signature.C_pair_20
                          (coe du_tag2TyTag_206 (coe v6)) (coe du_tag2TyTag_206 (coe v7)))
                       (coe v3))
             C_list_50 v5
               -> coe
                    C_tmCon_202
                    (coe
                       MAlonzo.Code.Builtin.Signature.C_list_16
                       (coe du_tag2TyTag_206 (coe v5)))
                    (coe v3)
             C_bls12'45'381'45'g1'45'element_52
               -> coe
                    C_tmCon_202
                    (coe
                       MAlonzo.Code.Builtin.Signature.C_atomic_12
                       (coe
                          MAlonzo.Code.Builtin.Constant.AtomicType.C_aBls12'45'381'45'g1'45'element_20))
                    (coe v3)
             C_bls12'45'381'45'g2'45'element_54
               -> coe
                    C_tmCon_202
                    (coe
                       MAlonzo.Code.Builtin.Signature.C_atomic_12
                       (coe
                          MAlonzo.Code.Builtin.Constant.AtomicType.C_aBls12'45'381'45'g2'45'element_22))
                    (coe v3)
             C_bls12'45'381'45'mlresult_56
               -> coe
                    C_tmCon_202
                    (coe
                       MAlonzo.Code.Builtin.Signature.C_atomic_12
                       (coe
                          MAlonzo.Code.Builtin.Constant.AtomicType.C_aBls12'45'381'45'mlresult_24))
                    (coe v3)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- RawU.tyTag2Tag
d_tyTag2Tag_272 ::
  MAlonzo.Code.Builtin.Signature.T__'8866''9839'_4 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_tyTag2Tag_272 v0
  = case coe v0 of
      MAlonzo.Code.Builtin.Signature.C_atomic_12 v2
        -> case coe v2 of
             MAlonzo.Code.Builtin.Constant.AtomicType.C_aInteger_8
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                    (coe C_integer_30)
             MAlonzo.Code.Builtin.Constant.AtomicType.C_aBytestring_10
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                    (coe C_bytestring_32)
             MAlonzo.Code.Builtin.Constant.AtomicType.C_aString_12
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                    (coe C_string_34)
             MAlonzo.Code.Builtin.Constant.AtomicType.C_aUnit_14
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased (coe C_unit_38)
             MAlonzo.Code.Builtin.Constant.AtomicType.C_aBool_16
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased (coe C_bool_36)
             MAlonzo.Code.Builtin.Constant.AtomicType.C_aData_18
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased (coe C_pdata_40)
             MAlonzo.Code.Builtin.Constant.AtomicType.C_aBls12'45'381'45'g1'45'element_20
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                    (coe C_bls12'45'381'45'g1'45'element_52)
             MAlonzo.Code.Builtin.Constant.AtomicType.C_aBls12'45'381'45'g2'45'element_22
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                    (coe C_bls12'45'381'45'g2'45'element_54)
             MAlonzo.Code.Builtin.Constant.AtomicType.C_aBls12'45'381'45'mlresult_24
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                    (coe C_bls12'45'381'45'mlresult_56)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Builtin.Signature.C_list_16 v2
        -> let v3 = d_tyTag2Tag_272 (coe v2) in
           coe
             (case coe v3 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                       (coe C_list_50 v5)
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Builtin.Signature.C_pair_20 v2 v3
        -> let v4 = d_tyTag2Tag_272 (coe v2) in
           coe
             (let v5 = d_tyTag2Tag_272 (coe v3) in
              coe
                (case coe v4 of
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
                     -> case coe v5 of
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
                            -> coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                                 (coe C_pair_46 v7 v9)
                          _ -> MAlonzo.RTE.mazUnreachableError
                   _ -> MAlonzo.RTE.mazUnreachableError))
      _ -> MAlonzo.RTE.mazUnreachableError
-- RawU.tyTagLemma
d_tyTagLemma_308 ::
  MAlonzo.Code.Builtin.Signature.T__'8866''9839'_4 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_tyTagLemma_308 = erased
-- RawU.tmCon2TagCon
d_tmCon2TagCon_316 :: T_TmCon_198 -> T_TagCon_58
d_tmCon2TagCon_316 v0
  = case coe v0 of
      C_tmCon_202 v1 v2
        -> case coe v1 of
             MAlonzo.Code.Builtin.Signature.C_atomic_12 v4
               -> case coe v4 of
                    MAlonzo.Code.Builtin.Constant.AtomicType.C_aInteger_8
                      -> coe C_tagCon_62 (coe C_integer_30) v2
                    MAlonzo.Code.Builtin.Constant.AtomicType.C_aBytestring_10
                      -> coe C_tagCon_62 (coe C_bytestring_32) v2
                    MAlonzo.Code.Builtin.Constant.AtomicType.C_aString_12
                      -> coe C_tagCon_62 (coe C_string_34) v2
                    MAlonzo.Code.Builtin.Constant.AtomicType.C_aUnit_14
                      -> coe
                           C_tagCon_62 (coe C_unit_38)
                           (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                    MAlonzo.Code.Builtin.Constant.AtomicType.C_aBool_16
                      -> coe C_tagCon_62 (coe C_bool_36) v2
                    MAlonzo.Code.Builtin.Constant.AtomicType.C_aData_18
                      -> coe C_tagCon_62 (coe C_pdata_40) v2
                    MAlonzo.Code.Builtin.Constant.AtomicType.C_aBls12'45'381'45'g1'45'element_20
                      -> coe C_tagCon_62 (coe C_bls12'45'381'45'g1'45'element_52) v2
                    MAlonzo.Code.Builtin.Constant.AtomicType.C_aBls12'45'381'45'g2'45'element_22
                      -> coe C_tagCon_62 (coe C_bls12'45'381'45'g2'45'element_54) v2
                    MAlonzo.Code.Builtin.Constant.AtomicType.C_aBls12'45'381'45'mlresult_24
                      -> coe C_tagCon_62 (coe C_bls12'45'381'45'mlresult_56) v2
                    _ -> MAlonzo.RTE.mazUnreachableError
             MAlonzo.Code.Builtin.Signature.C_list_16 v4
               -> coe
                    C_tagCon_62
                    (coe
                       C_list_50
                       (MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                          (coe d_tyTag2Tag_272 (coe v4))))
                    v2
             MAlonzo.Code.Builtin.Signature.C_pair_20 v4 v5
               -> coe
                    seq (coe v2)
                    (coe
                       C_tagCon_62
                       (coe
                          C_pair_46
                          (MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                             (coe d_tyTag2Tag_272 (coe v4)))
                          (MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                             (coe d_tyTag2Tag_272 (coe v5))))
                       v2)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
