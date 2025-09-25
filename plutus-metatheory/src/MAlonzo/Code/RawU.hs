{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

{-# OPTIONS_GHC -Wno-overlapping-patterns #-}
{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
{-# LANGUAGE GADTs #-}

module MAlonzo.Code.RawU where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Bool
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Agda.Builtin.Unit
import qualified MAlonzo.Code.Builtin
import qualified MAlonzo.Code.Builtin.Constant.AtomicType
import qualified MAlonzo.Code.Builtin.Signature
import qualified MAlonzo.Code.Data.Bool.Base
import qualified MAlonzo.Code.Data.Bool.Properties
import qualified MAlonzo.Code.Data.Integer.Properties
import qualified MAlonzo.Code.Data.String.Properties
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core
import qualified MAlonzo.Code.Relation.Nullary.Reflects
import qualified MAlonzo.Code.Type
import qualified MAlonzo.Code.Type.BetaNormal
import qualified MAlonzo.Code.Utils
import qualified MAlonzo.Code.Utils.Decidable

import PlutusCore
import Raw
import FFI.Untyped
type Tag = DefaultUni
pattern TagInt                  = DefaultUniInteger
pattern TagBS                   = DefaultUniByteString
pattern TagStr                  = DefaultUniString
pattern TagBool                 = DefaultUniBool
pattern TagUnit                 = DefaultUniUnit
pattern TagData                 = DefaultUniData
pattern TagValue                = DefaultUniValue
pattern TagPair ta tb           = DefaultUniPair ta tb
pattern TagList ta              = DefaultUniList ta
pattern TagArray ta              = DefaultUniArray ta
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
  MAlonzo.Code.Builtin.Signature.T_SigTy_268 ->
  MAlonzo.Code.Builtin.Signature.T_SigTy_268
d_convSigTy_6 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11
              ~v12 ~v13 ~v14 v15
  = du_convSigTy_6 v15
du_convSigTy_6 ::
  MAlonzo.Code.Builtin.Signature.T_SigTy_268 ->
  MAlonzo.Code.Builtin.Signature.T_SigTy_268
du_convSigTy_6 v0 = coe v0
-- RawU._.sig2type
d_sig2type_8 ::
  MAlonzo.Code.Builtin.Signature.T_Sig_74 ->
  MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4
d_sig2type_8
  = coe
      MAlonzo.Code.Builtin.Signature.du_sig2type_244
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
  MAlonzo.Code.Builtin.Signature.T_SigTy_268 ->
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
      MAlonzo.Code.Builtin.Signature.du_'8866''9839'2TyNe'9839'_188
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
pattern C_value_40 = TagData
pattern C_pdata_42 = TagValue
pattern C_pair_48 a0 a1 = TagPair a0 a1
pattern C_list_52 a0 = TagList a0
pattern C_array_56 a0 = TagArray a0
pattern C_bls12'45'381'45'g1'45'element_58 = TagBLS12_381_G1_Element
pattern C_bls12'45'381'45'g2'45'element_60 = TagBLS12_381_G2_Element
pattern C_bls12'45'381'45'mlresult_62 = TagBLS12_381_MlResult
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
check_value_40 ::
  T_Tag_28 (T_Esc_24 MAlonzo.Code.Utils.T_Value_362)
check_value_40 = TagData
check_pdata_42 :: T_Tag_28 (T_Esc_24 MAlonzo.Code.Utils.T_DATA_498)
check_pdata_42 = TagValue
check_pair_48 ::
  forall xA.
    forall xB.
      T_Tag_28 (T_Esc_24 xA) ->
      T_Tag_28 (T_Esc_24 xB) ->
      T_Tag_28 (T_Esc_24 (MAlonzo.Code.Utils.T__'215'__370 xA xB))
check_pair_48 = TagPair
check_list_52 ::
  forall xA.
    T_Tag_28 (T_Esc_24 xA) ->
    T_Tag_28 (T_Esc_24 (MAlonzo.Code.Utils.T_List_388 xA))
check_list_52 = TagList
check_array_56 ::
  forall xA.
    T_Tag_28 (T_Esc_24 xA) ->
    T_Tag_28 (T_Esc_24 (MAlonzo.Code.Utils.T_Array_482 xA))
check_array_56 = TagArray
check_bls12'45'381'45'g1'45'element_58 ::
  T_Tag_28
    (T_Esc_24 MAlonzo.Code.Utils.T_Bls12'45'381'45'G1'45'Element_644)
check_bls12'45'381'45'g1'45'element_58 = TagBLS12_381_G1_Element
check_bls12'45'381'45'g2'45'element_60 ::
  T_Tag_28
    (T_Esc_24 MAlonzo.Code.Utils.T_Bls12'45'381'45'G2'45'Element_648)
check_bls12'45'381'45'g2'45'element_60 = TagBLS12_381_G2_Element
check_bls12'45'381'45'mlresult_62 ::
  T_Tag_28
    (T_Esc_24 MAlonzo.Code.Utils.T_Bls12'45'381'45'MlResult_652)
check_bls12'45'381'45'mlresult_62 = TagBLS12_381_MlResult
cover_Tag_28 :: Tag a1 -> ()
cover_Tag_28 x
  = case x of
      TagInt -> ()
      TagBS -> ()
      TagStr -> ()
      TagBool -> ()
      TagUnit -> ()
      TagData -> ()
      TagValue -> ()
      TagPair _ _ -> ()
      TagList _ -> ()
      TagArray _ -> ()
      TagBLS12_381_G1_Element -> ()
      TagBLS12_381_G2_Element -> ()
      TagBLS12_381_MlResult -> ()
-- RawU.TyTag
d_TyTag_64 :: ()
d_TyTag_64 = erased
-- RawU.⟦_⟧tag
d_'10214'_'10215'tag_66 ::
  MAlonzo.Code.Builtin.Signature.T__'8866''9839'_4 -> ()
d_'10214'_'10215'tag_66 = erased
-- RawU.decTyTag
d_decTyTag_70 ::
  MAlonzo.Code.Builtin.Signature.T__'8866''9839'_4 ->
  MAlonzo.Code.Builtin.Signature.T__'8866''9839'_4 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_decTyTag_70 v0 v1
  = case coe v0 of
      MAlonzo.Code.Builtin.Signature.C_atomic_12 v3
        -> case coe v1 of
             MAlonzo.Code.Builtin.Signature.C_atomic_12 v5
               -> coe
                    MAlonzo.Code.Utils.Decidable.du_dcong_40
                    (MAlonzo.Code.Builtin.Constant.AtomicType.d_decAtomicTyCon_28
                       (coe v3) (coe v5))
             MAlonzo.Code.Builtin.Signature.C_list_16 v5
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Builtin.Signature.C_array_20 v5
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Builtin.Signature.C_pair_24 v5 v6
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
                    (d_decTyTag_70 (coe v3) (coe v5))
             MAlonzo.Code.Builtin.Signature.C_array_20 v5
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Builtin.Signature.C_pair_24 v5 v6
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Builtin.Signature.C_array_20 v3
        -> case coe v1 of
             MAlonzo.Code.Builtin.Signature.C_atomic_12 v5
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Builtin.Signature.C_list_16 v5
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Builtin.Signature.C_array_20 v5
               -> coe
                    MAlonzo.Code.Utils.Decidable.du_dcong_40
                    (d_decTyTag_70 (coe v3) (coe v5))
             MAlonzo.Code.Builtin.Signature.C_pair_24 v5 v6
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Builtin.Signature.C_pair_24 v3 v4
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
             MAlonzo.Code.Builtin.Signature.C_array_20 v6
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Builtin.Signature.C_pair_24 v6 v7
               -> coe
                    MAlonzo.Code.Utils.Decidable.du_dcong'8322'_70
                    (coe d_decTyTag_70 (coe v3) (coe v6))
                    (coe d_decTyTag_70 (coe v4) (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- RawU.TagCon
d_TagCon_108 = ()
type T_TagCon_108 = TagCon
pattern C_tagCon_112 a0 a1 = TagCon a0 a1
check_tagCon_112 ::
  forall xA. T_Tag_28 (T_Esc_24 xA) -> xA -> T_TagCon_108
check_tagCon_112 = TagCon
cover_TagCon_108 :: TagCon -> ()
cover_TagCon_108 x
  = case x of
      TagCon _ _ -> ()
-- RawU.decTagCon'
d_decTagCon''_126 ::
  () ->
  () ->
  T_Tag_28 (T_Esc_24 AgdaAny) ->
  AgdaAny -> T_Tag_28 (T_Esc_24 AgdaAny) -> AgdaAny -> Bool
d_decTagCon''_126 ~v0 ~v1 v2 v3 v4 v5
  = du_decTagCon''_126 v2 v3 v4 v5
du_decTagCon''_126 ::
  T_Tag_28 (T_Esc_24 AgdaAny) ->
  AgdaAny -> T_Tag_28 (T_Esc_24 AgdaAny) -> AgdaAny -> Bool
du_decTagCon''_126 v0 v1 v2 v3
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
                C_bytestring_32 -> coe MAlonzo.Code.Builtin.d_equals_342 v1 v3
                _ -> coe v4
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
                _ -> coe v4
         C_pdata_42
           -> case coe v2 of
                C_pdata_42 -> coe MAlonzo.Code.Utils.d_eqDATA_510 (coe v1) (coe v3)
                _ -> coe v4
         C_pair_48 v7 v8
           -> case coe v1 of
                MAlonzo.Code.Utils.C__'44'__384 v9 v10
                  -> case coe v2 of
                       C_pair_48 v13 v14
                         -> case coe v3 of
                              MAlonzo.Code.Utils.C__'44'__384 v15 v16
                                -> coe
                                     MAlonzo.Code.Data.Bool.Base.d__'8743'__24
                                     (coe du_decTagCon''_126 (coe v7) (coe v9) (coe v13) (coe v15))
                                     (coe du_decTagCon''_126 (coe v8) (coe v10) (coe v14) (coe v16))
                              _ -> MAlonzo.RTE.mazUnreachableError
                       _ -> coe v4
                _ -> MAlonzo.RTE.mazUnreachableError
         C_list_52 v6
           -> case coe v1 of
                MAlonzo.Code.Utils.C_'91''93'_392
                  -> case coe v2 of
                       C_list_52 v8
                         -> case coe v3 of
                              MAlonzo.Code.Utils.C_'91''93'_392
                                -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
                              _ -> coe v4
                       _ -> coe v4
                MAlonzo.Code.Utils.C__'8759'__394 v7 v8
                  -> case coe v2 of
                       C_list_52 v10
                         -> case coe v3 of
                              MAlonzo.Code.Utils.C__'8759'__394 v11 v12
                                -> coe
                                     MAlonzo.Code.Data.Bool.Base.d__'8743'__24
                                     (coe du_decTagCon''_126 (coe v6) (coe v7) (coe v10) (coe v11))
                                     (coe
                                        du_decTagCon''_126 (coe C_list_52 v6) (coe v8)
                                        (coe C_list_52 v10) (coe v12))
                              _ -> coe v4
                       _ -> coe v4
                _ -> MAlonzo.RTE.mazUnreachableError
         C_array_56 v6
           -> case coe v2 of
                C_array_56 v8 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
                _ -> coe v4
         _ -> coe v4)
-- RawU.decTagCon
d_decTagCon_194 :: T_TagCon_108 -> T_TagCon_108 -> Bool
d_decTagCon_194 v0 v1
  = case coe v0 of
      C_tagCon_112 v3 v4
        -> case coe v1 of
             C_tagCon_112 v6 v7
               -> coe du_decTagCon''_126 (coe v3) (coe v4) (coe v6) (coe v7)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- RawU.TmCon
d_TmCon_204 = ()
data T_TmCon_204
  = C_tmCon_208 MAlonzo.Code.Builtin.Signature.T__'8866''9839'_4
                AgdaAny
-- RawU.Untyped
d_Untyped_210 = ()
type T_Untyped_210 = UTerm
pattern C_UVar_212 a0 = UVar a0
pattern C_ULambda_214 a0 = ULambda a0
pattern C_UApp_216 a0 a1 = UApp a0 a1
pattern C_UCon_218 a0 = UCon a0
pattern C_UError_220 = UError
pattern C_UBuiltin_222 a0 = UBuiltin a0
pattern C_UDelay_224 a0 = UDelay a0
pattern C_UForce_226 a0 = UForce a0
pattern C_UConstr_228 a0 a1 = UConstr a0 a1
pattern C_UCase_230 a0 a1 = UCase a0 a1
check_UVar_212 :: Integer -> T_Untyped_210
check_UVar_212 = UVar
check_ULambda_214 :: T_Untyped_210 -> T_Untyped_210
check_ULambda_214 = ULambda
check_UApp_216 :: T_Untyped_210 -> T_Untyped_210 -> T_Untyped_210
check_UApp_216 = UApp
check_UCon_218 :: T_TagCon_108 -> T_Untyped_210
check_UCon_218 = UCon
check_UError_220 :: T_Untyped_210
check_UError_220 = UError
check_UBuiltin_222 ::
  MAlonzo.Code.Builtin.T_Builtin_2 -> T_Untyped_210
check_UBuiltin_222 = UBuiltin
check_UDelay_224 :: T_Untyped_210 -> T_Untyped_210
check_UDelay_224 = UDelay
check_UForce_226 :: T_Untyped_210 -> T_Untyped_210
check_UForce_226 = UForce
check_UConstr_228 ::
  Integer ->
  MAlonzo.Code.Utils.T_List_388 T_Untyped_210 -> T_Untyped_210
check_UConstr_228 = UConstr
check_UCase_230 ::
  T_Untyped_210 ->
  MAlonzo.Code.Utils.T_List_388 T_Untyped_210 -> T_Untyped_210
check_UCase_230 = UCase
cover_Untyped_210 :: UTerm -> ()
cover_Untyped_210 x
  = case x of
      UVar _ -> ()
      ULambda _ -> ()
      UApp _ _ -> ()
      UCon _ -> ()
      UError -> ()
      UBuiltin _ -> ()
      UDelay _ -> ()
      UForce _ -> ()
      UConstr _ _ -> ()
      UCase _ _ -> ()
-- RawU.tag2TyTag
d_tag2TyTag_234 ::
  () ->
  T_Tag_28 AgdaAny ->
  MAlonzo.Code.Builtin.Signature.T__'8866''9839'_4
d_tag2TyTag_234 ~v0 v1 = du_tag2TyTag_234 v1
du_tag2TyTag_234 ::
  T_Tag_28 AgdaAny ->
  MAlonzo.Code.Builtin.Signature.T__'8866''9839'_4
du_tag2TyTag_234 v0
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
      C_value_40
        -> coe
             MAlonzo.Code.Builtin.Signature.C_atomic_12
             (coe MAlonzo.Code.Builtin.Constant.AtomicType.C_aValue_20)
      C_pdata_42
        -> coe
             MAlonzo.Code.Builtin.Signature.C_atomic_12
             (coe MAlonzo.Code.Builtin.Constant.AtomicType.C_aData_18)
      C_pair_48 v3 v4
        -> coe
             MAlonzo.Code.Builtin.Signature.C_pair_24
             (coe du_tag2TyTag_234 (coe v3)) (coe du_tag2TyTag_234 (coe v4))
      C_list_52 v2
        -> coe
             MAlonzo.Code.Builtin.Signature.C_list_16
             (coe du_tag2TyTag_234 (coe v2))
      C_array_56 v2
        -> coe
             MAlonzo.Code.Builtin.Signature.C_array_20
             (coe du_tag2TyTag_234 (coe v2))
      C_bls12'45'381'45'g1'45'element_58
        -> coe
             MAlonzo.Code.Builtin.Signature.C_atomic_12
             (coe
                MAlonzo.Code.Builtin.Constant.AtomicType.C_aBls12'45'381'45'g1'45'element_22)
      C_bls12'45'381'45'g2'45'element_60
        -> coe
             MAlonzo.Code.Builtin.Signature.C_atomic_12
             (coe
                MAlonzo.Code.Builtin.Constant.AtomicType.C_aBls12'45'381'45'g2'45'element_24)
      C_bls12'45'381'45'mlresult_62
        -> coe
             MAlonzo.Code.Builtin.Signature.C_atomic_12
             (coe
                MAlonzo.Code.Builtin.Constant.AtomicType.C_aBls12'45'381'45'mlresult_26)
      _ -> MAlonzo.RTE.mazUnreachableError
-- RawU.tagLemma
d_tagLemma_248 ::
  () ->
  T_Tag_28 (T_Esc_24 AgdaAny) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_tagLemma_248 = erased
-- RawU.tagCon2TmCon
d_tagCon2TmCon_258 :: T_TagCon_108 -> T_TmCon_204
d_tagCon2TmCon_258 v0
  = case coe v0 of
      C_tagCon_112 v2 v3
        -> case coe v2 of
             C_integer_30
               -> coe
                    C_tmCon_208
                    (coe
                       MAlonzo.Code.Builtin.Signature.C_atomic_12
                       (coe MAlonzo.Code.Builtin.Constant.AtomicType.C_aInteger_8))
                    (coe v3)
             C_bytestring_32
               -> coe
                    C_tmCon_208
                    (coe
                       MAlonzo.Code.Builtin.Signature.C_atomic_12
                       (coe MAlonzo.Code.Builtin.Constant.AtomicType.C_aBytestring_10))
                    (coe v3)
             C_string_34
               -> coe
                    C_tmCon_208
                    (coe
                       MAlonzo.Code.Builtin.Signature.C_atomic_12
                       (coe MAlonzo.Code.Builtin.Constant.AtomicType.C_aString_12))
                    (coe v3)
             C_bool_36
               -> coe
                    C_tmCon_208
                    (coe
                       MAlonzo.Code.Builtin.Signature.C_atomic_12
                       (coe MAlonzo.Code.Builtin.Constant.AtomicType.C_aBool_16))
                    (coe v3)
             C_unit_38
               -> coe
                    C_tmCon_208
                    (coe
                       MAlonzo.Code.Builtin.Signature.C_atomic_12
                       (coe MAlonzo.Code.Builtin.Constant.AtomicType.C_aUnit_14))
                    (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
             C_value_40
               -> coe
                    C_tmCon_208
                    (coe
                       MAlonzo.Code.Builtin.Signature.C_atomic_12
                       (coe MAlonzo.Code.Builtin.Constant.AtomicType.C_aValue_20))
                    (coe v3)
             C_pdata_42
               -> coe
                    C_tmCon_208
                    (coe
                       MAlonzo.Code.Builtin.Signature.C_atomic_12
                       (coe MAlonzo.Code.Builtin.Constant.AtomicType.C_aData_18))
                    (coe v3)
             C_pair_48 v6 v7
               -> coe
                    seq (coe v3)
                    (coe
                       C_tmCon_208
                       (coe
                          MAlonzo.Code.Builtin.Signature.C_pair_24
                          (coe du_tag2TyTag_234 (coe v6)) (coe du_tag2TyTag_234 (coe v7)))
                       (coe v3))
             C_list_52 v5
               -> coe
                    C_tmCon_208
                    (coe
                       MAlonzo.Code.Builtin.Signature.C_list_16
                       (coe du_tag2TyTag_234 (coe v5)))
                    (coe v3)
             C_array_56 v5
               -> coe
                    C_tmCon_208
                    (coe
                       MAlonzo.Code.Builtin.Signature.C_array_20
                       (coe du_tag2TyTag_234 (coe v5)))
                    (coe v3)
             C_bls12'45'381'45'g1'45'element_58
               -> coe
                    C_tmCon_208
                    (coe
                       MAlonzo.Code.Builtin.Signature.C_atomic_12
                       (coe
                          MAlonzo.Code.Builtin.Constant.AtomicType.C_aBls12'45'381'45'g1'45'element_22))
                    (coe v3)
             C_bls12'45'381'45'g2'45'element_60
               -> coe
                    C_tmCon_208
                    (coe
                       MAlonzo.Code.Builtin.Signature.C_atomic_12
                       (coe
                          MAlonzo.Code.Builtin.Constant.AtomicType.C_aBls12'45'381'45'g2'45'element_24))
                    (coe v3)
             C_bls12'45'381'45'mlresult_62
               -> coe
                    C_tmCon_208
                    (coe
                       MAlonzo.Code.Builtin.Signature.C_atomic_12
                       (coe
                          MAlonzo.Code.Builtin.Constant.AtomicType.C_aBls12'45'381'45'mlresult_26))
                    (coe v3)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- RawU.tyTag2Tag
d_tyTag2Tag_314 ::
  MAlonzo.Code.Builtin.Signature.T__'8866''9839'_4 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_tyTag2Tag_314 v0
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
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased (coe C_pdata_42)
             MAlonzo.Code.Builtin.Constant.AtomicType.C_aValue_20
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased (coe C_value_40)
             MAlonzo.Code.Builtin.Constant.AtomicType.C_aBls12'45'381'45'g1'45'element_22
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                    (coe C_bls12'45'381'45'g1'45'element_58)
             MAlonzo.Code.Builtin.Constant.AtomicType.C_aBls12'45'381'45'g2'45'element_24
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                    (coe C_bls12'45'381'45'g2'45'element_60)
             MAlonzo.Code.Builtin.Constant.AtomicType.C_aBls12'45'381'45'mlresult_26
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                    (coe C_bls12'45'381'45'mlresult_62)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Builtin.Signature.C_list_16 v2
        -> let v3 = d_tyTag2Tag_314 (coe v2) in
           coe
             (case coe v3 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                       (coe C_list_52 v5)
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Builtin.Signature.C_array_20 v2
        -> let v3 = d_tyTag2Tag_314 (coe v2) in
           coe
             (case coe v3 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                       (coe C_array_56 v5)
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Builtin.Signature.C_pair_24 v2 v3
        -> let v4 = d_tyTag2Tag_314 (coe v2) in
           coe
             (let v5 = d_tyTag2Tag_314 (coe v3) in
              coe
                (case coe v4 of
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
                     -> case coe v5 of
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
                            -> coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                                 (coe C_pair_48 v7 v9)
                          _ -> MAlonzo.RTE.mazUnreachableError
                   _ -> MAlonzo.RTE.mazUnreachableError))
      _ -> MAlonzo.RTE.mazUnreachableError
-- RawU.tyTagLemma
d_tyTagLemma_362 ::
  MAlonzo.Code.Builtin.Signature.T__'8866''9839'_4 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_tyTagLemma_362 = erased
-- RawU.tmCon2TagCon
d_tmCon2TagCon_372 :: T_TmCon_204 -> T_TagCon_108
d_tmCon2TagCon_372 v0
  = case coe v0 of
      C_tmCon_208 v1 v2
        -> case coe v1 of
             MAlonzo.Code.Builtin.Signature.C_atomic_12 v4
               -> case coe v4 of
                    MAlonzo.Code.Builtin.Constant.AtomicType.C_aInteger_8
                      -> coe C_tagCon_112 (coe C_integer_30) v2
                    MAlonzo.Code.Builtin.Constant.AtomicType.C_aBytestring_10
                      -> coe C_tagCon_112 (coe C_bytestring_32) v2
                    MAlonzo.Code.Builtin.Constant.AtomicType.C_aString_12
                      -> coe C_tagCon_112 (coe C_string_34) v2
                    MAlonzo.Code.Builtin.Constant.AtomicType.C_aUnit_14
                      -> coe
                           C_tagCon_112 (coe C_unit_38)
                           (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                    MAlonzo.Code.Builtin.Constant.AtomicType.C_aBool_16
                      -> coe C_tagCon_112 (coe C_bool_36) v2
                    MAlonzo.Code.Builtin.Constant.AtomicType.C_aData_18
                      -> coe C_tagCon_112 (coe C_pdata_42) v2
                    MAlonzo.Code.Builtin.Constant.AtomicType.C_aValue_20
                      -> coe C_tagCon_112 (coe C_value_40) v2
                    MAlonzo.Code.Builtin.Constant.AtomicType.C_aBls12'45'381'45'g1'45'element_22
                      -> coe C_tagCon_112 (coe C_bls12'45'381'45'g1'45'element_58) v2
                    MAlonzo.Code.Builtin.Constant.AtomicType.C_aBls12'45'381'45'g2'45'element_24
                      -> coe C_tagCon_112 (coe C_bls12'45'381'45'g2'45'element_60) v2
                    MAlonzo.Code.Builtin.Constant.AtomicType.C_aBls12'45'381'45'mlresult_26
                      -> coe C_tagCon_112 (coe C_bls12'45'381'45'mlresult_62) v2
                    _ -> MAlonzo.RTE.mazUnreachableError
             MAlonzo.Code.Builtin.Signature.C_list_16 v4
               -> coe
                    C_tagCon_112
                    (coe
                       C_list_52
                       (MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                          (coe d_tyTag2Tag_314 (coe v4))))
                    v2
             MAlonzo.Code.Builtin.Signature.C_array_20 v4
               -> coe
                    C_tagCon_112
                    (coe
                       C_array_56
                       (MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                          (coe d_tyTag2Tag_314 (coe v4))))
                    v2
             MAlonzo.Code.Builtin.Signature.C_pair_24 v4 v5
               -> coe
                    seq (coe v2)
                    (coe
                       C_tagCon_112
                       (coe
                          C_pair_48
                          (MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                             (coe d_tyTag2Tag_314 (coe v4)))
                          (MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                             (coe d_tyTag2Tag_314 (coe v5))))
                       v2)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
