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

module MAlonzo.Code.Raw where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Bool
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Builtin
import qualified MAlonzo.Code.Builtin.Constant.AtomicType
import qualified MAlonzo.Code.Data.Bool.Base
import qualified MAlonzo.Code.Data.Integer.Show
import qualified MAlonzo.Code.Data.Nat.Properties
import qualified MAlonzo.Code.Data.String.Base
import qualified MAlonzo.Code.RawU
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core
import qualified MAlonzo.Code.Utils

import Raw
-- Raw.RawTy
d_RawTy_2 = ()
type T_RawTy_2 = RType
pattern C_'96'_6 a0 = RTyVar a0
pattern C__'8658'__8 a0 a1 = RTyFun a0 a1
pattern C_Π_10 a0 a1 = RTyPi a0 a1
pattern C_ƛ_12 a0 a1 = RTyLambda a0 a1
pattern C__'183'__14 a0 a1 = RTyApp a0 a1
pattern C_con_16 a0 = RTyCon a0
pattern C_μ_18 a0 a1 = RTyMu a0 a1
pattern C_SOP_22 a0 = RTySOP a0
check_'96'_6 :: Integer -> T_RawTy_2
check_'96'_6 = RTyVar
check__'8658'__8 :: T_RawTy_2 -> T_RawTy_2 -> T_RawTy_2
check__'8658'__8 = RTyFun
check_Π_10 ::
  MAlonzo.Code.Utils.T_Kind_652 -> T_RawTy_2 -> T_RawTy_2
check_Π_10 = RTyPi
check_ƛ_12 ::
  MAlonzo.Code.Utils.T_Kind_652 -> T_RawTy_2 -> T_RawTy_2
check_ƛ_12 = RTyLambda
check__'183'__14 :: T_RawTy_2 -> T_RawTy_2 -> T_RawTy_2
check__'183'__14 = RTyApp
check_con_16 :: T_RawTyCon_4 -> T_RawTy_2
check_con_16 = RTyCon
check_μ_18 :: T_RawTy_2 -> T_RawTy_2 -> T_RawTy_2
check_μ_18 = RTyMu
check_SOP_22 ::
  MAlonzo.Code.Utils.T_List_384
    (MAlonzo.Code.Utils.T_List_384 T_RawTy_2) ->
  T_RawTy_2
check_SOP_22 = RTySOP
cover_RawTy_2 :: RType -> ()
cover_RawTy_2 x
  = case x of
      RTyVar _ -> ()
      RTyFun _ _ -> ()
      RTyPi _ _ -> ()
      RTyLambda _ _ -> ()
      RTyApp _ _ -> ()
      RTyCon _ -> ()
      RTyMu _ _ -> ()
      RTySOP _ -> ()
-- Raw.RawTyCon
d_RawTyCon_4 = ()
type T_RawTyCon_4 = RTyCon
pattern C_atomic_24 a0 = RTyConAtom a0
pattern C_list_26 = RTyConList
pattern C_array_28 = RTyConArray
pattern C_pair_30 = RTyConPair
check_atomic_24 ::
  MAlonzo.Code.Builtin.Constant.AtomicType.T_AtomicTyCon_6 ->
  T_RawTyCon_4
check_atomic_24 = RTyConAtom
check_list_26 :: T_RawTyCon_4
check_list_26 = RTyConList
check_array_28 :: T_RawTyCon_4
check_array_28 = RTyConArray
check_pair_30 :: T_RawTyCon_4
check_pair_30 = RTyConPair
cover_RawTyCon_4 :: RTyCon -> ()
cover_RawTyCon_4 x
  = case x of
      RTyConAtom _ -> ()
      RTyConList -> ()
      RTyConArray -> ()
      RTyConPair -> ()
-- Raw.RawTm
d_RawTm_32 = ()
type T_RawTm_32 = RTerm
pattern C_'96'_34 a0 = RVar a0
pattern C_Λ_36 a0 a1 = RTLambda a0 a1
pattern C__'183''8902'__38 a0 a1 = RTApp a0 a1
pattern C_ƛ_40 a0 a1 = RLambda a0 a1
pattern C__'183'__42 a0 a1 = RApp a0 a1
pattern C_con_44 a0 = RCon a0
pattern C_error_46 a0 = RError a0
pattern C_builtin_48 a0 = RBuiltin a0
pattern C_wrap_50 a0 a1 a2 = RWrap a0 a1 a2
pattern C_unwrap_52 a0 = RUnWrap a0
pattern C_constr_60 a0 a1 a2 = RConstr a0 a1 a2
pattern C_case_68 a0 a1 a2 = RCase a0 a1 a2
check_'96'_34 :: Integer -> T_RawTm_32
check_'96'_34 = RVar
check_Λ_36 ::
  MAlonzo.Code.Utils.T_Kind_652 -> T_RawTm_32 -> T_RawTm_32
check_Λ_36 = RTLambda
check__'183''8902'__38 :: T_RawTm_32 -> T_RawTy_2 -> T_RawTm_32
check__'183''8902'__38 = RTApp
check_ƛ_40 :: T_RawTy_2 -> T_RawTm_32 -> T_RawTm_32
check_ƛ_40 = RLambda
check__'183'__42 :: T_RawTm_32 -> T_RawTm_32 -> T_RawTm_32
check__'183'__42 = RApp
check_con_44 :: MAlonzo.Code.RawU.T_TagCon_106 -> T_RawTm_32
check_con_44 = RCon
check_error_46 :: T_RawTy_2 -> T_RawTm_32
check_error_46 = RError
check_builtin_48 :: MAlonzo.Code.Builtin.T_Builtin_2 -> T_RawTm_32
check_builtin_48 = RBuiltin
check_wrap_50 :: T_RawTy_2 -> T_RawTy_2 -> T_RawTm_32 -> T_RawTm_32
check_wrap_50 = RWrap
check_unwrap_52 :: T_RawTm_32 -> T_RawTm_32
check_unwrap_52 = RUnWrap
check_constr_60 ::
  T_RawTy_2 ->
  Integer -> MAlonzo.Code.Utils.T_List_384 T_RawTm_32 -> T_RawTm_32
check_constr_60 = RConstr
check_case_68 ::
  T_RawTy_2 ->
  T_RawTm_32 ->
  MAlonzo.Code.Utils.T_List_384 T_RawTm_32 -> T_RawTm_32
check_case_68 = RCase
cover_RawTm_32 :: RTerm -> ()
cover_RawTm_32 x
  = case x of
      RVar _ -> ()
      RTLambda _ _ -> ()
      RTApp _ _ -> ()
      RLambda _ _ -> ()
      RApp _ _ -> ()
      RCon _ -> ()
      RError _ -> ()
      RBuiltin _ -> ()
      RWrap _ _ _ -> ()
      RUnWrap _ -> ()
      RConstr _ _ _ -> ()
      RCase _ _ _ -> ()
-- Raw.decRTyCon
d_decRTyCon_74 :: T_RawTyCon_4 -> T_RawTyCon_4 -> Bool
d_decRTyCon_74 v0 v1
  = let v2 = coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8 in
    coe
      (case coe v0 of
         C_atomic_24 v3
           -> case coe v1 of
                C_atomic_24 v4
                  -> coe
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
                       (coe
                          MAlonzo.Code.Builtin.Constant.AtomicType.d_decAtomicTyCon_26
                          (coe v3) (coe v4))
                _ -> coe v2
         C_list_26
           -> case coe v1 of
                C_list_26 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
                _ -> coe v2
         C_array_28
           -> case coe v1 of
                C_array_28 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
                _ -> coe v2
         C_pair_30
           -> case coe v1 of
                C_pair_30 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
                _ -> coe v2
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Raw.decRKi
d_decRKi_84 ::
  MAlonzo.Code.Utils.T_Kind_652 ->
  MAlonzo.Code.Utils.T_Kind_652 -> Bool
d_decRKi_84 v0 v1
  = case coe v0 of
      MAlonzo.Code.Utils.C_'42'_654
        -> let v2 = coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8 in
           coe
             (case coe v1 of
                MAlonzo.Code.Utils.C_'42'_654
                  -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
                _ -> coe v2)
      MAlonzo.Code.Utils.C_'9839'_656
        -> let v2 = coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8 in
           coe
             (case coe v1 of
                MAlonzo.Code.Utils.C_'9839'_656
                  -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
                _ -> coe v2)
      MAlonzo.Code.Utils.C__'8658'__658 v2 v3
        -> let v4 = coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8 in
           coe
             (case coe v1 of
                MAlonzo.Code.Utils.C__'8658'__658 v5 v6
                  -> coe
                       MAlonzo.Code.Data.Bool.Base.d__'8743'__24
                       (coe d_decRKi_84 (coe v2) (coe v5))
                       (coe d_decRKi_84 (coe v3) (coe v6))
                _ -> coe v4)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Raw.decRTy
d_decRTy_102 :: T_RawTy_2 -> T_RawTy_2 -> Bool
d_decRTy_102 v0 v1
  = let v2 = coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8 in
    coe
      (case coe v0 of
         C_'96'_6 v3
           -> case coe v1 of
                C_'96'_6 v4
                  -> coe
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
                       (coe
                          MAlonzo.Code.Data.Nat.Properties.d__'8799'__2688 (coe v3) (coe v4))
                _ -> coe v2
         C__'8658'__8 v3 v4
           -> case coe v1 of
                C__'8658'__8 v5 v6
                  -> coe
                       MAlonzo.Code.Data.Bool.Base.d__'8743'__24
                       (coe d_decRTy_102 (coe v3) (coe v5))
                       (coe d_decRTy_102 (coe v4) (coe v6))
                _ -> coe v2
         C_Π_10 v3 v4
           -> case coe v1 of
                C_Π_10 v5 v6
                  -> coe
                       MAlonzo.Code.Data.Bool.Base.d__'8743'__24
                       (coe d_decRKi_84 (coe v3) (coe v5))
                       (coe d_decRTy_102 (coe v4) (coe v6))
                _ -> coe v2
         C_ƛ_12 v3 v4
           -> case coe v1 of
                C_ƛ_12 v5 v6
                  -> coe
                       MAlonzo.Code.Data.Bool.Base.d__'8743'__24
                       (coe d_decRKi_84 (coe v3) (coe v5))
                       (coe d_decRTy_102 (coe v4) (coe v6))
                _ -> coe v2
         C__'183'__14 v3 v4
           -> case coe v1 of
                C__'183'__14 v5 v6
                  -> coe
                       MAlonzo.Code.Data.Bool.Base.d__'8743'__24
                       (coe d_decRTy_102 (coe v3) (coe v5))
                       (coe d_decRTy_102 (coe v4) (coe v6))
                _ -> coe v2
         C_con_16 v3
           -> case coe v1 of
                C_con_16 v4 -> coe d_decRTyCon_74 (coe v3) (coe v4)
                _ -> coe v2
         C_μ_18 v3 v4
           -> case coe v1 of
                C_μ_18 v5 v6
                  -> coe
                       MAlonzo.Code.Data.Bool.Base.d__'8743'__24
                       (coe d_decRTy_102 (coe v3) (coe v5))
                       (coe d_decRTy_102 (coe v4) (coe v6))
                _ -> coe v2
         C_SOP_22 v3
           -> case coe v1 of
                C_SOP_22 v4 -> coe d_decRTyListList_114 (coe v3) (coe v4)
                _ -> coe v2
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Raw.decRTyList
d_decRTyList_108 ::
  MAlonzo.Code.Utils.T_List_384 T_RawTy_2 ->
  MAlonzo.Code.Utils.T_List_384 T_RawTy_2 -> Bool
d_decRTyList_108 v0 v1
  = let v2 = coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8 in
    coe
      (case coe v0 of
         MAlonzo.Code.Utils.C_'91''93'_388
           -> case coe v1 of
                MAlonzo.Code.Utils.C_'91''93'_388
                  -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
                _ -> coe v2
         MAlonzo.Code.Utils.C__'8759'__390 v3 v4
           -> case coe v1 of
                MAlonzo.Code.Utils.C__'8759'__390 v5 v6
                  -> coe
                       MAlonzo.Code.Data.Bool.Base.d__'8743'__24
                       (coe d_decRTy_102 (coe v3) (coe v5))
                       (coe d_decRTyList_108 (coe v4) (coe v6))
                _ -> coe v2
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Raw.decRTyListList
d_decRTyListList_114 ::
  MAlonzo.Code.Utils.T_List_384
    (MAlonzo.Code.Utils.T_List_384 T_RawTy_2) ->
  MAlonzo.Code.Utils.T_List_384
    (MAlonzo.Code.Utils.T_List_384 T_RawTy_2) ->
  Bool
d_decRTyListList_114 v0 v1
  = let v2 = coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8 in
    coe
      (case coe v0 of
         MAlonzo.Code.Utils.C_'91''93'_388
           -> case coe v1 of
                MAlonzo.Code.Utils.C_'91''93'_388
                  -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
                _ -> coe v2
         MAlonzo.Code.Utils.C__'8759'__390 v3 v4
           -> case coe v1 of
                MAlonzo.Code.Utils.C__'8759'__390 v5 v6
                  -> coe
                       MAlonzo.Code.Data.Bool.Base.d__'8743'__24
                       (coe d_decRTyList_108 (coe v3) (coe v5))
                       (coe d_decRTyListList_114 (coe v4) (coe v6))
                _ -> coe v2
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Raw.decRTm
d_decRTm_188 :: T_RawTm_32 -> T_RawTm_32 -> Bool
d_decRTm_188 v0 v1
  = let v2 = coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8 in
    coe
      (case coe v0 of
         C_'96'_34 v3
           -> case coe v1 of
                C_'96'_34 v4
                  -> coe
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
                       (coe
                          MAlonzo.Code.Data.Nat.Properties.d__'8799'__2688 (coe v3) (coe v4))
                _ -> coe v2
         C_Λ_36 v3 v4
           -> case coe v1 of
                C_Λ_36 v5 v6
                  -> coe
                       MAlonzo.Code.Data.Bool.Base.d__'8743'__24
                       (coe d_decRKi_84 (coe v3) (coe v5))
                       (coe d_decRTm_188 (coe v4) (coe v6))
                _ -> coe v2
         C__'183''8902'__38 v3 v4
           -> case coe v1 of
                C__'183''8902'__38 v5 v6
                  -> coe
                       MAlonzo.Code.Data.Bool.Base.d__'8743'__24
                       (coe d_decRTm_188 (coe v3) (coe v5))
                       (coe d_decRTy_102 (coe v4) (coe v6))
                _ -> coe v2
         C_ƛ_40 v3 v4
           -> case coe v1 of
                C_ƛ_40 v5 v6
                  -> coe
                       MAlonzo.Code.Data.Bool.Base.d__'8743'__24
                       (coe d_decRTy_102 (coe v3) (coe v5))
                       (coe d_decRTm_188 (coe v4) (coe v6))
                _ -> coe v2
         C__'183'__42 v3 v4
           -> case coe v1 of
                C__'183'__42 v5 v6
                  -> coe
                       MAlonzo.Code.Data.Bool.Base.d__'8743'__24
                       (coe d_decRTm_188 (coe v3) (coe v5))
                       (coe d_decRTm_188 (coe v4) (coe v6))
                _ -> coe v2
         C_con_44 v3
           -> case coe v1 of
                C_con_44 v4
                  -> coe MAlonzo.Code.RawU.d_decTagCon_192 (coe v3) (coe v4)
                _ -> coe v2
         C_error_46 v3
           -> case coe v1 of
                C_error_46 v4 -> coe d_decRTy_102 (coe v3) (coe v4)
                _ -> coe v2
         C_builtin_48 v3
           -> case coe v1 of
                C_builtin_48 v4
                  -> coe
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
                       (coe MAlonzo.Code.Builtin.d_decBuiltin_426 (coe v3) (coe v4))
                _ -> coe v2
         C_wrap_50 v3 v4 v5
           -> case coe v1 of
                C_wrap_50 v6 v7 v8
                  -> coe
                       MAlonzo.Code.Data.Bool.Base.d__'8743'__24
                       (coe d_decRTy_102 (coe v3) (coe v6))
                       (coe
                          MAlonzo.Code.Data.Bool.Base.d__'8743'__24
                          (coe d_decRTy_102 (coe v4) (coe v7))
                          (coe d_decRTm_188 (coe v5) (coe v8)))
                _ -> coe v2
         C_unwrap_52 v3
           -> case coe v1 of
                C_unwrap_52 v4 -> coe d_decRTm_188 (coe v3) (coe v4)
                _ -> coe v2
         C_constr_60 v3 v4 v5
           -> case coe v1 of
                C_constr_60 v6 v7 v8
                  -> coe
                       MAlonzo.Code.Data.Bool.Base.d__'8743'__24
                       (coe d_decRTy_102 (coe v3) (coe v6))
                       (coe
                          MAlonzo.Code.Data.Bool.Base.d__'8743'__24
                          (coe
                             MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
                             (coe
                                MAlonzo.Code.Data.Nat.Properties.d__'8799'__2688 (coe v4)
                                (coe v7)))
                          (coe d_decRTmList_194 (coe v5) (coe v8)))
                _ -> coe v2
         C_case_68 v3 v4 v5
           -> case coe v1 of
                C_case_68 v6 v7 v8
                  -> coe
                       MAlonzo.Code.Data.Bool.Base.d__'8743'__24
                       (coe d_decRTy_102 (coe v3) (coe v6))
                       (coe
                          MAlonzo.Code.Data.Bool.Base.d__'8743'__24
                          (coe d_decRTm_188 (coe v4) (coe v7))
                          (coe d_decRTmList_194 (coe v5) (coe v8)))
                _ -> coe v2
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Raw.decRTmList
d_decRTmList_194 ::
  MAlonzo.Code.Utils.T_List_384 T_RawTm_32 ->
  MAlonzo.Code.Utils.T_List_384 T_RawTm_32 -> Bool
d_decRTmList_194 v0 v1
  = let v2 = coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8 in
    coe
      (case coe v0 of
         MAlonzo.Code.Utils.C_'91''93'_388
           -> case coe v1 of
                MAlonzo.Code.Utils.C_'91''93'_388
                  -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
                _ -> coe v2
         MAlonzo.Code.Utils.C__'8759'__390 v3 v4
           -> case coe v1 of
                MAlonzo.Code.Utils.C__'8759'__390 v5 v6
                  -> coe
                       MAlonzo.Code.Data.Bool.Base.d__'8743'__24
                       (coe d_decRTm_188 (coe v3) (coe v5))
                       (coe d_decRTmList_194 (coe v4) (coe v6))
                _ -> coe v2
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Raw.addBrackets
d_addBrackets_292 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_addBrackets_292 v0
  = coe
      MAlonzo.Code.Data.String.Base.d__'43''43'__20
      ("[" :: Data.Text.Text)
      (coe
         MAlonzo.Code.Data.String.Base.d__'43''43'__20 v0
         ("]" :: Data.Text.Text))
-- Raw.rawTyPrinter
d_rawTyPrinter_296 ::
  T_RawTy_2 -> MAlonzo.Code.Agda.Builtin.String.T_String_6
d_rawTyPrinter_296 v0
  = case coe v0 of
      C_'96'_6 v1 -> coe MAlonzo.Code.Data.Integer.Show.d_show_6 (coe v1)
      C__'8658'__8 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("(" :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_rawTyPrinter_296 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   ("\8658" :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (d_rawTyPrinter_296 (coe v2)) (")" :: Data.Text.Text))))
      C_Π_10 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("(\928" :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                ("kind" :: Data.Text.Text)
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (d_rawTyPrinter_296 (coe v2)) (")" :: Data.Text.Text)))
      C_ƛ_12 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("(\411" :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                ("kind" :: Data.Text.Text)
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (d_rawTyPrinter_296 (coe v2)) (")" :: Data.Text.Text)))
      C__'183'__14 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("(" :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_rawTyPrinter_296 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   ("\183" :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (d_rawTyPrinter_296 (coe v2)) (")" :: Data.Text.Text))))
      C_con_16 v1 -> coe ("(con)" :: Data.Text.Text)
      C_μ_18 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("(\956" :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_rawTyPrinter_296 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (d_rawTyPrinter_296 (coe v2)) (")" :: Data.Text.Text)))
      C_SOP_22 v1
        -> coe d_addBrackets_292 (coe d_rawTyListListPrinter_300 (coe v1))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Raw.rawTyListPrinter
d_rawTyListPrinter_298 ::
  MAlonzo.Code.Utils.T_List_384 T_RawTy_2 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_rawTyListPrinter_298 v0
  = case coe v0 of
      MAlonzo.Code.Utils.C_'91''93'_388 -> coe ("" :: Data.Text.Text)
      MAlonzo.Code.Utils.C__'8759'__390 v1 v2
        -> case coe v2 of
             MAlonzo.Code.Utils.C_'91''93'_388
               -> coe d_rawTyPrinter_296 (coe v1)
             MAlonzo.Code.Utils.C__'8759'__390 v3 v4
               -> coe
                    MAlonzo.Code.Data.String.Base.d__'43''43'__20
                    (d_rawTyPrinter_296 (coe v1))
                    (coe
                       MAlonzo.Code.Data.String.Base.d__'43''43'__20
                       (" , " :: Data.Text.Text) (d_rawTyListPrinter_298 (coe v2)))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Raw.rawTyListListPrinter
d_rawTyListListPrinter_300 ::
  MAlonzo.Code.Utils.T_List_384
    (MAlonzo.Code.Utils.T_List_384 T_RawTy_2) ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_rawTyListListPrinter_300 v0
  = case coe v0 of
      MAlonzo.Code.Utils.C_'91''93'_388 -> coe ("" :: Data.Text.Text)
      MAlonzo.Code.Utils.C__'8759'__390 v1 v2
        -> case coe v2 of
             MAlonzo.Code.Utils.C_'91''93'_388
               -> coe d_addBrackets_292 (coe d_rawTyListPrinter_298 (coe v1))
             MAlonzo.Code.Utils.C__'8759'__390 v3 v4
               -> coe
                    MAlonzo.Code.Data.String.Base.d__'43''43'__20
                    (d_addBrackets_292 (coe d_rawTyListPrinter_298 (coe v1)))
                    (coe
                       MAlonzo.Code.Data.String.Base.d__'43''43'__20
                       (" , " :: Data.Text.Text) (d_rawTyListListPrinter_300 (coe v2)))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Raw.rawListPrinter
d_rawListPrinter_344 ::
  MAlonzo.Code.Utils.T_List_384 T_RawTm_32 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_rawListPrinter_344 v0
  = case coe v0 of
      MAlonzo.Code.Utils.C_'91''93'_388 -> coe ("" :: Data.Text.Text)
      MAlonzo.Code.Utils.C__'8759'__390 v1 v2
        -> case coe v2 of
             MAlonzo.Code.Utils.C_'91''93'_388 -> coe d_rawPrinter_346 (coe v1)
             MAlonzo.Code.Utils.C__'8759'__390 v3 v4
               -> coe
                    MAlonzo.Code.Data.String.Base.d__'43''43'__20
                    (d_rawPrinter_346 (coe v1))
                    (coe
                       MAlonzo.Code.Data.String.Base.d__'43''43'__20
                       (" , " :: Data.Text.Text) (d_rawListPrinter_344 (coe v2)))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Raw.rawPrinter
d_rawPrinter_346 ::
  T_RawTm_32 -> MAlonzo.Code.Agda.Builtin.String.T_String_6
d_rawPrinter_346 v0
  = case coe v0 of
      C_'96'_34 v1
        -> coe MAlonzo.Code.Data.Integer.Show.d_show_6 (coe v1)
      C_Λ_36 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("(" :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                ("\923" :: Data.Text.Text)
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   ("kind" :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (d_rawPrinter_346 (coe v2)) (")" :: Data.Text.Text))))
      C__'183''8902'__38 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("(" :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_rawPrinter_346 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   ("\183\8902" :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (d_rawTyPrinter_296 (coe v2)) (")" :: Data.Text.Text))))
      C_ƛ_40 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("(" :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                ("\411" :: Data.Text.Text)
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (d_rawTyPrinter_296 (coe v1))
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (d_rawPrinter_346 (coe v2)) (")" :: Data.Text.Text))))
      C__'183'__42 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("(" :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_rawPrinter_346 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   ("\183" :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (d_rawPrinter_346 (coe v2)) (")" :: Data.Text.Text))))
      C_con_44 v1 -> coe ("(con)" :: Data.Text.Text)
      C_error_46 v1
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("(error" :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_rawTyPrinter_296 (coe v1)) (")" :: Data.Text.Text))
      C_builtin_48 v1 -> coe ("(builtin)" :: Data.Text.Text)
      C_wrap_50 v1 v2 v3
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("(wrap" :: Data.Text.Text) (")" :: Data.Text.Text)
      C_unwrap_52 v1
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("(unwrap" :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_rawPrinter_346 (coe v1)) (")" :: Data.Text.Text))
      C_constr_60 v1 v2 v3
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("(const" :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_rawTyPrinter_296 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (" " :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (MAlonzo.Code.Data.Integer.Show.d_show_6 (coe v2))
                      (coe
                         MAlonzo.Code.Data.String.Base.d__'43''43'__20
                         (" [" :: Data.Text.Text)
                         (coe
                            MAlonzo.Code.Data.String.Base.d__'43''43'__20
                            (d_rawListPrinter_344 (coe v3)) ("])" :: Data.Text.Text))))))
      C_case_68 v1 v2 v3
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("(case" :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_rawTyPrinter_296 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (" " :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (d_rawPrinter_346 (coe v2))
                      (coe
                         MAlonzo.Code.Data.String.Base.d__'43''43'__20
                         (" [" :: Data.Text.Text)
                         (coe
                            MAlonzo.Code.Data.String.Base.d__'43''43'__20
                            (d_rawListPrinter_344 (coe v3)) ("])" :: Data.Text.Text))))))
      _ -> MAlonzo.RTE.mazUnreachableError
