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

module MAlonzo.Code.Untyped where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Bool
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.Nat
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Builtin
import qualified MAlonzo.Code.Builtin.Constant.AtomicType
import qualified MAlonzo.Code.Builtin.Signature
import qualified MAlonzo.Code.Data.Bool.Base
import qualified MAlonzo.Code.Data.Integer.Show
import qualified MAlonzo.Code.Data.Nat.Properties
import qualified MAlonzo.Code.Data.Nat.Show
import qualified MAlonzo.Code.Data.String.Base
import qualified MAlonzo.Code.RawU
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core
import qualified MAlonzo.Code.Scoped
import qualified MAlonzo.Code.Utils

import qualified Data.Text as T
-- Untyped._⊢
d__'8866'_14 a0 = ()
data T__'8866'_14
  = C_'96'_18 AgdaAny | C_ƛ_20 T__'8866'_14 |
    C__'183'__22 T__'8866'_14 T__'8866'_14 | C_force_24 T__'8866'_14 |
    C_delay_26 T__'8866'_14 | C_con_28 MAlonzo.Code.RawU.T_TmCon_198 |
    C_constr_34 Integer [T__'8866'_14] |
    C_case_40 T__'8866'_14 [T__'8866'_14] |
    C_builtin_44 MAlonzo.Code.Builtin.T_Builtin_2 | C_error_46
-- Untyped.uglyDATA
d_uglyDATA_64 ::
  MAlonzo.Code.Utils.T_DATA_478 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_uglyDATA_64 ~v0 = du_uglyDATA_64
du_uglyDATA_64 :: MAlonzo.Code.Agda.Builtin.String.T_String_6
du_uglyDATA_64 = coe ("(DATA)" :: Data.Text.Text)
-- Untyped.uglyTmCon
d_uglyTmCon_68 ::
  MAlonzo.Code.RawU.T_TmCon_198 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_uglyTmCon_68 v0
  = case coe v0 of
      MAlonzo.Code.RawU.C_tmCon_202 v1 v2
        -> case coe v1 of
             MAlonzo.Code.Builtin.Signature.C_atomic_12 v4
               -> case coe v4 of
                    MAlonzo.Code.Builtin.Constant.AtomicType.C_aInteger_8
                      -> coe
                           MAlonzo.Code.Data.String.Base.d__'43''43'__20
                           ("(integer " :: Data.Text.Text)
                           (coe
                              MAlonzo.Code.Data.String.Base.d__'43''43'__20
                              (MAlonzo.Code.Data.Integer.Show.d_show_6 (coe v2))
                              (")" :: Data.Text.Text))
                    MAlonzo.Code.Builtin.Constant.AtomicType.C_aBytestring_10
                      -> coe ("bytestring" :: Data.Text.Text)
                    MAlonzo.Code.Builtin.Constant.AtomicType.C_aString_12
                      -> coe
                           MAlonzo.Code.Data.String.Base.d__'43''43'__20
                           ("(string " :: Data.Text.Text)
                           (coe
                              MAlonzo.Code.Data.String.Base.d__'43''43'__20 v2
                              (")" :: Data.Text.Text))
                    MAlonzo.Code.Builtin.Constant.AtomicType.C_aUnit_14
                      -> coe ("()" :: Data.Text.Text)
                    MAlonzo.Code.Builtin.Constant.AtomicType.C_aBool_16
                      -> if coe v2
                           then coe ("(bool true)" :: Data.Text.Text)
                           else coe ("(bool false)" :: Data.Text.Text)
                    MAlonzo.Code.Builtin.Constant.AtomicType.C_aData_18
                      -> coe du_uglyDATA_64
                    MAlonzo.Code.Builtin.Constant.AtomicType.C_aBls12'45'381'45'g1'45'element_20
                      -> coe ("(bls12-381-g1-element ???)" :: Data.Text.Text)
                    MAlonzo.Code.Builtin.Constant.AtomicType.C_aBls12'45'381'45'g2'45'element_22
                      -> coe ("(bls12-381-g2-element ???)" :: Data.Text.Text)
                    MAlonzo.Code.Builtin.Constant.AtomicType.C_aBls12'45'381'45'mlresult_24
                      -> coe ("(bls12-381-mlresult ???)" :: Data.Text.Text)
                    _ -> MAlonzo.RTE.mazUnreachableError
             MAlonzo.Code.Builtin.Signature.C_list_16 v4
               -> coe
                    MAlonzo.Code.Data.String.Base.d__'43''43'__20
                    ("(list [ " :: Data.Text.Text)
                    (coe
                       MAlonzo.Code.Data.String.Base.d__'43''43'__20
                       (d_uglyTmConList_72 (coe v4) (coe v2)) (" ])" :: Data.Text.Text))
             MAlonzo.Code.Builtin.Signature.C_pair_20 v4 v5
               -> case coe v2 of
                    MAlonzo.Code.Utils.C__'44'__380 v6 v7
                      -> coe
                           MAlonzo.Code.Data.String.Base.d__'43''43'__20
                           ("(pair (" :: Data.Text.Text)
                           (coe
                              MAlonzo.Code.Data.String.Base.d__'43''43'__20
                              (d_uglyTmCon_68
                                 (coe MAlonzo.Code.RawU.C_tmCon_202 (coe v4) (coe v6)))
                              (coe
                                 MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                 (" , " :: Data.Text.Text)
                                 (coe
                                    MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                    (d_uglyTmCon_68
                                       (coe MAlonzo.Code.RawU.C_tmCon_202 (coe v5) (coe v7)))
                                    (") )" :: Data.Text.Text))))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Untyped.uglyTmConList
d_uglyTmConList_72 ::
  MAlonzo.Code.Builtin.Signature.T__'8866''9839'_4 ->
  MAlonzo.Code.Utils.T_List_384 AgdaAny ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_uglyTmConList_72 v0 v1
  = case coe v1 of
      MAlonzo.Code.Utils.C_'91''93'_388 -> coe ("" :: Data.Text.Text)
      MAlonzo.Code.Utils.C__'8759'__390 v2 v3
        -> case coe v3 of
             MAlonzo.Code.Utils.C_'91''93'_388
               -> coe
                    d_uglyTmCon_68
                    (coe MAlonzo.Code.RawU.C_tmCon_202 (coe v0) (coe v2))
             MAlonzo.Code.Utils.C__'8759'__390 v4 v5
               -> coe
                    MAlonzo.Code.Data.String.Base.d__'43''43'__20
                    (d_uglyTmCon_68
                       (coe MAlonzo.Code.RawU.C_tmCon_202 (coe v0) (coe v2)))
                    (coe
                       MAlonzo.Code.Data.String.Base.d__'43''43'__20
                       (" , " :: Data.Text.Text) (d_uglyTmConList_72 (coe v0) (coe v3)))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Untyped.showNat
d_showNat_114 ::
  Integer -> MAlonzo.Code.Agda.Builtin.String.T_String_6
d_showNat_114 = T.pack . show
-- Untyped.uglyBuiltin
d_uglyBuiltin_116 ::
  MAlonzo.Code.Builtin.T_Builtin_2 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_uglyBuiltin_116 v0
  = let v1 = "other" :: Data.Text.Text in
    coe
      (case coe v0 of
         MAlonzo.Code.Builtin.C_addInteger_4
           -> coe ("addInteger" :: Data.Text.Text)
         _ -> coe v1)
-- Untyped.uglyList
d_uglyList_120 ::
  () -> [T__'8866'_14] -> MAlonzo.Code.Agda.Builtin.String.T_String_6
d_uglyList_120 ~v0 v1 = du_uglyList_120 v1
du_uglyList_120 ::
  [T__'8866'_14] -> MAlonzo.Code.Agda.Builtin.String.T_String_6
du_uglyList_120 v0
  = coe
      MAlonzo.Code.Data.String.Base.d__'43''43'__20
      ("[" :: Data.Text.Text)
      (coe
         MAlonzo.Code.Data.String.Base.d__'43''43'__20
         (coe du_uglyList''_124 (coe v0)) ("]" :: Data.Text.Text))
-- Untyped.uglyList'
d_uglyList''_124 ::
  () -> [T__'8866'_14] -> MAlonzo.Code.Agda.Builtin.String.T_String_6
d_uglyList''_124 ~v0 v1 = du_uglyList''_124 v1
du_uglyList''_124 ::
  [T__'8866'_14] -> MAlonzo.Code.Agda.Builtin.String.T_String_6
du_uglyList''_124 v0
  = case coe v0 of
      [] -> coe ("" :: Data.Text.Text)
      (:) v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             (coe du_ugly_128 (coe v1))
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (" , " :: Data.Text.Text) (coe du_uglyList''_124 (coe v2)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Untyped.ugly
d_ugly_128 ::
  () -> T__'8866'_14 -> MAlonzo.Code.Agda.Builtin.String.T_String_6
d_ugly_128 ~v0 v1 = du_ugly_128 v1
du_ugly_128 ::
  T__'8866'_14 -> MAlonzo.Code.Agda.Builtin.String.T_String_6
du_ugly_128 v0
  = case coe v0 of
      C_'96'_18 v1 -> coe ("(` var )" :: Data.Text.Text)
      C_ƛ_20 v1
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("(\411 " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (coe du_ugly_128 (coe v1)) (")" :: Data.Text.Text))
      C__'183'__22 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("( " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (coe du_ugly_128 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (" \183 " :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (coe du_ugly_128 (coe v2)) (")" :: Data.Text.Text))))
      C_force_24 v1
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("(force " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (coe du_ugly_128 (coe v1)) (")" :: Data.Text.Text))
      C_delay_26 v1
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("(delay " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (coe du_ugly_128 (coe v1)) (")" :: Data.Text.Text))
      C_con_28 v1
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("(con " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_uglyTmCon_68 (coe v1)) (")" :: Data.Text.Text))
      C_constr_34 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("(constr " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (coe MAlonzo.Code.Data.Nat.Show.d_show_56 v1)
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (coe du_uglyList_120 (coe v2)) (")" :: Data.Text.Text)))
      C_case_40 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("(case " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (coe du_ugly_128 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (" " :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (coe du_uglyList_120 (coe v2)) (")" :: Data.Text.Text))))
      C_builtin_44 v1
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("(builtin " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_uglyBuiltin_116 (coe v1)) (")" :: Data.Text.Text))
      C_error_46 -> coe ("error" :: Data.Text.Text)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Untyped.extG
d_extG_162 ::
  () -> (AgdaAny -> Integer) -> Maybe AgdaAny -> Integer
d_extG_162 ~v0 v1 v2 = du_extG_162 v1 v2
du_extG_162 :: (AgdaAny -> Integer) -> Maybe AgdaAny -> Integer
du_extG_162 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
        -> coe addInt (coe (1 :: Integer)) (coe v0 v2)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe (0 :: Integer)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Untyped.extricateUList
d_extricateUList_172 ::
  () ->
  (AgdaAny -> Integer) ->
  [T__'8866'_14] ->
  MAlonzo.Code.Utils.T_List_384 MAlonzo.Code.RawU.T_Untyped_146
d_extricateUList_172 ~v0 v1 v2 = du_extricateUList_172 v1 v2
du_extricateUList_172 ::
  (AgdaAny -> Integer) ->
  [T__'8866'_14] ->
  MAlonzo.Code.Utils.T_List_384 MAlonzo.Code.RawU.T_Untyped_146
du_extricateUList_172 v0 v1
  = case coe v1 of
      [] -> coe MAlonzo.Code.Utils.C_'91''93'_388
      (:) v2 v3
        -> coe
             MAlonzo.Code.Utils.C__'8759'__390
             (coe du_extricateU_176 (coe v0) (coe v2))
             (coe du_extricateUList_172 (coe v0) (coe v3))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Untyped.extricateU
d_extricateU_176 ::
  () ->
  (AgdaAny -> Integer) ->
  T__'8866'_14 -> MAlonzo.Code.RawU.T_Untyped_146
d_extricateU_176 ~v0 v1 v2 = du_extricateU_176 v1 v2
du_extricateU_176 ::
  (AgdaAny -> Integer) ->
  T__'8866'_14 -> MAlonzo.Code.RawU.T_Untyped_146
du_extricateU_176 v0 v1
  = case coe v1 of
      C_'96'_18 v2 -> coe MAlonzo.Code.RawU.C_UVar_148 (coe v0 v2)
      C_ƛ_20 v2
        -> coe
             MAlonzo.Code.RawU.C_ULambda_150
             (coe du_extricateU_176 (coe du_extG_162 (coe v0)) (coe v2))
      C__'183'__22 v2 v3
        -> coe
             MAlonzo.Code.RawU.C_UApp_152
             (coe du_extricateU_176 (coe v0) (coe v2))
             (coe du_extricateU_176 (coe v0) (coe v3))
      C_force_24 v2
        -> coe
             MAlonzo.Code.RawU.C_UForce_162
             (coe du_extricateU_176 (coe v0) (coe v2))
      C_delay_26 v2
        -> coe
             MAlonzo.Code.RawU.C_UDelay_160
             (coe du_extricateU_176 (coe v0) (coe v2))
      C_con_28 v2
        -> coe
             MAlonzo.Code.RawU.C_UCon_154
             (coe MAlonzo.Code.RawU.d_tmCon2TagCon_316 (coe v2))
      C_constr_34 v2 v3
        -> case coe v3 of
             []
               -> coe
                    MAlonzo.Code.RawU.C_UConstr_164 (coe v2)
                    (coe MAlonzo.Code.Utils.C_'91''93'_388)
             (:) v4 v5
               -> coe
                    MAlonzo.Code.RawU.C_UConstr_164 (coe v2)
                    (coe
                       MAlonzo.Code.Utils.C__'8759'__390
                       (coe du_extricateU_176 (coe v0) (coe v4))
                       (coe du_extricateUList_172 (coe v0) (coe v5)))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_case_40 v2 v3
        -> coe
             MAlonzo.Code.RawU.C_UCase_166
             (coe du_extricateU_176 (coe v0) (coe v2))
             (coe du_extricateUList_172 (coe v0) (coe v3))
      C_builtin_44 v2 -> coe MAlonzo.Code.RawU.C_UBuiltin_158 (coe v2)
      C_error_46 -> coe MAlonzo.Code.RawU.C_UError_156
      _ -> MAlonzo.RTE.mazUnreachableError
-- Untyped.extricateU0
d_extricateU0_236 ::
  T__'8866'_14 -> MAlonzo.Code.RawU.T_Untyped_146
d_extricateU0_236 v0 = coe du_extricateU_176 erased (coe v0)
-- Untyped.extG'
d_extG''_242 ::
  () ->
  (Integer ->
   MAlonzo.Code.Utils.T_Either_6
     MAlonzo.Code.Scoped.T_ScopeError_576 AgdaAny) ->
  Integer ->
  MAlonzo.Code.Utils.T_Either_6
    MAlonzo.Code.Scoped.T_ScopeError_576 (Maybe AgdaAny)
d_extG''_242 ~v0 v1 v2 = du_extG''_242 v1 v2
du_extG''_242 ::
  (Integer ->
   MAlonzo.Code.Utils.T_Either_6
     MAlonzo.Code.Scoped.T_ScopeError_576 AgdaAny) ->
  Integer ->
  MAlonzo.Code.Utils.T_Either_6
    MAlonzo.Code.Scoped.T_ScopeError_576 (Maybe AgdaAny)
du_extG''_242 v0 v1
  = case coe v1 of
      0 -> coe
             MAlonzo.Code.Utils.C_inj'8322'_14
             (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18)
      _ -> let v2 = subInt (coe v1) (coe (1 :: Integer)) in
           coe
             (coe
                MAlonzo.Code.Utils.du_fmap_224
                (coe MAlonzo.Code.Utils.du_EitherP_274)
                (coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16) (coe v0 v2))
-- Untyped.scopeCheckUList
d_scopeCheckUList_252 ::
  () ->
  (Integer ->
   MAlonzo.Code.Utils.T_Either_6
     MAlonzo.Code.Scoped.T_ScopeError_576 AgdaAny) ->
  MAlonzo.Code.Utils.T_List_384 MAlonzo.Code.RawU.T_Untyped_146 ->
  MAlonzo.Code.Utils.T_Either_6
    MAlonzo.Code.Scoped.T_ScopeError_576 [T__'8866'_14]
d_scopeCheckUList_252 ~v0 v1 v2 = du_scopeCheckUList_252 v1 v2
du_scopeCheckUList_252 ::
  (Integer ->
   MAlonzo.Code.Utils.T_Either_6
     MAlonzo.Code.Scoped.T_ScopeError_576 AgdaAny) ->
  MAlonzo.Code.Utils.T_List_384 MAlonzo.Code.RawU.T_Untyped_146 ->
  MAlonzo.Code.Utils.T_Either_6
    MAlonzo.Code.Scoped.T_ScopeError_576 [T__'8866'_14]
du_scopeCheckUList_252 v0 v1
  = case coe v1 of
      MAlonzo.Code.Utils.C_'91''93'_388
        -> coe
             MAlonzo.Code.Utils.C_inj'8322'_14
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Utils.C__'8759'__390 v2 v3
        -> coe
             MAlonzo.Code.Utils.du_eitherBind_42
             (coe du_scopeCheckU_256 (coe v0) (coe v2))
             (coe
                (\ v4 ->
                   coe
                     MAlonzo.Code.Utils.du_eitherBind_42
                     (coe du_scopeCheckUList_252 (coe v0) (coe v3))
                     (coe
                        (\ v5 ->
                           coe
                             MAlonzo.Code.Utils.C_inj'8322'_14
                             (coe
                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v4) (coe v5))))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Untyped.scopeCheckU
d_scopeCheckU_256 ::
  () ->
  (Integer ->
   MAlonzo.Code.Utils.T_Either_6
     MAlonzo.Code.Scoped.T_ScopeError_576 AgdaAny) ->
  MAlonzo.Code.RawU.T_Untyped_146 ->
  MAlonzo.Code.Utils.T_Either_6
    MAlonzo.Code.Scoped.T_ScopeError_576 T__'8866'_14
d_scopeCheckU_256 ~v0 v1 v2 = du_scopeCheckU_256 v1 v2
du_scopeCheckU_256 ::
  (Integer ->
   MAlonzo.Code.Utils.T_Either_6
     MAlonzo.Code.Scoped.T_ScopeError_576 AgdaAny) ->
  MAlonzo.Code.RawU.T_Untyped_146 ->
  MAlonzo.Code.Utils.T_Either_6
    MAlonzo.Code.Scoped.T_ScopeError_576 T__'8866'_14
du_scopeCheckU_256 v0 v1
  = case coe v1 of
      MAlonzo.Code.RawU.C_UVar_148 v2
        -> coe
             MAlonzo.Code.Utils.du_fmap_224
             (coe MAlonzo.Code.Utils.du_EitherP_274) (coe C_'96'_18) (coe v0 v2)
      MAlonzo.Code.RawU.C_ULambda_150 v2
        -> coe
             MAlonzo.Code.Utils.du_fmap_224
             (coe MAlonzo.Code.Utils.du_EitherP_274) (coe C_ƛ_20)
             (coe du_scopeCheckU_256 (coe du_extG''_242 (coe v0)) (coe v2))
      MAlonzo.Code.RawU.C_UApp_152 v2 v3
        -> coe
             MAlonzo.Code.Utils.du_eitherBind_42
             (coe du_scopeCheckU_256 (coe v0) (coe v2))
             (coe
                (\ v4 ->
                   coe
                     MAlonzo.Code.Utils.du_eitherBind_42
                     (coe du_scopeCheckU_256 (coe v0) (coe v3))
                     (coe
                        (\ v5 ->
                           coe
                             MAlonzo.Code.Utils.C_inj'8322'_14
                             (coe C__'183'__22 (coe v4) (coe v5))))))
      MAlonzo.Code.RawU.C_UCon_154 v2
        -> coe
             MAlonzo.Code.Utils.C_inj'8322'_14
             (coe C_con_28 (coe MAlonzo.Code.RawU.d_tagCon2TmCon_226 (coe v2)))
      MAlonzo.Code.RawU.C_UError_156
        -> coe MAlonzo.Code.Utils.C_inj'8322'_14 (coe C_error_46)
      MAlonzo.Code.RawU.C_UBuiltin_158 v2
        -> coe
             MAlonzo.Code.Utils.C_inj'8322'_14 (coe C_builtin_44 (coe v2))
      MAlonzo.Code.RawU.C_UDelay_160 v2
        -> coe
             MAlonzo.Code.Utils.du_fmap_224
             (coe MAlonzo.Code.Utils.du_EitherP_274) (coe C_delay_26)
             (coe du_scopeCheckU_256 (coe v0) (coe v2))
      MAlonzo.Code.RawU.C_UForce_162 v2
        -> coe
             MAlonzo.Code.Utils.du_fmap_224
             (coe MAlonzo.Code.Utils.du_EitherP_274) (coe C_force_24)
             (coe du_scopeCheckU_256 (coe v0) (coe v2))
      MAlonzo.Code.RawU.C_UConstr_164 v2 v3
        -> coe
             MAlonzo.Code.Utils.du_fmap_224
             (coe MAlonzo.Code.Utils.du_EitherP_274) (coe C_constr_34 (coe v2))
             (coe du_scopeCheckUList_252 (coe v0) (coe v3))
      MAlonzo.Code.RawU.C_UCase_166 v2 v3
        -> coe
             MAlonzo.Code.Utils.du_eitherBind_42
             (coe du_scopeCheckU_256 (coe v0) (coe v2))
             (coe
                (\ v4 ->
                   coe
                     MAlonzo.Code.Utils.du_eitherBind_42
                     (coe du_scopeCheckUList_252 (coe v0) (coe v3))
                     (coe
                        (\ v5 ->
                           coe
                             MAlonzo.Code.Utils.C_inj'8322'_14
                             (coe C_case_40 (coe v4) (coe v5))))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Untyped.scopeCheckU0
d_scopeCheckU0_322 ::
  MAlonzo.Code.RawU.T_Untyped_146 ->
  MAlonzo.Code.Utils.T_Either_6
    MAlonzo.Code.Scoped.T_ScopeError_576 T__'8866'_14
d_scopeCheckU0_322 v0
  = coe
      du_scopeCheckU_256
      (coe
         (\ v1 ->
            coe
              MAlonzo.Code.Utils.C_inj'8321'_12
              (coe MAlonzo.Code.Scoped.C_deBError_578)))
      (coe v0)
-- Untyped.decUTm
d_decUTm_332 ::
  MAlonzo.Code.RawU.T_Untyped_146 ->
  MAlonzo.Code.RawU.T_Untyped_146 -> Bool
d_decUTm_332 v0 v1
  = let v2 = coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8 in
    coe
      (case coe v0 of
         MAlonzo.Code.RawU.C_UVar_148 v3
           -> case coe v1 of
                MAlonzo.Code.RawU.C_UVar_148 v4
                  -> coe
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
                       (coe
                          MAlonzo.Code.Data.Nat.Properties.d__'8799'__2688 (coe v3) (coe v3))
                _ -> coe v2
         MAlonzo.Code.RawU.C_ULambda_150 v3
           -> case coe v1 of
                MAlonzo.Code.RawU.C_ULambda_150 v4
                  -> coe d_decUTm_332 (coe v3) (coe v4)
                _ -> coe v2
         MAlonzo.Code.RawU.C_UApp_152 v3 v4
           -> case coe v1 of
                MAlonzo.Code.RawU.C_UApp_152 v5 v6
                  -> coe
                       MAlonzo.Code.Data.Bool.Base.d__'8743'__24
                       (coe d_decUTm_332 (coe v3) (coe v5))
                       (coe d_decUTm_332 (coe v4) (coe v6))
                _ -> coe v2
         MAlonzo.Code.RawU.C_UCon_154 v3
           -> case coe v1 of
                MAlonzo.Code.RawU.C_UCon_154 v4
                  -> coe MAlonzo.Code.RawU.d_decTagCon_136 (coe v3) (coe v4)
                _ -> coe v2
         MAlonzo.Code.RawU.C_UError_156
           -> case coe v1 of
                MAlonzo.Code.RawU.C_UError_156
                  -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
                _ -> coe v2
         MAlonzo.Code.RawU.C_UBuiltin_158 v3
           -> case coe v1 of
                MAlonzo.Code.RawU.C_UBuiltin_158 v4
                  -> coe
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
                       (coe MAlonzo.Code.Builtin.d_decBuiltin_404 (coe v3) (coe v4))
                _ -> coe v2
         MAlonzo.Code.RawU.C_UDelay_160 v3
           -> case coe v1 of
                MAlonzo.Code.RawU.C_UDelay_160 v4
                  -> coe d_decUTm_332 (coe v3) (coe v4)
                _ -> coe v2
         MAlonzo.Code.RawU.C_UForce_162 v3
           -> case coe v1 of
                MAlonzo.Code.RawU.C_UForce_162 v4
                  -> coe d_decUTm_332 (coe v3) (coe v4)
                _ -> coe v2
         _ -> coe v2)
-- Untyped.buildDebruijnEncoding
d_buildDebruijnEncoding_368 ::
  () ->
  Integer ->
  MAlonzo.Code.Utils.T_Either_6
    MAlonzo.Code.Scoped.T_ScopeError_576 (Maybe AgdaAny)
d_buildDebruijnEncoding_368 ~v0 v1
  = du_buildDebruijnEncoding_368 v1
du_buildDebruijnEncoding_368 ::
  Integer ->
  MAlonzo.Code.Utils.T_Either_6
    MAlonzo.Code.Scoped.T_ScopeError_576 (Maybe AgdaAny)
du_buildDebruijnEncoding_368 v0
  = coe
      du_extG''_242
      (coe
         (\ v1 ->
            coe
              MAlonzo.Code.Utils.C_inj'8321'_12
              (coe MAlonzo.Code.Scoped.C_deBError_578)))
      (coe v0)
-- Untyped.toWellScoped
d_toWellScoped_376 ::
  () ->
  MAlonzo.Code.RawU.T_Untyped_146 ->
  MAlonzo.Code.Utils.T_Either_6
    MAlonzo.Code.Scoped.T_ScopeError_576 T__'8866'_14
d_toWellScoped_376 ~v0 = du_toWellScoped_376
du_toWellScoped_376 ::
  MAlonzo.Code.RawU.T_Untyped_146 ->
  MAlonzo.Code.Utils.T_Either_6
    MAlonzo.Code.Scoped.T_ScopeError_576 T__'8866'_14
du_toWellScoped_376
  = coe du_scopeCheckU_256 (coe du_buildDebruijnEncoding_368)
-- Untyped.make-integer
d_make'45'integer_378 ::
  MAlonzo.Code.Builtin.Signature.T__'8866''9839'_4
d_make'45'integer_378
  = coe
      MAlonzo.Code.RawU.du_tag2TyTag_206
      (coe MAlonzo.Code.RawU.C_integer_30)
-- Untyped.con-integer
d_con'45'integer_382 :: () -> Integer -> T__'8866'_14
d_con'45'integer_382 ~v0 v1 = du_con'45'integer_382 v1
du_con'45'integer_382 :: Integer -> T__'8866'_14
du_con'45'integer_382 v0
  = coe
      C_con_28
      (coe
         MAlonzo.Code.RawU.C_tmCon_202 (coe d_make'45'integer_378) (coe v0))
