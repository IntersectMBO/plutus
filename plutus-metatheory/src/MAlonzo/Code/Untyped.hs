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

module MAlonzo.Code.Untyped where

import Data.Text qualified
import MAlonzo.Code.Agda.Builtin.Bool qualified
import MAlonzo.Code.Agda.Builtin.List qualified
import MAlonzo.Code.Agda.Builtin.Maybe qualified
import MAlonzo.Code.Agda.Builtin.Nat qualified
import MAlonzo.Code.Agda.Builtin.String qualified
import MAlonzo.Code.Builtin qualified
import MAlonzo.Code.Builtin.Constant.AtomicType qualified
import MAlonzo.Code.Builtin.Signature qualified
import MAlonzo.Code.Data.Bool.Base qualified
import MAlonzo.Code.Data.Integer.Show qualified
import MAlonzo.Code.Data.Nat.Properties qualified
import MAlonzo.Code.Data.Nat.Show qualified
import MAlonzo.Code.Data.String.Base qualified
import MAlonzo.Code.RawU qualified
import MAlonzo.Code.Relation.Nullary.Decidable.Core qualified
import MAlonzo.Code.Scoped qualified
import MAlonzo.Code.Utils qualified
import MAlonzo.RTE (AgdaAny, add64, addInt, coe, eq64, eqInt, erased, geqInt, lt64, ltInt, mul64,
                    mulInt, quot64, quotInt, rem64, remInt, sub64, subInt, word64FromNat,
                    word64ToNat)
import MAlonzo.RTE qualified

import Data.Text qualified as T
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
                           then coe
                                  MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                  ("(bool " :: Data.Text.Text)
                                  (coe
                                     MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                     ("true" :: Data.Text.Text) (")" :: Data.Text.Text))
                           else coe
                                  MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                  ("(bool " :: Data.Text.Text)
                                  (coe
                                     MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                     ("false" :: Data.Text.Text) (")" :: Data.Text.Text))
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
               -> coe ("(list [ something ])" :: Data.Text.Text)
             MAlonzo.Code.Builtin.Signature.C_pair_20 v4 v5
               -> case coe v2 of
                    MAlonzo.Code.Utils.C__'44'__380 v6 v7
                      -> coe
                           MAlonzo.Code.Data.String.Base.d__'43''43'__20
                           ("(pair " :: Data.Text.Text)
                           (coe
                              MAlonzo.Code.Data.String.Base.d__'43''43'__20
                              (d_uglyTmCon_68
                                 (coe MAlonzo.Code.RawU.C_tmCon_202 (coe v4) (coe v6)))
                              (coe
                                 MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                 (" " :: Data.Text.Text)
                                 (coe
                                    MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                    (d_uglyTmCon_68
                                       (coe MAlonzo.Code.RawU.C_tmCon_202 (coe v5) (coe v7)))
                                    (")" :: Data.Text.Text))))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Untyped.showNat
d_showNat_96 ::
  Integer -> MAlonzo.Code.Agda.Builtin.String.T_String_6
d_showNat_96 = T.pack . show
-- Untyped.uglyBuiltin
d_uglyBuiltin_98 ::
  MAlonzo.Code.Builtin.T_Builtin_2 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_uglyBuiltin_98 v0
  = let v1 = "other" :: Data.Text.Text in
    coe
      (case coe v0 of
         MAlonzo.Code.Builtin.C_addInteger_4
           -> coe ("addInteger" :: Data.Text.Text)
         _ -> coe v1)
-- Untyped.uglyList
d_uglyList_102 ::
  () -> [T__'8866'_14] -> MAlonzo.Code.Agda.Builtin.String.T_String_6
d_uglyList_102 ~v0 v1 = du_uglyList_102 v1
du_uglyList_102 ::
  [T__'8866'_14] -> MAlonzo.Code.Agda.Builtin.String.T_String_6
du_uglyList_102 v0
  = coe
      MAlonzo.Code.Data.String.Base.d__'43''43'__20
      ("[" :: Data.Text.Text)
      (coe
         MAlonzo.Code.Data.String.Base.d__'43''43'__20
         (coe du_uglyList''_106 (coe v0)) ("]" :: Data.Text.Text))
-- Untyped.uglyList'
d_uglyList''_106 ::
  () -> [T__'8866'_14] -> MAlonzo.Code.Agda.Builtin.String.T_String_6
d_uglyList''_106 ~v0 v1 = du_uglyList''_106 v1
du_uglyList''_106 ::
  [T__'8866'_14] -> MAlonzo.Code.Agda.Builtin.String.T_String_6
du_uglyList''_106 v0
  = case coe v0 of
      [] -> coe ("" :: Data.Text.Text)
      (:) v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             (coe du_ugly_110 (coe v1))
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (" , " :: Data.Text.Text) (coe du_uglyList''_106 (coe v2)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Untyped.ugly
d_ugly_110 ::
  () -> T__'8866'_14 -> MAlonzo.Code.Agda.Builtin.String.T_String_6
d_ugly_110 ~v0 v1 = du_ugly_110 v1
du_ugly_110 ::
  T__'8866'_14 -> MAlonzo.Code.Agda.Builtin.String.T_String_6
du_ugly_110 v0
  = case coe v0 of
      C_'96'_18 v1 -> coe ("(` var )" :: Data.Text.Text)
      C_ƛ_20 v1
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("(\411 " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (coe du_ugly_110 (coe v1)) (")" :: Data.Text.Text))
      C__'183'__22 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("( " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (coe du_ugly_110 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (" \183 " :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (coe du_ugly_110 (coe v2)) (")" :: Data.Text.Text))))
      C_force_24 v1
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("(force " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (coe du_ugly_110 (coe v1)) (")" :: Data.Text.Text))
      C_delay_26 v1
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("(delay " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (coe du_ugly_110 (coe v1)) (")" :: Data.Text.Text))
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
                   (coe du_uglyList_102 (coe v2)) (")" :: Data.Text.Text)))
      C_case_40 v1 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("(case " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (coe du_ugly_110 (coe v1))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (" " :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (coe du_uglyList_102 (coe v2)) (")" :: Data.Text.Text))))
      C_builtin_44 v1
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("(builtin " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_uglyBuiltin_98 (coe v1)) (")" :: Data.Text.Text))
      C_error_46 -> coe ("error" :: Data.Text.Text)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Untyped.extG
d_extG_144 ::
  () -> (AgdaAny -> Integer) -> Maybe AgdaAny -> Integer
d_extG_144 ~v0 v1 v2 = du_extG_144 v1 v2
du_extG_144 :: (AgdaAny -> Integer) -> Maybe AgdaAny -> Integer
du_extG_144 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
        -> coe addInt (coe (1 :: Integer)) (coe v0 v2)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe (0 :: Integer)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Untyped.extricateUList
d_extricateUList_154 ::
  () ->
  (AgdaAny -> Integer) ->
  [T__'8866'_14] ->
  MAlonzo.Code.Utils.T_List_384 MAlonzo.Code.RawU.T_Untyped_146
d_extricateUList_154 ~v0 v1 v2 = du_extricateUList_154 v1 v2
du_extricateUList_154 ::
  (AgdaAny -> Integer) ->
  [T__'8866'_14] ->
  MAlonzo.Code.Utils.T_List_384 MAlonzo.Code.RawU.T_Untyped_146
du_extricateUList_154 v0 v1
  = case coe v1 of
      [] -> coe MAlonzo.Code.Utils.C_'91''93'_388
      (:) v2 v3
        -> coe
             MAlonzo.Code.Utils.C__'8759'__390
             (coe du_extricateU_158 (coe v0) (coe v2))
             (coe du_extricateUList_154 (coe v0) (coe v3))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Untyped.extricateU
d_extricateU_158 ::
  () ->
  (AgdaAny -> Integer) ->
  T__'8866'_14 -> MAlonzo.Code.RawU.T_Untyped_146
d_extricateU_158 ~v0 v1 v2 = du_extricateU_158 v1 v2
du_extricateU_158 ::
  (AgdaAny -> Integer) ->
  T__'8866'_14 -> MAlonzo.Code.RawU.T_Untyped_146
du_extricateU_158 v0 v1
  = case coe v1 of
      C_'96'_18 v2 -> coe MAlonzo.Code.RawU.C_UVar_148 (coe v0 v2)
      C_ƛ_20 v2
        -> coe
             MAlonzo.Code.RawU.C_ULambda_150
             (coe du_extricateU_158 (coe du_extG_144 (coe v0)) (coe v2))
      C__'183'__22 v2 v3
        -> coe
             MAlonzo.Code.RawU.C_UApp_152
             (coe du_extricateU_158 (coe v0) (coe v2))
             (coe du_extricateU_158 (coe v0) (coe v3))
      C_force_24 v2
        -> coe
             MAlonzo.Code.RawU.C_UForce_162
             (coe du_extricateU_158 (coe v0) (coe v2))
      C_delay_26 v2
        -> coe
             MAlonzo.Code.RawU.C_UDelay_160
             (coe du_extricateU_158 (coe v0) (coe v2))
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
                       (coe du_extricateU_158 (coe v0) (coe v4))
                       (coe du_extricateUList_154 (coe v0) (coe v5)))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_case_40 v2 v3
        -> coe
             MAlonzo.Code.RawU.C_UCase_166
             (coe du_extricateU_158 (coe v0) (coe v2))
             (coe du_extricateUList_154 (coe v0) (coe v3))
      C_builtin_44 v2 -> coe MAlonzo.Code.RawU.C_UBuiltin_158 (coe v2)
      C_error_46 -> coe MAlonzo.Code.RawU.C_UError_156
      _ -> MAlonzo.RTE.mazUnreachableError
-- Untyped.extricateU0
d_extricateU0_218 ::
  T__'8866'_14 -> MAlonzo.Code.RawU.T_Untyped_146
d_extricateU0_218 v0 = coe du_extricateU_158 erased (coe v0)
-- Untyped.extG'
d_extG''_224 ::
  () ->
  (Integer ->
   MAlonzo.Code.Utils.T_Either_6
     MAlonzo.Code.Scoped.T_ScopeError_576 AgdaAny) ->
  Integer ->
  MAlonzo.Code.Utils.T_Either_6
    MAlonzo.Code.Scoped.T_ScopeError_576 (Maybe AgdaAny)
d_extG''_224 ~v0 v1 v2 = du_extG''_224 v1 v2
du_extG''_224 ::
  (Integer ->
   MAlonzo.Code.Utils.T_Either_6
     MAlonzo.Code.Scoped.T_ScopeError_576 AgdaAny) ->
  Integer ->
  MAlonzo.Code.Utils.T_Either_6
    MAlonzo.Code.Scoped.T_ScopeError_576 (Maybe AgdaAny)
du_extG''_224 v0 v1
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
d_scopeCheckUList_234 ::
  () ->
  (Integer ->
   MAlonzo.Code.Utils.T_Either_6
     MAlonzo.Code.Scoped.T_ScopeError_576 AgdaAny) ->
  MAlonzo.Code.Utils.T_List_384 MAlonzo.Code.RawU.T_Untyped_146 ->
  MAlonzo.Code.Utils.T_Either_6
    MAlonzo.Code.Scoped.T_ScopeError_576 [T__'8866'_14]
d_scopeCheckUList_234 ~v0 v1 v2 = du_scopeCheckUList_234 v1 v2
du_scopeCheckUList_234 ::
  (Integer ->
   MAlonzo.Code.Utils.T_Either_6
     MAlonzo.Code.Scoped.T_ScopeError_576 AgdaAny) ->
  MAlonzo.Code.Utils.T_List_384 MAlonzo.Code.RawU.T_Untyped_146 ->
  MAlonzo.Code.Utils.T_Either_6
    MAlonzo.Code.Scoped.T_ScopeError_576 [T__'8866'_14]
du_scopeCheckUList_234 v0 v1
  = case coe v1 of
      MAlonzo.Code.Utils.C_'91''93'_388
        -> coe
             MAlonzo.Code.Utils.C_inj'8322'_14
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Utils.C__'8759'__390 v2 v3
        -> coe
             MAlonzo.Code.Utils.du_eitherBind_42
             (coe du_scopeCheckU_238 (coe v0) (coe v2))
             (coe
                (\ v4 ->
                   coe
                     MAlonzo.Code.Utils.du_eitherBind_42
                     (coe du_scopeCheckUList_234 (coe v0) (coe v3))
                     (coe
                        (\ v5 ->
                           coe
                             MAlonzo.Code.Utils.C_inj'8322'_14
                             (coe
                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v4) (coe v5))))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Untyped.scopeCheckU
d_scopeCheckU_238 ::
  () ->
  (Integer ->
   MAlonzo.Code.Utils.T_Either_6
     MAlonzo.Code.Scoped.T_ScopeError_576 AgdaAny) ->
  MAlonzo.Code.RawU.T_Untyped_146 ->
  MAlonzo.Code.Utils.T_Either_6
    MAlonzo.Code.Scoped.T_ScopeError_576 T__'8866'_14
d_scopeCheckU_238 ~v0 v1 v2 = du_scopeCheckU_238 v1 v2
du_scopeCheckU_238 ::
  (Integer ->
   MAlonzo.Code.Utils.T_Either_6
     MAlonzo.Code.Scoped.T_ScopeError_576 AgdaAny) ->
  MAlonzo.Code.RawU.T_Untyped_146 ->
  MAlonzo.Code.Utils.T_Either_6
    MAlonzo.Code.Scoped.T_ScopeError_576 T__'8866'_14
du_scopeCheckU_238 v0 v1
  = case coe v1 of
      MAlonzo.Code.RawU.C_UVar_148 v2
        -> coe
             MAlonzo.Code.Utils.du_fmap_224
             (coe MAlonzo.Code.Utils.du_EitherP_274) (coe C_'96'_18) (coe v0 v2)
      MAlonzo.Code.RawU.C_ULambda_150 v2
        -> coe
             MAlonzo.Code.Utils.du_fmap_224
             (coe MAlonzo.Code.Utils.du_EitherP_274) (coe C_ƛ_20)
             (coe du_scopeCheckU_238 (coe du_extG''_224 (coe v0)) (coe v2))
      MAlonzo.Code.RawU.C_UApp_152 v2 v3
        -> coe
             MAlonzo.Code.Utils.du_eitherBind_42
             (coe du_scopeCheckU_238 (coe v0) (coe v2))
             (coe
                (\ v4 ->
                   coe
                     MAlonzo.Code.Utils.du_eitherBind_42
                     (coe du_scopeCheckU_238 (coe v0) (coe v3))
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
             (coe du_scopeCheckU_238 (coe v0) (coe v2))
      MAlonzo.Code.RawU.C_UForce_162 v2
        -> coe
             MAlonzo.Code.Utils.du_fmap_224
             (coe MAlonzo.Code.Utils.du_EitherP_274) (coe C_force_24)
             (coe du_scopeCheckU_238 (coe v0) (coe v2))
      MAlonzo.Code.RawU.C_UConstr_164 v2 v3
        -> coe
             MAlonzo.Code.Utils.du_fmap_224
             (coe MAlonzo.Code.Utils.du_EitherP_274) (coe C_constr_34 (coe v2))
             (coe du_scopeCheckUList_234 (coe v0) (coe v3))
      MAlonzo.Code.RawU.C_UCase_166 v2 v3
        -> coe
             MAlonzo.Code.Utils.du_eitherBind_42
             (coe du_scopeCheckU_238 (coe v0) (coe v2))
             (coe
                (\ v4 ->
                   coe
                     MAlonzo.Code.Utils.du_eitherBind_42
                     (coe du_scopeCheckUList_234 (coe v0) (coe v3))
                     (coe
                        (\ v5 ->
                           coe
                             MAlonzo.Code.Utils.C_inj'8322'_14
                             (coe C_case_40 (coe v4) (coe v5))))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Untyped.scopeCheckU0
d_scopeCheckU0_304 ::
  MAlonzo.Code.RawU.T_Untyped_146 ->
  MAlonzo.Code.Utils.T_Either_6
    MAlonzo.Code.Scoped.T_ScopeError_576 T__'8866'_14
d_scopeCheckU0_304 v0
  = coe
      du_scopeCheckU_238
      (coe
         (\ v1 ->
            coe
              MAlonzo.Code.Utils.C_inj'8321'_12
              (coe MAlonzo.Code.Scoped.C_deBError_578)))
      (coe v0)
-- Untyped.decUTm
d_decUTm_314 ::
  MAlonzo.Code.RawU.T_Untyped_146 ->
  MAlonzo.Code.RawU.T_Untyped_146 -> Bool
d_decUTm_314 v0 v1
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
                  -> coe d_decUTm_314 (coe v3) (coe v4)
                _ -> coe v2
         MAlonzo.Code.RawU.C_UApp_152 v3 v4
           -> case coe v1 of
                MAlonzo.Code.RawU.C_UApp_152 v5 v6
                  -> coe
                       MAlonzo.Code.Data.Bool.Base.d__'8743'__24
                       (coe d_decUTm_314 (coe v3) (coe v5))
                       (coe d_decUTm_314 (coe v4) (coe v6))
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
                  -> coe d_decUTm_314 (coe v3) (coe v4)
                _ -> coe v2
         MAlonzo.Code.RawU.C_UForce_162 v3
           -> case coe v1 of
                MAlonzo.Code.RawU.C_UForce_162 v4
                  -> coe d_decUTm_314 (coe v3) (coe v4)
                _ -> coe v2
         _ -> coe v2)
-- Untyped.buildDebruijnEncoding
d_buildDebruijnEncoding_350 ::
  () ->
  Integer ->
  MAlonzo.Code.Utils.T_Either_6
    MAlonzo.Code.Scoped.T_ScopeError_576 (Maybe AgdaAny)
d_buildDebruijnEncoding_350 ~v0 v1
  = du_buildDebruijnEncoding_350 v1
du_buildDebruijnEncoding_350 ::
  Integer ->
  MAlonzo.Code.Utils.T_Either_6
    MAlonzo.Code.Scoped.T_ScopeError_576 (Maybe AgdaAny)
du_buildDebruijnEncoding_350 v0
  = coe
      du_extG''_224
      (coe
         (\ v1 ->
            coe
              MAlonzo.Code.Utils.C_inj'8321'_12
              (coe MAlonzo.Code.Scoped.C_deBError_578)))
      (coe v0)
-- Untyped.toWellScoped
d_toWellScoped_358 ::
  () ->
  MAlonzo.Code.RawU.T_Untyped_146 ->
  MAlonzo.Code.Utils.T_Either_6
    MAlonzo.Code.Scoped.T_ScopeError_576 T__'8866'_14
d_toWellScoped_358 ~v0 = du_toWellScoped_358
du_toWellScoped_358 ::
  MAlonzo.Code.RawU.T_Untyped_146 ->
  MAlonzo.Code.Utils.T_Either_6
    MAlonzo.Code.Scoped.T_ScopeError_576 T__'8866'_14
du_toWellScoped_358
  = coe du_scopeCheckU_238 (coe du_buildDebruijnEncoding_350)
-- Untyped.make-integer
d_make'45'integer_360 ::
  MAlonzo.Code.Builtin.Signature.T__'8866''9839'_4
d_make'45'integer_360
  = coe
      MAlonzo.Code.RawU.du_tag2TyTag_206
      (coe MAlonzo.Code.RawU.C_integer_30)
-- Untyped.con-integer
d_con'45'integer_364 :: () -> Integer -> T__'8866'_14
d_con'45'integer_364 ~v0 v1 = du_con'45'integer_364 v1
du_con'45'integer_364 :: Integer -> T__'8866'_14
du_con'45'integer_364 v0
  = coe
      C_con_28
      (coe
         MAlonzo.Code.RawU.C_tmCon_202 (coe d_make'45'integer_360) (coe v0))
