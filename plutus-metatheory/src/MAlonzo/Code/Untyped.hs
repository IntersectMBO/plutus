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
import qualified MAlonzo.Code.Data.Fin.Base
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
  = C_'96'_18 MAlonzo.Code.Data.Fin.Base.T_Fin_10 |
    C_ƛ_20 T__'8866'_14 | C__'183'__22 T__'8866'_14 T__'8866'_14 |
    C_force_24 T__'8866'_14 | C_delay_26 T__'8866'_14 |
    C_con_28 MAlonzo.Code.RawU.T_TmCon_202 |
    C_constr_34 Integer [T__'8866'_14] |
    C_case_40 T__'8866'_14 [T__'8866'_14] |
    C_builtin_44 MAlonzo.Code.Builtin.T_Builtin_2 | C_error_46
-- Untyped.uglyDATA
d_uglyDATA_196 ::
  MAlonzo.Code.Utils.T_DATA_618 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_uglyDATA_196 ~v0 = du_uglyDATA_196
du_uglyDATA_196 :: MAlonzo.Code.Agda.Builtin.String.T_String_6
du_uglyDATA_196 = coe ("(DATA)" :: Data.Text.Text)
-- Untyped.uglyTmCon
d_uglyTmCon_200 ::
  MAlonzo.Code.RawU.T_TmCon_202 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_uglyTmCon_200 v0
  = case coe v0 of
      MAlonzo.Code.RawU.C_tmCon_206 v1 v2
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
                      -> coe du_uglyDATA_196
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
                       (d_uglyTmConList_204 (coe v4) (coe v2)) (" ])" :: Data.Text.Text))
             MAlonzo.Code.Builtin.Signature.C_array_20 v4
               -> coe ("(array [ something ])" :: Data.Text.Text)
             MAlonzo.Code.Builtin.Signature.C_pair_24 v4 v5
               -> case coe v2 of
                    MAlonzo.Code.Utils.C__'44'__450 v6 v7
                      -> coe
                           MAlonzo.Code.Data.String.Base.d__'43''43'__20
                           ("(pair (" :: Data.Text.Text)
                           (coe
                              MAlonzo.Code.Data.String.Base.d__'43''43'__20
                              (d_uglyTmCon_200
                                 (coe MAlonzo.Code.RawU.C_tmCon_206 (coe v4) (coe v6)))
                              (coe
                                 MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                 (" , " :: Data.Text.Text)
                                 (coe
                                    MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                    (d_uglyTmCon_200
                                       (coe MAlonzo.Code.RawU.C_tmCon_206 (coe v5) (coe v7)))
                                    (") )" :: Data.Text.Text))))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Untyped.uglyTmConList
d_uglyTmConList_204 ::
  MAlonzo.Code.Builtin.Signature.T__'8866''9839'_4 ->
  MAlonzo.Code.Utils.T_List_454 AgdaAny ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_uglyTmConList_204 v0 v1
  = case coe v1 of
      MAlonzo.Code.Utils.C_'91''93'_458 -> coe ("" :: Data.Text.Text)
      MAlonzo.Code.Utils.C__'8759'__460 v2 v3
        -> case coe v3 of
             MAlonzo.Code.Utils.C_'91''93'_458
               -> coe
                    d_uglyTmCon_200
                    (coe MAlonzo.Code.RawU.C_tmCon_206 (coe v0) (coe v2))
             MAlonzo.Code.Utils.C__'8759'__460 v4 v5
               -> coe
                    MAlonzo.Code.Data.String.Base.d__'43''43'__20
                    (d_uglyTmCon_200
                       (coe MAlonzo.Code.RawU.C_tmCon_206 (coe v0) (coe v2)))
                    (coe
                       MAlonzo.Code.Data.String.Base.d__'43''43'__20
                       (" , " :: Data.Text.Text) (d_uglyTmConList_204 (coe v0) (coe v3)))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Untyped.showNat
d_showNat_250 ::
  Integer -> MAlonzo.Code.Agda.Builtin.String.T_String_6
d_showNat_250 = T.pack . show
-- Untyped.uglyBuiltin
d_uglyBuiltin_252 ::
  MAlonzo.Code.Builtin.T_Builtin_2 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_uglyBuiltin_252 v0
  = let v1 = "other" :: Data.Text.Text in
    coe
      (case coe v0 of
         MAlonzo.Code.Builtin.C_addInteger_4
           -> coe ("addInteger" :: Data.Text.Text)
         _ -> coe v1)
-- Untyped.uglyList
d_uglyList_256 ::
  Integer ->
  [T__'8866'_14] -> MAlonzo.Code.Agda.Builtin.String.T_String_6
d_uglyList_256 v0 v1
  = coe
      MAlonzo.Code.Data.String.Base.d__'43''43'__20
      ("[" :: Data.Text.Text)
      (coe
         MAlonzo.Code.Data.String.Base.d__'43''43'__20
         (d_uglyList''_260 (coe v0) (coe v1)) ("]" :: Data.Text.Text))
-- Untyped.uglyList'
d_uglyList''_260 ::
  Integer ->
  [T__'8866'_14] -> MAlonzo.Code.Agda.Builtin.String.T_String_6
d_uglyList''_260 v0 v1
  = case coe v1 of
      [] -> coe ("" :: Data.Text.Text)
      (:) v2 v3
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             (d_ugly_264 (coe v0) (coe v2))
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (" , " :: Data.Text.Text) (d_uglyList''_260 (coe v0) (coe v3)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Untyped.ugly
d_ugly_264 ::
  Integer ->
  T__'8866'_14 -> MAlonzo.Code.Agda.Builtin.String.T_String_6
d_ugly_264 v0 v1
  = case coe v1 of
      C_'96'_18 v2 -> coe ("(` var )" :: Data.Text.Text)
      C_ƛ_20 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("(\411 " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_ugly_264 (coe addInt (coe (1 :: Integer)) (coe v0)) (coe v2))
                (")" :: Data.Text.Text))
      C__'183'__22 v2 v3
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("( " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_ugly_264 (coe v0) (coe v2))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (" \183 " :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (d_ugly_264 (coe v0) (coe v3)) (")" :: Data.Text.Text))))
      C_force_24 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("(force " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_ugly_264 (coe v0) (coe v2)) (")" :: Data.Text.Text))
      C_delay_26 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("(delay " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_ugly_264 (coe v0) (coe v2)) (")" :: Data.Text.Text))
      C_con_28 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("(con " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_uglyTmCon_200 (coe v2)) (")" :: Data.Text.Text))
      C_constr_34 v2 v3
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("(constr " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (coe MAlonzo.Code.Data.Nat.Show.d_show_56 v2)
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (d_uglyList_256 (coe v0) (coe v3)) (")" :: Data.Text.Text)))
      C_case_40 v2 v3
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("(case " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_ugly_264 (coe v0) (coe v2))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (" " :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (d_uglyList_256 (coe v0) (coe v3)) (")" :: Data.Text.Text))))
      C_builtin_44 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("(builtin " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (d_uglyBuiltin_252 (coe v2)) (")" :: Data.Text.Text))
      C_error_46 -> coe ("error" :: Data.Text.Text)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Untyped.extG
d_extG_298 ::
  () -> (AgdaAny -> Integer) -> Maybe AgdaAny -> Integer
d_extG_298 ~v0 v1 v2 = du_extG_298 v1 v2
du_extG_298 :: (AgdaAny -> Integer) -> Maybe AgdaAny -> Integer
du_extG_298 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
        -> coe addInt (coe (1 :: Integer)) (coe v0 v2)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe (0 :: Integer)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Untyped.extricateUList
d_extricateUList_308 ::
  Integer ->
  [T__'8866'_14] ->
  MAlonzo.Code.Utils.T_List_454 MAlonzo.Code.RawU.T_Untyped_208
d_extricateUList_308 v0 v1
  = case coe v1 of
      [] -> coe MAlonzo.Code.Utils.C_'91''93'_458
      (:) v2 v3
        -> coe
             MAlonzo.Code.Utils.C__'8759'__460
             (coe d_extricateU_312 (coe v0) (coe v2))
             (coe d_extricateUList_308 (coe v0) (coe v3))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Untyped.extricateU
d_extricateU_312 ::
  Integer -> T__'8866'_14 -> MAlonzo.Code.RawU.T_Untyped_208
d_extricateU_312 v0 v1
  = case coe v1 of
      C_'96'_18 v2
        -> coe
             MAlonzo.Code.RawU.C_UVar_210
             (coe MAlonzo.Code.Data.Fin.Base.du_toℕ_18 (coe v2))
      C_ƛ_20 v2
        -> coe
             MAlonzo.Code.RawU.C_ULambda_212
             (coe
                d_extricateU_312 (coe addInt (coe (1 :: Integer)) (coe v0))
                (coe v2))
      C__'183'__22 v2 v3
        -> coe
             MAlonzo.Code.RawU.C_UApp_214
             (coe d_extricateU_312 (coe v0) (coe v2))
             (coe d_extricateU_312 (coe v0) (coe v3))
      C_force_24 v2
        -> coe
             MAlonzo.Code.RawU.C_UForce_224
             (coe d_extricateU_312 (coe v0) (coe v2))
      C_delay_26 v2
        -> coe
             MAlonzo.Code.RawU.C_UDelay_222
             (coe d_extricateU_312 (coe v0) (coe v2))
      C_con_28 v2
        -> coe
             MAlonzo.Code.RawU.C_UCon_216
             (coe MAlonzo.Code.RawU.d_tmCon2TagCon_368 (coe v2))
      C_constr_34 v2 v3
        -> case coe v3 of
             []
               -> coe
                    MAlonzo.Code.RawU.C_UConstr_226 (coe v2)
                    (coe MAlonzo.Code.Utils.C_'91''93'_458)
             (:) v4 v5
               -> coe
                    MAlonzo.Code.RawU.C_UConstr_226 (coe v2)
                    (coe
                       MAlonzo.Code.Utils.C__'8759'__460
                       (coe d_extricateU_312 (coe v0) (coe v4))
                       (coe d_extricateUList_308 (coe v0) (coe v5)))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_case_40 v2 v3
        -> coe
             MAlonzo.Code.RawU.C_UCase_228
             (coe d_extricateU_312 (coe v0) (coe v2))
             (coe d_extricateUList_308 (coe v0) (coe v3))
      C_builtin_44 v2 -> coe MAlonzo.Code.RawU.C_UBuiltin_220 (coe v2)
      C_error_46 -> coe MAlonzo.Code.RawU.C_UError_218
      _ -> MAlonzo.RTE.mazUnreachableError
-- Untyped.extricateU0
d_extricateU0_346 ::
  T__'8866'_14 -> MAlonzo.Code.RawU.T_Untyped_208
d_extricateU0_346 v0
  = coe d_extricateU_312 (coe (0 :: Integer)) (coe v0)
-- Untyped.extG'
d_extG''_352 ::
  () ->
  (Integer ->
   MAlonzo.Code.Utils.T_Either_6
     MAlonzo.Code.Scoped.T_ScopeError_576 AgdaAny) ->
  Integer ->
  MAlonzo.Code.Utils.T_Either_6
    MAlonzo.Code.Scoped.T_ScopeError_576 (Maybe AgdaAny)
d_extG''_352 ~v0 v1 v2 = du_extG''_352 v1 v2
du_extG''_352 ::
  (Integer ->
   MAlonzo.Code.Utils.T_Either_6
     MAlonzo.Code.Scoped.T_ScopeError_576 AgdaAny) ->
  Integer ->
  MAlonzo.Code.Utils.T_Either_6
    MAlonzo.Code.Scoped.T_ScopeError_576 (Maybe AgdaAny)
du_extG''_352 v0 v1
  = case coe v1 of
      0 -> coe
             MAlonzo.Code.Utils.C_inj'8322'_14
             (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18)
      _ -> let v2 = subInt (coe v1) (coe (1 :: Integer)) in
           coe
             (coe
                MAlonzo.Code.Utils.du_fmap_292
                (coe MAlonzo.Code.Utils.du_EitherP_344)
                (coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16) (coe v0 v2))
-- Untyped.scopeCheckUList
d_scopeCheckUList_362 ::
  Integer ->
  MAlonzo.Code.Utils.T_List_454 MAlonzo.Code.RawU.T_Untyped_208 ->
  MAlonzo.Code.Utils.T_Either_6
    MAlonzo.Code.Scoped.T_ScopeError_576 [T__'8866'_14]
d_scopeCheckUList_362 v0 v1
  = case coe v1 of
      MAlonzo.Code.Utils.C_'91''93'_458
        -> coe
             MAlonzo.Code.Utils.C_inj'8322'_14
             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      MAlonzo.Code.Utils.C__'8759'__460 v2 v3
        -> coe
             MAlonzo.Code.Utils.du_eitherBind_54
             (coe d_scopeCheckU_366 (coe v0) (coe v2))
             (coe
                (\ v4 ->
                   coe
                     MAlonzo.Code.Utils.du_eitherBind_54
                     (coe d_scopeCheckUList_362 (coe v0) (coe v3))
                     (coe
                        (\ v5 ->
                           coe
                             MAlonzo.Code.Utils.C_inj'8322'_14
                             (coe
                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v4) (coe v5))))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Untyped.scopeCheckU
d_scopeCheckU_366 ::
  Integer ->
  MAlonzo.Code.RawU.T_Untyped_208 ->
  MAlonzo.Code.Utils.T_Either_6
    MAlonzo.Code.Scoped.T_ScopeError_576 T__'8866'_14
d_scopeCheckU_366 v0 v1
  = case coe v1 of
      MAlonzo.Code.RawU.C_UVar_210 v2
        -> coe
             MAlonzo.Code.Utils.du_fmap_292
             (coe MAlonzo.Code.Utils.du_EitherP_344) (coe C_'96'_18)
             (coe
                MAlonzo.Code.Utils.du_maybeToEither_94
                (coe MAlonzo.Code.Scoped.C_deBError_578)
                (MAlonzo.Code.Utils.d_natToFin_118 (coe v0) (coe v2)))
      MAlonzo.Code.RawU.C_ULambda_212 v2
        -> coe
             MAlonzo.Code.Utils.du_fmap_292
             (coe MAlonzo.Code.Utils.du_EitherP_344) (coe C_ƛ_20)
             (coe
                d_scopeCheckU_366 (coe addInt (coe (1 :: Integer)) (coe v0))
                (coe v2))
      MAlonzo.Code.RawU.C_UApp_214 v2 v3
        -> coe
             MAlonzo.Code.Utils.du_eitherBind_54
             (coe d_scopeCheckU_366 (coe v0) (coe v2))
             (coe
                (\ v4 ->
                   coe
                     MAlonzo.Code.Utils.du_eitherBind_54
                     (coe d_scopeCheckU_366 (coe v0) (coe v3))
                     (coe
                        (\ v5 ->
                           coe
                             MAlonzo.Code.Utils.C_inj'8322'_14
                             (coe C__'183'__22 (coe v4) (coe v5))))))
      MAlonzo.Code.RawU.C_UCon_216 v2
        -> coe
             MAlonzo.Code.Utils.C_inj'8322'_14
             (coe C_con_28 (coe MAlonzo.Code.RawU.d_tagCon2TmCon_256 (coe v2)))
      MAlonzo.Code.RawU.C_UError_218
        -> coe MAlonzo.Code.Utils.C_inj'8322'_14 (coe C_error_46)
      MAlonzo.Code.RawU.C_UBuiltin_220 v2
        -> coe
             MAlonzo.Code.Utils.C_inj'8322'_14 (coe C_builtin_44 (coe v2))
      MAlonzo.Code.RawU.C_UDelay_222 v2
        -> coe
             MAlonzo.Code.Utils.du_fmap_292
             (coe MAlonzo.Code.Utils.du_EitherP_344) (coe C_delay_26)
             (coe d_scopeCheckU_366 (coe v0) (coe v2))
      MAlonzo.Code.RawU.C_UForce_224 v2
        -> coe
             MAlonzo.Code.Utils.du_fmap_292
             (coe MAlonzo.Code.Utils.du_EitherP_344) (coe C_force_24)
             (coe d_scopeCheckU_366 (coe v0) (coe v2))
      MAlonzo.Code.RawU.C_UConstr_226 v2 v3
        -> coe
             MAlonzo.Code.Utils.du_fmap_292
             (coe MAlonzo.Code.Utils.du_EitherP_344) (coe C_constr_34 (coe v2))
             (coe d_scopeCheckUList_362 (coe v0) (coe v3))
      MAlonzo.Code.RawU.C_UCase_228 v2 v3
        -> coe
             MAlonzo.Code.Utils.du_eitherBind_54
             (coe d_scopeCheckU_366 (coe v0) (coe v2))
             (coe
                (\ v4 ->
                   coe
                     MAlonzo.Code.Utils.du_eitherBind_54
                     (coe d_scopeCheckUList_362 (coe v0) (coe v3))
                     (coe
                        (\ v5 ->
                           coe
                             MAlonzo.Code.Utils.C_inj'8322'_14
                             (coe C_case_40 (coe v4) (coe v5))))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Untyped.scopeCheckU0
d_scopeCheckU0_408 ::
  MAlonzo.Code.RawU.T_Untyped_208 ->
  MAlonzo.Code.Utils.T_Either_6
    MAlonzo.Code.Scoped.T_ScopeError_576 T__'8866'_14
d_scopeCheckU0_408 v0
  = coe d_scopeCheckU_366 (coe (0 :: Integer)) (coe v0)
-- Untyped.decUTm
d_decUTm_416 ::
  MAlonzo.Code.RawU.T_Untyped_208 ->
  MAlonzo.Code.RawU.T_Untyped_208 -> Bool
d_decUTm_416 v0 v1
  = let v2 = coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8 in
    coe
      (case coe v0 of
         MAlonzo.Code.RawU.C_UVar_210 v3
           -> case coe v1 of
                MAlonzo.Code.RawU.C_UVar_210 v4
                  -> coe
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
                       (coe
                          MAlonzo.Code.Data.Nat.Properties.d__'8799'__2796 (coe v3) (coe v3))
                _ -> coe v2
         MAlonzo.Code.RawU.C_ULambda_212 v3
           -> case coe v1 of
                MAlonzo.Code.RawU.C_ULambda_212 v4
                  -> coe d_decUTm_416 (coe v3) (coe v4)
                _ -> coe v2
         MAlonzo.Code.RawU.C_UApp_214 v3 v4
           -> case coe v1 of
                MAlonzo.Code.RawU.C_UApp_214 v5 v6
                  -> coe
                       MAlonzo.Code.Data.Bool.Base.d__'8743'__24
                       (coe d_decUTm_416 (coe v3) (coe v5))
                       (coe d_decUTm_416 (coe v4) (coe v6))
                _ -> coe v2
         MAlonzo.Code.RawU.C_UCon_216 v3
           -> case coe v1 of
                MAlonzo.Code.RawU.C_UCon_216 v4
                  -> coe MAlonzo.Code.RawU.d_decTagCon_192 (coe v3) (coe v4)
                _ -> coe v2
         MAlonzo.Code.RawU.C_UError_218
           -> case coe v1 of
                MAlonzo.Code.RawU.C_UError_218
                  -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
                _ -> coe v2
         MAlonzo.Code.RawU.C_UBuiltin_220 v3
           -> case coe v1 of
                MAlonzo.Code.RawU.C_UBuiltin_220 v4
                  -> coe
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
                       (coe MAlonzo.Code.Builtin.d_decBuiltin_440 (coe v3) (coe v4))
                _ -> coe v2
         MAlonzo.Code.RawU.C_UDelay_222 v3
           -> case coe v1 of
                MAlonzo.Code.RawU.C_UDelay_222 v4
                  -> coe d_decUTm_416 (coe v3) (coe v4)
                _ -> coe v2
         MAlonzo.Code.RawU.C_UForce_224 v3
           -> case coe v1 of
                MAlonzo.Code.RawU.C_UForce_224 v4
                  -> coe d_decUTm_416 (coe v3) (coe v4)
                _ -> coe v2
         _ -> coe v2)
-- Untyped.buildDebruijnEncoding
d_buildDebruijnEncoding_452 ::
  () ->
  Integer ->
  MAlonzo.Code.Utils.T_Either_6
    MAlonzo.Code.Scoped.T_ScopeError_576 (Maybe AgdaAny)
d_buildDebruijnEncoding_452 ~v0 v1
  = du_buildDebruijnEncoding_452 v1
du_buildDebruijnEncoding_452 ::
  Integer ->
  MAlonzo.Code.Utils.T_Either_6
    MAlonzo.Code.Scoped.T_ScopeError_576 (Maybe AgdaAny)
du_buildDebruijnEncoding_452 v0
  = coe
      du_extG''_352
      (coe
         (\ v1 ->
            coe
              MAlonzo.Code.Utils.C_inj'8321'_12
              (coe MAlonzo.Code.Scoped.C_deBError_578)))
      (coe v0)
-- Untyped.make-integer
d_make'45'integer_458 ::
  MAlonzo.Code.Builtin.Signature.T__'8866''9839'_4
d_make'45'integer_458
  = coe
      MAlonzo.Code.RawU.du_tag2TyTag_232
      (coe MAlonzo.Code.RawU.C_integer_30)
-- Untyped.con-integer
d_con'45'integer_462 :: Integer -> Integer -> T__'8866'_14
d_con'45'integer_462 ~v0 v1 = du_con'45'integer_462 v1
du_con'45'integer_462 :: Integer -> T__'8866'_14
du_con'45'integer_462 v0
  = coe
      C_con_28
      (coe
         MAlonzo.Code.RawU.C_tmCon_206 (coe d_make'45'integer_458) (coe v0))
