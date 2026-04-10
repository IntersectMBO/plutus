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

module MAlonzo.Code.Untyped.Transform where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base
import qualified MAlonzo.Code.Data.Maybe.Base
import qualified MAlonzo.Code.Untyped
import qualified MAlonzo.Code.Untyped.Relation

-- Untyped.Transform._↑_
d__'8593'__8 ::
  (Integer ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Untyped.T__'8866'_14) ->
  Integer ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14
d__'8593'__8 v0 v1 v2
  = coe v0 v1 (d_subterms_20 (coe v0) (coe v1) (coe v2))
-- Untyped.Transform._↑*_
d__'8593''42'__14 ::
  (Integer ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Untyped.T__'8866'_14) ->
  Integer ->
  [MAlonzo.Code.Untyped.T__'8866'_14] ->
  [MAlonzo.Code.Untyped.T__'8866'_14]
d__'8593''42'__14 v0 v1 v2
  = case coe v2 of
      [] -> coe v2
      (:) v3 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe d__'8593'__8 (coe v0) (coe v1) (coe v3))
             (coe d__'8593''42'__14 (coe v0) (coe v1) (coe v4))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Untyped.Transform.subterms
d_subterms_20 ::
  (Integer ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Untyped.T__'8866'_14) ->
  Integer ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14
d_subterms_20 v0 v1 v2
  = coe du_'46'extendedlambda0_38 (coe v0) (coe v1) (coe v2)
-- Untyped.Transform..extendedlambda0
d_'46'extendedlambda0_38 ::
  (Integer ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Untyped.T__'8866'_14) ->
  Integer ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14
d_'46'extendedlambda0_38 v0 v1 ~v2 v3
  = du_'46'extendedlambda0_38 v0 v1 v3
du_'46'extendedlambda0_38 ::
  (Integer ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Untyped.T__'8866'_14) ->
  Integer ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14
du_'46'extendedlambda0_38 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Untyped.C_'96'_18 v3 -> coe v2
      MAlonzo.Code.Untyped.C_ƛ_20 v3
        -> coe
             MAlonzo.Code.Untyped.C_ƛ_20
             (coe
                d__'8593'__8 (coe v0) (coe addInt (coe (1 :: Integer)) (coe v1))
                (coe v3))
      MAlonzo.Code.Untyped.C__'183'__22 v3 v4
        -> coe
             MAlonzo.Code.Untyped.C__'183'__22
             (coe d__'8593'__8 (coe v0) (coe v1) (coe v3))
             (coe d__'8593'__8 (coe v0) (coe v1) (coe v4))
      MAlonzo.Code.Untyped.C_force_24 v3
        -> coe
             MAlonzo.Code.Untyped.C_force_24
             (coe d__'8593'__8 (coe v0) (coe v1) (coe v3))
      MAlonzo.Code.Untyped.C_delay_26 v3
        -> coe
             MAlonzo.Code.Untyped.C_delay_26
             (coe d__'8593'__8 (coe v0) (coe v1) (coe v3))
      MAlonzo.Code.Untyped.C_con_28 v3 -> coe v2
      MAlonzo.Code.Untyped.C_constr_34 v3 v4
        -> coe
             MAlonzo.Code.Untyped.C_constr_34 (coe v3)
             (coe d__'8593''42'__14 (coe v0) (coe v1) (coe v4))
      MAlonzo.Code.Untyped.C_case_40 v3 v4
        -> coe
             MAlonzo.Code.Untyped.C_case_40
             (coe d__'8593'__8 (coe v0) (coe v1) (coe v3))
             (coe d__'8593''42'__14 (coe v0) (coe v1) (coe v4))
      MAlonzo.Code.Untyped.C_builtin_44 v3 -> coe v2
      MAlonzo.Code.Untyped.C_error_46 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Untyped.Transform._⇑_
d__'8657'__68 ::
  (Integer ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   Maybe MAlonzo.Code.Untyped.T__'8866'_14) ->
  Integer ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14
d__'8657'__68 v0 v1 v2
  = coe
      MAlonzo.Code.Data.Maybe.Base.du_fromMaybe_46
      (d_sub_80 (coe v0) (coe v1) (coe v2))
      (coe v0 v1 (d_sub_80 (coe v0) (coe v1) (coe v2)))
-- Untyped.Transform._⇑*_
d__'8657''42'__74 ::
  (Integer ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   Maybe MAlonzo.Code.Untyped.T__'8866'_14) ->
  Integer ->
  [MAlonzo.Code.Untyped.T__'8866'_14] ->
  [MAlonzo.Code.Untyped.T__'8866'_14]
d__'8657''42'__74 v0 v1 v2
  = case coe v2 of
      [] -> coe v2
      (:) v3 v4
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
             (coe d__'8657'__68 (coe v0) (coe v1) (coe v3))
             (coe d__'8657''42'__74 (coe v0) (coe v1) (coe v4))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Untyped.Transform.sub
d_sub_80 ::
  (Integer ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   Maybe MAlonzo.Code.Untyped.T__'8866'_14) ->
  Integer ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14
d_sub_80 v0 v1 v2
  = coe du_'46'extendedlambda1_100 (coe v0) (coe v1) (coe v2)
-- Untyped.Transform..extendedlambda1
d_'46'extendedlambda1_100 ::
  (Integer ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   Maybe MAlonzo.Code.Untyped.T__'8866'_14) ->
  Integer ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14
d_'46'extendedlambda1_100 v0 v1 ~v2 v3
  = du_'46'extendedlambda1_100 v0 v1 v3
du_'46'extendedlambda1_100 ::
  (Integer ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   Maybe MAlonzo.Code.Untyped.T__'8866'_14) ->
  Integer ->
  MAlonzo.Code.Untyped.T__'8866'_14 ->
  MAlonzo.Code.Untyped.T__'8866'_14
du_'46'extendedlambda1_100 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Untyped.C_'96'_18 v3 -> coe v2
      MAlonzo.Code.Untyped.C_ƛ_20 v3
        -> coe
             MAlonzo.Code.Untyped.C_ƛ_20
             (coe
                d__'8657'__68 (coe v0) (coe addInt (coe (1 :: Integer)) (coe v1))
                (coe v3))
      MAlonzo.Code.Untyped.C__'183'__22 v3 v4
        -> coe
             MAlonzo.Code.Untyped.C__'183'__22
             (coe d__'8657'__68 (coe v0) (coe v1) (coe v3))
             (coe d__'8657'__68 (coe v0) (coe v1) (coe v4))
      MAlonzo.Code.Untyped.C_force_24 v3
        -> coe
             MAlonzo.Code.Untyped.C_force_24
             (coe d__'8657'__68 (coe v0) (coe v1) (coe v3))
      MAlonzo.Code.Untyped.C_delay_26 v3
        -> coe
             MAlonzo.Code.Untyped.C_delay_26
             (coe d__'8657'__68 (coe v0) (coe v1) (coe v3))
      MAlonzo.Code.Untyped.C_con_28 v3 -> coe v2
      MAlonzo.Code.Untyped.C_constr_34 v3 v4
        -> coe
             MAlonzo.Code.Untyped.C_constr_34 (coe v3)
             (coe d__'8657''42'__74 (coe v0) (coe v1) (coe v4))
      MAlonzo.Code.Untyped.C_case_40 v3 v4
        -> coe
             MAlonzo.Code.Untyped.C_case_40
             (coe d__'8657'__68 (coe v0) (coe v1) (coe v3))
             (coe d__'8657''42'__74 (coe v0) (coe v1) (coe v4))
      MAlonzo.Code.Untyped.C_builtin_44 v3 -> coe v2
      MAlonzo.Code.Untyped.C_error_46 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Untyped.Transform.Extensive.↑-extensive
d_'8593''45'extensive_162 ::
  (Integer ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Untyped.T__'8866'_14 -> ()) ->
  (Integer ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Untyped.Relation.T_TermCompatible_176 ->
  (Integer ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Untyped.T__'8866'_14) ->
  (Integer -> MAlonzo.Code.Untyped.T__'8866'_14 -> AgdaAny) ->
  Integer -> MAlonzo.Code.Untyped.T__'8866'_14 -> AgdaAny
d_'8593''45'extensive_162 ~v0 v1 v2 v3 v4 v5 v6
  = du_'8593''45'extensive_162 v1 v2 v3 v4 v5 v6
du_'8593''45'extensive_162 ::
  (Integer ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Untyped.Relation.T_TermCompatible_176 ->
  (Integer ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Untyped.T__'8866'_14) ->
  (Integer -> MAlonzo.Code.Untyped.T__'8866'_14 -> AgdaAny) ->
  Integer -> MAlonzo.Code.Untyped.T__'8866'_14 -> AgdaAny
du_'8593''45'extensive_162 v0 v1 v2 v3 v4 v5
  = coe
      v0 v4 v5 (d_subterms_20 (coe v2) (coe v4) (coe v5))
      (coe v2 v4 (d_subterms_20 (coe v2) (coe v4) (coe v5)))
      (coe
         du_subterms'45'extensive_170 (coe v0) (coe v1) (coe v2) (coe v3)
         (coe v4) (coe v5))
      (coe v3 v4 (d_subterms_20 (coe v2) (coe v4) (coe v5)))
-- Untyped.Transform.Extensive.↑*-extensive
d_'8593''42''45'extensive_168 ::
  (Integer ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Untyped.T__'8866'_14 -> ()) ->
  (Integer ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Untyped.Relation.T_TermCompatible_176 ->
  (Integer ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Untyped.T__'8866'_14) ->
  (Integer -> MAlonzo.Code.Untyped.T__'8866'_14 -> AgdaAny) ->
  Integer ->
  [MAlonzo.Code.Untyped.T__'8866'_14] ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48
d_'8593''42''45'extensive_168 ~v0 v1 v2 v3 v4 v5 v6
  = du_'8593''42''45'extensive_168 v1 v2 v3 v4 v5 v6
du_'8593''42''45'extensive_168 ::
  (Integer ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Untyped.Relation.T_TermCompatible_176 ->
  (Integer ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Untyped.T__'8866'_14) ->
  (Integer -> MAlonzo.Code.Untyped.T__'8866'_14 -> AgdaAny) ->
  Integer ->
  [MAlonzo.Code.Untyped.T__'8866'_14] ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48
du_'8593''42''45'extensive_168 v0 v1 v2 v3 v4 v5
  = case coe v5 of
      []
        -> coe
             MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.C_'91''93'_56
      (:) v6 v7
        -> coe
             MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.C__'8759'__62
             (coe
                du_'8593''45'extensive_162 (coe v0) (coe v1) (coe v2) (coe v3)
                (coe v4) (coe v6))
             (coe
                du_'8593''42''45'extensive_168 (coe v0) (coe v1) (coe v2) (coe v3)
                (coe v4) (coe v7))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Untyped.Transform.Extensive.subterms-extensive
d_subterms'45'extensive_170 ::
  (Integer ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Untyped.T__'8866'_14 -> ()) ->
  (Integer ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Untyped.Relation.T_TermCompatible_176 ->
  (Integer ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Untyped.T__'8866'_14) ->
  (Integer -> MAlonzo.Code.Untyped.T__'8866'_14 -> AgdaAny) ->
  Integer -> MAlonzo.Code.Untyped.T__'8866'_14 -> AgdaAny
d_subterms'45'extensive_170 ~v0 v1 v2 v3 v4 v5 v6
  = du_subterms'45'extensive_170 v1 v2 v3 v4 v5 v6
du_subterms'45'extensive_170 ::
  (Integer ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Untyped.Relation.T_TermCompatible_176 ->
  (Integer ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Untyped.T__'8866'_14) ->
  (Integer -> MAlonzo.Code.Untyped.T__'8866'_14 -> AgdaAny) ->
  Integer -> MAlonzo.Code.Untyped.T__'8866'_14 -> AgdaAny
du_subterms'45'extensive_170 v0 v1 v2 v3 v4 v5
  = case coe v5 of
      MAlonzo.Code.Untyped.C_'96'_18 v6
        -> coe MAlonzo.Code.Untyped.Relation.d_compat'45'var_242 v1 v4 v6
      MAlonzo.Code.Untyped.C_ƛ_20 v6
        -> coe
             MAlonzo.Code.Untyped.Relation.d_compat'45'ƛ_250 v1 v4 v6
             (d__'8593'__8
                (coe v2) (coe addInt (coe (1 :: Integer)) (coe v4)) (coe v6))
             (coe
                du_'8593''45'extensive_162 (coe v0) (coe v1) (coe v2) (coe v3)
                (coe addInt (coe (1 :: Integer)) (coe v4)) (coe v6))
      MAlonzo.Code.Untyped.C__'183'__22 v6 v7
        -> coe
             MAlonzo.Code.Untyped.Relation.d_compat'45''183'_252 v1 v4 v6
             (d__'8593'__8 (coe v2) (coe v4) (coe v6)) v7
             (d__'8593'__8 (coe v2) (coe v4) (coe v7))
             (coe
                du_'8593''45'extensive_162 (coe v0) (coe v1) (coe v2) (coe v3)
                (coe v4) (coe v6))
             (coe
                du_'8593''45'extensive_162 (coe v0) (coe v1) (coe v2) (coe v3)
                (coe v4) (coe v7))
      MAlonzo.Code.Untyped.C_force_24 v6
        -> coe
             MAlonzo.Code.Untyped.Relation.d_compat'45'force_254 v1 v4 v6
             (d__'8593'__8 (coe v2) (coe v4) (coe v6))
             (coe
                du_'8593''45'extensive_162 (coe v0) (coe v1) (coe v2) (coe v3)
                (coe v4) (coe v6))
      MAlonzo.Code.Untyped.C_delay_26 v6
        -> coe
             MAlonzo.Code.Untyped.Relation.d_compat'45'delay_256 v1 v4 v6
             (d__'8593'__8 (coe v2) (coe v4) (coe v6))
             (coe
                du_'8593''45'extensive_162 (coe v0) (coe v1) (coe v2) (coe v3)
                (coe v4) (coe v6))
      MAlonzo.Code.Untyped.C_con_28 v6
        -> coe MAlonzo.Code.Untyped.Relation.d_compat'45'con_284 v1 v6 v4
      MAlonzo.Code.Untyped.C_constr_34 v6 v7
        -> coe
             MAlonzo.Code.Untyped.Relation.d_compat'45'constr_266 v1 v4 v6 v7
             (d__'8593''42'__14 (coe v2) (coe v4) (coe v7))
             (coe
                du_'8593''42''45'extensive_168 (coe v0) (coe v1) (coe v2) (coe v3)
                (coe v4) (coe v7))
      MAlonzo.Code.Untyped.C_case_40 v6 v7
        -> coe
             MAlonzo.Code.Untyped.Relation.d_compat'45'case_278 v1 v4 v6
             (d__'8593'__8 (coe v2) (coe v4) (coe v6)) v7
             (d__'8593''42'__14 (coe v2) (coe v4) (coe v7))
             (coe
                du_'8593''45'extensive_162 (coe v0) (coe v1) (coe v2) (coe v3)
                (coe v4) (coe v6))
             (coe
                du_'8593''42''45'extensive_168 (coe v0) (coe v1) (coe v2) (coe v3)
                (coe v4) (coe v7))
      MAlonzo.Code.Untyped.C_builtin_44 v6
        -> coe
             MAlonzo.Code.Untyped.Relation.d_compat'45'builtin_290 v1 v4 v6
      MAlonzo.Code.Untyped.C_error_46
        -> coe MAlonzo.Code.Untyped.Relation.d_compat'45'error_294 v1 v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Untyped.Transform.Extensive?.⇑-extensive
d_'8657''45'extensive_270 ::
  (Integer ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Untyped.T__'8866'_14 -> ()) ->
  (Integer ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Untyped.Relation.T_TermCompatible_176 ->
  (Integer ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   Maybe MAlonzo.Code.Untyped.T__'8866'_14) ->
  (Integer ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny) ->
  Integer -> MAlonzo.Code.Untyped.T__'8866'_14 -> AgdaAny
d_'8657''45'extensive_270 ~v0 v1 v2 v3 v4 v5 v6
  = du_'8657''45'extensive_270 v1 v2 v3 v4 v5 v6
du_'8657''45'extensive_270 ::
  (Integer ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Untyped.Relation.T_TermCompatible_176 ->
  (Integer ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   Maybe MAlonzo.Code.Untyped.T__'8866'_14) ->
  (Integer ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny) ->
  Integer -> MAlonzo.Code.Untyped.T__'8866'_14 -> AgdaAny
du_'8657''45'extensive_270 v0 v1 v2 v3 v4 v5
  = let v6
          = coe
              du_sub'45'extensive_278 (coe v0) (coe v1) (coe v2) (coe v3)
              (coe v4) (coe v5) in
    coe
      (let v7 = coe v2 v4 (d_sub_80 (coe v2) (coe v4) (coe v5)) in
       coe
         (case coe v7 of
            MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v8
              -> coe
                   v0 v4 v5
                   (coe du_'46'extendedlambda1_100 (coe v2) (coe v4) (coe v5)) v8 v6
                   (coe
                      v3 v4 (coe du_'46'extendedlambda1_100 (coe v2) (coe v4) (coe v5))
                      v8 erased)
            MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v6
            _ -> MAlonzo.RTE.mazUnreachableError))
-- Untyped.Transform.Extensive?.⇑*-extensive
d_'8657''42''45'extensive_276 ::
  (Integer ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Untyped.T__'8866'_14 -> ()) ->
  (Integer ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Untyped.Relation.T_TermCompatible_176 ->
  (Integer ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   Maybe MAlonzo.Code.Untyped.T__'8866'_14) ->
  (Integer ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny) ->
  Integer ->
  [MAlonzo.Code.Untyped.T__'8866'_14] ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48
d_'8657''42''45'extensive_276 ~v0 v1 v2 v3 v4 v5 v6
  = du_'8657''42''45'extensive_276 v1 v2 v3 v4 v5 v6
du_'8657''42''45'extensive_276 ::
  (Integer ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Untyped.Relation.T_TermCompatible_176 ->
  (Integer ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   Maybe MAlonzo.Code.Untyped.T__'8866'_14) ->
  (Integer ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny) ->
  Integer ->
  [MAlonzo.Code.Untyped.T__'8866'_14] ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48
du_'8657''42''45'extensive_276 v0 v1 v2 v3 v4 v5
  = case coe v5 of
      []
        -> coe
             MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.C_'91''93'_56
      (:) v6 v7
        -> coe
             MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.C__'8759'__62
             (coe
                du_'8657''45'extensive_270 (coe v0) (coe v1) (coe v2) (coe v3)
                (coe v4) (coe v6))
             (coe
                du_'8657''42''45'extensive_276 (coe v0) (coe v1) (coe v2) (coe v3)
                (coe v4) (coe v7))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Untyped.Transform.Extensive?.sub-extensive
d_sub'45'extensive_278 ::
  (Integer ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Untyped.T__'8866'_14 -> ()) ->
  (Integer ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Untyped.Relation.T_TermCompatible_176 ->
  (Integer ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   Maybe MAlonzo.Code.Untyped.T__'8866'_14) ->
  (Integer ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny) ->
  Integer -> MAlonzo.Code.Untyped.T__'8866'_14 -> AgdaAny
d_sub'45'extensive_278 ~v0 v1 v2 v3 v4 v5 v6
  = du_sub'45'extensive_278 v1 v2 v3 v4 v5 v6
du_sub'45'extensive_278 ::
  (Integer ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Untyped.Relation.T_TermCompatible_176 ->
  (Integer ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   Maybe MAlonzo.Code.Untyped.T__'8866'_14) ->
  (Integer ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Untyped.T__'8866'_14 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny) ->
  Integer -> MAlonzo.Code.Untyped.T__'8866'_14 -> AgdaAny
du_sub'45'extensive_278 v0 v1 v2 v3 v4 v5
  = case coe v5 of
      MAlonzo.Code.Untyped.C_'96'_18 v6
        -> coe MAlonzo.Code.Untyped.Relation.d_compat'45'var_242 v1 v4 v6
      MAlonzo.Code.Untyped.C_ƛ_20 v6
        -> coe
             MAlonzo.Code.Untyped.Relation.d_compat'45'ƛ_250 v1 v4 v6
             (d__'8657'__68
                (coe v2) (coe addInt (coe (1 :: Integer)) (coe v4)) (coe v6))
             (coe
                du_'8657''45'extensive_270 (coe v0) (coe v1) (coe v2) (coe v3)
                (coe addInt (coe (1 :: Integer)) (coe v4)) (coe v6))
      MAlonzo.Code.Untyped.C__'183'__22 v6 v7
        -> coe
             MAlonzo.Code.Untyped.Relation.d_compat'45''183'_252 v1 v4 v6
             (d__'8657'__68 (coe v2) (coe v4) (coe v6)) v7
             (d__'8657'__68 (coe v2) (coe v4) (coe v7))
             (coe
                du_'8657''45'extensive_270 (coe v0) (coe v1) (coe v2) (coe v3)
                (coe v4) (coe v6))
             (coe
                du_'8657''45'extensive_270 (coe v0) (coe v1) (coe v2) (coe v3)
                (coe v4) (coe v7))
      MAlonzo.Code.Untyped.C_force_24 v6
        -> coe
             MAlonzo.Code.Untyped.Relation.d_compat'45'force_254 v1 v4 v6
             (d__'8657'__68 (coe v2) (coe v4) (coe v6))
             (coe
                du_'8657''45'extensive_270 (coe v0) (coe v1) (coe v2) (coe v3)
                (coe v4) (coe v6))
      MAlonzo.Code.Untyped.C_delay_26 v6
        -> coe
             MAlonzo.Code.Untyped.Relation.d_compat'45'delay_256 v1 v4 v6
             (d__'8657'__68 (coe v2) (coe v4) (coe v6))
             (coe
                du_'8657''45'extensive_270 (coe v0) (coe v1) (coe v2) (coe v3)
                (coe v4) (coe v6))
      MAlonzo.Code.Untyped.C_con_28 v6
        -> coe MAlonzo.Code.Untyped.Relation.d_compat'45'con_284 v1 v6 v4
      MAlonzo.Code.Untyped.C_constr_34 v6 v7
        -> coe
             MAlonzo.Code.Untyped.Relation.d_compat'45'constr_266 v1 v4 v6 v7
             (d__'8657''42'__74 (coe v2) (coe v4) (coe v7))
             (coe
                du_'8657''42''45'extensive_276 (coe v0) (coe v1) (coe v2) (coe v3)
                (coe v4) (coe v7))
      MAlonzo.Code.Untyped.C_case_40 v6 v7
        -> coe
             MAlonzo.Code.Untyped.Relation.d_compat'45'case_278 v1 v4 v6
             (d__'8657'__68 (coe v2) (coe v4) (coe v6)) v7
             (d__'8657''42'__74 (coe v2) (coe v4) (coe v7))
             (coe
                du_'8657''45'extensive_270 (coe v0) (coe v1) (coe v2) (coe v3)
                (coe v4) (coe v6))
             (coe
                du_'8657''42''45'extensive_276 (coe v0) (coe v1) (coe v2) (coe v3)
                (coe v4) (coe v7))
      MAlonzo.Code.Untyped.C_builtin_44 v6
        -> coe
             MAlonzo.Code.Untyped.Relation.d_compat'45'builtin_290 v1 v4 v6
      MAlonzo.Code.Untyped.C_error_46
        -> coe MAlonzo.Code.Untyped.Relation.d_compat'45'error_294 v1 v4
      _ -> MAlonzo.RTE.mazUnreachableError
