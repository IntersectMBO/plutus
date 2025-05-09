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

module MAlonzo.Code.Function.Nary.NonDependent.Base where

import Data.Text qualified
import MAlonzo.Code.Agda.Builtin.Sigma qualified
import MAlonzo.Code.Agda.Builtin.Unit qualified
import MAlonzo.Code.Agda.Primitive qualified
import MAlonzo.Code.Function.Base qualified
import MAlonzo.Code.Level qualified
import MAlonzo.RTE (AgdaAny, add64, addInt, coe, eq64, eqInt, erased, geqInt, lt64, ltInt, mul64,
                    mulInt, quot64, quotInt, rem64, remInt, sub64, subInt, word64FromNat,
                    word64ToNat)
import MAlonzo.RTE qualified

-- Function.Nary.NonDependent.Base.Levels
d_Levels_20 :: Integer -> ()
d_Levels_20 = erased
-- Function.Nary.NonDependent.Base.⨆
d_'10758'_26 ::
  Integer -> AgdaAny -> MAlonzo.Code.Agda.Primitive.T_Level_18
d_'10758'_26 v0 v1
  = case coe v0 of
      0 -> coe MAlonzo.Code.Agda.Primitive.d_lzero_20
      _ -> let v2 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (case coe v1 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
                  -> coe
                       MAlonzo.Code.Agda.Primitive.d__'8852'__30 v3
                       (d_'10758'_26 (coe v2) (coe v4))
                _ -> MAlonzo.RTE.mazUnreachableError)
-- Function.Nary.NonDependent.Base.Sets
d_Sets_38 :: Integer -> AgdaAny -> ()
d_Sets_38 = erased
-- Function.Nary.NonDependent.Base.Arrows
d_Arrows_52 ::
  Integer ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  AgdaAny -> AgdaAny -> () -> ()
d_Arrows_52 = erased
-- Function.Nary.NonDependent.Base._⇉_
d__'8649'__70 ::
  Integer ->
  AgdaAny ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 -> AgdaAny -> () -> ()
d__'8649'__70 = erased
-- Function.Nary.NonDependent.Base._<$>_
d__'60''36''62'__78 ::
  (MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()) ->
  Integer -> AgdaAny -> AgdaAny -> AgdaAny
d__'60''36''62'__78 v0 v1 v2 v3
  = case coe v1 of
      0 -> coe
             MAlonzo.Code.Level.C_lift_20
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      _ -> let v4 = subInt (coe v1) (coe (1 :: Integer)) in
           coe
             (case coe v3 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                       (coe v0 (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v2)) v5)
                       (coe
                          d__'60''36''62'__78 erased (coe v4)
                          (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v2)) (coe v6))
                _ -> MAlonzo.RTE.mazUnreachableError)
-- Function.Nary.NonDependent.Base.lmap
d_lmap_94 ::
  (MAlonzo.Code.Agda.Primitive.T_Level_18 ->
   MAlonzo.Code.Agda.Primitive.T_Level_18) ->
  Integer -> AgdaAny -> AgdaAny
d_lmap_94 v0 v1 v2
  = case coe v1 of
      0 -> coe
             MAlonzo.Code.Level.C_lift_20
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      _ -> let v3 = subInt (coe v1) (coe (1 :: Integer)) in
           coe
             (case coe v2 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0 v4)
                       (coe d_lmap_94 (coe v0) (coe v3) (coe v5))
                _ -> MAlonzo.RTE.mazUnreachableError)
-- Function.Nary.NonDependent.Base.smap
d_smap_116 ::
  (MAlonzo.Code.Agda.Primitive.T_Level_18 ->
   MAlonzo.Code.Agda.Primitive.T_Level_18) ->
  (MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()) ->
  Integer -> AgdaAny -> AgdaAny -> AgdaAny
d_smap_116 ~v0 v1 v2 v3 v4 = du_smap_116 v1 v2 v3 v4
du_smap_116 ::
  (MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()) ->
  Integer -> AgdaAny -> AgdaAny -> AgdaAny
du_smap_116 v0 v1 v2 v3
  = case coe v1 of
      0 -> coe
             MAlonzo.Code.Level.C_lift_20
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      _ -> let v4 = subInt (coe v1) (coe (1 :: Integer)) in
           coe
             (case coe v3 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                       (coe v0 (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v2)) v5)
                       (coe
                          du_smap_116 erased (coe v4)
                          (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v2)) (coe v6))
                _ -> MAlonzo.RTE.mazUnreachableError)
-- Function.Nary.NonDependent.Base.mapₙ
d_map'8345'_140 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  Integer ->
  AgdaAny -> AgdaAny -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_map'8345'_140 ~v0 ~v1 ~v2 ~v3 v4 ~v5 ~v6 v7 v8
  = du_map'8345'_140 v4 v7 v8
du_map'8345'_140 ::
  Integer -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du_map'8345'_140 v0 v1 v2
  = case coe v0 of
      0 -> coe v1 v2
      _ -> let v3 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (coe
                MAlonzo.Code.Function.Base.du__'8728''8242'__216
                (coe du_map'8345'_140 (coe v3) (coe v1)) (coe v2))
-- Function.Nary.NonDependent.Base._%=_⊢_
d__'37''61'_'8866'__158 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  Integer ->
  AgdaAny -> AgdaAny -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d__'37''61'_'8866'__158 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 ~v7 ~v8 v9 v10
  = du__'37''61'_'8866'__158 v6 v9 v10
du__'37''61'_'8866'__158 ::
  Integer -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du__'37''61'_'8866'__158 v0 v1 v2
  = coe
      du_map'8345'_140 (coe v0)
      (coe
         (\ v3 ->
            coe
              MAlonzo.Code.Function.Base.du__'8728''8242'__216 (coe v3)
              (coe v1)))
      (coe v2)
-- Function.Nary.NonDependent.Base._∷=_⊢_
d__'8759''61'_'8866'__174 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  Integer -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d__'8759''61'_'8866'__174 ~v0 ~v1 ~v2 ~v3 v4 ~v5 ~v6 v7 v8
  = du__'8759''61'_'8866'__174 v4 v7 v8
du__'8759''61'_'8866'__174 ::
  Integer -> AgdaAny -> AgdaAny -> AgdaAny
du__'8759''61'_'8866'__174 v0 v1 v2
  = coe du_map'8345'_140 (coe v0) (coe (\ v3 -> coe v3 v1)) (coe v2)
-- Function.Nary.NonDependent.Base.holeₙ
d_hole'8345'_190 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  Integer -> AgdaAny -> AgdaAny -> (AgdaAny -> AgdaAny) -> AgdaAny
d_hole'8345'_190 ~v0 ~v1 ~v2 ~v3 v4 ~v5 ~v6 v7
  = du_hole'8345'_190 v4 v7
du_hole'8345'_190 :: Integer -> (AgdaAny -> AgdaAny) -> AgdaAny
du_hole'8345'_190 v0 v1
  = case coe v0 of
      0 -> coe v1
      _ -> let v2 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (coe
                MAlonzo.Code.Function.Base.du__'8728''8242'__216
                (coe du_hole'8345'_190 (coe v2)) (coe (\ v3 v4 -> coe v1 v4 v3)))
-- Function.Nary.NonDependent.Base.constₙ
d_const'8345'_208 ::
  Integer ->
  AgdaAny ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  AgdaAny -> () -> AgdaAny -> AgdaAny
d_const'8345'_208 v0 ~v1 ~v2 ~v3 ~v4 v5 = du_const'8345'_208 v0 v5
du_const'8345'_208 :: Integer -> AgdaAny -> AgdaAny
du_const'8345'_208 v0 v1
  = case coe v0 of
      0 -> coe v1
      _ -> let v2 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (let v3 = coe du_const'8345'_208 (coe v2) (coe v1) in
              coe (coe (\ v4 -> v3)))
