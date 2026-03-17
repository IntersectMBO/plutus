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

module MAlonzo.Code.Relation.Binary.Reflection where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Data.Fin.Base
import qualified MAlonzo.Code.Data.Vec.Base
import qualified MAlonzo.Code.Data.Vec.NZ45Zary
import qualified MAlonzo.Code.Function.Bundles
import qualified MAlonzo.Code.Relation.Binary.Bundles
import qualified MAlonzo.Code.Relation.Binary.Reasoning.Base.Single
import qualified MAlonzo.Code.Relation.Binary.Reasoning.Syntax
import qualified MAlonzo.Code.Relation.Binary.Structures

-- Relation.Binary.Reflection.prove
d_prove_90 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (Integer -> ()) ->
  () ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  (Integer -> MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> AgdaAny) ->
  (Integer ->
   AgdaAny -> MAlonzo.Code.Data.Vec.Base.T_Vec_28 -> AgdaAny) ->
  (Integer ->
   AgdaAny -> MAlonzo.Code.Data.Vec.Base.T_Vec_28 -> AgdaAny) ->
  (Integer ->
   AgdaAny -> MAlonzo.Code.Data.Vec.Base.T_Vec_28 -> AgdaAny) ->
  Integer ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_prove_90 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 v7 v8 v9 v10 v11 v12 v13 v14
  = du_prove_90 v5 v7 v8 v9 v10 v11 v12 v13 v14
du_prove_90 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  (Integer ->
   AgdaAny -> MAlonzo.Code.Data.Vec.Base.T_Vec_28 -> AgdaAny) ->
  (Integer ->
   AgdaAny -> MAlonzo.Code.Data.Vec.Base.T_Vec_28 -> AgdaAny) ->
  (Integer ->
   AgdaAny -> MAlonzo.Code.Data.Vec.Base.T_Vec_28 -> AgdaAny) ->
  Integer ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_prove_90 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
      (\ v9 v10 v11 ->
         coe
           MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_start_36 v11)
      (coe v1 v4 v6 v5) (coe v1 v4 v7 v5)
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10216'_370
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_trans_38
               (coe
                  MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v0))))
         (MAlonzo.Code.Relation.Binary.Structures.d_sym_36
            (coe
               MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v0)))
         (coe v1 v4 v6 v5) (coe v2 v4 v6 v5) (coe v1 v4 v7 v5)
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                  (coe
                     MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v0))))
            (coe v2 v4 v6 v5) (coe v2 v4 v7 v5) (coe v1 v4 v7 v5)
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                     (coe
                        MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v0))))
               (coe v2 v4 v7 v5) (coe v1 v4 v7 v5) (coe v1 v4 v7 v5)
               (let v9
                      = MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                          (coe
                             MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                             (coe v0)) in
                coe
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                     (coe
                        MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_stop_54
                        (coe v9))
                     (coe v1 v4 v7 v5)))
               (coe v3 v4 v7 v5))
            v8)
         (coe v3 v4 v6 v5))
-- Relation.Binary.Reflection.close
d_close_104 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (Integer -> ()) ->
  () ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  (Integer -> MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> AgdaAny) ->
  (Integer ->
   AgdaAny -> MAlonzo.Code.Data.Vec.Base.T_Vec_28 -> AgdaAny) ->
  (Integer ->
   AgdaAny -> MAlonzo.Code.Data.Vec.Base.T_Vec_28 -> AgdaAny) ->
  (Integer ->
   AgdaAny -> MAlonzo.Code.Data.Vec.Base.T_Vec_28 -> AgdaAny) ->
  () -> Integer -> AgdaAny -> AgdaAny
d_close_104 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 ~v7 ~v8 ~v9 ~v10 v11 v12
  = du_close_104 v6 v11 v12
du_close_104 ::
  (Integer -> MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> AgdaAny) ->
  Integer -> AgdaAny -> AgdaAny
du_close_104 v0 v1 v2
  = coe
      MAlonzo.Code.Data.Vec.NZ45Zary.du__'36''8319'__64 (coe v2)
      (coe
         MAlonzo.Code.Data.Vec.Base.du_map_178 (coe v0 v1)
         (coe MAlonzo.Code.Data.Vec.Base.d_allFin_462 (coe v1)))
-- Relation.Binary.Reflection.solve
d_solve_114 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (Integer -> ()) ->
  () ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  (Integer -> MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> AgdaAny) ->
  (Integer ->
   AgdaAny -> MAlonzo.Code.Data.Vec.Base.T_Vec_28 -> AgdaAny) ->
  (Integer ->
   AgdaAny -> MAlonzo.Code.Data.Vec.Base.T_Vec_28 -> AgdaAny) ->
  (Integer ->
   AgdaAny -> MAlonzo.Code.Data.Vec.Base.T_Vec_28 -> AgdaAny) ->
  Integer -> AgdaAny -> AgdaAny -> AgdaAny
d_solve_114 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6 v7 v8 v9 v10 v11 v12
  = du_solve_114 v5 v6 v7 v8 v9 v10 v11 v12
du_solve_114 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  (Integer -> MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> AgdaAny) ->
  (Integer ->
   AgdaAny -> MAlonzo.Code.Data.Vec.Base.T_Vec_28 -> AgdaAny) ->
  (Integer ->
   AgdaAny -> MAlonzo.Code.Data.Vec.Base.T_Vec_28 -> AgdaAny) ->
  (Integer ->
   AgdaAny -> MAlonzo.Code.Data.Vec.Base.T_Vec_28 -> AgdaAny) ->
  Integer -> AgdaAny -> AgdaAny -> AgdaAny
du_solve_114 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Data.Vec.NZ45Zary.du_curry'8319''45'cong_316 (coe v5)
      (coe
         (\ v8 ->
            coe
              du_prove_90 (coe v0) (coe v2) (coe v3) (coe v4) (coe v5) (coe v8)
              (coe
                 MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                 (coe du_close_104 (coe v1) (coe v5) (coe v6)))
              (coe
                 MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                 (coe du_close_104 (coe v1) (coe v5) (coe v6)))
              (coe
                 MAlonzo.Code.Data.Vec.NZ45Zary.du_curry'8319''45'cong'8315''185'_344
                 (coe
                    MAlonzo.Code.Data.Vec.NZ45Zary.du_Eq'688''45'to'45'Eq_444 (coe v5)
                    (coe v7))
                 (coe v8))))
-- Relation.Binary.Reflection.solve₁
d_solve'8321'_130 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (Integer -> ()) ->
  () ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  (Integer -> MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> AgdaAny) ->
  (Integer ->
   AgdaAny -> MAlonzo.Code.Data.Vec.Base.T_Vec_28 -> AgdaAny) ->
  (Integer ->
   AgdaAny -> MAlonzo.Code.Data.Vec.Base.T_Vec_28 -> AgdaAny) ->
  (Integer ->
   AgdaAny -> MAlonzo.Code.Data.Vec.Base.T_Vec_28 -> AgdaAny) ->
  Integer -> AgdaAny -> AgdaAny
d_solve'8321'_130 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6 v7 v8 v9 v10 v11
  = du_solve'8321'_130 v5 v6 v7 v8 v9 v10 v11
du_solve'8321'_130 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  (Integer -> MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> AgdaAny) ->
  (Integer ->
   AgdaAny -> MAlonzo.Code.Data.Vec.Base.T_Vec_28 -> AgdaAny) ->
  (Integer ->
   AgdaAny -> MAlonzo.Code.Data.Vec.Base.T_Vec_28 -> AgdaAny) ->
  (Integer ->
   AgdaAny -> MAlonzo.Code.Data.Vec.Base.T_Vec_28 -> AgdaAny) ->
  Integer -> AgdaAny -> AgdaAny
du_solve'8321'_130 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Function.Bundles.d_from_1822
      (coe
         MAlonzo.Code.Data.Vec.NZ45Zary.du_uncurry'45''8704''8319'_194
         (coe v5))
      (\ v7 ->
         coe
           du_prove_90 (coe v0) (coe v2) (coe v3) (coe v4) (coe v5) (coe v7)
           (coe
              MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
              (coe du_close_104 (coe v1) (coe v5) (coe v6)))
           (coe
              MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
              (coe du_close_104 (coe v1) (coe v5) (coe v6))))
-- Relation.Binary.Reflection._⊜_
d__'8860'__142 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (Integer -> ()) ->
  () ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  (Integer -> MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> AgdaAny) ->
  (Integer ->
   AgdaAny -> MAlonzo.Code.Data.Vec.Base.T_Vec_28 -> AgdaAny) ->
  (Integer ->
   AgdaAny -> MAlonzo.Code.Data.Vec.Base.T_Vec_28 -> AgdaAny) ->
  (Integer ->
   AgdaAny -> MAlonzo.Code.Data.Vec.Base.T_Vec_28 -> AgdaAny) ->
  Integer ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d__'8860'__142 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
  = du__'8860'__142
du__'8860'__142 ::
  AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du__'8860'__142 = coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
