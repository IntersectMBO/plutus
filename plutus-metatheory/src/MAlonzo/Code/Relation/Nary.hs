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

module MAlonzo.Code.Relation.Nary where

import Data.Text qualified
import MAlonzo.Code.Agda.Builtin.Equality qualified
import MAlonzo.Code.Agda.Builtin.Sigma qualified
import MAlonzo.Code.Agda.Builtin.Unit qualified
import MAlonzo.Code.Agda.Primitive qualified
import MAlonzo.Code.Data.Empty qualified
import MAlonzo.Code.Data.Product.Nary.NonDependent qualified
import MAlonzo.Code.Function.Base qualified
import MAlonzo.Code.Level qualified
import MAlonzo.Code.Relation.Nullary.Decidable.Core qualified
import MAlonzo.Code.Relation.Nullary.Reflects qualified
import MAlonzo.RTE (AgdaAny, add64, addInt, coe, eq64, eqInt, erased, geqInt, lt64, ltInt, mul64,
                    mulInt, quot64, quotInt, rem64, remInt, sub64, subInt, word64FromNat,
                    word64ToNat)
import MAlonzo.RTE qualified

-- Relation.Nary.quantₙ
d_quant'8345'_20 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (MAlonzo.Code.Agda.Primitive.T_Level_18 ->
   MAlonzo.Code.Agda.Primitive.T_Level_18 ->
   () -> (AgdaAny -> ()) -> ()) ->
  Integer -> AgdaAny -> AgdaAny -> AgdaAny -> ()
d_quant'8345'_20 = erased
-- Relation.Nary.∃⟨_⟩
d_'8707''10216'_'10217'_42 ::
  Integer ->
  AgdaAny ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 -> AgdaAny -> AgdaAny -> ()
d_'8707''10216'_'10217'_42 = erased
-- Relation.Nary.Π[_]
d_Π'91'_'93'_52 ::
  Integer ->
  AgdaAny ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 -> AgdaAny -> AgdaAny -> ()
d_Π'91'_'93'_52 = erased
-- Relation.Nary.∀[_]
d_'8704''91'_'93'_62 ::
  Integer ->
  AgdaAny ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 -> AgdaAny -> AgdaAny -> ()
d_'8704''91'_'93'_62 = erased
-- Relation.Nary.≟-mapₙ
d_'8799''45'map'8345'_76 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  Integer ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny) ->
  AgdaAny -> AgdaAny -> AgdaAny
d_'8799''45'map'8345'_76 ~v0 ~v1 v2 ~v3 ~v4 ~v5 v6 v7 v8
  = du_'8799''45'map'8345'_76 v2 v6 v7 v8
du_'8799''45'map'8345'_76 ::
  Integer ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny) ->
  AgdaAny -> AgdaAny -> AgdaAny
du_'8799''45'map'8345'_76 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Data.Product.Nary.NonDependent.du_curry'8345'_130
      (coe v0)
      (coe
         (\ v4 ->
            coe
              MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_168
              (coe
                 MAlonzo.Code.Function.Base.du__'8728''8242'__216 erased erased)
              (coe v1 v2 v3)
              (coe
                 MAlonzo.Code.Data.Product.Nary.NonDependent.du_Product'45'dec_216
                 (coe v0) (coe v4))))
-- Relation.Nary._.Substitutionₙ
d_Substitution'8345'_102 ::
  Integer ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  AgdaAny -> AgdaAny -> AgdaAny -> ()
d_Substitution'8345'_102 = erased
-- Relation.Nary._.substₙ
d_subst'8345'_108 ::
  Integer ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_subst'8345'_108 v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6
  = du_subst'8345'_108 v0
du_subst'8345'_108 :: Integer -> AgdaAny
du_subst'8345'_108 v0
  = coe
      MAlonzo.Code.Data.Product.Nary.NonDependent.du_curry'8345'_130
      (coe v0)
      (coe
         MAlonzo.Code.Function.Base.du__'8728''8242'__216
         (coe (\ v1 v2 -> v2)) erased)
-- Relation.Nary.liftₙ
d_lift'8345'_122 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  Integer ->
  Integer ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_lift'8345'_122 ~v0 ~v1 v2 v3 ~v4 v5 ~v6 v7 v8
  = du_lift'8345'_122 v2 v3 v5 v7 v8
du_lift'8345'_122 ::
  Integer -> Integer -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_lift'8345'_122 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Data.Product.Nary.NonDependent.du_curry'8868''8345'_170
      (coe v0)
      (coe
         (\ v5 ->
            coe
              MAlonzo.Code.Data.Product.Nary.NonDependent.du_curry'8868''8345'_170
              (coe v1)
              (coe
                 (\ v6 ->
                    coe
                      MAlonzo.Code.Data.Product.Nary.NonDependent.du_uncurry'8868''8345'_188
                      v0 v4
                      (coe
                         du_palg_150 (coe v0) (coe v2) (coe v3)
                         (coe
                            (\ v7 v8 v9 ->
                               coe
                                 MAlonzo.Code.Data.Product.Nary.NonDependent.du_uncurry'8868''8345'_188
                                 v1 v9 v6))
                         (coe v5))))))
-- Relation.Nary._.palg
d_palg_150 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  Integer ->
  Integer ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  (MAlonzo.Code.Agda.Primitive.T_Level_18 ->
   MAlonzo.Code.Agda.Primitive.T_Level_18) ->
  (MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()) ->
  Integer ->
  AgdaAny ->
  AgdaAny ->
  (MAlonzo.Code.Agda.Primitive.T_Level_18 ->
   () -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny
d_palg_150 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 v11 v12 v13
           v14 v15
  = du_palg_150 v11 v12 v13 v14 v15
du_palg_150 ::
  Integer ->
  AgdaAny ->
  AgdaAny ->
  (MAlonzo.Code.Agda.Primitive.T_Level_18 ->
   () -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny
du_palg_150 v0 v1 v2 v3 v4
  = case coe v0 of
      0 -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      _ -> let v5 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (case coe v4 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                       (coe
                          v3 (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v1))
                          (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v2)) v6)
                       (coe
                          du_palg_150 (coe v5)
                          (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v1))
                          (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v2)) (coe v3)
                          (coe v7))
                _ -> MAlonzo.RTE.mazUnreachableError)
-- Relation.Nary._⇒_
d__'8658'__188 ::
  Integer ->
  AgdaAny ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d__'8658'__188 v0 ~v1 ~v2 ~v3 ~v4 = du__'8658'__188 v0
du__'8658'__188 :: Integer -> AgdaAny -> AgdaAny -> AgdaAny
du__'8658'__188 v0
  = coe
      du_lift'8345'_122 (coe (2 :: Integer)) (coe v0)
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe ())
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe ())
            (coe
               MAlonzo.Code.Level.C_lift_20
               (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe ())
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe ())
            (coe
               MAlonzo.Code.Level.C_lift_20
               (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))))
      (coe (\ v1 v2 -> ()))
-- Relation.Nary._∩_
d__'8745'__204 ::
  Integer ->
  AgdaAny ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d__'8745'__204 v0 ~v1 v2 v3 ~v4 = du__'8745'__204 v0 v2 v3
du__'8745'__204 ::
  Integer ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  AgdaAny -> AgdaAny -> AgdaAny
du__'8745'__204 v0 v1 v2
  = coe
      du_lift'8345'_122 (coe (2 :: Integer)) (coe v0)
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
         (coe MAlonzo.Code.Agda.Primitive.d_lsuc_24 v1)
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
            (coe MAlonzo.Code.Agda.Primitive.d_lsuc_24 v2)
            (coe
               MAlonzo.Code.Level.C_lift_20
               (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe ())
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe ())
            (coe
               MAlonzo.Code.Level.C_lift_20
               (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))))
      erased
-- Relation.Nary._∪_
d__'8746'__216 ::
  Integer ->
  AgdaAny ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d__'8746'__216 v0 ~v1 v2 v3 ~v4 = du__'8746'__216 v0 v2 v3
du__'8746'__216 ::
  Integer ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  AgdaAny -> AgdaAny -> AgdaAny
du__'8746'__216 v0 v1 v2
  = coe
      du_lift'8345'_122 (coe (2 :: Integer)) (coe v0)
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
         (coe MAlonzo.Code.Agda.Primitive.d_lsuc_24 v1)
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
            (coe MAlonzo.Code.Agda.Primitive.d_lsuc_24 v2)
            (coe
               MAlonzo.Code.Level.C_lift_20
               (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe ())
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe ())
            (coe
               MAlonzo.Code.Level.C_lift_20
               (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))))
      erased
-- Relation.Nary.∁
d_'8705'_226 ::
  Integer ->
  AgdaAny ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_'8705'_226 v0 ~v1 v2 ~v3 = du_'8705'_226 v0 v2
du_'8705'_226 ::
  Integer ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 -> AgdaAny -> AgdaAny
du_'8705'_226 v0 v1
  = coe
      du_lift'8345'_122 (coe (1 :: Integer)) (coe v0)
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
         (coe MAlonzo.Code.Agda.Primitive.d_lsuc_24 v1)
         (coe
            MAlonzo.Code.Level.C_lift_20
            (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe ())
         (coe
            MAlonzo.Code.Level.C_lift_20
            (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)))
      erased
-- Relation.Nary.apply⊤ₙ
d_apply'8868''8345'_240 ::
  Integer ->
  AgdaAny ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_apply'8868''8345'_240 v0 ~v1 ~v2 ~v3 ~v4 v5 v6
  = du_apply'8868''8345'_240 v0 v5 v6
du_apply'8868''8345'_240 ::
  Integer -> AgdaAny -> AgdaAny -> AgdaAny
du_apply'8868''8345'_240 v0 v1 v2
  = case coe v0 of
      0 -> coe v1
      _ -> let v3 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (case coe v2 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
                  -> coe du_apply'8868''8345'_240 (coe v3) (coe v1 v4) (coe v5)
                _ -> MAlonzo.RTE.mazUnreachableError)
-- Relation.Nary.applyₙ
d_apply'8345'_266 ::
  Integer ->
  AgdaAny ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_apply'8345'_266 v0 ~v1 ~v2 ~v3 ~v4 v5 v6
  = du_apply'8345'_266 v0 v5 v6
du_apply'8345'_266 :: Integer -> AgdaAny -> AgdaAny -> AgdaAny
du_apply'8345'_266 v0 v1 v2
  = coe
      du_apply'8868''8345'_240 (coe v0) (coe v1)
      (coe
         MAlonzo.Code.Data.Product.Nary.NonDependent.du_toProduct'8868'_110
         (coe v0) (coe v2))
-- Relation.Nary.iapply⊤ₙ
d_iapply'8868''8345'_286 ::
  Integer ->
  AgdaAny ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_iapply'8868''8345'_286 v0 ~v1 ~v2 ~v3 ~v4 v5 v6
  = du_iapply'8868''8345'_286 v0 v5 v6
du_iapply'8868''8345'_286 ::
  Integer -> AgdaAny -> AgdaAny -> AgdaAny
du_iapply'8868''8345'_286 v0 v1 v2
  = case coe v0 of
      0 -> coe v1
      _ -> let v3 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (coe
                du_iapply'8868''8345'_286 (coe v3)
                (coe v1 (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v2)))
                (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v2)))
-- Relation.Nary.iapplyₙ
d_iapply'8345'_306 ::
  Integer ->
  AgdaAny ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_iapply'8345'_306 v0 ~v1 ~v2 ~v3 ~v4 v5 v6
  = du_iapply'8345'_306 v0 v5 v6
du_iapply'8345'_306 :: Integer -> AgdaAny -> AgdaAny -> AgdaAny
du_iapply'8345'_306 v0 v1 v2
  = coe
      du_iapply'8868''8345'_286 (coe v0) (coe v1)
      (coe
         MAlonzo.Code.Data.Product.Nary.NonDependent.du_toProduct'8868'_110
         (coe v0) (coe v2))
-- Relation.Nary.Decidable
d_Decidable_320 ::
  Integer ->
  AgdaAny ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 -> AgdaAny -> AgdaAny -> ()
d_Decidable_320 = erased
-- Relation.Nary.⌊_⌋
d_'8970'_'8971'_334 ::
  Integer ->
  AgdaAny ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8970'_'8971'_334 v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_'8970'_'8971'_334 v0
du_'8970'_'8971'_334 :: Integer -> AgdaAny
du_'8970'_'8971'_334 v0
  = case coe v0 of
      0 -> erased
      _ -> let v1 = subInt (coe v0) (coe (1 :: Integer)) in
           coe (coe (\ v2 -> coe du_'8970'_'8971'_334 (coe v1)))
-- Relation.Nary.fromWitness
d_fromWitness_356 ::
  Integer ->
  AgdaAny ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_fromWitness_356 v0 ~v1 ~v2 ~v3 ~v4 v5 = du_fromWitness_356 v0 v5
du_fromWitness_356 :: Integer -> AgdaAny -> AgdaAny
du_fromWitness_356 v0 v1
  = case coe v0 of
      0 -> case coe v1 of
             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v2 v3
               -> if coe v2
                    then case coe v3 of
                           MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v4
                             -> coe (\ v5 -> v4)
                           _ -> MAlonzo.RTE.mazUnreachableError
                    else erased
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> let v2 = subInt (coe v0) (coe (1 :: Integer)) in
           coe (coe (\ v3 -> coe du_fromWitness_356 (coe v2) (coe v1 v3)))
-- Relation.Nary.toWitness
d_toWitness_396 ::
  Integer ->
  AgdaAny ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_toWitness_396 v0 ~v1 ~v2 ~v3 ~v4 v5 = du_toWitness_396 v0 v5
du_toWitness_396 :: Integer -> AgdaAny -> AgdaAny
du_toWitness_396 v0 v1
  = case coe v0 of
      0 -> case coe v1 of
             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v2 v3
               -> if coe v2
                    then coe
                           (\ v4 ->
                              coe
                                MAlonzo.Code.Level.C_lift_20
                                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                    else coe
                           seq (coe v3)
                           (coe
                              MAlonzo.Code.Function.Base.du__'8728''8242'__216
                              (\ v4 -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_14) erased)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> let v2 = subInt (coe v0) (coe (1 :: Integer)) in
           coe (coe (\ v3 -> coe du_toWitness_396 (coe v2) (coe v1 v3)))
