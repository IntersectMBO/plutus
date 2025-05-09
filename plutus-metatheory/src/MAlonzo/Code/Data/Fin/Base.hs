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

module MAlonzo.Code.Data.Fin.Base where

import Data.Text qualified
import MAlonzo.Code.Agda.Builtin.Equality qualified
import MAlonzo.Code.Agda.Builtin.Nat qualified
import MAlonzo.Code.Agda.Builtin.Sigma qualified
import MAlonzo.Code.Agda.Primitive qualified
import MAlonzo.Code.Algebra.Definitions.RawMagma qualified
import MAlonzo.Code.Data.Irrelevant qualified
import MAlonzo.Code.Data.Nat.Base qualified
import MAlonzo.Code.Data.Product.Base qualified
import MAlonzo.Code.Data.Sum.Base qualified
import MAlonzo.Code.Relation.Nullary.Negation.Core qualified
import MAlonzo.RTE (AgdaAny, add64, addInt, coe, eq64, eqInt, erased, geqInt, lt64, ltInt, mul64,
                    mulInt, quot64, quotInt, rem64, remInt, sub64, subInt, word64FromNat,
                    word64ToNat)
import MAlonzo.RTE qualified

-- Data.Fin.Base.Fin
d_Fin_10 a0 = ()
data T_Fin_10 = C_zero_12 | C_suc_16 T_Fin_10
-- Data.Fin.Base.toℕ
d_toℕ_18 :: Integer -> T_Fin_10 -> Integer
d_toℕ_18 ~v0 v1 = du_toℕ_18 v1
du_toℕ_18 :: T_Fin_10 -> Integer
du_toℕ_18 v0
  = case coe v0 of
      C_zero_12 -> coe (0 :: Integer)
      C_suc_16 v2
        -> coe addInt (coe (1 :: Integer)) (coe du_toℕ_18 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Fin.Base.Fin′
d_Fin'8242'_22 :: Integer -> T_Fin_10 -> ()
d_Fin'8242'_22 = erased
-- Data.Fin.Base.cast
d_cast_26 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_Fin_10 -> T_Fin_10
d_cast_26 v0 ~v1 ~v2 v3 = du_cast_26 v0 v3
du_cast_26 :: Integer -> T_Fin_10 -> T_Fin_10
du_cast_26 v0 v1
  = case coe v0 of
      0 -> coe v1
      _ -> case coe v1 of
             C_zero_12 -> coe C_zero_12
             C_suc_16 v3
               -> coe
                    C_suc_16
                    (coe
                       du_cast_26
                       (coe MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22 v0 (1 :: Integer))
                       (coe v3))
             _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Fin.Base.fromℕ
d_fromℕ_48 :: Integer -> T_Fin_10
d_fromℕ_48 v0
  = case coe v0 of
      0 -> coe C_zero_12
      _ -> let v1 = subInt (coe v0) (coe (1 :: Integer)) in
           coe (coe C_suc_16 (d_fromℕ_48 (coe v1)))
-- Data.Fin.Base.fromℕ<
d_fromℕ'60'_52 ::
  Integer ->
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> T_Fin_10
d_fromℕ'60'_52 v0 ~v1 ~v2 = du_fromℕ'60'_52 v0
du_fromℕ'60'_52 :: Integer -> T_Fin_10
du_fromℕ'60'_52 v0
  = case coe v0 of
      0 -> coe C_zero_12
      _ -> let v1 = subInt (coe v0) (coe (1 :: Integer)) in
           coe (coe C_suc_16 (coe du_fromℕ'60'_52 (coe v1)))
-- Data.Fin.Base.fromℕ<″
d_fromℕ'60''8243'_62 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Algebra.Definitions.RawMagma.T__'8739''737'__26 ->
  T_Fin_10
d_fromℕ'60''8243'_62 v0 ~v1 ~v2 = du_fromℕ'60''8243'_62 v0
du_fromℕ'60''8243'_62 :: Integer -> T_Fin_10
du_fromℕ'60''8243'_62 v0
  = case coe v0 of
      0 -> coe C_zero_12
      _ -> let v1 = subInt (coe v0) (coe (1 :: Integer)) in
           coe (coe C_suc_16 (coe du_fromℕ'60''8243'_62 (coe v1)))
-- Data.Fin.Base._↑ˡ_
d__'8593''737'__72 :: Integer -> T_Fin_10 -> Integer -> T_Fin_10
d__'8593''737'__72 ~v0 v1 ~v2 = du__'8593''737'__72 v1
du__'8593''737'__72 :: T_Fin_10 -> T_Fin_10
du__'8593''737'__72 v0 = coe v0
-- Data.Fin.Base._↑ʳ_
d__'8593''691'__84 :: Integer -> Integer -> T_Fin_10 -> T_Fin_10
d__'8593''691'__84 ~v0 v1 v2 = du__'8593''691'__84 v1 v2
du__'8593''691'__84 :: Integer -> T_Fin_10 -> T_Fin_10
du__'8593''691'__84 v0 v1
  = case coe v0 of
      0 -> coe v1
      _ -> let v2 = subInt (coe v0) (coe (1 :: Integer)) in
           coe (coe C_suc_16 (coe du__'8593''691'__84 (coe v2) (coe v1)))
-- Data.Fin.Base.reduce≥
d_reduce'8805'_94 ::
  Integer ->
  Integer ->
  T_Fin_10 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> T_Fin_10
d_reduce'8805'_94 v0 ~v1 v2 ~v3 = du_reduce'8805'_94 v0 v2
du_reduce'8805'_94 :: Integer -> T_Fin_10 -> T_Fin_10
du_reduce'8805'_94 v0 v1
  = case coe v0 of
      0 -> coe v1
      _ -> let v2 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (case coe v1 of
                C_suc_16 v4 -> coe du_reduce'8805'_94 (coe v2) (coe v4)
                _           -> MAlonzo.RTE.mazUnreachableError)
-- Data.Fin.Base.inject
d_inject_104 :: Integer -> T_Fin_10 -> T_Fin_10 -> T_Fin_10
d_inject_104 ~v0 v1 v2 = du_inject_104 v1 v2
du_inject_104 :: T_Fin_10 -> T_Fin_10 -> T_Fin_10
du_inject_104 v0 v1
  = case coe v0 of
      C_suc_16 v3
        -> case coe v1 of
             C_zero_12   -> coe C_zero_12
             C_suc_16 v5 -> coe C_suc_16 (coe du_inject_104 (coe v3) (coe v5))
             _           -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Fin.Base.inject!
d_inject'33'_114 :: Integer -> T_Fin_10 -> T_Fin_10 -> T_Fin_10
d_inject'33'_114 ~v0 v1 v2 = du_inject'33'_114 v1 v2
du_inject'33'_114 :: T_Fin_10 -> T_Fin_10 -> T_Fin_10
du_inject'33'_114 v0 v1
  = case coe v0 of
      C_suc_16 v3
        -> case coe v1 of
             C_zero_12 -> coe C_zero_12
             C_suc_16 v5
               -> coe C_suc_16 (coe du_inject'33'_114 (coe v3) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Fin.Base.inject₁
d_inject'8321'_118 :: Integer -> T_Fin_10 -> T_Fin_10
d_inject'8321'_118 ~v0 v1 = du_inject'8321'_118 v1
du_inject'8321'_118 :: T_Fin_10 -> T_Fin_10
du_inject'8321'_118 v0 = coe v0
-- Data.Fin.Base.inject≤
d_inject'8804'_122 ::
  Integer ->
  Integer ->
  T_Fin_10 -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> T_Fin_10
d_inject'8804'_122 ~v0 ~v1 v2 ~v3 = du_inject'8804'_122 v2
du_inject'8804'_122 :: T_Fin_10 -> T_Fin_10
du_inject'8804'_122 v0 = coe v0
-- Data.Fin.Base.lower₁
d_lower'8321'_130 ::
  Integer ->
  T_Fin_10 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  T_Fin_10
d_lower'8321'_130 v0 v1 ~v2 = du_lower'8321'_130 v0 v1
du_lower'8321'_130 :: Integer -> T_Fin_10 -> T_Fin_10
du_lower'8321'_130 v0 v1
  = case coe v0 of
      0 -> coe
             seq (coe v1)
             (coe
                MAlonzo.Code.Relation.Nullary.Negation.Core.du_contradiction_44
                erased)
      _ -> let v2 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (case coe v1 of
                C_zero_12 -> coe C_zero_12
                C_suc_16 v4
                  -> coe C_suc_16 (coe du_lower'8321'_130 (coe v2) (coe v4))
                _ -> MAlonzo.RTE.mazUnreachableError)
-- Data.Fin.Base.strengthen
d_strengthen_144 :: Integer -> T_Fin_10 -> T_Fin_10
d_strengthen_144 ~v0 v1 = du_strengthen_144 v1
du_strengthen_144 :: T_Fin_10 -> T_Fin_10
du_strengthen_144 v0 = coe v0
-- Data.Fin.Base.splitAt
d_splitAt_152 ::
  Integer ->
  Integer -> T_Fin_10 -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_splitAt_152 v0 ~v1 v2 = du_splitAt_152 v0 v2
du_splitAt_152 ::
  Integer -> T_Fin_10 -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_splitAt_152 v0 v1
  = case coe v0 of
      0 -> coe MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 (coe v1)
      _ -> let v2 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (case coe v1 of
                C_zero_12
                  -> coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 (coe C_zero_12)
                C_suc_16 v4
                  -> coe
                       MAlonzo.Code.Data.Sum.Base.du_map'8321'_90 (coe C_suc_16)
                       (coe du_splitAt_152 (coe v2) (coe v4))
                _ -> MAlonzo.RTE.mazUnreachableError)
-- Data.Fin.Base.join
d_join_166 ::
  Integer ->
  Integer -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30 -> T_Fin_10
d_join_166 v0 ~v1 = du_join_166 v0
du_join_166 ::
  Integer -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30 -> T_Fin_10
du_join_166 v0
  = coe
      MAlonzo.Code.Data.Sum.Base.du_'91'_'44'_'93''8242'_66 (\ v1 -> v1)
      (coe du__'8593''691'__84 (coe v0))
-- Data.Fin.Base.quotRem
d_quotRem_178 ::
  Integer ->
  Integer -> T_Fin_10 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_quotRem_178 ~v0 v1 v2 = du_quotRem_178 v1 v2
du_quotRem_178 ::
  Integer -> T_Fin_10 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_quotRem_178 v0 v1
  = coe
      MAlonzo.Code.Data.Sum.Base.du_'91'_'44'_'93''8242'_66
      (\ v2 ->
         coe
           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2)
           (coe C_zero_12))
      (\ v2 ->
         coe
           MAlonzo.Code.Data.Product.Base.du_map'8322'_150
           (\ v3 -> coe C_suc_16) (coe du_quotRem_178 (coe v0) (coe v2)))
      (coe du_splitAt_152 (coe v0) (coe v1))
-- Data.Fin.Base.remQuot
d_remQuot_190 ::
  Integer ->
  Integer -> T_Fin_10 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_remQuot_190 ~v0 v1 v2 = du_remQuot_190 v1 v2
du_remQuot_190 ::
  Integer -> T_Fin_10 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_remQuot_190 v0 v1
  = coe
      MAlonzo.Code.Data.Product.Base.du_swap_370
      (coe du_quotRem_178 (coe v0) (coe v1))
-- Data.Fin.Base.quotient
d_quotient_196 :: Integer -> Integer -> T_Fin_10 -> T_Fin_10
d_quotient_196 ~v0 v1 v2 = du_quotient_196 v1 v2
du_quotient_196 :: Integer -> T_Fin_10 -> T_Fin_10
du_quotient_196 v0 v1
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
      (coe du_remQuot_190 (coe v0) (coe v1))
-- Data.Fin.Base.remainder
d_remainder_202 :: Integer -> Integer -> T_Fin_10 -> T_Fin_10
d_remainder_202 ~v0 v1 v2 = du_remainder_202 v1 v2
du_remainder_202 :: Integer -> T_Fin_10 -> T_Fin_10
du_remainder_202 v0 v1
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
      (coe du_remQuot_190 (coe v0) (coe v1))
-- Data.Fin.Base.combine
d_combine_208 ::
  Integer -> Integer -> T_Fin_10 -> T_Fin_10 -> T_Fin_10
d_combine_208 ~v0 v1 v2 v3 = du_combine_208 v1 v2 v3
du_combine_208 :: Integer -> T_Fin_10 -> T_Fin_10 -> T_Fin_10
du_combine_208 v0 v1 v2
  = case coe v1 of
      C_zero_12 -> coe v2
      C_suc_16 v4
        -> coe
             du__'8593''691'__84 (coe v0)
             (coe du_combine_208 (coe v0) (coe v4) (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Fin.Base.finToFun
d_finToFun_224 ::
  Integer -> Integer -> T_Fin_10 -> T_Fin_10 -> T_Fin_10
d_finToFun_224 v0 v1 v2 v3
  = let v4 = subInt (coe v1) (coe (1 :: Integer)) in
    coe
      (case coe v3 of
         C_zero_12
           -> coe
                du_quotient_196
                (coe MAlonzo.Code.Data.Nat.Base.d__'94'__272 (coe v0) (coe v4))
                (coe v2)
         C_suc_16 v6
           -> coe
                d_finToFun_224 (coe v0) (coe v4)
                (coe
                   du_remainder_202
                   (coe MAlonzo.Code.Data.Nat.Base.d__'94'__272 (coe v0) (coe v4))
                   (coe v2))
                (coe v6)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Data.Fin.Base.funToFin
d_funToFin_240 ::
  Integer -> Integer -> (T_Fin_10 -> T_Fin_10) -> T_Fin_10
d_funToFin_240 v0 v1 v2
  = case coe v0 of
      0 -> coe C_zero_12
      _ -> let v3 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (coe
                du_combine_208
                (coe MAlonzo.Code.Data.Nat.Base.d__'94'__272 (coe v1) (coe v3))
                (coe v2 (coe C_zero_12))
                (coe
                   d_funToFin_240 (coe v3) (coe v1)
                   (coe (\ v4 -> coe v2 (coe C_suc_16 v4)))))
-- Data.Fin.Base.fold
d_fold_258 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (Integer -> ()) ->
  Integer ->
  (Integer -> AgdaAny -> AgdaAny) ->
  (Integer -> AgdaAny) -> T_Fin_10 -> AgdaAny
d_fold_258 ~v0 ~v1 v2 v3 v4 v5 = du_fold_258 v2 v3 v4 v5
du_fold_258 ::
  Integer ->
  (Integer -> AgdaAny -> AgdaAny) ->
  (Integer -> AgdaAny) -> T_Fin_10 -> AgdaAny
du_fold_258 v0 v1 v2 v3
  = case coe v3 of
      C_zero_12
        -> let v5 = subInt (coe v0) (coe (1 :: Integer)) in coe (coe v2 v5)
      C_suc_16 v5
        -> let v6 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (coe v1 v6 (coe du_fold_258 (coe v6) (coe v1) (coe v2) (coe v5)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Fin.Base.fold′
d_fold'8242'_284 ::
  Integer ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (T_Fin_10 -> ()) ->
  (T_Fin_10 -> AgdaAny -> AgdaAny) -> AgdaAny -> T_Fin_10 -> AgdaAny
d_fold'8242'_284 ~v0 ~v1 ~v2 v3 v4 v5 = du_fold'8242'_284 v3 v4 v5
du_fold'8242'_284 ::
  (T_Fin_10 -> AgdaAny -> AgdaAny) -> AgdaAny -> T_Fin_10 -> AgdaAny
du_fold'8242'_284 v0 v1 v2
  = case coe v2 of
      C_zero_12 -> coe v1
      C_suc_16 v4
        -> coe
             v0 v4
             (coe du_fold'8242'_284 (coe (\ v5 -> coe v0 v5)) (coe v1) (coe v4))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Fin.Base.lift
d_lift_304 ::
  Integer ->
  Integer ->
  Integer -> (T_Fin_10 -> T_Fin_10) -> T_Fin_10 -> T_Fin_10
d_lift_304 ~v0 ~v1 v2 v3 v4 = du_lift_304 v2 v3 v4
du_lift_304 ::
  Integer -> (T_Fin_10 -> T_Fin_10) -> T_Fin_10 -> T_Fin_10
du_lift_304 v0 v1 v2
  = case coe v0 of
      0 -> coe v1 v2
      _ -> let v3 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (case coe v2 of
                C_zero_12 -> coe C_zero_12
                C_suc_16 v5
                  -> coe C_suc_16 (coe du_lift_304 (coe v3) (coe v1) (coe v5))
                _ -> MAlonzo.RTE.mazUnreachableError)
-- Data.Fin.Base._+_
d__'43'__324 ::
  Integer -> Integer -> T_Fin_10 -> T_Fin_10 -> T_Fin_10
d__'43'__324 ~v0 ~v1 v2 v3 = du__'43'__324 v2 v3
du__'43'__324 :: T_Fin_10 -> T_Fin_10 -> T_Fin_10
du__'43'__324 v0 v1
  = case coe v0 of
      C_zero_12   -> coe v1
      C_suc_16 v3 -> coe C_suc_16 (coe du__'43'__324 (coe v3) (coe v1))
      _           -> MAlonzo.RTE.mazUnreachableError
-- Data.Fin.Base._-_
d__'45'__336 :: Integer -> T_Fin_10 -> T_Fin_10 -> T_Fin_10
d__'45'__336 ~v0 v1 v2 = du__'45'__336 v1 v2
du__'45'__336 :: T_Fin_10 -> T_Fin_10 -> T_Fin_10
du__'45'__336 v0 v1
  = case coe v1 of
      C_zero_12 -> coe v0
      C_suc_16 v3
        -> case coe v0 of
             C_suc_16 v5 -> coe du__'45'__336 (coe v5) (coe v3)
             _           -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Fin.Base._ℕ-_
d__ℕ'45'__348 :: Integer -> T_Fin_10 -> T_Fin_10
d__ℕ'45'__348 v0 v1
  = case coe v1 of
      C_zero_12 -> coe d_fromℕ_48 (coe v0)
      C_suc_16 v3
        -> let v4 = subInt (coe v0) (coe (1 :: Integer)) in
           coe (coe d__ℕ'45'__348 (coe v4) (coe v3))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Fin.Base._ℕ-ℕ_
d__ℕ'45'ℕ__358 :: Integer -> T_Fin_10 -> Integer
d__ℕ'45'ℕ__358 v0 v1
  = case coe v1 of
      C_zero_12 -> coe v0
      C_suc_16 v3
        -> let v4 = subInt (coe v0) (coe (1 :: Integer)) in
           coe (coe d__ℕ'45'ℕ__358 (coe v4) (coe v3))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Fin.Base.pred
d_pred_366 :: Integer -> T_Fin_10 -> T_Fin_10
d_pred_366 ~v0 v1 = du_pred_366 v1
du_pred_366 :: T_Fin_10 -> T_Fin_10
du_pred_366 v0
  = case coe v0 of
      C_zero_12   -> coe C_zero_12
      C_suc_16 v2 -> coe v2
      _           -> MAlonzo.RTE.mazUnreachableError
-- Data.Fin.Base.opposite
d_opposite_370 :: Integer -> T_Fin_10 -> T_Fin_10
d_opposite_370 v0 v1
  = let v2 = subInt (coe v0) (coe (1 :: Integer)) in
    coe
      (case coe v1 of
         C_zero_12   -> coe d_fromℕ_48 (coe v2)
         C_suc_16 v4 -> coe d_opposite_370 (coe v2) (coe v4)
         _           -> MAlonzo.RTE.mazUnreachableError)
-- Data.Fin.Base.punchOut
d_punchOut_382 ::
  Integer ->
  T_Fin_10 ->
  T_Fin_10 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  T_Fin_10
d_punchOut_382 ~v0 v1 v2 ~v3 = du_punchOut_382 v1 v2
du_punchOut_382 :: T_Fin_10 -> T_Fin_10 -> T_Fin_10
du_punchOut_382 v0 v1
  = case coe v0 of
      C_zero_12
        -> case coe v1 of
             C_zero_12
               -> coe
                    MAlonzo.Code.Relation.Nullary.Negation.Core.du_contradiction_44
                    erased
             C_suc_16 v4 -> coe v4
             _ -> MAlonzo.RTE.mazUnreachableError
      C_suc_16 v3
        -> case coe v1 of
             C_zero_12   -> coe C_zero_12
             C_suc_16 v5 -> coe C_suc_16 (coe du_punchOut_382 (coe v3) (coe v5))
             _           -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Fin.Base.punchIn
d_punchIn_396 :: Integer -> T_Fin_10 -> T_Fin_10 -> T_Fin_10
d_punchIn_396 ~v0 v1 v2 = du_punchIn_396 v1 v2
du_punchIn_396 :: T_Fin_10 -> T_Fin_10 -> T_Fin_10
du_punchIn_396 v0 v1
  = case coe v0 of
      C_zero_12 -> coe C_suc_16 v1
      C_suc_16 v3
        -> case coe v1 of
             C_zero_12   -> coe C_zero_12
             C_suc_16 v5 -> coe C_suc_16 (coe du_punchIn_396 (coe v3) (coe v5))
             _           -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Fin.Base.pinch
d_pinch_406 :: Integer -> T_Fin_10 -> T_Fin_10 -> T_Fin_10
d_pinch_406 ~v0 v1 v2 = du_pinch_406 v1 v2
du_pinch_406 :: T_Fin_10 -> T_Fin_10 -> T_Fin_10
du_pinch_406 v0 v1
  = case coe v1 of
      C_zero_12 -> coe C_zero_12
      C_suc_16 v3
        -> case coe v0 of
             C_zero_12   -> coe v3
             C_suc_16 v5 -> coe C_suc_16 (coe du_pinch_406 (coe v5) (coe v3))
             _           -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Fin.Base._≤_
d__'8804'__420 :: Integer -> Integer -> T_Fin_10 -> T_Fin_10 -> ()
d__'8804'__420 = erased
-- Data.Fin.Base._≥_
d__'8805'__426 :: Integer -> Integer -> T_Fin_10 -> T_Fin_10 -> ()
d__'8805'__426 = erased
-- Data.Fin.Base._<_
d__'60'__432 :: Integer -> Integer -> T_Fin_10 -> T_Fin_10 -> ()
d__'60'__432 = erased
-- Data.Fin.Base._>_
d__'62'__438 :: Integer -> Integer -> T_Fin_10 -> T_Fin_10 -> ()
d__'62'__438 = erased
-- Data.Fin.Base.Ordering
d_Ordering_446 a0 a1 a2 = ()
data T_Ordering_446
  = C_less_454 T_Fin_10 | C_equal_458 | C_greater_464 T_Fin_10
-- Data.Fin.Base.compare
d_compare_470 :: Integer -> T_Fin_10 -> T_Fin_10 -> T_Ordering_446
d_compare_470 ~v0 v1 v2 = du_compare_470 v1 v2
du_compare_470 :: T_Fin_10 -> T_Fin_10 -> T_Ordering_446
du_compare_470 v0 v1
  = case coe v0 of
      C_zero_12
        -> case coe v1 of
             C_zero_12   -> coe C_equal_458
             C_suc_16 v4 -> coe C_less_454 (coe C_zero_12)
             _           -> MAlonzo.RTE.mazUnreachableError
      C_suc_16 v3
        -> case coe v1 of
             C_zero_12 -> coe C_greater_464 (coe C_zero_12)
             C_suc_16 v5
               -> let v6 = coe du_compare_470 (coe v3) (coe v5) in
                  coe
                    (case coe v6 of
                       C_less_454 v8    -> coe C_less_454 (coe C_suc_16 v8)
                       C_equal_458      -> coe C_equal_458
                       C_greater_464 v8 -> coe C_greater_464 (coe C_suc_16 v8)
                       _                -> MAlonzo.RTE.mazUnreachableError)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Fin.Base.raise
d_raise_506 :: Integer -> Integer -> T_Fin_10 -> T_Fin_10
d_raise_506 v0 v1 v2 = coe du__'8593''691'__84 v1 v2
-- Data.Fin.Base.inject+
d_inject'43'_512 :: Integer -> Integer -> T_Fin_10 -> T_Fin_10
d_inject'43'_512 ~v0 ~v1 v2 = du_inject'43'_512 v2
du_inject'43'_512 :: T_Fin_10 -> T_Fin_10
du_inject'43'_512 v0 = coe v0
-- Data.Fin.Base._≺_
d__'8826'__518 a0 a1 = ()
newtype T__'8826'__518 = C__'8827'toℕ__524 T_Fin_10
