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

module MAlonzo.Code.Algebra.Apartness.Structures where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Algebra.Consequences.Base
import qualified MAlonzo.Code.Algebra.Structures
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Relation.Binary.Bundles
import qualified MAlonzo.Code.Relation.Binary.Properties.ApartnessRelation
import qualified MAlonzo.Code.Relation.Binary.Structures

-- Algebra.Apartness.Structures._.Invertible
d_Invertible_30 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> (AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny -> ()
d_Invertible_30 = erased
-- Algebra.Apartness.Structures._.IsCommutativeRing
d_IsCommutativeRing_34 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12
                       a13 a14 a15
  = ()
-- Algebra.Apartness.Structures._.IsCommutativeRing._//_
d__'47''47'__38 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2816 ->
  AgdaAny -> AgdaAny -> AgdaAny
d__'47''47'__38 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 v11
                ~v12 v13 ~v14 ~v15 ~v16
  = du__'47''47'__38 v11 v13
du__'47''47'__38 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny -> AgdaAny
du__'47''47'__38 v0 v1
  = coe
      MAlonzo.Code.Algebra.Structures.du__'47''47'__1096 (coe v0)
      (coe v1)
-- Algebra.Apartness.Structures._.IsCommutativeRing.*-comm
d_'42''45'comm_42 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2816 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_'42''45'comm_42 v0
  = coe MAlonzo.Code.Algebra.Structures.d_'42''45'comm_2834 (coe v0)
-- Algebra.Apartness.Structures._.IsCommutativeRing.∙-congʳ
d_'8729''45'cong'691'_46 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2816 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'691'_46 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                         ~v10 v11 v12 v13 v14 ~v15 v16
  = du_'8729''45'cong'691'_46 v11 v12 v13 v14 v16
du_'8729''45'cong'691'_46 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2816 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'691'_46 v0 v1 v2 v3 v4
  = let v5
          = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v4) in
    coe
      (let v6
             = coe
                 MAlonzo.Code.Algebra.Structures.du_isRingWithoutOne_2702
                 (coe v5) in
       coe
         (let v7
                = coe
                    MAlonzo.Code.Algebra.Structures.du_isNearSemiring_2406 (coe v0)
                    (coe v1) (coe v2) (coe v3) (coe v6) in
          coe
            (let v8
                   = coe
                       MAlonzo.Code.Algebra.Structures.du_'42''45'isMagma_1280 (coe v7) in
             coe
               (let v9
                      = coe MAlonzo.Code.Algebra.Structures.du_setoid_200 (coe v8) in
                coe
                  (let v10
                         = MAlonzo.Code.Algebra.Structures.d_'8729''45'cong_186 (coe v8) in
                   coe
                     (coe
                        MAlonzo.Code.Algebra.Consequences.Base.du_'8729''45'cong'691'_46
                        (coe v10)
                        (coe
                           MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                           (coe
                              MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                              (coe v9)))))))))
-- Algebra.Apartness.Structures._.IsCommutativeRing.∙-congˡ
d_'8729''45'cong'737'_48 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2816 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'737'_48 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                         ~v10 v11 v12 v13 v14 ~v15 v16
  = du_'8729''45'cong'737'_48 v11 v12 v13 v14 v16
du_'8729''45'cong'737'_48 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2816 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'737'_48 v0 v1 v2 v3 v4
  = let v5
          = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v4) in
    coe
      (let v6
             = coe
                 MAlonzo.Code.Algebra.Structures.du_isRingWithoutOne_2702
                 (coe v5) in
       coe
         (let v7
                = coe
                    MAlonzo.Code.Algebra.Structures.du_isNearSemiring_2406 (coe v0)
                    (coe v1) (coe v2) (coe v3) (coe v6) in
          coe
            (let v8
                   = coe
                       MAlonzo.Code.Algebra.Structures.du_'42''45'isMagma_1280 (coe v7) in
             coe
               (let v9
                      = coe MAlonzo.Code.Algebra.Structures.du_setoid_200 (coe v8) in
                coe
                  (let v10
                         = MAlonzo.Code.Algebra.Structures.d_'8729''45'cong_186 (coe v8) in
                   coe
                     (coe
                        MAlonzo.Code.Algebra.Consequences.Base.du_'8729''45'cong'737'_42
                        (coe v10)
                        (coe
                           MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                           (coe
                              MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                              (coe v9)))))))))
-- Algebra.Apartness.Structures._.IsCommutativeRing.identityʳ
d_identity'691'_52 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2816 ->
  AgdaAny -> AgdaAny
d_identity'691'_52 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 v11
                   v12 v13 v14 ~v15 v16
  = du_identity'691'_52 v11 v12 v13 v14 v16
du_identity'691'_52 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2816 ->
  AgdaAny -> AgdaAny
du_identity'691'_52 v0 v1 v2 v3 v4
  = let v5
          = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v4) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.du_identity'691'_726
         (coe
            MAlonzo.Code.Algebra.Structures.du_'42''45'isMonoid_2790 (coe v0)
            (coe v1) (coe v2) (coe v3) (coe v5)))
-- Algebra.Apartness.Structures._.IsCommutativeRing.identityˡ
d_identity'737'_54 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2816 ->
  AgdaAny -> AgdaAny
d_identity'737'_54 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 v11
                   v12 v13 v14 ~v15 v16
  = du_identity'737'_54 v11 v12 v13 v14 v16
du_identity'737'_54 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2816 ->
  AgdaAny -> AgdaAny
du_identity'737'_54 v0 v1 v2 v3 v4
  = let v5
          = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v4) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.du_identity'737'_724
         (coe
            MAlonzo.Code.Algebra.Structures.du_'42''45'isMonoid_2790 (coe v0)
            (coe v1) (coe v2) (coe v3) (coe v5)))
-- Algebra.Apartness.Structures._.IsCommutativeRing.isCommutativeMagma
d_isCommutativeMagma_56 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2816 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMagma_210
d_isCommutativeMagma_56 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                        ~v10 v11 v12 v13 v14 ~v15 v16
  = du_isCommutativeMagma_56 v11 v12 v13 v14 v16
du_isCommutativeMagma_56 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2816 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMagma_210
du_isCommutativeMagma_56 v0 v1 v2 v3 v4
  = let v5
          = coe
              MAlonzo.Code.Algebra.Structures.du_isCommutativeSemiring_2946
              (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) in
    coe
      (let v6
             = coe
                 MAlonzo.Code.Algebra.Structures.du_isCommutativeSemiringWithoutOne_1798
                 (coe v5) in
       coe
         (coe
            MAlonzo.Code.Algebra.Structures.du_isCommutativeMagma_584
            (coe
               MAlonzo.Code.Algebra.Structures.du_'42''45'isCommutativeSemigroup_1472
               (coe v6))))
-- Algebra.Apartness.Structures._.IsCommutativeRing.*-isCommutativeMonoid
d_'42''45'isCommutativeMonoid_58 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2816 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_734
d_'42''45'isCommutativeMonoid_58 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
                                 ~v8 ~v9 ~v10 v11 v12 v13 v14 ~v15 v16
  = du_'42''45'isCommutativeMonoid_58 v11 v12 v13 v14 v16
du_'42''45'isCommutativeMonoid_58 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2816 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_734
du_'42''45'isCommutativeMonoid_58 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Algebra.Structures.du_'42''45'isCommutativeMonoid_1806
      (coe
         MAlonzo.Code.Algebra.Structures.du_isCommutativeSemiring_2946
         (coe v0) (coe v1) (coe v2) (coe v3) (coe v4))
-- Algebra.Apartness.Structures._.IsCommutativeRing.*-isCommutativeSemigroup
d_'42''45'isCommutativeSemigroup_60 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2816 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_546
d_'42''45'isCommutativeSemigroup_60 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
                                    ~v8 ~v9 ~v10 v11 v12 v13 v14 ~v15 v16
  = du_'42''45'isCommutativeSemigroup_60 v11 v12 v13 v14 v16
du_'42''45'isCommutativeSemigroup_60 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2816 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_546
du_'42''45'isCommutativeSemigroup_60 v0 v1 v2 v3 v4
  = let v5
          = coe
              MAlonzo.Code.Algebra.Structures.du_isCommutativeSemiring_2946
              (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.du_'42''45'isCommutativeSemigroup_1472
         (coe
            MAlonzo.Code.Algebra.Structures.du_isCommutativeSemiringWithoutOne_1798
            (coe v5)))
-- Algebra.Apartness.Structures._.IsCommutativeRing.*-isMagma
d_'42''45'isMagma_62 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2816 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176
d_'42''45'isMagma_62 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
                     v11 v12 v13 v14 ~v15 v16
  = du_'42''45'isMagma_62 v11 v12 v13 v14 v16
du_'42''45'isMagma_62 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2816 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176
du_'42''45'isMagma_62 v0 v1 v2 v3 v4
  = let v5
          = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v4) in
    coe
      (let v6
             = coe
                 MAlonzo.Code.Algebra.Structures.du_isRingWithoutOne_2702
                 (coe v5) in
       coe
         (coe
            MAlonzo.Code.Algebra.Structures.du_'42''45'isMagma_1280
            (coe
               MAlonzo.Code.Algebra.Structures.du_isNearSemiring_2406 (coe v0)
               (coe v1) (coe v2) (coe v3) (coe v6))))
-- Algebra.Apartness.Structures._.IsCommutativeRing.*-isMonoid
d_'42''45'isMonoid_64 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2816 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_684
d_'42''45'isMonoid_64 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
                      v11 v12 v13 v14 ~v15 v16
  = du_'42''45'isMonoid_64 v11 v12 v13 v14 v16
du_'42''45'isMonoid_64 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2816 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_684
du_'42''45'isMonoid_64 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Algebra.Structures.du_'42''45'isMonoid_2790 (coe v0)
      (coe v1) (coe v2) (coe v3)
      (coe MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v4))
-- Algebra.Apartness.Structures._.IsCommutativeRing.*-isSemigroup
d_'42''45'isSemigroup_66 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2816 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_470
d_'42''45'isSemigroup_66 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                         ~v10 v11 v12 v13 v14 ~v15 v16
  = du_'42''45'isSemigroup_66 v11 v12 v13 v14 v16
du_'42''45'isSemigroup_66 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2816 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_470
du_'42''45'isSemigroup_66 v0 v1 v2 v3 v4
  = let v5
          = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v4) in
    coe
      (let v6
             = coe
                 MAlonzo.Code.Algebra.Structures.du_isRingWithoutOne_2702
                 (coe v5) in
       coe
         (coe
            MAlonzo.Code.Algebra.Structures.du_'42''45'isSemigroup_1282
            (coe
               MAlonzo.Code.Algebra.Structures.du_isNearSemiring_2406 (coe v0)
               (coe v1) (coe v2) (coe v3) (coe v6))))
-- Algebra.Apartness.Structures._.IsCommutativeRing.assoc
d_assoc_68 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2816 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_assoc_68 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12
           ~v13 ~v14 ~v15 v16
  = du_assoc_68 v16
du_assoc_68 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2816 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_assoc_68 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.d_assoc_480
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
            (coe
               MAlonzo.Code.Algebra.Structures.d_isMonoid_1048
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isGroup_1142
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2692
                     (coe v1))))))
-- Algebra.Apartness.Structures._.IsCommutativeRing.comm
d_comm_70 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2816 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_comm_70 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12
          ~v13 ~v14 ~v15 v16
  = du_comm_70 v16
du_comm_70 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2816 ->
  AgdaAny -> AgdaAny -> AgdaAny
du_comm_70 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.d_comm_1144
         (coe
            MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2692
            (coe v1)))
-- Algebra.Apartness.Structures._.IsCommutativeRing.∙-cong
d_'8729''45'cong_72 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2816 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong_72 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
                    ~v11 ~v12 ~v13 ~v14 ~v15 v16
  = du_'8729''45'cong_72 v16
du_'8729''45'cong_72 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2816 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong_72 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.d_'8729''45'cong_186
         (coe
            MAlonzo.Code.Algebra.Structures.d_isMagma_478
            (coe
               MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isMonoid_1048
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_isGroup_1142
                     (coe
                        MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2692
                        (coe v1)))))))
-- Algebra.Apartness.Structures._.IsCommutativeRing.∙-congʳ
d_'8729''45'cong'691'_74 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2816 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'691'_74 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                         ~v10 ~v11 ~v12 ~v13 ~v14 ~v15 v16
  = du_'8729''45'cong'691'_74 v16
du_'8729''45'cong'691'_74 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2816 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'691'_74 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v0) in
    coe
      (let v2
             = coe
                 MAlonzo.Code.Algebra.Structures.du_isRingWithoutOne_2702
                 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2322
                    (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Algebra.Structures.d_isGroup_1142 (coe v3) in
             coe
               (let v5
                      = MAlonzo.Code.Algebra.Structures.d_isMonoid_1048 (coe v4) in
                coe
                  (let v6
                         = MAlonzo.Code.Algebra.Structures.d_isSemigroup_694 (coe v5) in
                   coe
                     (let v7 = MAlonzo.Code.Algebra.Structures.d_isMagma_478 (coe v6) in
                      coe
                        (let v8
                               = coe MAlonzo.Code.Algebra.Structures.du_setoid_200 (coe v7) in
                         coe
                           (let v9
                                  = MAlonzo.Code.Algebra.Structures.d_'8729''45'cong_186 (coe v7) in
                            coe
                              (coe
                                 MAlonzo.Code.Algebra.Consequences.Base.du_'8729''45'cong'691'_46
                                 (coe v9)
                                 (coe
                                    MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                                    (coe
                                       MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                                       (coe v8))))))))))))
-- Algebra.Apartness.Structures._.IsCommutativeRing.∙-congˡ
d_'8729''45'cong'737'_76 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2816 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'737'_76 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                         ~v10 ~v11 ~v12 ~v13 ~v14 ~v15 v16
  = du_'8729''45'cong'737'_76 v16
du_'8729''45'cong'737'_76 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2816 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'737'_76 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v0) in
    coe
      (let v2
             = coe
                 MAlonzo.Code.Algebra.Structures.du_isRingWithoutOne_2702
                 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2322
                    (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Algebra.Structures.d_isGroup_1142 (coe v3) in
             coe
               (let v5
                      = MAlonzo.Code.Algebra.Structures.d_isMonoid_1048 (coe v4) in
                coe
                  (let v6
                         = MAlonzo.Code.Algebra.Structures.d_isSemigroup_694 (coe v5) in
                   coe
                     (let v7 = MAlonzo.Code.Algebra.Structures.d_isMagma_478 (coe v6) in
                      coe
                        (let v8
                               = coe MAlonzo.Code.Algebra.Structures.du_setoid_200 (coe v7) in
                         coe
                           (let v9
                                  = MAlonzo.Code.Algebra.Structures.d_'8729''45'cong_186 (coe v7) in
                            coe
                              (coe
                                 MAlonzo.Code.Algebra.Consequences.Base.du_'8729''45'cong'737'_42
                                 (coe v9)
                                 (coe
                                    MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                                    (coe
                                       MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                                       (coe v8))))))))))))
-- Algebra.Apartness.Structures._.IsCommutativeRing.identity
d_identity_78 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2816 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_78 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11
              ~v12 ~v13 ~v14 ~v15 v16
  = du_identity_78 v16
du_identity_78 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2816 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_identity_78 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.d_identity_696
         (coe
            MAlonzo.Code.Algebra.Structures.d_isMonoid_1048
            (coe
               MAlonzo.Code.Algebra.Structures.d_isGroup_1142
               (coe
                  MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2692
                  (coe v1)))))
-- Algebra.Apartness.Structures._.IsCommutativeRing.identityʳ
d_identity'691'_80 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2816 ->
  AgdaAny -> AgdaAny
d_identity'691'_80 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
                   ~v11 ~v12 ~v13 ~v14 ~v15 v16
  = du_identity'691'_80 v16
du_identity'691'_80 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2816 ->
  AgdaAny -> AgdaAny
du_identity'691'_80 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v0) in
    coe
      (let v2
             = coe
                 MAlonzo.Code.Algebra.Structures.du_isRingWithoutOne_2702
                 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2322
                    (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Algebra.Structures.d_isGroup_1142 (coe v3) in
             coe
               (coe
                  MAlonzo.Code.Algebra.Structures.du_identity'691'_726
                  (coe MAlonzo.Code.Algebra.Structures.d_isMonoid_1048 (coe v4))))))
-- Algebra.Apartness.Structures._.IsCommutativeRing.identityˡ
d_identity'737'_82 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2816 ->
  AgdaAny -> AgdaAny
d_identity'737'_82 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
                   ~v11 ~v12 ~v13 ~v14 ~v15 v16
  = du_identity'737'_82 v16
du_identity'737'_82 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2816 ->
  AgdaAny -> AgdaAny
du_identity'737'_82 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v0) in
    coe
      (let v2
             = coe
                 MAlonzo.Code.Algebra.Structures.du_isRingWithoutOne_2702
                 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2322
                    (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Algebra.Structures.d_isGroup_1142 (coe v3) in
             coe
               (coe
                  MAlonzo.Code.Algebra.Structures.du_identity'737'_724
                  (coe MAlonzo.Code.Algebra.Structures.d_isMonoid_1048 (coe v4))))))
-- Algebra.Apartness.Structures._.IsCommutativeRing.isCommutativeMagma
d_isCommutativeMagma_86 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2816 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMagma_210
d_isCommutativeMagma_86 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                        ~v10 ~v11 ~v12 ~v13 ~v14 ~v15 v16
  = du_isCommutativeMagma_86 v16
du_isCommutativeMagma_86 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2816 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMagma_210
du_isCommutativeMagma_86 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v0) in
    coe
      (let v2
             = coe
                 MAlonzo.Code.Algebra.Structures.du_isRingWithoutOne_2702
                 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2322
                    (coe v2) in
          coe
            (let v4
                   = coe
                       MAlonzo.Code.Algebra.Structures.du_isCommutativeMonoid_1202
                       (coe v3) in
             coe
               (coe
                  MAlonzo.Code.Algebra.Structures.du_isCommutativeMagma_584
                  (coe
                     MAlonzo.Code.Algebra.Structures.du_isCommutativeSemigroup_784
                     (coe v4))))))
-- Algebra.Apartness.Structures._.IsCommutativeRing.isCommutativeMonoid
d_isCommutativeMonoid_88 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2816 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_734
d_isCommutativeMonoid_88 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                         ~v10 ~v11 ~v12 ~v13 ~v14 ~v15 v16
  = du_isCommutativeMonoid_88 v16
du_isCommutativeMonoid_88 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2816 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_734
du_isCommutativeMonoid_88 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v0) in
    coe
      (let v2
             = coe
                 MAlonzo.Code.Algebra.Structures.du_isRingWithoutOne_2702
                 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Algebra.Structures.du_isCommutativeMonoid_1202
            (coe
               MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2322
               (coe v2))))
-- Algebra.Apartness.Structures._.IsCommutativeRing.isCommutativeSemigroup
d_isCommutativeSemigroup_90 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2816 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_546
d_isCommutativeSemigroup_90 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                            ~v10 ~v11 ~v12 ~v13 ~v14 ~v15 v16
  = du_isCommutativeSemigroup_90 v16
du_isCommutativeSemigroup_90 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2816 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_546
du_isCommutativeSemigroup_90 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v0) in
    coe
      (let v2
             = coe
                 MAlonzo.Code.Algebra.Structures.du_isRingWithoutOne_2702
                 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2322
                    (coe v2) in
          coe
            (coe
               MAlonzo.Code.Algebra.Structures.du_isCommutativeSemigroup_784
               (coe
                  MAlonzo.Code.Algebra.Structures.du_isCommutativeMonoid_1202
                  (coe v3)))))
-- Algebra.Apartness.Structures._.IsCommutativeRing.isGroup
d_isGroup_92 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2816 ->
  MAlonzo.Code.Algebra.Structures.T_IsGroup_1034
d_isGroup_92 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12
             ~v13 ~v14 ~v15 v16
  = du_isGroup_92 v16
du_isGroup_92 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2816 ->
  MAlonzo.Code.Algebra.Structures.T_IsGroup_1034
du_isGroup_92 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.d_isGroup_1142
         (coe
            MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2692
            (coe v1)))
-- Algebra.Apartness.Structures._.IsCommutativeRing.isInvertibleMagma
d_isInvertibleMagma_94 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2816 ->
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleMagma_922
d_isInvertibleMagma_94 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
                       ~v11 ~v12 ~v13 ~v14 ~v15 v16
  = du_isInvertibleMagma_94 v16
du_isInvertibleMagma_94 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2816 ->
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleMagma_922
du_isInvertibleMagma_94 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v0) in
    coe
      (let v2
             = coe
                 MAlonzo.Code.Algebra.Structures.du_isRingWithoutOne_2702
                 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2322
                    (coe v2) in
          coe
            (coe
               MAlonzo.Code.Algebra.Structures.du_isInvertibleMagma_1120
               (coe MAlonzo.Code.Algebra.Structures.d_isGroup_1142 (coe v3)))))
-- Algebra.Apartness.Structures._.IsCommutativeRing.isInvertibleUnitalMagma
d_isInvertibleUnitalMagma_96 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2816 ->
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleUnitalMagma_974
d_isInvertibleUnitalMagma_96 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8
                             ~v9 ~v10 ~v11 ~v12 ~v13 ~v14 ~v15 v16
  = du_isInvertibleUnitalMagma_96 v16
du_isInvertibleUnitalMagma_96 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2816 ->
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleUnitalMagma_974
du_isInvertibleUnitalMagma_96 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v0) in
    coe
      (let v2
             = coe
                 MAlonzo.Code.Algebra.Structures.du_isRingWithoutOne_2702
                 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2322
                    (coe v2) in
          coe
            (coe
               MAlonzo.Code.Algebra.Structures.du_isInvertibleUnitalMagma_1122
               (coe MAlonzo.Code.Algebra.Structures.d_isGroup_1142 (coe v3)))))
-- Algebra.Apartness.Structures._.IsCommutativeRing.isMagma
d_isMagma_98 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2816 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176
d_isMagma_98 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12
             ~v13 ~v14 ~v15 v16
  = du_isMagma_98 v16
du_isMagma_98 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2816 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176
du_isMagma_98 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMagma_478
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
            (coe
               MAlonzo.Code.Algebra.Structures.d_isMonoid_1048
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isGroup_1142
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2692
                     (coe v1))))))
-- Algebra.Apartness.Structures._.IsCommutativeRing.isMonoid
d_isMonoid_100 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2816 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_684
d_isMonoid_100 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11
               ~v12 ~v13 ~v14 ~v15 v16
  = du_isMonoid_100 v16
du_isMonoid_100 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2816 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_684
du_isMonoid_100 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMonoid_1048
         (coe
            MAlonzo.Code.Algebra.Structures.d_isGroup_1142
            (coe
               MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2692
               (coe v1))))
-- Algebra.Apartness.Structures._.IsCommutativeRing.isSemigroup
d_isSemigroup_102 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2816 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_470
d_isSemigroup_102 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11
                  ~v12 ~v13 ~v14 ~v15 v16
  = du_isSemigroup_102 v16
du_isSemigroup_102 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2816 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_470
du_isSemigroup_102 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
         (coe
            MAlonzo.Code.Algebra.Structures.d_isMonoid_1048
            (coe
               MAlonzo.Code.Algebra.Structures.d_isGroup_1142
               (coe
                  MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2692
                  (coe v1)))))
-- Algebra.Apartness.Structures._.IsCommutativeRing.isUnitalMagma
d_isUnitalMagma_104 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2816 ->
  MAlonzo.Code.Algebra.Structures.T_IsUnitalMagma_640
d_isUnitalMagma_104 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
                    ~v11 ~v12 ~v13 ~v14 ~v15 v16
  = du_isUnitalMagma_104 v16
du_isUnitalMagma_104 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2816 ->
  MAlonzo.Code.Algebra.Structures.T_IsUnitalMagma_640
du_isUnitalMagma_104 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v0) in
    coe
      (let v2
             = coe
                 MAlonzo.Code.Algebra.Structures.du_isRingWithoutOne_2702
                 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2322
                    (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Algebra.Structures.d_isGroup_1142 (coe v3) in
             coe
               (coe
                  MAlonzo.Code.Algebra.Structures.du_isUnitalMagma_728
                  (coe MAlonzo.Code.Algebra.Structures.d_isMonoid_1048 (coe v4))))))
-- Algebra.Apartness.Structures._.IsCommutativeRing.⁻¹-cong
d_'8315''185''45'cong_106 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2816 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8315''185''45'cong_106 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                          ~v10 ~v11 ~v12 ~v13 ~v14 ~v15 v16
  = du_'8315''185''45'cong_106 v16
du_'8315''185''45'cong_106 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2816 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8315''185''45'cong_106 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.d_'8315''185''45'cong_1052
         (coe
            MAlonzo.Code.Algebra.Structures.d_isGroup_1142
            (coe
               MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2692
               (coe v1))))
-- Algebra.Apartness.Structures._.IsCommutativeRing.inverse
d_inverse_108 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2816 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inverse_108 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11
              ~v12 ~v13 ~v14 ~v15 v16
  = du_inverse_108 v16
du_inverse_108 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2816 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_inverse_108 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.d_inverse_1050
         (coe
            MAlonzo.Code.Algebra.Structures.d_isGroup_1142
            (coe
               MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2692
               (coe v1))))
-- Algebra.Apartness.Structures._.IsCommutativeRing.inverseʳ
d_inverse'691'_110 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2816 ->
  AgdaAny -> AgdaAny
d_inverse'691'_110 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
                   ~v11 ~v12 ~v13 ~v14 ~v15 v16
  = du_inverse'691'_110 v16
du_inverse'691'_110 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2816 ->
  AgdaAny -> AgdaAny
du_inverse'691'_110 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v0) in
    coe
      (let v2
             = coe
                 MAlonzo.Code.Algebra.Structures.du_isRingWithoutOne_2702
                 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2322
                    (coe v2) in
          coe
            (coe
               MAlonzo.Code.Algebra.Structures.du_inverse'691'_1106
               (coe MAlonzo.Code.Algebra.Structures.d_isGroup_1142 (coe v3)))))
-- Algebra.Apartness.Structures._.IsCommutativeRing.inverseˡ
d_inverse'737'_112 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2816 ->
  AgdaAny -> AgdaAny
d_inverse'737'_112 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
                   ~v11 ~v12 ~v13 ~v14 ~v15 v16
  = du_inverse'737'_112 v16
du_inverse'737'_112 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2816 ->
  AgdaAny -> AgdaAny
du_inverse'737'_112 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v0) in
    coe
      (let v2
             = coe
                 MAlonzo.Code.Algebra.Structures.du_isRingWithoutOne_2702
                 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2322
                    (coe v2) in
          coe
            (coe
               MAlonzo.Code.Algebra.Structures.du_inverse'737'_1104
               (coe MAlonzo.Code.Algebra.Structures.d_isGroup_1142 (coe v3)))))
-- Algebra.Apartness.Structures._.IsCommutativeRing.distribʳ
d_distrib'691'_116 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2816 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_distrib'691'_116 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
                   ~v11 ~v12 ~v13 ~v14 ~v15 v16
  = du_distrib'691'_116 v16
du_distrib'691'_116 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2816 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_distrib'691'_116 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.du_distrib'691'_2398
         (coe
            MAlonzo.Code.Algebra.Structures.du_isRingWithoutOne_2702 (coe v1)))
-- Algebra.Apartness.Structures._.IsCommutativeRing.distribˡ
d_distrib'737'_118 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2816 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_distrib'737'_118 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
                   ~v11 ~v12 ~v13 ~v14 ~v15 v16
  = du_distrib'737'_118 v16
du_distrib'737'_118 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2816 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_distrib'737'_118 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.du_distrib'737'_2396
         (coe
            MAlonzo.Code.Algebra.Structures.du_isRingWithoutOne_2702 (coe v1)))
-- Algebra.Apartness.Structures._.IsCommutativeRing.isCommutativeSemiring
d_isCommutativeSemiring_120 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2816 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1696
d_isCommutativeSemiring_120 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                            ~v10
  = du_isCommutativeSemiring_120
du_isCommutativeSemiring_120 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2816 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1696
du_isCommutativeSemiring_120 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Algebra.Structures.du_isCommutativeSemiring_2946 v0 v1
      v2 v3 v5
-- Algebra.Apartness.Structures._.IsCommutativeRing.isCommutativeSemiringWithoutOne
d_isCommutativeSemiringWithoutOne_122 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2816 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiringWithoutOne_1390
d_isCommutativeSemiringWithoutOne_122 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6
                                      ~v7 ~v8 ~v9 ~v10 v11 v12 v13 v14 ~v15 v16
  = du_isCommutativeSemiringWithoutOne_122 v11 v12 v13 v14 v16
du_isCommutativeSemiringWithoutOne_122 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2816 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiringWithoutOne_1390
du_isCommutativeSemiringWithoutOne_122 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Algebra.Structures.du_isCommutativeSemiringWithoutOne_1798
      (coe
         MAlonzo.Code.Algebra.Structures.du_isCommutativeSemiring_2946
         (coe v0) (coe v1) (coe v2) (coe v3) (coe v4))
-- Algebra.Apartness.Structures._.IsCommutativeRing.isEquivalence
d_isEquivalence_124 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2816 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_124 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
                    ~v11 ~v12 ~v13 ~v14 ~v15 v16
  = du_isEquivalence_124 v16
du_isEquivalence_124 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2816 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
du_isEquivalence_124 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
         (coe
            MAlonzo.Code.Algebra.Structures.d_isMagma_478
            (coe
               MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isMonoid_1048
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_isGroup_1142
                     (coe
                        MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2692
                        (coe v1)))))))
-- Algebra.Apartness.Structures._.IsCommutativeRing.isNearSemiring
d_isNearSemiring_126 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2816 ->
  MAlonzo.Code.Algebra.Structures.T_IsNearSemiring_1216
d_isNearSemiring_126 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
                     v11 v12 v13 v14 ~v15 v16
  = du_isNearSemiring_126 v11 v12 v13 v14 v16
du_isNearSemiring_126 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2816 ->
  MAlonzo.Code.Algebra.Structures.T_IsNearSemiring_1216
du_isNearSemiring_126 v0 v1 v2 v3 v4
  = let v5
          = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v4) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.du_isNearSemiring_2406 (coe v0)
         (coe v1) (coe v2) (coe v3)
         (coe
            MAlonzo.Code.Algebra.Structures.du_isRingWithoutOne_2702 (coe v5)))
-- Algebra.Apartness.Structures._.IsCommutativeRing.isPartialEquivalence
d_isPartialEquivalence_128 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2816 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_128 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                           ~v10 ~v11 ~v12 ~v13 ~v14 ~v15 v16
  = du_isPartialEquivalence_128 v16
du_isPartialEquivalence_128 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2816 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_128 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v0) in
    coe
      (let v2
             = coe
                 MAlonzo.Code.Algebra.Structures.du_isRingWithoutOne_2702
                 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2322
                    (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Algebra.Structures.d_isGroup_1142 (coe v3) in
             coe
               (let v5
                      = MAlonzo.Code.Algebra.Structures.d_isMonoid_1048 (coe v4) in
                coe
                  (let v6
                         = MAlonzo.Code.Algebra.Structures.d_isSemigroup_694 (coe v5) in
                   coe
                     (let v7 = MAlonzo.Code.Algebra.Structures.d_isMagma_478 (coe v6) in
                      coe
                        (coe
                           MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_42
                           (coe
                              MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
                              (coe v7)))))))))
-- Algebra.Apartness.Structures._.IsCommutativeRing.isRing
d_isRing_130 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2816 ->
  MAlonzo.Code.Algebra.Structures.T_IsRing_2670
d_isRing_130 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v0)
-- Algebra.Apartness.Structures._.IsCommutativeRing.isRingWithoutOne
d_isRingWithoutOne_132 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2816 ->
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2304
d_isRingWithoutOne_132 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
                       ~v11 ~v12 ~v13 ~v14 ~v15 v16
  = du_isRingWithoutOne_132 v16
du_isRingWithoutOne_132 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2816 ->
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2304
du_isRingWithoutOne_132 v0
  = coe
      MAlonzo.Code.Algebra.Structures.du_isRingWithoutOne_2702
      (coe MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v0))
-- Algebra.Apartness.Structures._.IsCommutativeRing.isSemiring
d_isSemiring_134 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2816 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1588
d_isSemiring_134 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 v11
                 v12 v13 v14 ~v15 v16
  = du_isSemiring_134 v11 v12 v13 v14 v16
du_isSemiring_134 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2816 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1588
du_isSemiring_134 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Algebra.Structures.du_isSemiring_2800 (coe v0)
      (coe v1) (coe v2) (coe v3)
      (coe MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v4))
-- Algebra.Apartness.Structures._.IsCommutativeRing.isSemiringWithoutAnnihilatingZero
d_isSemiringWithoutAnnihilatingZero_136 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2816 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1486
d_isSemiringWithoutAnnihilatingZero_136 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6
                                        ~v7 ~v8 ~v9 ~v10 ~v11 ~v12 ~v13 ~v14 ~v15 v16
  = du_isSemiringWithoutAnnihilatingZero_136 v16
du_isSemiringWithoutAnnihilatingZero_136 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2816 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1486
du_isSemiringWithoutAnnihilatingZero_136 v0
  = coe
      MAlonzo.Code.Algebra.Structures.du_isSemiringWithoutAnnihilatingZero_2798
      (coe MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v0))
-- Algebra.Apartness.Structures._.IsCommutativeRing.isSemiringWithoutOne
d_isSemiringWithoutOne_138 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2816 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutOne_1296
d_isSemiringWithoutOne_138 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                           ~v10 v11 v12 v13 v14 ~v15 v16
  = du_isSemiringWithoutOne_138 v11 v12 v13 v14 v16
du_isSemiringWithoutOne_138 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2816 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutOne_1296
du_isSemiringWithoutOne_138 v0 v1 v2 v3 v4
  = let v5
          = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v4) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.du_isSemiringWithoutOne_1678
         (coe
            MAlonzo.Code.Algebra.Structures.du_isSemiring_2800 (coe v0)
            (coe v1) (coe v2) (coe v3) (coe v5)))
-- Algebra.Apartness.Structures._.IsCommutativeRing.refl
d_refl_140 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2816 ->
  AgdaAny -> AgdaAny
d_refl_140 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12
           ~v13 ~v14 ~v15 v16
  = du_refl_140 v16
du_refl_140 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2816 ->
  AgdaAny -> AgdaAny
du_refl_140 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_refl_34
         (coe
            MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
            (coe
               MAlonzo.Code.Algebra.Structures.d_isMagma_478
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_isMonoid_1048
                     (coe
                        MAlonzo.Code.Algebra.Structures.d_isGroup_1142
                        (coe
                           MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2692
                           (coe v1))))))))
-- Algebra.Apartness.Structures._.IsCommutativeRing.reflexive
d_reflexive_142 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2816 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_142 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11
                ~v12 ~v13 ~v14 ~v15 v16
  = du_reflexive_142 v16
du_reflexive_142 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2816 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_142 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v0) in
    coe
      (let v2
             = coe
                 MAlonzo.Code.Algebra.Structures.du_isRingWithoutOne_2702
                 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2322
                    (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Algebra.Structures.d_isGroup_1142 (coe v3) in
             coe
               (let v5
                      = MAlonzo.Code.Algebra.Structures.d_isMonoid_1048 (coe v4) in
                coe
                  (let v6
                         = MAlonzo.Code.Algebra.Structures.d_isSemigroup_694 (coe v5) in
                   coe
                     (let v7 = MAlonzo.Code.Algebra.Structures.d_isMagma_478 (coe v6) in
                      coe
                        (\ v8 v9 v10 ->
                           coe
                             MAlonzo.Code.Relation.Binary.Structures.du_reflexive_40
                             (coe MAlonzo.Code.Algebra.Structures.d_isEquivalence_184 (coe v7))
                             v8)))))))
-- Algebra.Apartness.Structures._.IsCommutativeRing.setoid
d_setoid_144 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2816 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
d_setoid_144 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12
             ~v13 ~v14 ~v15 v16
  = du_setoid_144 v16
du_setoid_144 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2816 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
du_setoid_144 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v0) in
    coe
      (let v2
             = coe
                 MAlonzo.Code.Algebra.Structures.du_isRingWithoutOne_2702
                 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2322
                    (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Algebra.Structures.d_isGroup_1142 (coe v3) in
             coe
               (let v5
                      = MAlonzo.Code.Algebra.Structures.d_isMonoid_1048 (coe v4) in
                coe
                  (let v6
                         = MAlonzo.Code.Algebra.Structures.d_isSemigroup_694 (coe v5) in
                   coe
                     (coe
                        MAlonzo.Code.Algebra.Structures.du_setoid_200
                        (coe MAlonzo.Code.Algebra.Structures.d_isMagma_478 (coe v6))))))))
-- Algebra.Apartness.Structures._.IsCommutativeRing.sym
d_sym_146 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2816 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_146 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12
          ~v13 ~v14 ~v15 v16
  = du_sym_146 v16
du_sym_146 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2816 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_sym_146 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_sym_36
         (coe
            MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
            (coe
               MAlonzo.Code.Algebra.Structures.d_isMagma_478
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_isMonoid_1048
                     (coe
                        MAlonzo.Code.Algebra.Structures.d_isGroup_1142
                        (coe
                           MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2692
                           (coe v1))))))))
-- Algebra.Apartness.Structures._.IsCommutativeRing.trans
d_trans_148 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2816 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_148 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 ~v12
            ~v13 ~v14 ~v15 v16
  = du_trans_148 v16
du_trans_148 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2816 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_trans_148 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_trans_38
         (coe
            MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
            (coe
               MAlonzo.Code.Algebra.Structures.d_isMagma_478
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_isMonoid_1048
                     (coe
                        MAlonzo.Code.Algebra.Structures.d_isGroup_1142
                        (coe
                           MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2692
                           (coe v1))))))))
-- Algebra.Apartness.Structures._.IsCommutativeRing.uniqueʳ-⁻¹
d_unique'691''45''8315''185'_150 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2816 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_unique'691''45''8315''185'_150 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
                                 ~v8 ~v9 ~v10 v11 ~v12 v13 v14 ~v15 v16
  = du_unique'691''45''8315''185'_150 v11 v13 v14 v16
du_unique'691''45''8315''185'_150 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2816 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_unique'691''45''8315''185'_150 v0 v1 v2 v3
  = let v4
          = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v3) in
    coe
      (let v5
             = coe
                 MAlonzo.Code.Algebra.Structures.du_isRingWithoutOne_2702
                 (coe v4) in
       coe
         (let v6
                = MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2322
                    (coe v5) in
          coe
            (coe
               MAlonzo.Code.Algebra.Structures.du_unique'691''45''8315''185'_1118
               (coe v0) (coe v2) (coe v1)
               (coe MAlonzo.Code.Algebra.Structures.d_isGroup_1142 (coe v6)))))
-- Algebra.Apartness.Structures._.IsCommutativeRing.uniqueˡ-⁻¹
d_unique'737''45''8315''185'_152 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2816 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_unique'737''45''8315''185'_152 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
                                 ~v8 ~v9 ~v10 v11 ~v12 v13 v14 ~v15 v16
  = du_unique'737''45''8315''185'_152 v11 v13 v14 v16
du_unique'737''45''8315''185'_152 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2816 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_unique'737''45''8315''185'_152 v0 v1 v2 v3
  = let v4
          = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v3) in
    coe
      (let v5
             = coe
                 MAlonzo.Code.Algebra.Structures.du_isRingWithoutOne_2702
                 (coe v4) in
       coe
         (let v6
                = MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2322
                    (coe v5) in
          coe
            (coe
               MAlonzo.Code.Algebra.Structures.du_unique'737''45''8315''185'_1112
               (coe v0) (coe v2) (coe v1)
               (coe MAlonzo.Code.Algebra.Structures.d_isGroup_1142 (coe v6)))))
-- Algebra.Apartness.Structures._.IsCommutativeRing.zero
d_zero_154 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2816 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_zero_154 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 v11 v12 v13
           v14 ~v15 v16
  = du_zero_154 v11 v12 v13 v14 v16
du_zero_154 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2816 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_zero_154 v0 v1 v2 v3 v4
  = let v5
          = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v4) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.du_zero_2404 (coe v0) (coe v1)
         (coe v2) (coe v3)
         (coe
            MAlonzo.Code.Algebra.Structures.du_isRingWithoutOne_2702 (coe v5)))
-- Algebra.Apartness.Structures._.IsCommutativeRing.zeroʳ
d_zero'691'_156 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2816 ->
  AgdaAny -> AgdaAny
d_zero'691'_156 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 v11
                v12 v13 v14 ~v15 v16
  = du_zero'691'_156 v11 v12 v13 v14 v16
du_zero'691'_156 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2816 ->
  AgdaAny -> AgdaAny
du_zero'691'_156 v0 v1 v2 v3 v4
  = let v5
          = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v4) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.du_zero'691'_2402 (coe v0) (coe v1)
         (coe v2) (coe v3)
         (coe
            MAlonzo.Code.Algebra.Structures.du_isRingWithoutOne_2702 (coe v5)))
-- Algebra.Apartness.Structures._.IsCommutativeRing.zeroˡ
d_zero'737'_158 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2816 ->
  AgdaAny -> AgdaAny
d_zero'737'_158 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 v11
                v12 v13 v14 ~v15 v16
  = du_zero'737'_158 v11 v12 v13 v14 v16
du_zero'737'_158 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2816 ->
  AgdaAny -> AgdaAny
du_zero'737'_158 v0 v1 v2 v3 v4
  = let v5
          = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v4) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.du_zero'737'_2400 (coe v0) (coe v1)
         (coe v2) (coe v3)
         (coe
            MAlonzo.Code.Algebra.Structures.du_isRingWithoutOne_2702 (coe v5)))
-- Algebra.Apartness.Structures.IsHeytingCommutativeRing
d_IsHeytingCommutativeRing_160 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10
  = ()
data T_IsHeytingCommutativeRing_160
  = C_IsHeytingCommutativeRing'46'constructor_4849 MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2816
                                                   MAlonzo.Code.Relation.Binary.Structures.T_IsApartnessRelation_722
                                                   (AgdaAny ->
                                                    AgdaAny ->
                                                    AgdaAny ->
                                                    MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14)
                                                   (AgdaAny ->
                                                    AgdaAny ->
                                                    MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
                                                    AgdaAny)
-- Algebra.Apartness.Structures._._//_
d__'47''47'__168 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2816 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsApartnessRelation_722 ->
  AgdaAny -> AgdaAny -> AgdaAny
d__'47''47'__168 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 ~v7 v8 ~v9 ~v10 ~v11
                 ~v12
  = du__'47''47'__168 v6 v8
du__'47''47'__168 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny -> AgdaAny
du__'47''47'__168 v0 v1
  = coe
      MAlonzo.Code.Algebra.Structures.du__'47''47'__1096 (coe v0)
      (coe v1)
-- Algebra.Apartness.Structures._.∙-congʳ
d_'8729''45'cong'691'_176 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2816 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsApartnessRelation_722 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'691'_176 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 v8 v9 ~v10
                          v11 ~v12
  = du_'8729''45'cong'691'_176 v6 v7 v8 v9 v11
du_'8729''45'cong'691'_176 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2816 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'691'_176 v0 v1 v2 v3 v4
  = let v5
          = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v4) in
    coe
      (let v6
             = coe
                 MAlonzo.Code.Algebra.Structures.du_isRingWithoutOne_2702
                 (coe v5) in
       coe
         (let v7
                = coe
                    MAlonzo.Code.Algebra.Structures.du_isNearSemiring_2406 (coe v0)
                    (coe v1) (coe v2) (coe v3) (coe v6) in
          coe
            (let v8
                   = coe
                       MAlonzo.Code.Algebra.Structures.du_'42''45'isMagma_1280 (coe v7) in
             coe
               (let v9
                      = coe MAlonzo.Code.Algebra.Structures.du_setoid_200 (coe v8) in
                coe
                  (let v10
                         = MAlonzo.Code.Algebra.Structures.d_'8729''45'cong_186 (coe v8) in
                   coe
                     (coe
                        MAlonzo.Code.Algebra.Consequences.Base.du_'8729''45'cong'691'_46
                        (coe v10)
                        (coe
                           MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                           (coe
                              MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                              (coe v9)))))))))
-- Algebra.Apartness.Structures._.∙-congˡ
d_'8729''45'cong'737'_178 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2816 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsApartnessRelation_722 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'737'_178 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 v8 v9 ~v10
                          v11 ~v12
  = du_'8729''45'cong'737'_178 v6 v7 v8 v9 v11
du_'8729''45'cong'737'_178 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2816 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'737'_178 v0 v1 v2 v3 v4
  = let v5
          = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v4) in
    coe
      (let v6
             = coe
                 MAlonzo.Code.Algebra.Structures.du_isRingWithoutOne_2702
                 (coe v5) in
       coe
         (let v7
                = coe
                    MAlonzo.Code.Algebra.Structures.du_isNearSemiring_2406 (coe v0)
                    (coe v1) (coe v2) (coe v3) (coe v6) in
          coe
            (let v8
                   = coe
                       MAlonzo.Code.Algebra.Structures.du_'42''45'isMagma_1280 (coe v7) in
             coe
               (let v9
                      = coe MAlonzo.Code.Algebra.Structures.du_setoid_200 (coe v8) in
                coe
                  (let v10
                         = MAlonzo.Code.Algebra.Structures.d_'8729''45'cong_186 (coe v8) in
                   coe
                     (coe
                        MAlonzo.Code.Algebra.Consequences.Base.du_'8729''45'cong'737'_42
                        (coe v10)
                        (coe
                           MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                           (coe
                              MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                              (coe v9)))))))))
-- Algebra.Apartness.Structures._.identityʳ
d_identity'691'_182 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2816 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsApartnessRelation_722 ->
  AgdaAny -> AgdaAny
d_identity'691'_182 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 v8 v9 ~v10 v11
                    ~v12
  = du_identity'691'_182 v6 v7 v8 v9 v11
du_identity'691'_182 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2816 ->
  AgdaAny -> AgdaAny
du_identity'691'_182 v0 v1 v2 v3 v4
  = let v5
          = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v4) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.du_identity'691'_726
         (coe
            MAlonzo.Code.Algebra.Structures.du_'42''45'isMonoid_2790 (coe v0)
            (coe v1) (coe v2) (coe v3) (coe v5)))
-- Algebra.Apartness.Structures._.identityˡ
d_identity'737'_184 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2816 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsApartnessRelation_722 ->
  AgdaAny -> AgdaAny
d_identity'737'_184 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 v8 v9 ~v10 v11
                    ~v12
  = du_identity'737'_184 v6 v7 v8 v9 v11
du_identity'737'_184 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2816 ->
  AgdaAny -> AgdaAny
du_identity'737'_184 v0 v1 v2 v3 v4
  = let v5
          = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v4) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.du_identity'737'_724
         (coe
            MAlonzo.Code.Algebra.Structures.du_'42''45'isMonoid_2790 (coe v0)
            (coe v1) (coe v2) (coe v3) (coe v5)))
-- Algebra.Apartness.Structures._.isCommutativeMagma
d_isCommutativeMagma_186 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2816 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsApartnessRelation_722 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMagma_210
d_isCommutativeMagma_186 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 v8 v9 ~v10
                         v11 ~v12
  = du_isCommutativeMagma_186 v6 v7 v8 v9 v11
du_isCommutativeMagma_186 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2816 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMagma_210
du_isCommutativeMagma_186 v0 v1 v2 v3 v4
  = let v5
          = coe
              MAlonzo.Code.Algebra.Structures.du_isCommutativeSemiring_2946
              (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) in
    coe
      (let v6
             = coe
                 MAlonzo.Code.Algebra.Structures.du_isCommutativeSemiringWithoutOne_1798
                 (coe v5) in
       coe
         (coe
            MAlonzo.Code.Algebra.Structures.du_isCommutativeMagma_584
            (coe
               MAlonzo.Code.Algebra.Structures.du_'42''45'isCommutativeSemigroup_1472
               (coe v6))))
-- Algebra.Apartness.Structures._.*-isCommutativeMonoid
d_'42''45'isCommutativeMonoid_188 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2816 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsApartnessRelation_722 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_734
d_'42''45'isCommutativeMonoid_188 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 v8
                                  v9 ~v10 v11 ~v12
  = du_'42''45'isCommutativeMonoid_188 v6 v7 v8 v9 v11
du_'42''45'isCommutativeMonoid_188 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2816 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_734
du_'42''45'isCommutativeMonoid_188 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Algebra.Structures.du_'42''45'isCommutativeMonoid_1806
      (coe
         MAlonzo.Code.Algebra.Structures.du_isCommutativeSemiring_2946
         (coe v0) (coe v1) (coe v2) (coe v3) (coe v4))
-- Algebra.Apartness.Structures._.*-isCommutativeSemigroup
d_'42''45'isCommutativeSemigroup_190 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2816 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsApartnessRelation_722 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_546
d_'42''45'isCommutativeSemigroup_190 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7
                                     v8 v9 ~v10 v11 ~v12
  = du_'42''45'isCommutativeSemigroup_190 v6 v7 v8 v9 v11
du_'42''45'isCommutativeSemigroup_190 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2816 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_546
du_'42''45'isCommutativeSemigroup_190 v0 v1 v2 v3 v4
  = let v5
          = coe
              MAlonzo.Code.Algebra.Structures.du_isCommutativeSemiring_2946
              (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.du_'42''45'isCommutativeSemigroup_1472
         (coe
            MAlonzo.Code.Algebra.Structures.du_isCommutativeSemiringWithoutOne_1798
            (coe v5)))
-- Algebra.Apartness.Structures._.*-isMagma
d_'42''45'isMagma_192 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2816 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsApartnessRelation_722 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176
d_'42''45'isMagma_192 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 v8 v9 ~v10 v11
                      ~v12
  = du_'42''45'isMagma_192 v6 v7 v8 v9 v11
du_'42''45'isMagma_192 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2816 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176
du_'42''45'isMagma_192 v0 v1 v2 v3 v4
  = let v5
          = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v4) in
    coe
      (let v6
             = coe
                 MAlonzo.Code.Algebra.Structures.du_isRingWithoutOne_2702
                 (coe v5) in
       coe
         (coe
            MAlonzo.Code.Algebra.Structures.du_'42''45'isMagma_1280
            (coe
               MAlonzo.Code.Algebra.Structures.du_isNearSemiring_2406 (coe v0)
               (coe v1) (coe v2) (coe v3) (coe v6))))
-- Algebra.Apartness.Structures._.*-isMonoid
d_'42''45'isMonoid_194 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2816 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsApartnessRelation_722 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_684
d_'42''45'isMonoid_194 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 v8 v9 ~v10 v11
                       ~v12
  = du_'42''45'isMonoid_194 v6 v7 v8 v9 v11
du_'42''45'isMonoid_194 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2816 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_684
du_'42''45'isMonoid_194 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Algebra.Structures.du_'42''45'isMonoid_2790 (coe v0)
      (coe v1) (coe v2) (coe v3)
      (coe MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v4))
-- Algebra.Apartness.Structures._.*-isSemigroup
d_'42''45'isSemigroup_196 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2816 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsApartnessRelation_722 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_470
d_'42''45'isSemigroup_196 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 v8 v9 ~v10
                          v11 ~v12
  = du_'42''45'isSemigroup_196 v6 v7 v8 v9 v11
du_'42''45'isSemigroup_196 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2816 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_470
du_'42''45'isSemigroup_196 v0 v1 v2 v3 v4
  = let v5
          = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v4) in
    coe
      (let v6
             = coe
                 MAlonzo.Code.Algebra.Structures.du_isRingWithoutOne_2702
                 (coe v5) in
       coe
         (coe
            MAlonzo.Code.Algebra.Structures.du_'42''45'isSemigroup_1282
            (coe
               MAlonzo.Code.Algebra.Structures.du_isNearSemiring_2406 (coe v0)
               (coe v1) (coe v2) (coe v3) (coe v6))))
-- Algebra.Apartness.Structures._.assoc
d_assoc_198 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2816 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsApartnessRelation_722 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_assoc_198 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 v11 ~v12
  = du_assoc_198 v11
du_assoc_198 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2816 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_assoc_198 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.d_assoc_480
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
            (coe
               MAlonzo.Code.Algebra.Structures.d_isMonoid_1048
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isGroup_1142
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2692
                     (coe v1))))))
-- Algebra.Apartness.Structures._.comm
d_comm_200 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2816 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsApartnessRelation_722 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_comm_200 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 v11 ~v12
  = du_comm_200 v11
du_comm_200 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2816 ->
  AgdaAny -> AgdaAny -> AgdaAny
du_comm_200 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.d_comm_1144
         (coe
            MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2692
            (coe v1)))
-- Algebra.Apartness.Structures._.∙-cong
d_'8729''45'cong_202 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2816 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsApartnessRelation_722 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong_202 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
                     v11 ~v12
  = du_'8729''45'cong_202 v11
du_'8729''45'cong_202 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2816 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong_202 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.d_'8729''45'cong_186
         (coe
            MAlonzo.Code.Algebra.Structures.d_isMagma_478
            (coe
               MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isMonoid_1048
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_isGroup_1142
                     (coe
                        MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2692
                        (coe v1)))))))
-- Algebra.Apartness.Structures._.∙-congʳ
d_'8729''45'cong'691'_204 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2816 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsApartnessRelation_722 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'691'_204 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                          ~v10 v11 ~v12
  = du_'8729''45'cong'691'_204 v11
du_'8729''45'cong'691'_204 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2816 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'691'_204 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v0) in
    coe
      (let v2
             = coe
                 MAlonzo.Code.Algebra.Structures.du_isRingWithoutOne_2702
                 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2322
                    (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Algebra.Structures.d_isGroup_1142 (coe v3) in
             coe
               (let v5
                      = MAlonzo.Code.Algebra.Structures.d_isMonoid_1048 (coe v4) in
                coe
                  (let v6
                         = MAlonzo.Code.Algebra.Structures.d_isSemigroup_694 (coe v5) in
                   coe
                     (let v7 = MAlonzo.Code.Algebra.Structures.d_isMagma_478 (coe v6) in
                      coe
                        (let v8
                               = coe MAlonzo.Code.Algebra.Structures.du_setoid_200 (coe v7) in
                         coe
                           (let v9
                                  = MAlonzo.Code.Algebra.Structures.d_'8729''45'cong_186 (coe v7) in
                            coe
                              (coe
                                 MAlonzo.Code.Algebra.Consequences.Base.du_'8729''45'cong'691'_46
                                 (coe v9)
                                 (coe
                                    MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                                    (coe
                                       MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                                       (coe v8))))))))))))
-- Algebra.Apartness.Structures._.∙-congˡ
d_'8729''45'cong'737'_206 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2816 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsApartnessRelation_722 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'737'_206 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                          ~v10 v11 ~v12
  = du_'8729''45'cong'737'_206 v11
du_'8729''45'cong'737'_206 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2816 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'737'_206 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v0) in
    coe
      (let v2
             = coe
                 MAlonzo.Code.Algebra.Structures.du_isRingWithoutOne_2702
                 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2322
                    (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Algebra.Structures.d_isGroup_1142 (coe v3) in
             coe
               (let v5
                      = MAlonzo.Code.Algebra.Structures.d_isMonoid_1048 (coe v4) in
                coe
                  (let v6
                         = MAlonzo.Code.Algebra.Structures.d_isSemigroup_694 (coe v5) in
                   coe
                     (let v7 = MAlonzo.Code.Algebra.Structures.d_isMagma_478 (coe v6) in
                      coe
                        (let v8
                               = coe MAlonzo.Code.Algebra.Structures.du_setoid_200 (coe v7) in
                         coe
                           (let v9
                                  = MAlonzo.Code.Algebra.Structures.d_'8729''45'cong_186 (coe v7) in
                            coe
                              (coe
                                 MAlonzo.Code.Algebra.Consequences.Base.du_'8729''45'cong'737'_42
                                 (coe v9)
                                 (coe
                                    MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                                    (coe
                                       MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                                       (coe v8))))))))))))
-- Algebra.Apartness.Structures._.identity
d_identity_208 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2816 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsApartnessRelation_722 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_208 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 v11
               ~v12
  = du_identity_208 v11
du_identity_208 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2816 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_identity_208 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.d_identity_696
         (coe
            MAlonzo.Code.Algebra.Structures.d_isMonoid_1048
            (coe
               MAlonzo.Code.Algebra.Structures.d_isGroup_1142
               (coe
                  MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2692
                  (coe v1)))))
-- Algebra.Apartness.Structures._.identityʳ
d_identity'691'_210 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2816 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsApartnessRelation_722 ->
  AgdaAny -> AgdaAny
d_identity'691'_210 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
                    v11 ~v12
  = du_identity'691'_210 v11
du_identity'691'_210 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2816 ->
  AgdaAny -> AgdaAny
du_identity'691'_210 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v0) in
    coe
      (let v2
             = coe
                 MAlonzo.Code.Algebra.Structures.du_isRingWithoutOne_2702
                 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2322
                    (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Algebra.Structures.d_isGroup_1142 (coe v3) in
             coe
               (coe
                  MAlonzo.Code.Algebra.Structures.du_identity'691'_726
                  (coe MAlonzo.Code.Algebra.Structures.d_isMonoid_1048 (coe v4))))))
-- Algebra.Apartness.Structures._.identityˡ
d_identity'737'_212 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2816 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsApartnessRelation_722 ->
  AgdaAny -> AgdaAny
d_identity'737'_212 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
                    v11 ~v12
  = du_identity'737'_212 v11
du_identity'737'_212 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2816 ->
  AgdaAny -> AgdaAny
du_identity'737'_212 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v0) in
    coe
      (let v2
             = coe
                 MAlonzo.Code.Algebra.Structures.du_isRingWithoutOne_2702
                 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2322
                    (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Algebra.Structures.d_isGroup_1142 (coe v3) in
             coe
               (coe
                  MAlonzo.Code.Algebra.Structures.du_identity'737'_724
                  (coe MAlonzo.Code.Algebra.Structures.d_isMonoid_1048 (coe v4))))))
-- Algebra.Apartness.Structures._.isCommutativeMagma
d_isCommutativeMagma_216 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2816 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsApartnessRelation_722 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMagma_210
d_isCommutativeMagma_216 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                         ~v10 v11 ~v12
  = du_isCommutativeMagma_216 v11
du_isCommutativeMagma_216 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2816 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMagma_210
du_isCommutativeMagma_216 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v0) in
    coe
      (let v2
             = coe
                 MAlonzo.Code.Algebra.Structures.du_isRingWithoutOne_2702
                 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2322
                    (coe v2) in
          coe
            (let v4
                   = coe
                       MAlonzo.Code.Algebra.Structures.du_isCommutativeMonoid_1202
                       (coe v3) in
             coe
               (coe
                  MAlonzo.Code.Algebra.Structures.du_isCommutativeMagma_584
                  (coe
                     MAlonzo.Code.Algebra.Structures.du_isCommutativeSemigroup_784
                     (coe v4))))))
-- Algebra.Apartness.Structures._.isCommutativeMonoid
d_isCommutativeMonoid_218 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2816 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsApartnessRelation_722 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_734
d_isCommutativeMonoid_218 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                          ~v10 v11 ~v12
  = du_isCommutativeMonoid_218 v11
du_isCommutativeMonoid_218 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2816 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_734
du_isCommutativeMonoid_218 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v0) in
    coe
      (let v2
             = coe
                 MAlonzo.Code.Algebra.Structures.du_isRingWithoutOne_2702
                 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Algebra.Structures.du_isCommutativeMonoid_1202
            (coe
               MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2322
               (coe v2))))
-- Algebra.Apartness.Structures._.isCommutativeSemigroup
d_isCommutativeSemigroup_220 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2816 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsApartnessRelation_722 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_546
d_isCommutativeSemigroup_220 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8
                             ~v9 ~v10 v11 ~v12
  = du_isCommutativeSemigroup_220 v11
du_isCommutativeSemigroup_220 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2816 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_546
du_isCommutativeSemigroup_220 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v0) in
    coe
      (let v2
             = coe
                 MAlonzo.Code.Algebra.Structures.du_isRingWithoutOne_2702
                 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2322
                    (coe v2) in
          coe
            (coe
               MAlonzo.Code.Algebra.Structures.du_isCommutativeSemigroup_784
               (coe
                  MAlonzo.Code.Algebra.Structures.du_isCommutativeMonoid_1202
                  (coe v3)))))
-- Algebra.Apartness.Structures._.isGroup
d_isGroup_222 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2816 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsApartnessRelation_722 ->
  MAlonzo.Code.Algebra.Structures.T_IsGroup_1034
d_isGroup_222 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 v11 ~v12
  = du_isGroup_222 v11
du_isGroup_222 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2816 ->
  MAlonzo.Code.Algebra.Structures.T_IsGroup_1034
du_isGroup_222 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.d_isGroup_1142
         (coe
            MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2692
            (coe v1)))
-- Algebra.Apartness.Structures._.isInvertibleMagma
d_isInvertibleMagma_224 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2816 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsApartnessRelation_722 ->
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleMagma_922
d_isInvertibleMagma_224 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                        ~v10 v11 ~v12
  = du_isInvertibleMagma_224 v11
du_isInvertibleMagma_224 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2816 ->
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleMagma_922
du_isInvertibleMagma_224 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v0) in
    coe
      (let v2
             = coe
                 MAlonzo.Code.Algebra.Structures.du_isRingWithoutOne_2702
                 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2322
                    (coe v2) in
          coe
            (coe
               MAlonzo.Code.Algebra.Structures.du_isInvertibleMagma_1120
               (coe MAlonzo.Code.Algebra.Structures.d_isGroup_1142 (coe v3)))))
-- Algebra.Apartness.Structures._.isInvertibleUnitalMagma
d_isInvertibleUnitalMagma_226 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2816 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsApartnessRelation_722 ->
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleUnitalMagma_974
d_isInvertibleUnitalMagma_226 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8
                              ~v9 ~v10 v11 ~v12
  = du_isInvertibleUnitalMagma_226 v11
du_isInvertibleUnitalMagma_226 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2816 ->
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleUnitalMagma_974
du_isInvertibleUnitalMagma_226 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v0) in
    coe
      (let v2
             = coe
                 MAlonzo.Code.Algebra.Structures.du_isRingWithoutOne_2702
                 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2322
                    (coe v2) in
          coe
            (coe
               MAlonzo.Code.Algebra.Structures.du_isInvertibleUnitalMagma_1122
               (coe MAlonzo.Code.Algebra.Structures.d_isGroup_1142 (coe v3)))))
-- Algebra.Apartness.Structures._.isMagma
d_isMagma_228 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2816 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsApartnessRelation_722 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176
d_isMagma_228 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 v11 ~v12
  = du_isMagma_228 v11
du_isMagma_228 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2816 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176
du_isMagma_228 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMagma_478
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
            (coe
               MAlonzo.Code.Algebra.Structures.d_isMonoid_1048
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isGroup_1142
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2692
                     (coe v1))))))
-- Algebra.Apartness.Structures._.isMonoid
d_isMonoid_230 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2816 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsApartnessRelation_722 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_684
d_isMonoid_230 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 v11
               ~v12
  = du_isMonoid_230 v11
du_isMonoid_230 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2816 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_684
du_isMonoid_230 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.d_isMonoid_1048
         (coe
            MAlonzo.Code.Algebra.Structures.d_isGroup_1142
            (coe
               MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2692
               (coe v1))))
-- Algebra.Apartness.Structures._.isSemigroup
d_isSemigroup_232 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2816 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsApartnessRelation_722 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_470
d_isSemigroup_232 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 v11
                  ~v12
  = du_isSemigroup_232 v11
du_isSemigroup_232 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2816 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_470
du_isSemigroup_232 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
         (coe
            MAlonzo.Code.Algebra.Structures.d_isMonoid_1048
            (coe
               MAlonzo.Code.Algebra.Structures.d_isGroup_1142
               (coe
                  MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2692
                  (coe v1)))))
-- Algebra.Apartness.Structures._.isUnitalMagma
d_isUnitalMagma_234 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2816 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsApartnessRelation_722 ->
  MAlonzo.Code.Algebra.Structures.T_IsUnitalMagma_640
d_isUnitalMagma_234 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
                    v11 ~v12
  = du_isUnitalMagma_234 v11
du_isUnitalMagma_234 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2816 ->
  MAlonzo.Code.Algebra.Structures.T_IsUnitalMagma_640
du_isUnitalMagma_234 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v0) in
    coe
      (let v2
             = coe
                 MAlonzo.Code.Algebra.Structures.du_isRingWithoutOne_2702
                 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2322
                    (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Algebra.Structures.d_isGroup_1142 (coe v3) in
             coe
               (coe
                  MAlonzo.Code.Algebra.Structures.du_isUnitalMagma_728
                  (coe MAlonzo.Code.Algebra.Structures.d_isMonoid_1048 (coe v4))))))
-- Algebra.Apartness.Structures._.⁻¹-cong
d_'8315''185''45'cong_236 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2816 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsApartnessRelation_722 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8315''185''45'cong_236 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                          ~v10 v11 ~v12
  = du_'8315''185''45'cong_236 v11
du_'8315''185''45'cong_236 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2816 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8315''185''45'cong_236 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.d_'8315''185''45'cong_1052
         (coe
            MAlonzo.Code.Algebra.Structures.d_isGroup_1142
            (coe
               MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2692
               (coe v1))))
-- Algebra.Apartness.Structures._.inverse
d_inverse_238 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2816 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsApartnessRelation_722 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inverse_238 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 v11 ~v12
  = du_inverse_238 v11
du_inverse_238 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2816 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_inverse_238 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.d_inverse_1050
         (coe
            MAlonzo.Code.Algebra.Structures.d_isGroup_1142
            (coe
               MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2692
               (coe v1))))
-- Algebra.Apartness.Structures._.inverseʳ
d_inverse'691'_240 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2816 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsApartnessRelation_722 ->
  AgdaAny -> AgdaAny
d_inverse'691'_240 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 v11
                   ~v12
  = du_inverse'691'_240 v11
du_inverse'691'_240 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2816 ->
  AgdaAny -> AgdaAny
du_inverse'691'_240 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v0) in
    coe
      (let v2
             = coe
                 MAlonzo.Code.Algebra.Structures.du_isRingWithoutOne_2702
                 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2322
                    (coe v2) in
          coe
            (coe
               MAlonzo.Code.Algebra.Structures.du_inverse'691'_1106
               (coe MAlonzo.Code.Algebra.Structures.d_isGroup_1142 (coe v3)))))
-- Algebra.Apartness.Structures._.inverseˡ
d_inverse'737'_242 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2816 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsApartnessRelation_722 ->
  AgdaAny -> AgdaAny
d_inverse'737'_242 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 v11
                   ~v12
  = du_inverse'737'_242 v11
du_inverse'737'_242 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2816 ->
  AgdaAny -> AgdaAny
du_inverse'737'_242 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v0) in
    coe
      (let v2
             = coe
                 MAlonzo.Code.Algebra.Structures.du_isRingWithoutOne_2702
                 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2322
                    (coe v2) in
          coe
            (coe
               MAlonzo.Code.Algebra.Structures.du_inverse'737'_1104
               (coe MAlonzo.Code.Algebra.Structures.d_isGroup_1142 (coe v3)))))
-- Algebra.Apartness.Structures._.distribʳ
d_distrib'691'_246 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2816 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsApartnessRelation_722 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_distrib'691'_246 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 v11
                   ~v12
  = du_distrib'691'_246 v11
du_distrib'691'_246 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2816 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_distrib'691'_246 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.du_distrib'691'_2398
         (coe
            MAlonzo.Code.Algebra.Structures.du_isRingWithoutOne_2702 (coe v1)))
-- Algebra.Apartness.Structures._.distribˡ
d_distrib'737'_248 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2816 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsApartnessRelation_722 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_distrib'737'_248 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 v11
                   ~v12
  = du_distrib'737'_248 v11
du_distrib'737'_248 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2816 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_distrib'737'_248 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.du_distrib'737'_2396
         (coe
            MAlonzo.Code.Algebra.Structures.du_isRingWithoutOne_2702 (coe v1)))
-- Algebra.Apartness.Structures._.isCommutativeSemiring
d_isCommutativeSemiring_250 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2816 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsApartnessRelation_722 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1696
d_isCommutativeSemiring_250 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 v8 v9
                            ~v10 v11 ~v12
  = du_isCommutativeSemiring_250 v6 v7 v8 v9 v11
du_isCommutativeSemiring_250 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2816 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1696
du_isCommutativeSemiring_250 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Algebra.Structures.du_isCommutativeSemiring_2946
      (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
-- Algebra.Apartness.Structures._.isCommutativeSemiringWithoutOne
d_isCommutativeSemiringWithoutOne_252 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2816 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsApartnessRelation_722 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiringWithoutOne_1390
d_isCommutativeSemiringWithoutOne_252 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7
                                      v8 v9 ~v10 v11 ~v12
  = du_isCommutativeSemiringWithoutOne_252 v6 v7 v8 v9 v11
du_isCommutativeSemiringWithoutOne_252 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2816 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiringWithoutOne_1390
du_isCommutativeSemiringWithoutOne_252 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Algebra.Structures.du_isCommutativeSemiringWithoutOne_1798
      (coe
         MAlonzo.Code.Algebra.Structures.du_isCommutativeSemiring_2946
         (coe v0) (coe v1) (coe v2) (coe v3) (coe v4))
-- Algebra.Apartness.Structures._.isEquivalence
d_isEquivalence_254 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2816 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsApartnessRelation_722 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_254 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
                    v11 ~v12
  = du_isEquivalence_254 v11
du_isEquivalence_254 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2816 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
du_isEquivalence_254 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
         (coe
            MAlonzo.Code.Algebra.Structures.d_isMagma_478
            (coe
               MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isMonoid_1048
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_isGroup_1142
                     (coe
                        MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2692
                        (coe v1)))))))
-- Algebra.Apartness.Structures._.isNearSemiring
d_isNearSemiring_256 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2816 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsApartnessRelation_722 ->
  MAlonzo.Code.Algebra.Structures.T_IsNearSemiring_1216
d_isNearSemiring_256 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 v8 v9 ~v10 v11
                     ~v12
  = du_isNearSemiring_256 v6 v7 v8 v9 v11
du_isNearSemiring_256 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2816 ->
  MAlonzo.Code.Algebra.Structures.T_IsNearSemiring_1216
du_isNearSemiring_256 v0 v1 v2 v3 v4
  = let v5
          = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v4) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.du_isNearSemiring_2406 (coe v0)
         (coe v1) (coe v2) (coe v3)
         (coe
            MAlonzo.Code.Algebra.Structures.du_isRingWithoutOne_2702 (coe v5)))
-- Algebra.Apartness.Structures._.isPartialEquivalence
d_isPartialEquivalence_258 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2816 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsApartnessRelation_722 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_258 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                           ~v10 v11 ~v12
  = du_isPartialEquivalence_258 v11
du_isPartialEquivalence_258 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2816 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_258 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v0) in
    coe
      (let v2
             = coe
                 MAlonzo.Code.Algebra.Structures.du_isRingWithoutOne_2702
                 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2322
                    (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Algebra.Structures.d_isGroup_1142 (coe v3) in
             coe
               (let v5
                      = MAlonzo.Code.Algebra.Structures.d_isMonoid_1048 (coe v4) in
                coe
                  (let v6
                         = MAlonzo.Code.Algebra.Structures.d_isSemigroup_694 (coe v5) in
                   coe
                     (let v7 = MAlonzo.Code.Algebra.Structures.d_isMagma_478 (coe v6) in
                      coe
                        (coe
                           MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_42
                           (coe
                              MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
                              (coe v7)))))))))
-- Algebra.Apartness.Structures._.isRingWithoutOne
d_isRingWithoutOne_262 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2816 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsApartnessRelation_722 ->
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2304
d_isRingWithoutOne_262 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
                       v11 ~v12
  = du_isRingWithoutOne_262 v11
du_isRingWithoutOne_262 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2816 ->
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2304
du_isRingWithoutOne_262 v0
  = coe
      MAlonzo.Code.Algebra.Structures.du_isRingWithoutOne_2702
      (coe MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v0))
-- Algebra.Apartness.Structures._.isSemiring
d_isSemiring_264 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2816 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsApartnessRelation_722 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1588
d_isSemiring_264 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 v8 v9 ~v10 v11 ~v12
  = du_isSemiring_264 v6 v7 v8 v9 v11
du_isSemiring_264 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2816 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1588
du_isSemiring_264 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Algebra.Structures.du_isSemiring_2800 (coe v0)
      (coe v1) (coe v2) (coe v3)
      (coe MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v4))
-- Algebra.Apartness.Structures._.isSemiringWithoutAnnihilatingZero
d_isSemiringWithoutAnnihilatingZero_266 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2816 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsApartnessRelation_722 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1486
d_isSemiringWithoutAnnihilatingZero_266 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6
                                        ~v7 ~v8 ~v9 ~v10 v11 ~v12
  = du_isSemiringWithoutAnnihilatingZero_266 v11
du_isSemiringWithoutAnnihilatingZero_266 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2816 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1486
du_isSemiringWithoutAnnihilatingZero_266 v0
  = coe
      MAlonzo.Code.Algebra.Structures.du_isSemiringWithoutAnnihilatingZero_2798
      (coe MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v0))
-- Algebra.Apartness.Structures._.isSemiringWithoutOne
d_isSemiringWithoutOne_268 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2816 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsApartnessRelation_722 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutOne_1296
d_isSemiringWithoutOne_268 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 v8 v9 ~v10
                           v11 ~v12
  = du_isSemiringWithoutOne_268 v6 v7 v8 v9 v11
du_isSemiringWithoutOne_268 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2816 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutOne_1296
du_isSemiringWithoutOne_268 v0 v1 v2 v3 v4
  = let v5
          = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v4) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.du_isSemiringWithoutOne_1678
         (coe
            MAlonzo.Code.Algebra.Structures.du_isSemiring_2800 (coe v0)
            (coe v1) (coe v2) (coe v3) (coe v5)))
-- Algebra.Apartness.Structures._.refl
d_refl_270 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2816 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsApartnessRelation_722 ->
  AgdaAny -> AgdaAny
d_refl_270 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 v11 ~v12
  = du_refl_270 v11
du_refl_270 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2816 ->
  AgdaAny -> AgdaAny
du_refl_270 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_refl_34
         (coe
            MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
            (coe
               MAlonzo.Code.Algebra.Structures.d_isMagma_478
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_isMonoid_1048
                     (coe
                        MAlonzo.Code.Algebra.Structures.d_isGroup_1142
                        (coe
                           MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2692
                           (coe v1))))))))
-- Algebra.Apartness.Structures._.reflexive
d_reflexive_272 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2816 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsApartnessRelation_722 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_272 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 v11
                ~v12
  = du_reflexive_272 v11
du_reflexive_272 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2816 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_272 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v0) in
    coe
      (let v2
             = coe
                 MAlonzo.Code.Algebra.Structures.du_isRingWithoutOne_2702
                 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2322
                    (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Algebra.Structures.d_isGroup_1142 (coe v3) in
             coe
               (let v5
                      = MAlonzo.Code.Algebra.Structures.d_isMonoid_1048 (coe v4) in
                coe
                  (let v6
                         = MAlonzo.Code.Algebra.Structures.d_isSemigroup_694 (coe v5) in
                   coe
                     (let v7 = MAlonzo.Code.Algebra.Structures.d_isMagma_478 (coe v6) in
                      coe
                        (\ v8 v9 v10 ->
                           coe
                             MAlonzo.Code.Relation.Binary.Structures.du_reflexive_40
                             (coe MAlonzo.Code.Algebra.Structures.d_isEquivalence_184 (coe v7))
                             v8)))))))
-- Algebra.Apartness.Structures._.setoid
d_setoid_274 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2816 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsApartnessRelation_722 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
d_setoid_274 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 v11 ~v12
  = du_setoid_274 v11
du_setoid_274 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2816 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
du_setoid_274 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v0) in
    coe
      (let v2
             = coe
                 MAlonzo.Code.Algebra.Structures.du_isRingWithoutOne_2702
                 (coe v1) in
       coe
         (let v3
                = MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2322
                    (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Algebra.Structures.d_isGroup_1142 (coe v3) in
             coe
               (let v5
                      = MAlonzo.Code.Algebra.Structures.d_isMonoid_1048 (coe v4) in
                coe
                  (let v6
                         = MAlonzo.Code.Algebra.Structures.d_isSemigroup_694 (coe v5) in
                   coe
                     (coe
                        MAlonzo.Code.Algebra.Structures.du_setoid_200
                        (coe MAlonzo.Code.Algebra.Structures.d_isMagma_478 (coe v6))))))))
-- Algebra.Apartness.Structures._.sym
d_sym_276 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2816 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsApartnessRelation_722 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_276 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 v11 ~v12
  = du_sym_276 v11
du_sym_276 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2816 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_sym_276 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_sym_36
         (coe
            MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
            (coe
               MAlonzo.Code.Algebra.Structures.d_isMagma_478
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_isMonoid_1048
                     (coe
                        MAlonzo.Code.Algebra.Structures.d_isGroup_1142
                        (coe
                           MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2692
                           (coe v1))))))))
-- Algebra.Apartness.Structures._.trans
d_trans_278 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2816 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsApartnessRelation_722 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_278 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 v11 ~v12
  = du_trans_278 v11
du_trans_278 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2816 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_trans_278 v0
  = let v1
          = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_trans_38
         (coe
            MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
            (coe
               MAlonzo.Code.Algebra.Structures.d_isMagma_478
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_isMonoid_1048
                     (coe
                        MAlonzo.Code.Algebra.Structures.d_isGroup_1142
                        (coe
                           MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2692
                           (coe v1))))))))
-- Algebra.Apartness.Structures._.uniqueʳ-⁻¹
d_unique'691''45''8315''185'_280 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2816 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsApartnessRelation_722 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_unique'691''45''8315''185'_280 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 ~v7 v8
                                 v9 ~v10 v11 ~v12
  = du_unique'691''45''8315''185'_280 v6 v8 v9 v11
du_unique'691''45''8315''185'_280 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2816 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_unique'691''45''8315''185'_280 v0 v1 v2 v3
  = let v4
          = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v3) in
    coe
      (let v5
             = coe
                 MAlonzo.Code.Algebra.Structures.du_isRingWithoutOne_2702
                 (coe v4) in
       coe
         (let v6
                = MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2322
                    (coe v5) in
          coe
            (coe
               MAlonzo.Code.Algebra.Structures.du_unique'691''45''8315''185'_1118
               (coe v0) (coe v2) (coe v1)
               (coe MAlonzo.Code.Algebra.Structures.d_isGroup_1142 (coe v6)))))
-- Algebra.Apartness.Structures._.uniqueˡ-⁻¹
d_unique'737''45''8315''185'_282 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2816 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsApartnessRelation_722 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_unique'737''45''8315''185'_282 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 ~v7 v8
                                 v9 ~v10 v11 ~v12
  = du_unique'737''45''8315''185'_282 v6 v8 v9 v11
du_unique'737''45''8315''185'_282 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2816 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_unique'737''45''8315''185'_282 v0 v1 v2 v3
  = let v4
          = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v3) in
    coe
      (let v5
             = coe
                 MAlonzo.Code.Algebra.Structures.du_isRingWithoutOne_2702
                 (coe v4) in
       coe
         (let v6
                = MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2322
                    (coe v5) in
          coe
            (coe
               MAlonzo.Code.Algebra.Structures.du_unique'737''45''8315''185'_1112
               (coe v0) (coe v2) (coe v1)
               (coe MAlonzo.Code.Algebra.Structures.d_isGroup_1142 (coe v6)))))
-- Algebra.Apartness.Structures._.zero
d_zero_284 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2816 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsApartnessRelation_722 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_zero_284 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 v8 v9 ~v10 v11 ~v12
  = du_zero_284 v6 v7 v8 v9 v11
du_zero_284 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2816 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_zero_284 v0 v1 v2 v3 v4
  = let v5
          = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v4) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.du_zero_2404 (coe v0) (coe v1)
         (coe v2) (coe v3)
         (coe
            MAlonzo.Code.Algebra.Structures.du_isRingWithoutOne_2702 (coe v5)))
-- Algebra.Apartness.Structures._.zeroʳ
d_zero'691'_286 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2816 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsApartnessRelation_722 ->
  AgdaAny -> AgdaAny
d_zero'691'_286 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 v8 v9 ~v10 v11 ~v12
  = du_zero'691'_286 v6 v7 v8 v9 v11
du_zero'691'_286 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2816 ->
  AgdaAny -> AgdaAny
du_zero'691'_286 v0 v1 v2 v3 v4
  = let v5
          = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v4) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.du_zero'691'_2402 (coe v0) (coe v1)
         (coe v2) (coe v3)
         (coe
            MAlonzo.Code.Algebra.Structures.du_isRingWithoutOne_2702 (coe v5)))
-- Algebra.Apartness.Structures._.zeroˡ
d_zero'737'_288 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2816 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsApartnessRelation_722 ->
  AgdaAny -> AgdaAny
d_zero'737'_288 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 v8 v9 ~v10 v11 ~v12
  = du_zero'737'_288 v6 v7 v8 v9 v11
du_zero'737'_288 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2816 ->
  AgdaAny -> AgdaAny
du_zero'737'_288 v0 v1 v2 v3 v4
  = let v5
          = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v4) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.du_zero'737'_2400 (coe v0) (coe v1)
         (coe v2) (coe v3)
         (coe
            MAlonzo.Code.Algebra.Structures.du_isRingWithoutOne_2702 (coe v5)))
-- Algebra.Apartness.Structures.IsHeytingCommutativeRing.isCommutativeRing
d_isCommutativeRing_312 ::
  T_IsHeytingCommutativeRing_160 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2816
d_isCommutativeRing_312 v0
  = case coe v0 of
      C_IsHeytingCommutativeRing'46'constructor_4849 v1 v2 v3 v4
        -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Apartness.Structures.IsHeytingCommutativeRing.isApartnessRelation
d_isApartnessRelation_314 ::
  T_IsHeytingCommutativeRing_160 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsApartnessRelation_722
d_isApartnessRelation_314 v0
  = case coe v0 of
      C_IsHeytingCommutativeRing'46'constructor_4849 v1 v2 v3 v4
        -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Apartness.Structures.IsHeytingCommutativeRing._._//_
d__'47''47'__318 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsHeytingCommutativeRing_160 -> AgdaAny -> AgdaAny -> AgdaAny
d__'47''47'__318 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 ~v7 v8 ~v9 ~v10 ~v11
  = du__'47''47'__318 v6 v8
du__'47''47'__318 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny -> AgdaAny
du__'47''47'__318 v0 v1
  = coe
      MAlonzo.Code.Algebra.Structures.du__'47''47'__1096 (coe v0)
      (coe v1)
-- Algebra.Apartness.Structures.IsHeytingCommutativeRing._.*-assoc
d_'42''45'assoc_320 ::
  T_IsHeytingCommutativeRing_160 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'42''45'assoc_320 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'42''45'assoc_2696
      (coe
         MAlonzo.Code.Algebra.Structures.d_isRing_2832
         (coe d_isCommutativeRing_312 (coe v0)))
-- Algebra.Apartness.Structures.IsHeytingCommutativeRing._.*-comm
d_'42''45'comm_322 ::
  T_IsHeytingCommutativeRing_160 -> AgdaAny -> AgdaAny -> AgdaAny
d_'42''45'comm_322 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'42''45'comm_2834
      (coe d_isCommutativeRing_312 (coe v0))
-- Algebra.Apartness.Structures.IsHeytingCommutativeRing._.*-cong
d_'42''45'cong_324 ::
  T_IsHeytingCommutativeRing_160 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'42''45'cong_324 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'42''45'cong_2694
      (coe
         MAlonzo.Code.Algebra.Structures.d_isRing_2832
         (coe d_isCommutativeRing_312 (coe v0)))
-- Algebra.Apartness.Structures.IsHeytingCommutativeRing._.∙-congʳ
d_'8729''45'cong'691'_326 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsHeytingCommutativeRing_160 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'691'_326 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 v8 v9 ~v10
                          v11
  = du_'8729''45'cong'691'_326 v6 v7 v8 v9 v11
du_'8729''45'cong'691'_326 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsHeytingCommutativeRing_160 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'691'_326 v0 v1 v2 v3 v4
  = let v5 = d_isCommutativeRing_312 (coe v4) in
    coe
      (let v6 = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v5) in
       coe
         (let v7
                = coe
                    MAlonzo.Code.Algebra.Structures.du_isRingWithoutOne_2702
                    (coe v6) in
          coe
            (let v8
                   = coe
                       MAlonzo.Code.Algebra.Structures.du_isNearSemiring_2406 (coe v0)
                       (coe v1) (coe v2) (coe v3) (coe v7) in
             coe
               (let v9
                      = coe
                          MAlonzo.Code.Algebra.Structures.du_'42''45'isMagma_1280 (coe v8) in
                coe
                  (let v10
                         = coe MAlonzo.Code.Algebra.Structures.du_setoid_200 (coe v9) in
                   coe
                     (let v11
                            = MAlonzo.Code.Algebra.Structures.d_'8729''45'cong_186 (coe v9) in
                      coe
                        (coe
                           MAlonzo.Code.Algebra.Consequences.Base.du_'8729''45'cong'691'_46
                           (coe v11)
                           (coe
                              MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                              (coe
                                 MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                                 (coe v10))))))))))
-- Algebra.Apartness.Structures.IsHeytingCommutativeRing._.∙-congˡ
d_'8729''45'cong'737'_328 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsHeytingCommutativeRing_160 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'737'_328 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 v8 v9 ~v10
                          v11
  = du_'8729''45'cong'737'_328 v6 v7 v8 v9 v11
du_'8729''45'cong'737'_328 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsHeytingCommutativeRing_160 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'737'_328 v0 v1 v2 v3 v4
  = let v5 = d_isCommutativeRing_312 (coe v4) in
    coe
      (let v6 = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v5) in
       coe
         (let v7
                = coe
                    MAlonzo.Code.Algebra.Structures.du_isRingWithoutOne_2702
                    (coe v6) in
          coe
            (let v8
                   = coe
                       MAlonzo.Code.Algebra.Structures.du_isNearSemiring_2406 (coe v0)
                       (coe v1) (coe v2) (coe v3) (coe v7) in
             coe
               (let v9
                      = coe
                          MAlonzo.Code.Algebra.Structures.du_'42''45'isMagma_1280 (coe v8) in
                coe
                  (let v10
                         = coe MAlonzo.Code.Algebra.Structures.du_setoid_200 (coe v9) in
                   coe
                     (let v11
                            = MAlonzo.Code.Algebra.Structures.d_'8729''45'cong_186 (coe v9) in
                      coe
                        (coe
                           MAlonzo.Code.Algebra.Consequences.Base.du_'8729''45'cong'737'_42
                           (coe v11)
                           (coe
                              MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                              (coe
                                 MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                                 (coe v10))))))))))
-- Algebra.Apartness.Structures.IsHeytingCommutativeRing._.*-identity
d_'42''45'identity_330 ::
  T_IsHeytingCommutativeRing_160 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'42''45'identity_330 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'42''45'identity_2698
      (coe
         MAlonzo.Code.Algebra.Structures.d_isRing_2832
         (coe d_isCommutativeRing_312 (coe v0)))
-- Algebra.Apartness.Structures.IsHeytingCommutativeRing._.identityʳ
d_identity'691'_332 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny -> T_IsHeytingCommutativeRing_160 -> AgdaAny -> AgdaAny
d_identity'691'_332 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 v8 v9 ~v10 v11
  = du_identity'691'_332 v6 v7 v8 v9 v11
du_identity'691'_332 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> T_IsHeytingCommutativeRing_160 -> AgdaAny -> AgdaAny
du_identity'691'_332 v0 v1 v2 v3 v4
  = let v5 = d_isCommutativeRing_312 (coe v4) in
    coe
      (let v6 = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v5) in
       coe
         (coe
            MAlonzo.Code.Algebra.Structures.du_identity'691'_726
            (coe
               MAlonzo.Code.Algebra.Structures.du_'42''45'isMonoid_2790 (coe v0)
               (coe v1) (coe v2) (coe v3) (coe v6))))
-- Algebra.Apartness.Structures.IsHeytingCommutativeRing._.identityˡ
d_identity'737'_334 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny -> T_IsHeytingCommutativeRing_160 -> AgdaAny -> AgdaAny
d_identity'737'_334 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 v8 v9 ~v10 v11
  = du_identity'737'_334 v6 v7 v8 v9 v11
du_identity'737'_334 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> T_IsHeytingCommutativeRing_160 -> AgdaAny -> AgdaAny
du_identity'737'_334 v0 v1 v2 v3 v4
  = let v5 = d_isCommutativeRing_312 (coe v4) in
    coe
      (let v6 = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v5) in
       coe
         (coe
            MAlonzo.Code.Algebra.Structures.du_identity'737'_724
            (coe
               MAlonzo.Code.Algebra.Structures.du_'42''45'isMonoid_2790 (coe v0)
               (coe v1) (coe v2) (coe v3) (coe v6))))
-- Algebra.Apartness.Structures.IsHeytingCommutativeRing._.isCommutativeMagma
d_isCommutativeMagma_336 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsHeytingCommutativeRing_160 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMagma_210
d_isCommutativeMagma_336 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 v8 v9 ~v10
                         v11
  = du_isCommutativeMagma_336 v6 v7 v8 v9 v11
du_isCommutativeMagma_336 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsHeytingCommutativeRing_160 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMagma_210
du_isCommutativeMagma_336 v0 v1 v2 v3 v4
  = let v5 = d_isCommutativeRing_312 (coe v4) in
    coe
      (let v6
             = coe
                 MAlonzo.Code.Algebra.Structures.du_isCommutativeSemiring_2946
                 (coe v0) (coe v1) (coe v2) (coe v3) (coe v5) in
       coe
         (let v7
                = coe
                    MAlonzo.Code.Algebra.Structures.du_isCommutativeSemiringWithoutOne_1798
                    (coe v6) in
          coe
            (coe
               MAlonzo.Code.Algebra.Structures.du_isCommutativeMagma_584
               (coe
                  MAlonzo.Code.Algebra.Structures.du_'42''45'isCommutativeSemigroup_1472
                  (coe v7)))))
-- Algebra.Apartness.Structures.IsHeytingCommutativeRing._.*-isCommutativeMonoid
d_'42''45'isCommutativeMonoid_338 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsHeytingCommutativeRing_160 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_734
d_'42''45'isCommutativeMonoid_338 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 v8
                                  v9 ~v10 v11
  = du_'42''45'isCommutativeMonoid_338 v6 v7 v8 v9 v11
du_'42''45'isCommutativeMonoid_338 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsHeytingCommutativeRing_160 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_734
du_'42''45'isCommutativeMonoid_338 v0 v1 v2 v3 v4
  = let v5 = d_isCommutativeRing_312 (coe v4) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.du_'42''45'isCommutativeMonoid_1806
         (coe
            MAlonzo.Code.Algebra.Structures.du_isCommutativeSemiring_2946
            (coe v0) (coe v1) (coe v2) (coe v3) (coe v5)))
-- Algebra.Apartness.Structures.IsHeytingCommutativeRing._.*-isCommutativeSemigroup
d_'42''45'isCommutativeSemigroup_340 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsHeytingCommutativeRing_160 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_546
d_'42''45'isCommutativeSemigroup_340 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7
                                     v8 v9 ~v10 v11
  = du_'42''45'isCommutativeSemigroup_340 v6 v7 v8 v9 v11
du_'42''45'isCommutativeSemigroup_340 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsHeytingCommutativeRing_160 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_546
du_'42''45'isCommutativeSemigroup_340 v0 v1 v2 v3 v4
  = let v5 = d_isCommutativeRing_312 (coe v4) in
    coe
      (let v6
             = coe
                 MAlonzo.Code.Algebra.Structures.du_isCommutativeSemiring_2946
                 (coe v0) (coe v1) (coe v2) (coe v3) (coe v5) in
       coe
         (coe
            MAlonzo.Code.Algebra.Structures.du_'42''45'isCommutativeSemigroup_1472
            (coe
               MAlonzo.Code.Algebra.Structures.du_isCommutativeSemiringWithoutOne_1798
               (coe v6))))
-- Algebra.Apartness.Structures.IsHeytingCommutativeRing._.*-isMagma
d_'42''45'isMagma_342 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsHeytingCommutativeRing_160 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176
d_'42''45'isMagma_342 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 v8 v9 ~v10 v11
  = du_'42''45'isMagma_342 v6 v7 v8 v9 v11
du_'42''45'isMagma_342 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsHeytingCommutativeRing_160 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176
du_'42''45'isMagma_342 v0 v1 v2 v3 v4
  = let v5 = d_isCommutativeRing_312 (coe v4) in
    coe
      (let v6 = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v5) in
       coe
         (let v7
                = coe
                    MAlonzo.Code.Algebra.Structures.du_isRingWithoutOne_2702
                    (coe v6) in
          coe
            (coe
               MAlonzo.Code.Algebra.Structures.du_'42''45'isMagma_1280
               (coe
                  MAlonzo.Code.Algebra.Structures.du_isNearSemiring_2406 (coe v0)
                  (coe v1) (coe v2) (coe v3) (coe v7)))))
-- Algebra.Apartness.Structures.IsHeytingCommutativeRing._.*-isMonoid
d_'42''45'isMonoid_344 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsHeytingCommutativeRing_160 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_684
d_'42''45'isMonoid_344 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 v8 v9 ~v10 v11
  = du_'42''45'isMonoid_344 v6 v7 v8 v9 v11
du_'42''45'isMonoid_344 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsHeytingCommutativeRing_160 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_684
du_'42''45'isMonoid_344 v0 v1 v2 v3 v4
  = let v5 = d_isCommutativeRing_312 (coe v4) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.du_'42''45'isMonoid_2790 (coe v0)
         (coe v1) (coe v2) (coe v3)
         (coe MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v5)))
-- Algebra.Apartness.Structures.IsHeytingCommutativeRing._.*-isSemigroup
d_'42''45'isSemigroup_346 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsHeytingCommutativeRing_160 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_470
d_'42''45'isSemigroup_346 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 v8 v9 ~v10
                          v11
  = du_'42''45'isSemigroup_346 v6 v7 v8 v9 v11
du_'42''45'isSemigroup_346 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsHeytingCommutativeRing_160 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_470
du_'42''45'isSemigroup_346 v0 v1 v2 v3 v4
  = let v5 = d_isCommutativeRing_312 (coe v4) in
    coe
      (let v6 = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v5) in
       coe
         (let v7
                = coe
                    MAlonzo.Code.Algebra.Structures.du_isRingWithoutOne_2702
                    (coe v6) in
          coe
            (coe
               MAlonzo.Code.Algebra.Structures.du_'42''45'isSemigroup_1282
               (coe
                  MAlonzo.Code.Algebra.Structures.du_isNearSemiring_2406 (coe v0)
                  (coe v1) (coe v2) (coe v3) (coe v7)))))
-- Algebra.Apartness.Structures.IsHeytingCommutativeRing._.assoc
d_assoc_348 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsHeytingCommutativeRing_160 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_assoc_348 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 v11
  = du_assoc_348 v11
du_assoc_348 ::
  T_IsHeytingCommutativeRing_160 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_assoc_348 v0
  = let v1 = d_isCommutativeRing_312 (coe v0) in
    coe
      (let v2 = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Algebra.Structures.d_assoc_480
            (coe
               MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isMonoid_1048
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_isGroup_1142
                     (coe
                        MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2692
                        (coe v2)))))))
-- Algebra.Apartness.Structures.IsHeytingCommutativeRing._.comm
d_comm_350 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsHeytingCommutativeRing_160 -> AgdaAny -> AgdaAny -> AgdaAny
d_comm_350 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 v11
  = du_comm_350 v11
du_comm_350 ::
  T_IsHeytingCommutativeRing_160 -> AgdaAny -> AgdaAny -> AgdaAny
du_comm_350 v0
  = let v1 = d_isCommutativeRing_312 (coe v0) in
    coe
      (let v2 = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Algebra.Structures.d_comm_1144
            (coe
               MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2692
               (coe v2))))
-- Algebra.Apartness.Structures.IsHeytingCommutativeRing._.∙-cong
d_'8729''45'cong_352 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsHeytingCommutativeRing_160 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong_352 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
                     v11
  = du_'8729''45'cong_352 v11
du_'8729''45'cong_352 ::
  T_IsHeytingCommutativeRing_160 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong_352 v0
  = let v1 = d_isCommutativeRing_312 (coe v0) in
    coe
      (let v2 = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Algebra.Structures.d_'8729''45'cong_186
            (coe
               MAlonzo.Code.Algebra.Structures.d_isMagma_478
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_isMonoid_1048
                     (coe
                        MAlonzo.Code.Algebra.Structures.d_isGroup_1142
                        (coe
                           MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2692
                           (coe v2))))))))
-- Algebra.Apartness.Structures.IsHeytingCommutativeRing._.∙-congʳ
d_'8729''45'cong'691'_354 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsHeytingCommutativeRing_160 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'691'_354 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                          ~v10 v11
  = du_'8729''45'cong'691'_354 v11
du_'8729''45'cong'691'_354 ::
  T_IsHeytingCommutativeRing_160 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'691'_354 v0
  = let v1 = d_isCommutativeRing_312 (coe v0) in
    coe
      (let v2 = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v1) in
       coe
         (let v3
                = coe
                    MAlonzo.Code.Algebra.Structures.du_isRingWithoutOne_2702
                    (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2322
                       (coe v3) in
             coe
               (let v5
                      = MAlonzo.Code.Algebra.Structures.d_isGroup_1142 (coe v4) in
                coe
                  (let v6
                         = MAlonzo.Code.Algebra.Structures.d_isMonoid_1048 (coe v5) in
                   coe
                     (let v7
                            = MAlonzo.Code.Algebra.Structures.d_isSemigroup_694 (coe v6) in
                      coe
                        (let v8 = MAlonzo.Code.Algebra.Structures.d_isMagma_478 (coe v7) in
                         coe
                           (let v9
                                  = coe MAlonzo.Code.Algebra.Structures.du_setoid_200 (coe v8) in
                            coe
                              (let v10
                                     = MAlonzo.Code.Algebra.Structures.d_'8729''45'cong_186
                                         (coe v8) in
                               coe
                                 (coe
                                    MAlonzo.Code.Algebra.Consequences.Base.du_'8729''45'cong'691'_46
                                    (coe v10)
                                    (coe
                                       MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                                       (coe
                                          MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                                          (coe v9)))))))))))))
-- Algebra.Apartness.Structures.IsHeytingCommutativeRing._.∙-congˡ
d_'8729''45'cong'737'_356 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsHeytingCommutativeRing_160 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'737'_356 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                          ~v10 v11
  = du_'8729''45'cong'737'_356 v11
du_'8729''45'cong'737'_356 ::
  T_IsHeytingCommutativeRing_160 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'737'_356 v0
  = let v1 = d_isCommutativeRing_312 (coe v0) in
    coe
      (let v2 = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v1) in
       coe
         (let v3
                = coe
                    MAlonzo.Code.Algebra.Structures.du_isRingWithoutOne_2702
                    (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2322
                       (coe v3) in
             coe
               (let v5
                      = MAlonzo.Code.Algebra.Structures.d_isGroup_1142 (coe v4) in
                coe
                  (let v6
                         = MAlonzo.Code.Algebra.Structures.d_isMonoid_1048 (coe v5) in
                   coe
                     (let v7
                            = MAlonzo.Code.Algebra.Structures.d_isSemigroup_694 (coe v6) in
                      coe
                        (let v8 = MAlonzo.Code.Algebra.Structures.d_isMagma_478 (coe v7) in
                         coe
                           (let v9
                                  = coe MAlonzo.Code.Algebra.Structures.du_setoid_200 (coe v8) in
                            coe
                              (let v10
                                     = MAlonzo.Code.Algebra.Structures.d_'8729''45'cong_186
                                         (coe v8) in
                               coe
                                 (coe
                                    MAlonzo.Code.Algebra.Consequences.Base.du_'8729''45'cong'737'_42
                                    (coe v10)
                                    (coe
                                       MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                                       (coe
                                          MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                                          (coe v9)))))))))))))
-- Algebra.Apartness.Structures.IsHeytingCommutativeRing._.identity
d_identity_358 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsHeytingCommutativeRing_160 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_358 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 v11
  = du_identity_358 v11
du_identity_358 ::
  T_IsHeytingCommutativeRing_160 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_identity_358 v0
  = let v1 = d_isCommutativeRing_312 (coe v0) in
    coe
      (let v2 = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Algebra.Structures.d_identity_696
            (coe
               MAlonzo.Code.Algebra.Structures.d_isMonoid_1048
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isGroup_1142
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2692
                     (coe v2))))))
-- Algebra.Apartness.Structures.IsHeytingCommutativeRing._.identityʳ
d_identity'691'_360 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny -> T_IsHeytingCommutativeRing_160 -> AgdaAny -> AgdaAny
d_identity'691'_360 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
                    v11
  = du_identity'691'_360 v11
du_identity'691'_360 ::
  T_IsHeytingCommutativeRing_160 -> AgdaAny -> AgdaAny
du_identity'691'_360 v0
  = let v1 = d_isCommutativeRing_312 (coe v0) in
    coe
      (let v2 = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v1) in
       coe
         (let v3
                = coe
                    MAlonzo.Code.Algebra.Structures.du_isRingWithoutOne_2702
                    (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2322
                       (coe v3) in
             coe
               (let v5
                      = MAlonzo.Code.Algebra.Structures.d_isGroup_1142 (coe v4) in
                coe
                  (coe
                     MAlonzo.Code.Algebra.Structures.du_identity'691'_726
                     (coe MAlonzo.Code.Algebra.Structures.d_isMonoid_1048 (coe v5)))))))
-- Algebra.Apartness.Structures.IsHeytingCommutativeRing._.identityˡ
d_identity'737'_362 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny -> T_IsHeytingCommutativeRing_160 -> AgdaAny -> AgdaAny
d_identity'737'_362 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
                    v11
  = du_identity'737'_362 v11
du_identity'737'_362 ::
  T_IsHeytingCommutativeRing_160 -> AgdaAny -> AgdaAny
du_identity'737'_362 v0
  = let v1 = d_isCommutativeRing_312 (coe v0) in
    coe
      (let v2 = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v1) in
       coe
         (let v3
                = coe
                    MAlonzo.Code.Algebra.Structures.du_isRingWithoutOne_2702
                    (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2322
                       (coe v3) in
             coe
               (let v5
                      = MAlonzo.Code.Algebra.Structures.d_isGroup_1142 (coe v4) in
                coe
                  (coe
                     MAlonzo.Code.Algebra.Structures.du_identity'737'_724
                     (coe MAlonzo.Code.Algebra.Structures.d_isMonoid_1048 (coe v5)))))))
-- Algebra.Apartness.Structures.IsHeytingCommutativeRing._.+-isAbelianGroup
d_'43''45'isAbelianGroup_364 ::
  T_IsHeytingCommutativeRing_160 ->
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1130
d_'43''45'isAbelianGroup_364 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2692
      (coe
         MAlonzo.Code.Algebra.Structures.d_isRing_2832
         (coe d_isCommutativeRing_312 (coe v0)))
-- Algebra.Apartness.Structures.IsHeytingCommutativeRing._.isCommutativeMagma
d_isCommutativeMagma_366 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsHeytingCommutativeRing_160 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMagma_210
d_isCommutativeMagma_366 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                         ~v10 v11
  = du_isCommutativeMagma_366 v11
du_isCommutativeMagma_366 ::
  T_IsHeytingCommutativeRing_160 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMagma_210
du_isCommutativeMagma_366 v0
  = let v1 = d_isCommutativeRing_312 (coe v0) in
    coe
      (let v2 = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v1) in
       coe
         (let v3
                = coe
                    MAlonzo.Code.Algebra.Structures.du_isRingWithoutOne_2702
                    (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2322
                       (coe v3) in
             coe
               (let v5
                      = coe
                          MAlonzo.Code.Algebra.Structures.du_isCommutativeMonoid_1202
                          (coe v4) in
                coe
                  (coe
                     MAlonzo.Code.Algebra.Structures.du_isCommutativeMagma_584
                     (coe
                        MAlonzo.Code.Algebra.Structures.du_isCommutativeSemigroup_784
                        (coe v5)))))))
-- Algebra.Apartness.Structures.IsHeytingCommutativeRing._.isCommutativeMonoid
d_isCommutativeMonoid_368 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsHeytingCommutativeRing_160 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_734
d_isCommutativeMonoid_368 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                          ~v10 v11
  = du_isCommutativeMonoid_368 v11
du_isCommutativeMonoid_368 ::
  T_IsHeytingCommutativeRing_160 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_734
du_isCommutativeMonoid_368 v0
  = let v1 = d_isCommutativeRing_312 (coe v0) in
    coe
      (let v2 = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v1) in
       coe
         (let v3
                = coe
                    MAlonzo.Code.Algebra.Structures.du_isRingWithoutOne_2702
                    (coe v2) in
          coe
            (coe
               MAlonzo.Code.Algebra.Structures.du_isCommutativeMonoid_1202
               (coe
                  MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2322
                  (coe v3)))))
-- Algebra.Apartness.Structures.IsHeytingCommutativeRing._.isCommutativeSemigroup
d_isCommutativeSemigroup_370 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsHeytingCommutativeRing_160 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_546
d_isCommutativeSemigroup_370 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8
                             ~v9 ~v10 v11
  = du_isCommutativeSemigroup_370 v11
du_isCommutativeSemigroup_370 ::
  T_IsHeytingCommutativeRing_160 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_546
du_isCommutativeSemigroup_370 v0
  = let v1 = d_isCommutativeRing_312 (coe v0) in
    coe
      (let v2 = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v1) in
       coe
         (let v3
                = coe
                    MAlonzo.Code.Algebra.Structures.du_isRingWithoutOne_2702
                    (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2322
                       (coe v3) in
             coe
               (coe
                  MAlonzo.Code.Algebra.Structures.du_isCommutativeSemigroup_784
                  (coe
                     MAlonzo.Code.Algebra.Structures.du_isCommutativeMonoid_1202
                     (coe v4))))))
-- Algebra.Apartness.Structures.IsHeytingCommutativeRing._.isGroup
d_isGroup_372 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsHeytingCommutativeRing_160 ->
  MAlonzo.Code.Algebra.Structures.T_IsGroup_1034
d_isGroup_372 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 v11
  = du_isGroup_372 v11
du_isGroup_372 ::
  T_IsHeytingCommutativeRing_160 ->
  MAlonzo.Code.Algebra.Structures.T_IsGroup_1034
du_isGroup_372 v0
  = let v1 = d_isCommutativeRing_312 (coe v0) in
    coe
      (let v2 = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Algebra.Structures.d_isGroup_1142
            (coe
               MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2692
               (coe v2))))
-- Algebra.Apartness.Structures.IsHeytingCommutativeRing._.isInvertibleMagma
d_isInvertibleMagma_374 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsHeytingCommutativeRing_160 ->
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleMagma_922
d_isInvertibleMagma_374 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                        ~v10 v11
  = du_isInvertibleMagma_374 v11
du_isInvertibleMagma_374 ::
  T_IsHeytingCommutativeRing_160 ->
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleMagma_922
du_isInvertibleMagma_374 v0
  = let v1 = d_isCommutativeRing_312 (coe v0) in
    coe
      (let v2 = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v1) in
       coe
         (let v3
                = coe
                    MAlonzo.Code.Algebra.Structures.du_isRingWithoutOne_2702
                    (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2322
                       (coe v3) in
             coe
               (coe
                  MAlonzo.Code.Algebra.Structures.du_isInvertibleMagma_1120
                  (coe MAlonzo.Code.Algebra.Structures.d_isGroup_1142 (coe v4))))))
-- Algebra.Apartness.Structures.IsHeytingCommutativeRing._.isInvertibleUnitalMagma
d_isInvertibleUnitalMagma_376 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsHeytingCommutativeRing_160 ->
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleUnitalMagma_974
d_isInvertibleUnitalMagma_376 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8
                              ~v9 ~v10 v11
  = du_isInvertibleUnitalMagma_376 v11
du_isInvertibleUnitalMagma_376 ::
  T_IsHeytingCommutativeRing_160 ->
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleUnitalMagma_974
du_isInvertibleUnitalMagma_376 v0
  = let v1 = d_isCommutativeRing_312 (coe v0) in
    coe
      (let v2 = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v1) in
       coe
         (let v3
                = coe
                    MAlonzo.Code.Algebra.Structures.du_isRingWithoutOne_2702
                    (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2322
                       (coe v3) in
             coe
               (coe
                  MAlonzo.Code.Algebra.Structures.du_isInvertibleUnitalMagma_1122
                  (coe MAlonzo.Code.Algebra.Structures.d_isGroup_1142 (coe v4))))))
-- Algebra.Apartness.Structures.IsHeytingCommutativeRing._.isMagma
d_isMagma_378 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsHeytingCommutativeRing_160 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176
d_isMagma_378 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 v11
  = du_isMagma_378 v11
du_isMagma_378 ::
  T_IsHeytingCommutativeRing_160 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176
du_isMagma_378 v0
  = let v1 = d_isCommutativeRing_312 (coe v0) in
    coe
      (let v2 = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Algebra.Structures.d_isMagma_478
            (coe
               MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isMonoid_1048
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_isGroup_1142
                     (coe
                        MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2692
                        (coe v2)))))))
-- Algebra.Apartness.Structures.IsHeytingCommutativeRing._.isMonoid
d_isMonoid_380 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsHeytingCommutativeRing_160 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_684
d_isMonoid_380 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 v11
  = du_isMonoid_380 v11
du_isMonoid_380 ::
  T_IsHeytingCommutativeRing_160 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_684
du_isMonoid_380 v0
  = let v1 = d_isCommutativeRing_312 (coe v0) in
    coe
      (let v2 = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Algebra.Structures.d_isMonoid_1048
            (coe
               MAlonzo.Code.Algebra.Structures.d_isGroup_1142
               (coe
                  MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2692
                  (coe v2)))))
-- Algebra.Apartness.Structures.IsHeytingCommutativeRing._.isSemigroup
d_isSemigroup_382 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsHeytingCommutativeRing_160 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_470
d_isSemigroup_382 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 v11
  = du_isSemigroup_382 v11
du_isSemigroup_382 ::
  T_IsHeytingCommutativeRing_160 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_470
du_isSemigroup_382 v0
  = let v1 = d_isCommutativeRing_312 (coe v0) in
    coe
      (let v2 = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
            (coe
               MAlonzo.Code.Algebra.Structures.d_isMonoid_1048
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isGroup_1142
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2692
                     (coe v2))))))
-- Algebra.Apartness.Structures.IsHeytingCommutativeRing._.isUnitalMagma
d_isUnitalMagma_384 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsHeytingCommutativeRing_160 ->
  MAlonzo.Code.Algebra.Structures.T_IsUnitalMagma_640
d_isUnitalMagma_384 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
                    v11
  = du_isUnitalMagma_384 v11
du_isUnitalMagma_384 ::
  T_IsHeytingCommutativeRing_160 ->
  MAlonzo.Code.Algebra.Structures.T_IsUnitalMagma_640
du_isUnitalMagma_384 v0
  = let v1 = d_isCommutativeRing_312 (coe v0) in
    coe
      (let v2 = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v1) in
       coe
         (let v3
                = coe
                    MAlonzo.Code.Algebra.Structures.du_isRingWithoutOne_2702
                    (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2322
                       (coe v3) in
             coe
               (let v5
                      = MAlonzo.Code.Algebra.Structures.d_isGroup_1142 (coe v4) in
                coe
                  (coe
                     MAlonzo.Code.Algebra.Structures.du_isUnitalMagma_728
                     (coe MAlonzo.Code.Algebra.Structures.d_isMonoid_1048 (coe v5)))))))
-- Algebra.Apartness.Structures.IsHeytingCommutativeRing._.⁻¹-cong
d_'8315''185''45'cong_386 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsHeytingCommutativeRing_160 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8315''185''45'cong_386 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                          ~v10 v11
  = du_'8315''185''45'cong_386 v11
du_'8315''185''45'cong_386 ::
  T_IsHeytingCommutativeRing_160 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8315''185''45'cong_386 v0
  = let v1 = d_isCommutativeRing_312 (coe v0) in
    coe
      (let v2 = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Algebra.Structures.d_'8315''185''45'cong_1052
            (coe
               MAlonzo.Code.Algebra.Structures.d_isGroup_1142
               (coe
                  MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2692
                  (coe v2)))))
-- Algebra.Apartness.Structures.IsHeytingCommutativeRing._.inverse
d_inverse_388 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsHeytingCommutativeRing_160 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inverse_388 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 v11
  = du_inverse_388 v11
du_inverse_388 ::
  T_IsHeytingCommutativeRing_160 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_inverse_388 v0
  = let v1 = d_isCommutativeRing_312 (coe v0) in
    coe
      (let v2 = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Algebra.Structures.d_inverse_1050
            (coe
               MAlonzo.Code.Algebra.Structures.d_isGroup_1142
               (coe
                  MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2692
                  (coe v2)))))
-- Algebra.Apartness.Structures.IsHeytingCommutativeRing._.inverseʳ
d_inverse'691'_390 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny -> T_IsHeytingCommutativeRing_160 -> AgdaAny -> AgdaAny
d_inverse'691'_390 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 v11
  = du_inverse'691'_390 v11
du_inverse'691'_390 ::
  T_IsHeytingCommutativeRing_160 -> AgdaAny -> AgdaAny
du_inverse'691'_390 v0
  = let v1 = d_isCommutativeRing_312 (coe v0) in
    coe
      (let v2 = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v1) in
       coe
         (let v3
                = coe
                    MAlonzo.Code.Algebra.Structures.du_isRingWithoutOne_2702
                    (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2322
                       (coe v3) in
             coe
               (coe
                  MAlonzo.Code.Algebra.Structures.du_inverse'691'_1106
                  (coe MAlonzo.Code.Algebra.Structures.d_isGroup_1142 (coe v4))))))
-- Algebra.Apartness.Structures.IsHeytingCommutativeRing._.inverseˡ
d_inverse'737'_392 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny -> T_IsHeytingCommutativeRing_160 -> AgdaAny -> AgdaAny
d_inverse'737'_392 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 v11
  = du_inverse'737'_392 v11
du_inverse'737'_392 ::
  T_IsHeytingCommutativeRing_160 -> AgdaAny -> AgdaAny
du_inverse'737'_392 v0
  = let v1 = d_isCommutativeRing_312 (coe v0) in
    coe
      (let v2 = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v1) in
       coe
         (let v3
                = coe
                    MAlonzo.Code.Algebra.Structures.du_isRingWithoutOne_2702
                    (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2322
                       (coe v3) in
             coe
               (coe
                  MAlonzo.Code.Algebra.Structures.du_inverse'737'_1104
                  (coe MAlonzo.Code.Algebra.Structures.d_isGroup_1142 (coe v4))))))
-- Algebra.Apartness.Structures.IsHeytingCommutativeRing._.distrib
d_distrib_394 ::
  T_IsHeytingCommutativeRing_160 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_distrib_394 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_distrib_2700
      (coe
         MAlonzo.Code.Algebra.Structures.d_isRing_2832
         (coe d_isCommutativeRing_312 (coe v0)))
-- Algebra.Apartness.Structures.IsHeytingCommutativeRing._.distribʳ
d_distrib'691'_396 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsHeytingCommutativeRing_160 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_distrib'691'_396 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 v11
  = du_distrib'691'_396 v11
du_distrib'691'_396 ::
  T_IsHeytingCommutativeRing_160 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_distrib'691'_396 v0
  = let v1 = d_isCommutativeRing_312 (coe v0) in
    coe
      (let v2 = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Algebra.Structures.du_distrib'691'_2398
            (coe
               MAlonzo.Code.Algebra.Structures.du_isRingWithoutOne_2702
               (coe v2))))
-- Algebra.Apartness.Structures.IsHeytingCommutativeRing._.distribˡ
d_distrib'737'_398 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsHeytingCommutativeRing_160 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_distrib'737'_398 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 v11
  = du_distrib'737'_398 v11
du_distrib'737'_398 ::
  T_IsHeytingCommutativeRing_160 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_distrib'737'_398 v0
  = let v1 = d_isCommutativeRing_312 (coe v0) in
    coe
      (let v2 = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Algebra.Structures.du_distrib'737'_2396
            (coe
               MAlonzo.Code.Algebra.Structures.du_isRingWithoutOne_2702
               (coe v2))))
-- Algebra.Apartness.Structures.IsHeytingCommutativeRing._.isCommutativeSemiring
d_isCommutativeSemiring_400 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsHeytingCommutativeRing_160 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1696
d_isCommutativeSemiring_400 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 v8 v9
                            ~v10 v11
  = du_isCommutativeSemiring_400 v6 v7 v8 v9 v11
du_isCommutativeSemiring_400 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsHeytingCommutativeRing_160 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1696
du_isCommutativeSemiring_400 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Algebra.Structures.du_isCommutativeSemiring_2946
      (coe v0) (coe v1) (coe v2) (coe v3)
      (coe d_isCommutativeRing_312 (coe v4))
-- Algebra.Apartness.Structures.IsHeytingCommutativeRing._.isCommutativeSemiringWithoutOne
d_isCommutativeSemiringWithoutOne_402 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsHeytingCommutativeRing_160 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiringWithoutOne_1390
d_isCommutativeSemiringWithoutOne_402 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7
                                      v8 v9 ~v10 v11
  = du_isCommutativeSemiringWithoutOne_402 v6 v7 v8 v9 v11
du_isCommutativeSemiringWithoutOne_402 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsHeytingCommutativeRing_160 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiringWithoutOne_1390
du_isCommutativeSemiringWithoutOne_402 v0 v1 v2 v3 v4
  = let v5 = d_isCommutativeRing_312 (coe v4) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.du_isCommutativeSemiringWithoutOne_1798
         (coe
            MAlonzo.Code.Algebra.Structures.du_isCommutativeSemiring_2946
            (coe v0) (coe v1) (coe v2) (coe v3) (coe v5)))
-- Algebra.Apartness.Structures.IsHeytingCommutativeRing._.isEquivalence
d_isEquivalence_404 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsHeytingCommutativeRing_160 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_404 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
                    v11
  = du_isEquivalence_404 v11
du_isEquivalence_404 ::
  T_IsHeytingCommutativeRing_160 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
du_isEquivalence_404 v0
  = let v1 = d_isCommutativeRing_312 (coe v0) in
    coe
      (let v2 = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
            (coe
               MAlonzo.Code.Algebra.Structures.d_isMagma_478
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_isMonoid_1048
                     (coe
                        MAlonzo.Code.Algebra.Structures.d_isGroup_1142
                        (coe
                           MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2692
                           (coe v2))))))))
-- Algebra.Apartness.Structures.IsHeytingCommutativeRing._.isNearSemiring
d_isNearSemiring_406 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsHeytingCommutativeRing_160 ->
  MAlonzo.Code.Algebra.Structures.T_IsNearSemiring_1216
d_isNearSemiring_406 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 v8 v9 ~v10 v11
  = du_isNearSemiring_406 v6 v7 v8 v9 v11
du_isNearSemiring_406 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsHeytingCommutativeRing_160 ->
  MAlonzo.Code.Algebra.Structures.T_IsNearSemiring_1216
du_isNearSemiring_406 v0 v1 v2 v3 v4
  = let v5 = d_isCommutativeRing_312 (coe v4) in
    coe
      (let v6 = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v5) in
       coe
         (coe
            MAlonzo.Code.Algebra.Structures.du_isNearSemiring_2406 (coe v0)
            (coe v1) (coe v2) (coe v3)
            (coe
               MAlonzo.Code.Algebra.Structures.du_isRingWithoutOne_2702
               (coe v6))))
-- Algebra.Apartness.Structures.IsHeytingCommutativeRing._.isPartialEquivalence
d_isPartialEquivalence_408 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsHeytingCommutativeRing_160 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_408 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                           ~v10 v11
  = du_isPartialEquivalence_408 v11
du_isPartialEquivalence_408 ::
  T_IsHeytingCommutativeRing_160 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_408 v0
  = let v1 = d_isCommutativeRing_312 (coe v0) in
    coe
      (let v2 = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v1) in
       coe
         (let v3
                = coe
                    MAlonzo.Code.Algebra.Structures.du_isRingWithoutOne_2702
                    (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2322
                       (coe v3) in
             coe
               (let v5
                      = MAlonzo.Code.Algebra.Structures.d_isGroup_1142 (coe v4) in
                coe
                  (let v6
                         = MAlonzo.Code.Algebra.Structures.d_isMonoid_1048 (coe v5) in
                   coe
                     (let v7
                            = MAlonzo.Code.Algebra.Structures.d_isSemigroup_694 (coe v6) in
                      coe
                        (let v8 = MAlonzo.Code.Algebra.Structures.d_isMagma_478 (coe v7) in
                         coe
                           (coe
                              MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_42
                              (coe
                                 MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
                                 (coe v8))))))))))
-- Algebra.Apartness.Structures.IsHeytingCommutativeRing._.isRing
d_isRing_410 ::
  T_IsHeytingCommutativeRing_160 ->
  MAlonzo.Code.Algebra.Structures.T_IsRing_2670
d_isRing_410 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isRing_2832
      (coe d_isCommutativeRing_312 (coe v0))
-- Algebra.Apartness.Structures.IsHeytingCommutativeRing._.isRingWithoutOne
d_isRingWithoutOne_412 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsHeytingCommutativeRing_160 ->
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2304
d_isRingWithoutOne_412 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
                       v11
  = du_isRingWithoutOne_412 v11
du_isRingWithoutOne_412 ::
  T_IsHeytingCommutativeRing_160 ->
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2304
du_isRingWithoutOne_412 v0
  = let v1 = d_isCommutativeRing_312 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.du_isRingWithoutOne_2702
         (coe MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v1)))
-- Algebra.Apartness.Structures.IsHeytingCommutativeRing._.isSemiring
d_isSemiring_414 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsHeytingCommutativeRing_160 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1588
d_isSemiring_414 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 v8 v9 ~v10 v11
  = du_isSemiring_414 v6 v7 v8 v9 v11
du_isSemiring_414 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsHeytingCommutativeRing_160 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1588
du_isSemiring_414 v0 v1 v2 v3 v4
  = let v5 = d_isCommutativeRing_312 (coe v4) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.du_isSemiring_2800 (coe v0)
         (coe v1) (coe v2) (coe v3)
         (coe MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v5)))
-- Algebra.Apartness.Structures.IsHeytingCommutativeRing._.isSemiringWithoutAnnihilatingZero
d_isSemiringWithoutAnnihilatingZero_416 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsHeytingCommutativeRing_160 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1486
d_isSemiringWithoutAnnihilatingZero_416 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6
                                        ~v7 ~v8 ~v9 ~v10 v11
  = du_isSemiringWithoutAnnihilatingZero_416 v11
du_isSemiringWithoutAnnihilatingZero_416 ::
  T_IsHeytingCommutativeRing_160 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1486
du_isSemiringWithoutAnnihilatingZero_416 v0
  = let v1 = d_isCommutativeRing_312 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.du_isSemiringWithoutAnnihilatingZero_2798
         (coe MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v1)))
-- Algebra.Apartness.Structures.IsHeytingCommutativeRing._.isSemiringWithoutOne
d_isSemiringWithoutOne_418 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsHeytingCommutativeRing_160 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutOne_1296
d_isSemiringWithoutOne_418 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 v8 v9 ~v10
                           v11
  = du_isSemiringWithoutOne_418 v6 v7 v8 v9 v11
du_isSemiringWithoutOne_418 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsHeytingCommutativeRing_160 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutOne_1296
du_isSemiringWithoutOne_418 v0 v1 v2 v3 v4
  = let v5 = d_isCommutativeRing_312 (coe v4) in
    coe
      (let v6 = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v5) in
       coe
         (coe
            MAlonzo.Code.Algebra.Structures.du_isSemiringWithoutOne_1678
            (coe
               MAlonzo.Code.Algebra.Structures.du_isSemiring_2800 (coe v0)
               (coe v1) (coe v2) (coe v3) (coe v6))))
-- Algebra.Apartness.Structures.IsHeytingCommutativeRing._.refl
d_refl_420 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny -> T_IsHeytingCommutativeRing_160 -> AgdaAny -> AgdaAny
d_refl_420 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 v11
  = du_refl_420 v11
du_refl_420 :: T_IsHeytingCommutativeRing_160 -> AgdaAny -> AgdaAny
du_refl_420 v0
  = let v1 = d_isCommutativeRing_312 (coe v0) in
    coe
      (let v2 = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_refl_34
            (coe
               MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isMagma_478
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                     (coe
                        MAlonzo.Code.Algebra.Structures.d_isMonoid_1048
                        (coe
                           MAlonzo.Code.Algebra.Structures.d_isGroup_1142
                           (coe
                              MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2692
                              (coe v2)))))))))
-- Algebra.Apartness.Structures.IsHeytingCommutativeRing._.reflexive
d_reflexive_422 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsHeytingCommutativeRing_160 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_422 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 v11
  = du_reflexive_422 v11
du_reflexive_422 ::
  T_IsHeytingCommutativeRing_160 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_422 v0
  = let v1 = d_isCommutativeRing_312 (coe v0) in
    coe
      (let v2 = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v1) in
       coe
         (let v3
                = coe
                    MAlonzo.Code.Algebra.Structures.du_isRingWithoutOne_2702
                    (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2322
                       (coe v3) in
             coe
               (let v5
                      = MAlonzo.Code.Algebra.Structures.d_isGroup_1142 (coe v4) in
                coe
                  (let v6
                         = MAlonzo.Code.Algebra.Structures.d_isMonoid_1048 (coe v5) in
                   coe
                     (let v7
                            = MAlonzo.Code.Algebra.Structures.d_isSemigroup_694 (coe v6) in
                      coe
                        (let v8 = MAlonzo.Code.Algebra.Structures.d_isMagma_478 (coe v7) in
                         coe
                           (\ v9 v10 v11 ->
                              coe
                                MAlonzo.Code.Relation.Binary.Structures.du_reflexive_40
                                (coe MAlonzo.Code.Algebra.Structures.d_isEquivalence_184 (coe v8))
                                v9))))))))
-- Algebra.Apartness.Structures.IsHeytingCommutativeRing._.setoid
d_setoid_424 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsHeytingCommutativeRing_160 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
d_setoid_424 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 v11
  = du_setoid_424 v11
du_setoid_424 ::
  T_IsHeytingCommutativeRing_160 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
du_setoid_424 v0
  = let v1 = d_isCommutativeRing_312 (coe v0) in
    coe
      (let v2 = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v1) in
       coe
         (let v3
                = coe
                    MAlonzo.Code.Algebra.Structures.du_isRingWithoutOne_2702
                    (coe v2) in
          coe
            (let v4
                   = MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2322
                       (coe v3) in
             coe
               (let v5
                      = MAlonzo.Code.Algebra.Structures.d_isGroup_1142 (coe v4) in
                coe
                  (let v6
                         = MAlonzo.Code.Algebra.Structures.d_isMonoid_1048 (coe v5) in
                   coe
                     (let v7
                            = MAlonzo.Code.Algebra.Structures.d_isSemigroup_694 (coe v6) in
                      coe
                        (coe
                           MAlonzo.Code.Algebra.Structures.du_setoid_200
                           (coe MAlonzo.Code.Algebra.Structures.d_isMagma_478 (coe v7)))))))))
-- Algebra.Apartness.Structures.IsHeytingCommutativeRing._.sym
d_sym_426 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsHeytingCommutativeRing_160 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_426 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 v11
  = du_sym_426 v11
du_sym_426 ::
  T_IsHeytingCommutativeRing_160 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_sym_426 v0
  = let v1 = d_isCommutativeRing_312 (coe v0) in
    coe
      (let v2 = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_sym_36
            (coe
               MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isMagma_478
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                     (coe
                        MAlonzo.Code.Algebra.Structures.d_isMonoid_1048
                        (coe
                           MAlonzo.Code.Algebra.Structures.d_isGroup_1142
                           (coe
                              MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2692
                              (coe v2)))))))))
-- Algebra.Apartness.Structures.IsHeytingCommutativeRing._.trans
d_trans_428 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsHeytingCommutativeRing_160 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_428 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 v11
  = du_trans_428 v11
du_trans_428 ::
  T_IsHeytingCommutativeRing_160 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_trans_428 v0
  = let v1 = d_isCommutativeRing_312 (coe v0) in
    coe
      (let v2 = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_trans_38
            (coe
               MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isMagma_478
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                     (coe
                        MAlonzo.Code.Algebra.Structures.d_isMonoid_1048
                        (coe
                           MAlonzo.Code.Algebra.Structures.d_isGroup_1142
                           (coe
                              MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2692
                              (coe v2)))))))))
-- Algebra.Apartness.Structures.IsHeytingCommutativeRing._.uniqueʳ-⁻¹
d_unique'691''45''8315''185'_430 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsHeytingCommutativeRing_160 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_unique'691''45''8315''185'_430 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 ~v7 v8
                                 v9 ~v10 v11
  = du_unique'691''45''8315''185'_430 v6 v8 v9 v11
du_unique'691''45''8315''185'_430 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsHeytingCommutativeRing_160 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_unique'691''45''8315''185'_430 v0 v1 v2 v3
  = let v4 = d_isCommutativeRing_312 (coe v3) in
    coe
      (let v5 = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v4) in
       coe
         (let v6
                = coe
                    MAlonzo.Code.Algebra.Structures.du_isRingWithoutOne_2702
                    (coe v5) in
          coe
            (let v7
                   = MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2322
                       (coe v6) in
             coe
               (coe
                  MAlonzo.Code.Algebra.Structures.du_unique'691''45''8315''185'_1118
                  (coe v0) (coe v2) (coe v1)
                  (coe MAlonzo.Code.Algebra.Structures.d_isGroup_1142 (coe v7))))))
-- Algebra.Apartness.Structures.IsHeytingCommutativeRing._.uniqueˡ-⁻¹
d_unique'737''45''8315''185'_432 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsHeytingCommutativeRing_160 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_unique'737''45''8315''185'_432 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 ~v7 v8
                                 v9 ~v10 v11
  = du_unique'737''45''8315''185'_432 v6 v8 v9 v11
du_unique'737''45''8315''185'_432 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsHeytingCommutativeRing_160 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_unique'737''45''8315''185'_432 v0 v1 v2 v3
  = let v4 = d_isCommutativeRing_312 (coe v3) in
    coe
      (let v5 = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v4) in
       coe
         (let v6
                = coe
                    MAlonzo.Code.Algebra.Structures.du_isRingWithoutOne_2702
                    (coe v5) in
          coe
            (let v7
                   = MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2322
                       (coe v6) in
             coe
               (coe
                  MAlonzo.Code.Algebra.Structures.du_unique'737''45''8315''185'_1112
                  (coe v0) (coe v2) (coe v1)
                  (coe MAlonzo.Code.Algebra.Structures.d_isGroup_1142 (coe v7))))))
-- Algebra.Apartness.Structures.IsHeytingCommutativeRing._.zero
d_zero_434 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsHeytingCommutativeRing_160 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_zero_434 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 v8 v9 ~v10 v11
  = du_zero_434 v6 v7 v8 v9 v11
du_zero_434 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsHeytingCommutativeRing_160 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_zero_434 v0 v1 v2 v3 v4
  = let v5 = d_isCommutativeRing_312 (coe v4) in
    coe
      (let v6 = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v5) in
       coe
         (coe
            MAlonzo.Code.Algebra.Structures.du_zero_2404 (coe v0) (coe v1)
            (coe v2) (coe v3)
            (coe
               MAlonzo.Code.Algebra.Structures.du_isRingWithoutOne_2702
               (coe v6))))
-- Algebra.Apartness.Structures.IsHeytingCommutativeRing._.zeroʳ
d_zero'691'_436 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny -> T_IsHeytingCommutativeRing_160 -> AgdaAny -> AgdaAny
d_zero'691'_436 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 v8 v9 ~v10 v11
  = du_zero'691'_436 v6 v7 v8 v9 v11
du_zero'691'_436 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> T_IsHeytingCommutativeRing_160 -> AgdaAny -> AgdaAny
du_zero'691'_436 v0 v1 v2 v3 v4
  = let v5 = d_isCommutativeRing_312 (coe v4) in
    coe
      (let v6 = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v5) in
       coe
         (coe
            MAlonzo.Code.Algebra.Structures.du_zero'691'_2402 (coe v0) (coe v1)
            (coe v2) (coe v3)
            (coe
               MAlonzo.Code.Algebra.Structures.du_isRingWithoutOne_2702
               (coe v6))))
-- Algebra.Apartness.Structures.IsHeytingCommutativeRing._.zeroˡ
d_zero'737'_438 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny -> T_IsHeytingCommutativeRing_160 -> AgdaAny -> AgdaAny
d_zero'737'_438 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 v8 v9 ~v10 v11
  = du_zero'737'_438 v6 v7 v8 v9 v11
du_zero'737'_438 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> T_IsHeytingCommutativeRing_160 -> AgdaAny -> AgdaAny
du_zero'737'_438 v0 v1 v2 v3 v4
  = let v5 = d_isCommutativeRing_312 (coe v4) in
    coe
      (let v6 = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v5) in
       coe
         (coe
            MAlonzo.Code.Algebra.Structures.du_zero'737'_2400 (coe v0) (coe v1)
            (coe v2) (coe v3)
            (coe
               MAlonzo.Code.Algebra.Structures.du_isRingWithoutOne_2702
               (coe v6))))
-- Algebra.Apartness.Structures.IsHeytingCommutativeRing._._¬#_
d__'172''35'__442 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsHeytingCommutativeRing_160 -> AgdaAny -> AgdaAny -> ()
d__'172''35'__442 = erased
-- Algebra.Apartness.Structures.IsHeytingCommutativeRing._.cotrans
d_cotrans_444 ::
  T_IsHeytingCommutativeRing_160 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_cotrans_444 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_cotrans_736
      (coe d_isApartnessRelation_314 (coe v0))
-- Algebra.Apartness.Structures.IsHeytingCommutativeRing._.irrefl
d_irrefl_446 ::
  T_IsHeytingCommutativeRing_160 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_irrefl_446 = erased
-- Algebra.Apartness.Structures.IsHeytingCommutativeRing._.sym
d_sym_448 ::
  T_IsHeytingCommutativeRing_160 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_448 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_sym_734
      (coe d_isApartnessRelation_314 (coe v0))
-- Algebra.Apartness.Structures.IsHeytingCommutativeRing.#⇒invertible
d_'35''8658'invertible_454 ::
  T_IsHeytingCommutativeRing_160 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'35''8658'invertible_454 v0
  = case coe v0 of
      C_IsHeytingCommutativeRing'46'constructor_4849 v1 v2 v3 v4
        -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Apartness.Structures.IsHeytingCommutativeRing.invertible⇒#
d_invertible'8658''35'_460 ::
  T_IsHeytingCommutativeRing_160 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> AgdaAny
d_invertible'8658''35'_460 v0
  = case coe v0 of
      C_IsHeytingCommutativeRing'46'constructor_4849 v1 v2 v3 v4
        -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Apartness.Structures.IsHeytingCommutativeRing.¬#-isEquivalence
d_'172''35''45'isEquivalence_462 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsHeytingCommutativeRing_160 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_'172''35''45'isEquivalence_462 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
                                 ~v8 ~v9 ~v10 ~v11
  = du_'172''35''45'isEquivalence_462
du_'172''35''45'isEquivalence_462 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
du_'172''35''45'isEquivalence_462
  = coe
      MAlonzo.Code.Relation.Binary.Properties.ApartnessRelation.du_'172''35''45'isEquivalence_20
-- Algebra.Apartness.Structures.IsHeytingField
d_IsHeytingField_464 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 = ()
data T_IsHeytingField_464
  = C_IsHeytingField'46'constructor_16575 T_IsHeytingCommutativeRing_160
                                          (AgdaAny ->
                                           AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14)
-- Algebra.Apartness.Structures.IsHeytingField.isHeytingCommutativeRing
d_isHeytingCommutativeRing_470 ::
  T_IsHeytingField_464 -> T_IsHeytingCommutativeRing_160
d_isHeytingCommutativeRing_470 v0
  = case coe v0 of
      C_IsHeytingField'46'constructor_16575 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Apartness.Structures.IsHeytingField.tight
d_tight_472 ::
  T_IsHeytingField_464 ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_tight_472 v0
  = case coe v0 of
      C_IsHeytingField'46'constructor_16575 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Apartness.Structures.IsHeytingField._._//_
d__'47''47'__476 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny -> T_IsHeytingField_464 -> AgdaAny -> AgdaAny -> AgdaAny
d__'47''47'__476 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 ~v7 v8 ~v9 ~v10 ~v11
  = du__'47''47'__476 v6 v8
du__'47''47'__476 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny -> AgdaAny
du__'47''47'__476 v0 v1
  = coe
      MAlonzo.Code.Algebra.Structures.du__'47''47'__1096 (coe v0)
      (coe v1)
-- Algebra.Apartness.Structures.IsHeytingField._._¬#_
d__'172''35'__478 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny -> T_IsHeytingField_464 -> AgdaAny -> AgdaAny -> ()
d__'172''35'__478 = erased
-- Algebra.Apartness.Structures.IsHeytingField._.cotrans
d_cotrans_480 ::
  T_IsHeytingField_464 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_cotrans_480 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_cotrans_736
      (coe
         d_isApartnessRelation_314
         (coe d_isHeytingCommutativeRing_470 (coe v0)))
-- Algebra.Apartness.Structures.IsHeytingField._.irrefl
d_irrefl_482 ::
  T_IsHeytingField_464 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_irrefl_482 = erased
-- Algebra.Apartness.Structures.IsHeytingField._.sym
d_sym_484 ::
  T_IsHeytingField_464 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_484 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_sym_734
      (coe
         d_isApartnessRelation_314
         (coe d_isHeytingCommutativeRing_470 (coe v0)))
-- Algebra.Apartness.Structures.IsHeytingField._.#⇒invertible
d_'35''8658'invertible_486 ::
  T_IsHeytingField_464 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'35''8658'invertible_486 v0
  = coe
      d_'35''8658'invertible_454
      (coe d_isHeytingCommutativeRing_470 (coe v0))
-- Algebra.Apartness.Structures.IsHeytingField._.*-assoc
d_'42''45'assoc_488 ::
  T_IsHeytingField_464 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'42''45'assoc_488 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'42''45'assoc_2696
      (coe
         MAlonzo.Code.Algebra.Structures.d_isRing_2832
         (coe
            d_isCommutativeRing_312
            (coe d_isHeytingCommutativeRing_470 (coe v0))))
-- Algebra.Apartness.Structures.IsHeytingField._.*-comm
d_'42''45'comm_490 ::
  T_IsHeytingField_464 -> AgdaAny -> AgdaAny -> AgdaAny
d_'42''45'comm_490 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'42''45'comm_2834
      (coe
         d_isCommutativeRing_312
         (coe d_isHeytingCommutativeRing_470 (coe v0)))
-- Algebra.Apartness.Structures.IsHeytingField._.*-cong
d_'42''45'cong_492 ::
  T_IsHeytingField_464 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'42''45'cong_492 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'42''45'cong_2694
      (coe
         MAlonzo.Code.Algebra.Structures.d_isRing_2832
         (coe
            d_isCommutativeRing_312
            (coe d_isHeytingCommutativeRing_470 (coe v0))))
-- Algebra.Apartness.Structures.IsHeytingField._.∙-congʳ
d_'8729''45'cong'691'_494 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsHeytingField_464 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'691'_494 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 v8 v9 ~v10
                          v11
  = du_'8729''45'cong'691'_494 v6 v7 v8 v9 v11
du_'8729''45'cong'691'_494 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsHeytingField_464 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'691'_494 v0 v1 v2 v3 v4
  = let v5 = d_isHeytingCommutativeRing_470 (coe v4) in
    coe
      (let v6 = d_isCommutativeRing_312 (coe v5) in
       coe
         (let v7 = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v6) in
          coe
            (let v8
                   = coe
                       MAlonzo.Code.Algebra.Structures.du_isRingWithoutOne_2702
                       (coe v7) in
             coe
               (let v9
                      = coe
                          MAlonzo.Code.Algebra.Structures.du_isNearSemiring_2406 (coe v0)
                          (coe v1) (coe v2) (coe v3) (coe v8) in
                coe
                  (let v10
                         = coe
                             MAlonzo.Code.Algebra.Structures.du_'42''45'isMagma_1280 (coe v9) in
                   coe
                     (let v11
                            = coe MAlonzo.Code.Algebra.Structures.du_setoid_200 (coe v10) in
                      coe
                        (let v12
                               = MAlonzo.Code.Algebra.Structures.d_'8729''45'cong_186 (coe v10) in
                         coe
                           (coe
                              MAlonzo.Code.Algebra.Consequences.Base.du_'8729''45'cong'691'_46
                              (coe v12)
                              (coe
                                 MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                                 (coe
                                    MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                                    (coe v11)))))))))))
-- Algebra.Apartness.Structures.IsHeytingField._.∙-congˡ
d_'8729''45'cong'737'_496 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsHeytingField_464 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'737'_496 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 v8 v9 ~v10
                          v11
  = du_'8729''45'cong'737'_496 v6 v7 v8 v9 v11
du_'8729''45'cong'737'_496 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsHeytingField_464 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'737'_496 v0 v1 v2 v3 v4
  = let v5 = d_isHeytingCommutativeRing_470 (coe v4) in
    coe
      (let v6 = d_isCommutativeRing_312 (coe v5) in
       coe
         (let v7 = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v6) in
          coe
            (let v8
                   = coe
                       MAlonzo.Code.Algebra.Structures.du_isRingWithoutOne_2702
                       (coe v7) in
             coe
               (let v9
                      = coe
                          MAlonzo.Code.Algebra.Structures.du_isNearSemiring_2406 (coe v0)
                          (coe v1) (coe v2) (coe v3) (coe v8) in
                coe
                  (let v10
                         = coe
                             MAlonzo.Code.Algebra.Structures.du_'42''45'isMagma_1280 (coe v9) in
                   coe
                     (let v11
                            = coe MAlonzo.Code.Algebra.Structures.du_setoid_200 (coe v10) in
                      coe
                        (let v12
                               = MAlonzo.Code.Algebra.Structures.d_'8729''45'cong_186 (coe v10) in
                         coe
                           (coe
                              MAlonzo.Code.Algebra.Consequences.Base.du_'8729''45'cong'737'_42
                              (coe v12)
                              (coe
                                 MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                                 (coe
                                    MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                                    (coe v11)))))))))))
-- Algebra.Apartness.Structures.IsHeytingField._.*-identity
d_'42''45'identity_498 ::
  T_IsHeytingField_464 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'42''45'identity_498 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'42''45'identity_2698
      (coe
         MAlonzo.Code.Algebra.Structures.d_isRing_2832
         (coe
            d_isCommutativeRing_312
            (coe d_isHeytingCommutativeRing_470 (coe v0))))
-- Algebra.Apartness.Structures.IsHeytingField._.identityʳ
d_identity'691'_500 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> T_IsHeytingField_464 -> AgdaAny -> AgdaAny
d_identity'691'_500 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 v8 v9 ~v10 v11
  = du_identity'691'_500 v6 v7 v8 v9 v11
du_identity'691'_500 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> T_IsHeytingField_464 -> AgdaAny -> AgdaAny
du_identity'691'_500 v0 v1 v2 v3 v4
  = let v5 = d_isHeytingCommutativeRing_470 (coe v4) in
    coe
      (let v6 = d_isCommutativeRing_312 (coe v5) in
       coe
         (let v7 = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v6) in
          coe
            (coe
               MAlonzo.Code.Algebra.Structures.du_identity'691'_726
               (coe
                  MAlonzo.Code.Algebra.Structures.du_'42''45'isMonoid_2790 (coe v0)
                  (coe v1) (coe v2) (coe v3) (coe v7)))))
-- Algebra.Apartness.Structures.IsHeytingField._.identityˡ
d_identity'737'_502 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> T_IsHeytingField_464 -> AgdaAny -> AgdaAny
d_identity'737'_502 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 v8 v9 ~v10 v11
  = du_identity'737'_502 v6 v7 v8 v9 v11
du_identity'737'_502 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> T_IsHeytingField_464 -> AgdaAny -> AgdaAny
du_identity'737'_502 v0 v1 v2 v3 v4
  = let v5 = d_isHeytingCommutativeRing_470 (coe v4) in
    coe
      (let v6 = d_isCommutativeRing_312 (coe v5) in
       coe
         (let v7 = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v6) in
          coe
            (coe
               MAlonzo.Code.Algebra.Structures.du_identity'737'_724
               (coe
                  MAlonzo.Code.Algebra.Structures.du_'42''45'isMonoid_2790 (coe v0)
                  (coe v1) (coe v2) (coe v3) (coe v7)))))
-- Algebra.Apartness.Structures.IsHeytingField._.isCommutativeMagma
d_isCommutativeMagma_504 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsHeytingField_464 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMagma_210
d_isCommutativeMagma_504 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 v8 v9 ~v10
                         v11
  = du_isCommutativeMagma_504 v6 v7 v8 v9 v11
du_isCommutativeMagma_504 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsHeytingField_464 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMagma_210
du_isCommutativeMagma_504 v0 v1 v2 v3 v4
  = let v5 = d_isHeytingCommutativeRing_470 (coe v4) in
    coe
      (let v6 = d_isCommutativeRing_312 (coe v5) in
       coe
         (let v7
                = coe
                    MAlonzo.Code.Algebra.Structures.du_isCommutativeSemiring_2946
                    (coe v0) (coe v1) (coe v2) (coe v3) (coe v6) in
          coe
            (let v8
                   = coe
                       MAlonzo.Code.Algebra.Structures.du_isCommutativeSemiringWithoutOne_1798
                       (coe v7) in
             coe
               (coe
                  MAlonzo.Code.Algebra.Structures.du_isCommutativeMagma_584
                  (coe
                     MAlonzo.Code.Algebra.Structures.du_'42''45'isCommutativeSemigroup_1472
                     (coe v8))))))
-- Algebra.Apartness.Structures.IsHeytingField._.*-isCommutativeMonoid
d_'42''45'isCommutativeMonoid_506 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsHeytingField_464 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_734
d_'42''45'isCommutativeMonoid_506 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 v8
                                  v9 ~v10 v11
  = du_'42''45'isCommutativeMonoid_506 v6 v7 v8 v9 v11
du_'42''45'isCommutativeMonoid_506 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsHeytingField_464 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_734
du_'42''45'isCommutativeMonoid_506 v0 v1 v2 v3 v4
  = let v5 = d_isHeytingCommutativeRing_470 (coe v4) in
    coe
      (let v6 = d_isCommutativeRing_312 (coe v5) in
       coe
         (coe
            MAlonzo.Code.Algebra.Structures.du_'42''45'isCommutativeMonoid_1806
            (coe
               MAlonzo.Code.Algebra.Structures.du_isCommutativeSemiring_2946
               (coe v0) (coe v1) (coe v2) (coe v3) (coe v6))))
-- Algebra.Apartness.Structures.IsHeytingField._.*-isCommutativeSemigroup
d_'42''45'isCommutativeSemigroup_508 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsHeytingField_464 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_546
d_'42''45'isCommutativeSemigroup_508 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7
                                     v8 v9 ~v10 v11
  = du_'42''45'isCommutativeSemigroup_508 v6 v7 v8 v9 v11
du_'42''45'isCommutativeSemigroup_508 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsHeytingField_464 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_546
du_'42''45'isCommutativeSemigroup_508 v0 v1 v2 v3 v4
  = let v5 = d_isHeytingCommutativeRing_470 (coe v4) in
    coe
      (let v6 = d_isCommutativeRing_312 (coe v5) in
       coe
         (let v7
                = coe
                    MAlonzo.Code.Algebra.Structures.du_isCommutativeSemiring_2946
                    (coe v0) (coe v1) (coe v2) (coe v3) (coe v6) in
          coe
            (coe
               MAlonzo.Code.Algebra.Structures.du_'42''45'isCommutativeSemigroup_1472
               (coe
                  MAlonzo.Code.Algebra.Structures.du_isCommutativeSemiringWithoutOne_1798
                  (coe v7)))))
-- Algebra.Apartness.Structures.IsHeytingField._.*-isMagma
d_'42''45'isMagma_510 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsHeytingField_464 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176
d_'42''45'isMagma_510 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 v8 v9 ~v10 v11
  = du_'42''45'isMagma_510 v6 v7 v8 v9 v11
du_'42''45'isMagma_510 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsHeytingField_464 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176
du_'42''45'isMagma_510 v0 v1 v2 v3 v4
  = let v5 = d_isHeytingCommutativeRing_470 (coe v4) in
    coe
      (let v6 = d_isCommutativeRing_312 (coe v5) in
       coe
         (let v7 = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v6) in
          coe
            (let v8
                   = coe
                       MAlonzo.Code.Algebra.Structures.du_isRingWithoutOne_2702
                       (coe v7) in
             coe
               (coe
                  MAlonzo.Code.Algebra.Structures.du_'42''45'isMagma_1280
                  (coe
                     MAlonzo.Code.Algebra.Structures.du_isNearSemiring_2406 (coe v0)
                     (coe v1) (coe v2) (coe v3) (coe v8))))))
-- Algebra.Apartness.Structures.IsHeytingField._.*-isMonoid
d_'42''45'isMonoid_512 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsHeytingField_464 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_684
d_'42''45'isMonoid_512 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 v8 v9 ~v10 v11
  = du_'42''45'isMonoid_512 v6 v7 v8 v9 v11
du_'42''45'isMonoid_512 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsHeytingField_464 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_684
du_'42''45'isMonoid_512 v0 v1 v2 v3 v4
  = let v5 = d_isHeytingCommutativeRing_470 (coe v4) in
    coe
      (let v6 = d_isCommutativeRing_312 (coe v5) in
       coe
         (coe
            MAlonzo.Code.Algebra.Structures.du_'42''45'isMonoid_2790 (coe v0)
            (coe v1) (coe v2) (coe v3)
            (coe MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v6))))
-- Algebra.Apartness.Structures.IsHeytingField._.*-isSemigroup
d_'42''45'isSemigroup_514 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsHeytingField_464 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_470
d_'42''45'isSemigroup_514 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 v8 v9 ~v10
                          v11
  = du_'42''45'isSemigroup_514 v6 v7 v8 v9 v11
du_'42''45'isSemigroup_514 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsHeytingField_464 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_470
du_'42''45'isSemigroup_514 v0 v1 v2 v3 v4
  = let v5 = d_isHeytingCommutativeRing_470 (coe v4) in
    coe
      (let v6 = d_isCommutativeRing_312 (coe v5) in
       coe
         (let v7 = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v6) in
          coe
            (let v8
                   = coe
                       MAlonzo.Code.Algebra.Structures.du_isRingWithoutOne_2702
                       (coe v7) in
             coe
               (coe
                  MAlonzo.Code.Algebra.Structures.du_'42''45'isSemigroup_1282
                  (coe
                     MAlonzo.Code.Algebra.Structures.du_isNearSemiring_2406 (coe v0)
                     (coe v1) (coe v2) (coe v3) (coe v8))))))
-- Algebra.Apartness.Structures.IsHeytingField._.assoc
d_assoc_516 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsHeytingField_464 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_assoc_516 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 v11
  = du_assoc_516 v11
du_assoc_516 ::
  T_IsHeytingField_464 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_assoc_516 v0
  = let v1 = d_isHeytingCommutativeRing_470 (coe v0) in
    coe
      (let v2 = d_isCommutativeRing_312 (coe v1) in
       coe
         (let v3 = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Algebra.Structures.d_assoc_480
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_isMonoid_1048
                     (coe
                        MAlonzo.Code.Algebra.Structures.d_isGroup_1142
                        (coe
                           MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2692
                           (coe v3))))))))
-- Algebra.Apartness.Structures.IsHeytingField._.comm
d_comm_518 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny -> T_IsHeytingField_464 -> AgdaAny -> AgdaAny -> AgdaAny
d_comm_518 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 v11
  = du_comm_518 v11
du_comm_518 ::
  T_IsHeytingField_464 -> AgdaAny -> AgdaAny -> AgdaAny
du_comm_518 v0
  = let v1 = d_isHeytingCommutativeRing_470 (coe v0) in
    coe
      (let v2 = d_isCommutativeRing_312 (coe v1) in
       coe
         (let v3 = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Algebra.Structures.d_comm_1144
               (coe
                  MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2692
                  (coe v3)))))
-- Algebra.Apartness.Structures.IsHeytingField._.∙-cong
d_'8729''45'cong_520 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsHeytingField_464 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong_520 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
                     v11
  = du_'8729''45'cong_520 v11
du_'8729''45'cong_520 ::
  T_IsHeytingField_464 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong_520 v0
  = let v1 = d_isHeytingCommutativeRing_470 (coe v0) in
    coe
      (let v2 = d_isCommutativeRing_312 (coe v1) in
       coe
         (let v3 = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Algebra.Structures.d_'8729''45'cong_186
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isMagma_478
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                     (coe
                        MAlonzo.Code.Algebra.Structures.d_isMonoid_1048
                        (coe
                           MAlonzo.Code.Algebra.Structures.d_isGroup_1142
                           (coe
                              MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2692
                              (coe v3)))))))))
-- Algebra.Apartness.Structures.IsHeytingField._.∙-congʳ
d_'8729''45'cong'691'_522 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsHeytingField_464 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'691'_522 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                          ~v10 v11
  = du_'8729''45'cong'691'_522 v11
du_'8729''45'cong'691'_522 ::
  T_IsHeytingField_464 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'691'_522 v0
  = let v1 = d_isHeytingCommutativeRing_470 (coe v0) in
    coe
      (let v2 = d_isCommutativeRing_312 (coe v1) in
       coe
         (let v3 = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v2) in
          coe
            (let v4
                   = coe
                       MAlonzo.Code.Algebra.Structures.du_isRingWithoutOne_2702
                       (coe v3) in
             coe
               (let v5
                      = MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2322
                          (coe v4) in
                coe
                  (let v6
                         = MAlonzo.Code.Algebra.Structures.d_isGroup_1142 (coe v5) in
                   coe
                     (let v7
                            = MAlonzo.Code.Algebra.Structures.d_isMonoid_1048 (coe v6) in
                      coe
                        (let v8
                               = MAlonzo.Code.Algebra.Structures.d_isSemigroup_694 (coe v7) in
                         coe
                           (let v9 = MAlonzo.Code.Algebra.Structures.d_isMagma_478 (coe v8) in
                            coe
                              (let v10
                                     = coe MAlonzo.Code.Algebra.Structures.du_setoid_200 (coe v9) in
                               coe
                                 (let v11
                                        = MAlonzo.Code.Algebra.Structures.d_'8729''45'cong_186
                                            (coe v9) in
                                  coe
                                    (coe
                                       MAlonzo.Code.Algebra.Consequences.Base.du_'8729''45'cong'691'_46
                                       (coe v11)
                                       (coe
                                          MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                                          (coe
                                             MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                                             (coe v10))))))))))))))
-- Algebra.Apartness.Structures.IsHeytingField._.∙-congˡ
d_'8729''45'cong'737'_524 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsHeytingField_464 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'737'_524 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                          ~v10 v11
  = du_'8729''45'cong'737'_524 v11
du_'8729''45'cong'737'_524 ::
  T_IsHeytingField_464 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'737'_524 v0
  = let v1 = d_isHeytingCommutativeRing_470 (coe v0) in
    coe
      (let v2 = d_isCommutativeRing_312 (coe v1) in
       coe
         (let v3 = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v2) in
          coe
            (let v4
                   = coe
                       MAlonzo.Code.Algebra.Structures.du_isRingWithoutOne_2702
                       (coe v3) in
             coe
               (let v5
                      = MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2322
                          (coe v4) in
                coe
                  (let v6
                         = MAlonzo.Code.Algebra.Structures.d_isGroup_1142 (coe v5) in
                   coe
                     (let v7
                            = MAlonzo.Code.Algebra.Structures.d_isMonoid_1048 (coe v6) in
                      coe
                        (let v8
                               = MAlonzo.Code.Algebra.Structures.d_isSemigroup_694 (coe v7) in
                         coe
                           (let v9 = MAlonzo.Code.Algebra.Structures.d_isMagma_478 (coe v8) in
                            coe
                              (let v10
                                     = coe MAlonzo.Code.Algebra.Structures.du_setoid_200 (coe v9) in
                               coe
                                 (let v11
                                        = MAlonzo.Code.Algebra.Structures.d_'8729''45'cong_186
                                            (coe v9) in
                                  coe
                                    (coe
                                       MAlonzo.Code.Algebra.Consequences.Base.du_'8729''45'cong'737'_42
                                       (coe v11)
                                       (coe
                                          MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                                          (coe
                                             MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                                             (coe v10))))))))))))))
-- Algebra.Apartness.Structures.IsHeytingField._.identity
d_identity_526 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsHeytingField_464 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_526 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 v11
  = du_identity_526 v11
du_identity_526 ::
  T_IsHeytingField_464 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_identity_526 v0
  = let v1 = d_isHeytingCommutativeRing_470 (coe v0) in
    coe
      (let v2 = d_isCommutativeRing_312 (coe v1) in
       coe
         (let v3 = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Algebra.Structures.d_identity_696
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isMonoid_1048
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_isGroup_1142
                     (coe
                        MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2692
                        (coe v3)))))))
-- Algebra.Apartness.Structures.IsHeytingField._.identityʳ
d_identity'691'_528 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> T_IsHeytingField_464 -> AgdaAny -> AgdaAny
d_identity'691'_528 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
                    v11
  = du_identity'691'_528 v11
du_identity'691'_528 :: T_IsHeytingField_464 -> AgdaAny -> AgdaAny
du_identity'691'_528 v0
  = let v1 = d_isHeytingCommutativeRing_470 (coe v0) in
    coe
      (let v2 = d_isCommutativeRing_312 (coe v1) in
       coe
         (let v3 = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v2) in
          coe
            (let v4
                   = coe
                       MAlonzo.Code.Algebra.Structures.du_isRingWithoutOne_2702
                       (coe v3) in
             coe
               (let v5
                      = MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2322
                          (coe v4) in
                coe
                  (let v6
                         = MAlonzo.Code.Algebra.Structures.d_isGroup_1142 (coe v5) in
                   coe
                     (coe
                        MAlonzo.Code.Algebra.Structures.du_identity'691'_726
                        (coe
                           MAlonzo.Code.Algebra.Structures.d_isMonoid_1048 (coe v6))))))))
-- Algebra.Apartness.Structures.IsHeytingField._.identityˡ
d_identity'737'_530 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> T_IsHeytingField_464 -> AgdaAny -> AgdaAny
d_identity'737'_530 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
                    v11
  = du_identity'737'_530 v11
du_identity'737'_530 :: T_IsHeytingField_464 -> AgdaAny -> AgdaAny
du_identity'737'_530 v0
  = let v1 = d_isHeytingCommutativeRing_470 (coe v0) in
    coe
      (let v2 = d_isCommutativeRing_312 (coe v1) in
       coe
         (let v3 = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v2) in
          coe
            (let v4
                   = coe
                       MAlonzo.Code.Algebra.Structures.du_isRingWithoutOne_2702
                       (coe v3) in
             coe
               (let v5
                      = MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2322
                          (coe v4) in
                coe
                  (let v6
                         = MAlonzo.Code.Algebra.Structures.d_isGroup_1142 (coe v5) in
                   coe
                     (coe
                        MAlonzo.Code.Algebra.Structures.du_identity'737'_724
                        (coe
                           MAlonzo.Code.Algebra.Structures.d_isMonoid_1048 (coe v6))))))))
-- Algebra.Apartness.Structures.IsHeytingField._.+-isAbelianGroup
d_'43''45'isAbelianGroup_532 ::
  T_IsHeytingField_464 ->
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1130
d_'43''45'isAbelianGroup_532 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2692
      (coe
         MAlonzo.Code.Algebra.Structures.d_isRing_2832
         (coe
            d_isCommutativeRing_312
            (coe d_isHeytingCommutativeRing_470 (coe v0))))
-- Algebra.Apartness.Structures.IsHeytingField._.isCommutativeMagma
d_isCommutativeMagma_534 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsHeytingField_464 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMagma_210
d_isCommutativeMagma_534 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                         ~v10 v11
  = du_isCommutativeMagma_534 v11
du_isCommutativeMagma_534 ::
  T_IsHeytingField_464 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMagma_210
du_isCommutativeMagma_534 v0
  = let v1 = d_isHeytingCommutativeRing_470 (coe v0) in
    coe
      (let v2 = d_isCommutativeRing_312 (coe v1) in
       coe
         (let v3 = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v2) in
          coe
            (let v4
                   = coe
                       MAlonzo.Code.Algebra.Structures.du_isRingWithoutOne_2702
                       (coe v3) in
             coe
               (let v5
                      = MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2322
                          (coe v4) in
                coe
                  (let v6
                         = coe
                             MAlonzo.Code.Algebra.Structures.du_isCommutativeMonoid_1202
                             (coe v5) in
                   coe
                     (coe
                        MAlonzo.Code.Algebra.Structures.du_isCommutativeMagma_584
                        (coe
                           MAlonzo.Code.Algebra.Structures.du_isCommutativeSemigroup_784
                           (coe v6))))))))
-- Algebra.Apartness.Structures.IsHeytingField._.isCommutativeMonoid
d_isCommutativeMonoid_536 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsHeytingField_464 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_734
d_isCommutativeMonoid_536 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                          ~v10 v11
  = du_isCommutativeMonoid_536 v11
du_isCommutativeMonoid_536 ::
  T_IsHeytingField_464 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_734
du_isCommutativeMonoid_536 v0
  = let v1 = d_isHeytingCommutativeRing_470 (coe v0) in
    coe
      (let v2 = d_isCommutativeRing_312 (coe v1) in
       coe
         (let v3 = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v2) in
          coe
            (let v4
                   = coe
                       MAlonzo.Code.Algebra.Structures.du_isRingWithoutOne_2702
                       (coe v3) in
             coe
               (coe
                  MAlonzo.Code.Algebra.Structures.du_isCommutativeMonoid_1202
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2322
                     (coe v4))))))
-- Algebra.Apartness.Structures.IsHeytingField._.isCommutativeSemigroup
d_isCommutativeSemigroup_538 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsHeytingField_464 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_546
d_isCommutativeSemigroup_538 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8
                             ~v9 ~v10 v11
  = du_isCommutativeSemigroup_538 v11
du_isCommutativeSemigroup_538 ::
  T_IsHeytingField_464 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_546
du_isCommutativeSemigroup_538 v0
  = let v1 = d_isHeytingCommutativeRing_470 (coe v0) in
    coe
      (let v2 = d_isCommutativeRing_312 (coe v1) in
       coe
         (let v3 = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v2) in
          coe
            (let v4
                   = coe
                       MAlonzo.Code.Algebra.Structures.du_isRingWithoutOne_2702
                       (coe v3) in
             coe
               (let v5
                      = MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2322
                          (coe v4) in
                coe
                  (coe
                     MAlonzo.Code.Algebra.Structures.du_isCommutativeSemigroup_784
                     (coe
                        MAlonzo.Code.Algebra.Structures.du_isCommutativeMonoid_1202
                        (coe v5)))))))
-- Algebra.Apartness.Structures.IsHeytingField._.isGroup
d_isGroup_540 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsHeytingField_464 ->
  MAlonzo.Code.Algebra.Structures.T_IsGroup_1034
d_isGroup_540 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 v11
  = du_isGroup_540 v11
du_isGroup_540 ::
  T_IsHeytingField_464 ->
  MAlonzo.Code.Algebra.Structures.T_IsGroup_1034
du_isGroup_540 v0
  = let v1 = d_isHeytingCommutativeRing_470 (coe v0) in
    coe
      (let v2 = d_isCommutativeRing_312 (coe v1) in
       coe
         (let v3 = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Algebra.Structures.d_isGroup_1142
               (coe
                  MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2692
                  (coe v3)))))
-- Algebra.Apartness.Structures.IsHeytingField._.isInvertibleMagma
d_isInvertibleMagma_542 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsHeytingField_464 ->
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleMagma_922
d_isInvertibleMagma_542 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                        ~v10 v11
  = du_isInvertibleMagma_542 v11
du_isInvertibleMagma_542 ::
  T_IsHeytingField_464 ->
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleMagma_922
du_isInvertibleMagma_542 v0
  = let v1 = d_isHeytingCommutativeRing_470 (coe v0) in
    coe
      (let v2 = d_isCommutativeRing_312 (coe v1) in
       coe
         (let v3 = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v2) in
          coe
            (let v4
                   = coe
                       MAlonzo.Code.Algebra.Structures.du_isRingWithoutOne_2702
                       (coe v3) in
             coe
               (let v5
                      = MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2322
                          (coe v4) in
                coe
                  (coe
                     MAlonzo.Code.Algebra.Structures.du_isInvertibleMagma_1120
                     (coe MAlonzo.Code.Algebra.Structures.d_isGroup_1142 (coe v5)))))))
-- Algebra.Apartness.Structures.IsHeytingField._.isInvertibleUnitalMagma
d_isInvertibleUnitalMagma_544 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsHeytingField_464 ->
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleUnitalMagma_974
d_isInvertibleUnitalMagma_544 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8
                              ~v9 ~v10 v11
  = du_isInvertibleUnitalMagma_544 v11
du_isInvertibleUnitalMagma_544 ::
  T_IsHeytingField_464 ->
  MAlonzo.Code.Algebra.Structures.T_IsInvertibleUnitalMagma_974
du_isInvertibleUnitalMagma_544 v0
  = let v1 = d_isHeytingCommutativeRing_470 (coe v0) in
    coe
      (let v2 = d_isCommutativeRing_312 (coe v1) in
       coe
         (let v3 = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v2) in
          coe
            (let v4
                   = coe
                       MAlonzo.Code.Algebra.Structures.du_isRingWithoutOne_2702
                       (coe v3) in
             coe
               (let v5
                      = MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2322
                          (coe v4) in
                coe
                  (coe
                     MAlonzo.Code.Algebra.Structures.du_isInvertibleUnitalMagma_1122
                     (coe MAlonzo.Code.Algebra.Structures.d_isGroup_1142 (coe v5)))))))
-- Algebra.Apartness.Structures.IsHeytingField._.isMagma
d_isMagma_546 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsHeytingField_464 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176
d_isMagma_546 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 v11
  = du_isMagma_546 v11
du_isMagma_546 ::
  T_IsHeytingField_464 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176
du_isMagma_546 v0
  = let v1 = d_isHeytingCommutativeRing_470 (coe v0) in
    coe
      (let v2 = d_isCommutativeRing_312 (coe v1) in
       coe
         (let v3 = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Algebra.Structures.d_isMagma_478
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_isMonoid_1048
                     (coe
                        MAlonzo.Code.Algebra.Structures.d_isGroup_1142
                        (coe
                           MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2692
                           (coe v3))))))))
-- Algebra.Apartness.Structures.IsHeytingField._.isMonoid
d_isMonoid_548 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsHeytingField_464 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_684
d_isMonoid_548 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 v11
  = du_isMonoid_548 v11
du_isMonoid_548 ::
  T_IsHeytingField_464 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_684
du_isMonoid_548 v0
  = let v1 = d_isHeytingCommutativeRing_470 (coe v0) in
    coe
      (let v2 = d_isCommutativeRing_312 (coe v1) in
       coe
         (let v3 = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Algebra.Structures.d_isMonoid_1048
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isGroup_1142
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2692
                     (coe v3))))))
-- Algebra.Apartness.Structures.IsHeytingField._.isSemigroup
d_isSemigroup_550 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsHeytingField_464 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_470
d_isSemigroup_550 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 v11
  = du_isSemigroup_550 v11
du_isSemigroup_550 ::
  T_IsHeytingField_464 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_470
du_isSemigroup_550 v0
  = let v1 = d_isHeytingCommutativeRing_470 (coe v0) in
    coe
      (let v2 = d_isCommutativeRing_312 (coe v1) in
       coe
         (let v3 = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isMonoid_1048
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_isGroup_1142
                     (coe
                        MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2692
                        (coe v3)))))))
-- Algebra.Apartness.Structures.IsHeytingField._.isUnitalMagma
d_isUnitalMagma_552 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsHeytingField_464 ->
  MAlonzo.Code.Algebra.Structures.T_IsUnitalMagma_640
d_isUnitalMagma_552 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
                    v11
  = du_isUnitalMagma_552 v11
du_isUnitalMagma_552 ::
  T_IsHeytingField_464 ->
  MAlonzo.Code.Algebra.Structures.T_IsUnitalMagma_640
du_isUnitalMagma_552 v0
  = let v1 = d_isHeytingCommutativeRing_470 (coe v0) in
    coe
      (let v2 = d_isCommutativeRing_312 (coe v1) in
       coe
         (let v3 = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v2) in
          coe
            (let v4
                   = coe
                       MAlonzo.Code.Algebra.Structures.du_isRingWithoutOne_2702
                       (coe v3) in
             coe
               (let v5
                      = MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2322
                          (coe v4) in
                coe
                  (let v6
                         = MAlonzo.Code.Algebra.Structures.d_isGroup_1142 (coe v5) in
                   coe
                     (coe
                        MAlonzo.Code.Algebra.Structures.du_isUnitalMagma_728
                        (coe
                           MAlonzo.Code.Algebra.Structures.d_isMonoid_1048 (coe v6))))))))
-- Algebra.Apartness.Structures.IsHeytingField._.⁻¹-cong
d_'8315''185''45'cong_554 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsHeytingField_464 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8315''185''45'cong_554 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                          ~v10 v11
  = du_'8315''185''45'cong_554 v11
du_'8315''185''45'cong_554 ::
  T_IsHeytingField_464 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8315''185''45'cong_554 v0
  = let v1 = d_isHeytingCommutativeRing_470 (coe v0) in
    coe
      (let v2 = d_isCommutativeRing_312 (coe v1) in
       coe
         (let v3 = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Algebra.Structures.d_'8315''185''45'cong_1052
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isGroup_1142
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2692
                     (coe v3))))))
-- Algebra.Apartness.Structures.IsHeytingField._.inverse
d_inverse_556 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsHeytingField_464 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inverse_556 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 v11
  = du_inverse_556 v11
du_inverse_556 ::
  T_IsHeytingField_464 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_inverse_556 v0
  = let v1 = d_isHeytingCommutativeRing_470 (coe v0) in
    coe
      (let v2 = d_isCommutativeRing_312 (coe v1) in
       coe
         (let v3 = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Algebra.Structures.d_inverse_1050
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isGroup_1142
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2692
                     (coe v3))))))
-- Algebra.Apartness.Structures.IsHeytingField._.inverseʳ
d_inverse'691'_558 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> T_IsHeytingField_464 -> AgdaAny -> AgdaAny
d_inverse'691'_558 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 v11
  = du_inverse'691'_558 v11
du_inverse'691'_558 :: T_IsHeytingField_464 -> AgdaAny -> AgdaAny
du_inverse'691'_558 v0
  = let v1 = d_isHeytingCommutativeRing_470 (coe v0) in
    coe
      (let v2 = d_isCommutativeRing_312 (coe v1) in
       coe
         (let v3 = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v2) in
          coe
            (let v4
                   = coe
                       MAlonzo.Code.Algebra.Structures.du_isRingWithoutOne_2702
                       (coe v3) in
             coe
               (let v5
                      = MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2322
                          (coe v4) in
                coe
                  (coe
                     MAlonzo.Code.Algebra.Structures.du_inverse'691'_1106
                     (coe MAlonzo.Code.Algebra.Structures.d_isGroup_1142 (coe v5)))))))
-- Algebra.Apartness.Structures.IsHeytingField._.inverseˡ
d_inverse'737'_560 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> T_IsHeytingField_464 -> AgdaAny -> AgdaAny
d_inverse'737'_560 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 v11
  = du_inverse'737'_560 v11
du_inverse'737'_560 :: T_IsHeytingField_464 -> AgdaAny -> AgdaAny
du_inverse'737'_560 v0
  = let v1 = d_isHeytingCommutativeRing_470 (coe v0) in
    coe
      (let v2 = d_isCommutativeRing_312 (coe v1) in
       coe
         (let v3 = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v2) in
          coe
            (let v4
                   = coe
                       MAlonzo.Code.Algebra.Structures.du_isRingWithoutOne_2702
                       (coe v3) in
             coe
               (let v5
                      = MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2322
                          (coe v4) in
                coe
                  (coe
                     MAlonzo.Code.Algebra.Structures.du_inverse'737'_1104
                     (coe MAlonzo.Code.Algebra.Structures.d_isGroup_1142 (coe v5)))))))
-- Algebra.Apartness.Structures.IsHeytingField._.distrib
d_distrib_562 ::
  T_IsHeytingField_464 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_distrib_562 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_distrib_2700
      (coe
         MAlonzo.Code.Algebra.Structures.d_isRing_2832
         (coe
            d_isCommutativeRing_312
            (coe d_isHeytingCommutativeRing_470 (coe v0))))
-- Algebra.Apartness.Structures.IsHeytingField._.distribʳ
d_distrib'691'_564 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsHeytingField_464 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_distrib'691'_564 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 v11
  = du_distrib'691'_564 v11
du_distrib'691'_564 ::
  T_IsHeytingField_464 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_distrib'691'_564 v0
  = let v1 = d_isHeytingCommutativeRing_470 (coe v0) in
    coe
      (let v2 = d_isCommutativeRing_312 (coe v1) in
       coe
         (let v3 = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Algebra.Structures.du_distrib'691'_2398
               (coe
                  MAlonzo.Code.Algebra.Structures.du_isRingWithoutOne_2702
                  (coe v3)))))
-- Algebra.Apartness.Structures.IsHeytingField._.distribˡ
d_distrib'737'_566 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsHeytingField_464 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_distrib'737'_566 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 v11
  = du_distrib'737'_566 v11
du_distrib'737'_566 ::
  T_IsHeytingField_464 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_distrib'737'_566 v0
  = let v1 = d_isHeytingCommutativeRing_470 (coe v0) in
    coe
      (let v2 = d_isCommutativeRing_312 (coe v1) in
       coe
         (let v3 = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Algebra.Structures.du_distrib'737'_2396
               (coe
                  MAlonzo.Code.Algebra.Structures.du_isRingWithoutOne_2702
                  (coe v3)))))
-- Algebra.Apartness.Structures.IsHeytingField._.invertible⇒#
d_invertible'8658''35'_568 ::
  T_IsHeytingField_464 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> AgdaAny
d_invertible'8658''35'_568 v0
  = coe
      d_invertible'8658''35'_460
      (coe d_isHeytingCommutativeRing_470 (coe v0))
-- Algebra.Apartness.Structures.IsHeytingField._.isApartnessRelation
d_isApartnessRelation_570 ::
  T_IsHeytingField_464 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsApartnessRelation_722
d_isApartnessRelation_570 v0
  = coe
      d_isApartnessRelation_314
      (coe d_isHeytingCommutativeRing_470 (coe v0))
-- Algebra.Apartness.Structures.IsHeytingField._.isCommutativeRing
d_isCommutativeRing_572 ::
  T_IsHeytingField_464 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2816
d_isCommutativeRing_572 v0
  = coe
      d_isCommutativeRing_312
      (coe d_isHeytingCommutativeRing_470 (coe v0))
-- Algebra.Apartness.Structures.IsHeytingField._.isCommutativeSemiring
d_isCommutativeSemiring_574 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsHeytingField_464 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1696
d_isCommutativeSemiring_574 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 v8 v9
                            ~v10 v11
  = du_isCommutativeSemiring_574 v6 v7 v8 v9 v11
du_isCommutativeSemiring_574 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsHeytingField_464 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiring_1696
du_isCommutativeSemiring_574 v0 v1 v2 v3 v4
  = let v5 = d_isHeytingCommutativeRing_470 (coe v4) in
    coe
      (coe
         MAlonzo.Code.Algebra.Structures.du_isCommutativeSemiring_2946
         (coe v0) (coe v1) (coe v2) (coe v3)
         (coe d_isCommutativeRing_312 (coe v5)))
-- Algebra.Apartness.Structures.IsHeytingField._.isCommutativeSemiringWithoutOne
d_isCommutativeSemiringWithoutOne_576 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsHeytingField_464 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiringWithoutOne_1390
d_isCommutativeSemiringWithoutOne_576 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7
                                      v8 v9 ~v10 v11
  = du_isCommutativeSemiringWithoutOne_576 v6 v7 v8 v9 v11
du_isCommutativeSemiringWithoutOne_576 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsHeytingField_464 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemiringWithoutOne_1390
du_isCommutativeSemiringWithoutOne_576 v0 v1 v2 v3 v4
  = let v5 = d_isHeytingCommutativeRing_470 (coe v4) in
    coe
      (let v6 = d_isCommutativeRing_312 (coe v5) in
       coe
         (coe
            MAlonzo.Code.Algebra.Structures.du_isCommutativeSemiringWithoutOne_1798
            (coe
               MAlonzo.Code.Algebra.Structures.du_isCommutativeSemiring_2946
               (coe v0) (coe v1) (coe v2) (coe v3) (coe v6))))
-- Algebra.Apartness.Structures.IsHeytingField._.isEquivalence
d_isEquivalence_578 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsHeytingField_464 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_578 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
                    v11
  = du_isEquivalence_578 v11
du_isEquivalence_578 ::
  T_IsHeytingField_464 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
du_isEquivalence_578 v0
  = let v1 = d_isHeytingCommutativeRing_470 (coe v0) in
    coe
      (let v2 = d_isCommutativeRing_312 (coe v1) in
       coe
         (let v3 = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isMagma_478
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                     (coe
                        MAlonzo.Code.Algebra.Structures.d_isMonoid_1048
                        (coe
                           MAlonzo.Code.Algebra.Structures.d_isGroup_1142
                           (coe
                              MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2692
                              (coe v3)))))))))
-- Algebra.Apartness.Structures.IsHeytingField._.isNearSemiring
d_isNearSemiring_580 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsHeytingField_464 ->
  MAlonzo.Code.Algebra.Structures.T_IsNearSemiring_1216
d_isNearSemiring_580 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 v8 v9 ~v10 v11
  = du_isNearSemiring_580 v6 v7 v8 v9 v11
du_isNearSemiring_580 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsHeytingField_464 ->
  MAlonzo.Code.Algebra.Structures.T_IsNearSemiring_1216
du_isNearSemiring_580 v0 v1 v2 v3 v4
  = let v5 = d_isHeytingCommutativeRing_470 (coe v4) in
    coe
      (let v6 = d_isCommutativeRing_312 (coe v5) in
       coe
         (let v7 = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v6) in
          coe
            (coe
               MAlonzo.Code.Algebra.Structures.du_isNearSemiring_2406 (coe v0)
               (coe v1) (coe v2) (coe v3)
               (coe
                  MAlonzo.Code.Algebra.Structures.du_isRingWithoutOne_2702
                  (coe v7)))))
-- Algebra.Apartness.Structures.IsHeytingField._.isPartialEquivalence
d_isPartialEquivalence_582 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsHeytingField_464 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_582 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                           ~v10 v11
  = du_isPartialEquivalence_582 v11
du_isPartialEquivalence_582 ::
  T_IsHeytingField_464 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
du_isPartialEquivalence_582 v0
  = let v1 = d_isHeytingCommutativeRing_470 (coe v0) in
    coe
      (let v2 = d_isCommutativeRing_312 (coe v1) in
       coe
         (let v3 = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v2) in
          coe
            (let v4
                   = coe
                       MAlonzo.Code.Algebra.Structures.du_isRingWithoutOne_2702
                       (coe v3) in
             coe
               (let v5
                      = MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2322
                          (coe v4) in
                coe
                  (let v6
                         = MAlonzo.Code.Algebra.Structures.d_isGroup_1142 (coe v5) in
                   coe
                     (let v7
                            = MAlonzo.Code.Algebra.Structures.d_isMonoid_1048 (coe v6) in
                      coe
                        (let v8
                               = MAlonzo.Code.Algebra.Structures.d_isSemigroup_694 (coe v7) in
                         coe
                           (let v9 = MAlonzo.Code.Algebra.Structures.d_isMagma_478 (coe v8) in
                            coe
                              (coe
                                 MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_42
                                 (coe
                                    MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
                                    (coe v9)))))))))))
-- Algebra.Apartness.Structures.IsHeytingField._.isRing
d_isRing_584 ::
  T_IsHeytingField_464 ->
  MAlonzo.Code.Algebra.Structures.T_IsRing_2670
d_isRing_584 v0
  = coe
      MAlonzo.Code.Algebra.Structures.d_isRing_2832
      (coe
         d_isCommutativeRing_312
         (coe d_isHeytingCommutativeRing_470 (coe v0)))
-- Algebra.Apartness.Structures.IsHeytingField._.isRingWithoutOne
d_isRingWithoutOne_586 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsHeytingField_464 ->
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2304
d_isRingWithoutOne_586 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
                       v11
  = du_isRingWithoutOne_586 v11
du_isRingWithoutOne_586 ::
  T_IsHeytingField_464 ->
  MAlonzo.Code.Algebra.Structures.T_IsRingWithoutOne_2304
du_isRingWithoutOne_586 v0
  = let v1 = d_isHeytingCommutativeRing_470 (coe v0) in
    coe
      (let v2 = d_isCommutativeRing_312 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Algebra.Structures.du_isRingWithoutOne_2702
            (coe MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v2))))
-- Algebra.Apartness.Structures.IsHeytingField._.isSemiring
d_isSemiring_588 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsHeytingField_464 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1588
d_isSemiring_588 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 v8 v9 ~v10 v11
  = du_isSemiring_588 v6 v7 v8 v9 v11
du_isSemiring_588 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsHeytingField_464 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiring_1588
du_isSemiring_588 v0 v1 v2 v3 v4
  = let v5 = d_isHeytingCommutativeRing_470 (coe v4) in
    coe
      (let v6 = d_isCommutativeRing_312 (coe v5) in
       coe
         (coe
            MAlonzo.Code.Algebra.Structures.du_isSemiring_2800 (coe v0)
            (coe v1) (coe v2) (coe v3)
            (coe MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v6))))
-- Algebra.Apartness.Structures.IsHeytingField._.isSemiringWithoutAnnihilatingZero
d_isSemiringWithoutAnnihilatingZero_590 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsHeytingField_464 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1486
d_isSemiringWithoutAnnihilatingZero_590 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6
                                        ~v7 ~v8 ~v9 ~v10 v11
  = du_isSemiringWithoutAnnihilatingZero_590 v11
du_isSemiringWithoutAnnihilatingZero_590 ::
  T_IsHeytingField_464 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutAnnihilatingZero_1486
du_isSemiringWithoutAnnihilatingZero_590 v0
  = let v1 = d_isHeytingCommutativeRing_470 (coe v0) in
    coe
      (let v2 = d_isCommutativeRing_312 (coe v1) in
       coe
         (coe
            MAlonzo.Code.Algebra.Structures.du_isSemiringWithoutAnnihilatingZero_2798
            (coe MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v2))))
-- Algebra.Apartness.Structures.IsHeytingField._.isSemiringWithoutOne
d_isSemiringWithoutOne_592 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsHeytingField_464 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutOne_1296
d_isSemiringWithoutOne_592 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 v8 v9 ~v10
                           v11
  = du_isSemiringWithoutOne_592 v6 v7 v8 v9 v11
du_isSemiringWithoutOne_592 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsHeytingField_464 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemiringWithoutOne_1296
du_isSemiringWithoutOne_592 v0 v1 v2 v3 v4
  = let v5 = d_isHeytingCommutativeRing_470 (coe v4) in
    coe
      (let v6 = d_isCommutativeRing_312 (coe v5) in
       coe
         (let v7 = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v6) in
          coe
            (coe
               MAlonzo.Code.Algebra.Structures.du_isSemiringWithoutOne_1678
               (coe
                  MAlonzo.Code.Algebra.Structures.du_isSemiring_2800 (coe v0)
                  (coe v1) (coe v2) (coe v3) (coe v7)))))
-- Algebra.Apartness.Structures.IsHeytingField._.refl
d_refl_594 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> T_IsHeytingField_464 -> AgdaAny -> AgdaAny
d_refl_594 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 v11
  = du_refl_594 v11
du_refl_594 :: T_IsHeytingField_464 -> AgdaAny -> AgdaAny
du_refl_594 v0
  = let v1 = d_isHeytingCommutativeRing_470 (coe v0) in
    coe
      (let v2 = d_isCommutativeRing_312 (coe v1) in
       coe
         (let v3 = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_refl_34
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_isMagma_478
                     (coe
                        MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                        (coe
                           MAlonzo.Code.Algebra.Structures.d_isMonoid_1048
                           (coe
                              MAlonzo.Code.Algebra.Structures.d_isGroup_1142
                              (coe
                                 MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2692
                                 (coe v3))))))))))
-- Algebra.Apartness.Structures.IsHeytingField._.reflexive
d_reflexive_596 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsHeytingField_464 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_reflexive_596 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 v11
  = du_reflexive_596 v11
du_reflexive_596 ::
  T_IsHeytingField_464 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
du_reflexive_596 v0
  = let v1 = d_isHeytingCommutativeRing_470 (coe v0) in
    coe
      (let v2 = d_isCommutativeRing_312 (coe v1) in
       coe
         (let v3 = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v2) in
          coe
            (let v4
                   = coe
                       MAlonzo.Code.Algebra.Structures.du_isRingWithoutOne_2702
                       (coe v3) in
             coe
               (let v5
                      = MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2322
                          (coe v4) in
                coe
                  (let v6
                         = MAlonzo.Code.Algebra.Structures.d_isGroup_1142 (coe v5) in
                   coe
                     (let v7
                            = MAlonzo.Code.Algebra.Structures.d_isMonoid_1048 (coe v6) in
                      coe
                        (let v8
                               = MAlonzo.Code.Algebra.Structures.d_isSemigroup_694 (coe v7) in
                         coe
                           (let v9 = MAlonzo.Code.Algebra.Structures.d_isMagma_478 (coe v8) in
                            coe
                              (\ v10 v11 v12 ->
                                 coe
                                   MAlonzo.Code.Relation.Binary.Structures.du_reflexive_40
                                   (coe
                                      MAlonzo.Code.Algebra.Structures.d_isEquivalence_184 (coe v9))
                                   v10)))))))))
-- Algebra.Apartness.Structures.IsHeytingField._.setoid
d_setoid_598 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsHeytingField_464 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
d_setoid_598 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 v11
  = du_setoid_598 v11
du_setoid_598 ::
  T_IsHeytingField_464 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
du_setoid_598 v0
  = let v1 = d_isHeytingCommutativeRing_470 (coe v0) in
    coe
      (let v2 = d_isCommutativeRing_312 (coe v1) in
       coe
         (let v3 = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v2) in
          coe
            (let v4
                   = coe
                       MAlonzo.Code.Algebra.Structures.du_isRingWithoutOne_2702
                       (coe v3) in
             coe
               (let v5
                      = MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2322
                          (coe v4) in
                coe
                  (let v6
                         = MAlonzo.Code.Algebra.Structures.d_isGroup_1142 (coe v5) in
                   coe
                     (let v7
                            = MAlonzo.Code.Algebra.Structures.d_isMonoid_1048 (coe v6) in
                      coe
                        (let v8
                               = MAlonzo.Code.Algebra.Structures.d_isSemigroup_694 (coe v7) in
                         coe
                           (coe
                              MAlonzo.Code.Algebra.Structures.du_setoid_200
                              (coe
                                 MAlonzo.Code.Algebra.Structures.d_isMagma_478 (coe v8))))))))))
-- Algebra.Apartness.Structures.IsHeytingField._.sym
d_sym_600 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsHeytingField_464 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_600 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 v11
  = du_sym_600 v11
du_sym_600 ::
  T_IsHeytingField_464 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_sym_600 v0
  = let v1 = d_isHeytingCommutativeRing_470 (coe v0) in
    coe
      (let v2 = d_isCommutativeRing_312 (coe v1) in
       coe
         (let v3 = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_sym_36
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_isMagma_478
                     (coe
                        MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                        (coe
                           MAlonzo.Code.Algebra.Structures.d_isMonoid_1048
                           (coe
                              MAlonzo.Code.Algebra.Structures.d_isGroup_1142
                              (coe
                                 MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2692
                                 (coe v3))))))))))
-- Algebra.Apartness.Structures.IsHeytingField._.trans
d_trans_602 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsHeytingField_464 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_602 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 v11
  = du_trans_602 v11
du_trans_602 ::
  T_IsHeytingField_464 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_trans_602 v0
  = let v1 = d_isHeytingCommutativeRing_470 (coe v0) in
    coe
      (let v2 = d_isCommutativeRing_312 (coe v1) in
       coe
         (let v3 = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v2) in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_trans_38
               (coe
                  MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
                  (coe
                     MAlonzo.Code.Algebra.Structures.d_isMagma_478
                     (coe
                        MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                        (coe
                           MAlonzo.Code.Algebra.Structures.d_isMonoid_1048
                           (coe
                              MAlonzo.Code.Algebra.Structures.d_isGroup_1142
                              (coe
                                 MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2692
                                 (coe v3))))))))))
-- Algebra.Apartness.Structures.IsHeytingField._.uniqueʳ-⁻¹
d_unique'691''45''8315''185'_604 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsHeytingField_464 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_unique'691''45''8315''185'_604 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 ~v7 v8
                                 v9 ~v10 v11
  = du_unique'691''45''8315''185'_604 v6 v8 v9 v11
du_unique'691''45''8315''185'_604 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsHeytingField_464 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_unique'691''45''8315''185'_604 v0 v1 v2 v3
  = let v4 = d_isHeytingCommutativeRing_470 (coe v3) in
    coe
      (let v5 = d_isCommutativeRing_312 (coe v4) in
       coe
         (let v6 = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v5) in
          coe
            (let v7
                   = coe
                       MAlonzo.Code.Algebra.Structures.du_isRingWithoutOne_2702
                       (coe v6) in
             coe
               (let v8
                      = MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2322
                          (coe v7) in
                coe
                  (coe
                     MAlonzo.Code.Algebra.Structures.du_unique'691''45''8315''185'_1118
                     (coe v0) (coe v2) (coe v1)
                     (coe MAlonzo.Code.Algebra.Structures.d_isGroup_1142 (coe v8)))))))
-- Algebra.Apartness.Structures.IsHeytingField._.uniqueˡ-⁻¹
d_unique'737''45''8315''185'_606 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsHeytingField_464 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_unique'737''45''8315''185'_606 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 ~v7 v8
                                 v9 ~v10 v11
  = du_unique'737''45''8315''185'_606 v6 v8 v9 v11
du_unique'737''45''8315''185'_606 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsHeytingField_464 -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_unique'737''45''8315''185'_606 v0 v1 v2 v3
  = let v4 = d_isHeytingCommutativeRing_470 (coe v3) in
    coe
      (let v5 = d_isCommutativeRing_312 (coe v4) in
       coe
         (let v6 = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v5) in
          coe
            (let v7
                   = coe
                       MAlonzo.Code.Algebra.Structures.du_isRingWithoutOne_2702
                       (coe v6) in
             coe
               (let v8
                      = MAlonzo.Code.Algebra.Structures.d_'43''45'isAbelianGroup_2322
                          (coe v7) in
                coe
                  (coe
                     MAlonzo.Code.Algebra.Structures.du_unique'737''45''8315''185'_1112
                     (coe v0) (coe v2) (coe v1)
                     (coe MAlonzo.Code.Algebra.Structures.d_isGroup_1142 (coe v8)))))))
-- Algebra.Apartness.Structures.IsHeytingField._.zero
d_zero_608 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsHeytingField_464 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_zero_608 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 v8 v9 ~v10 v11
  = du_zero_608 v6 v7 v8 v9 v11
du_zero_608 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_IsHeytingField_464 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_zero_608 v0 v1 v2 v3 v4
  = let v5 = d_isHeytingCommutativeRing_470 (coe v4) in
    coe
      (let v6 = d_isCommutativeRing_312 (coe v5) in
       coe
         (let v7 = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v6) in
          coe
            (coe
               MAlonzo.Code.Algebra.Structures.du_zero_2404 (coe v0) (coe v1)
               (coe v2) (coe v3)
               (coe
                  MAlonzo.Code.Algebra.Structures.du_isRingWithoutOne_2702
                  (coe v7)))))
-- Algebra.Apartness.Structures.IsHeytingField._.zeroʳ
d_zero'691'_610 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> T_IsHeytingField_464 -> AgdaAny -> AgdaAny
d_zero'691'_610 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 v8 v9 ~v10 v11
  = du_zero'691'_610 v6 v7 v8 v9 v11
du_zero'691'_610 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> T_IsHeytingField_464 -> AgdaAny -> AgdaAny
du_zero'691'_610 v0 v1 v2 v3 v4
  = let v5 = d_isHeytingCommutativeRing_470 (coe v4) in
    coe
      (let v6 = d_isCommutativeRing_312 (coe v5) in
       coe
         (let v7 = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v6) in
          coe
            (coe
               MAlonzo.Code.Algebra.Structures.du_zero'691'_2402 (coe v0) (coe v1)
               (coe v2) (coe v3)
               (coe
                  MAlonzo.Code.Algebra.Structures.du_isRingWithoutOne_2702
                  (coe v7)))))
-- Algebra.Apartness.Structures.IsHeytingField._.zeroˡ
d_zero'737'_612 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> T_IsHeytingField_464 -> AgdaAny -> AgdaAny
d_zero'737'_612 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 v8 v9 ~v10 v11
  = du_zero'737'_612 v6 v7 v8 v9 v11
du_zero'737'_612 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> T_IsHeytingField_464 -> AgdaAny -> AgdaAny
du_zero'737'_612 v0 v1 v2 v3 v4
  = let v5 = d_isHeytingCommutativeRing_470 (coe v4) in
    coe
      (let v6 = d_isCommutativeRing_312 (coe v5) in
       coe
         (let v7 = MAlonzo.Code.Algebra.Structures.d_isRing_2832 (coe v6) in
          coe
            (coe
               MAlonzo.Code.Algebra.Structures.du_zero'737'_2400 (coe v0) (coe v1)
               (coe v2) (coe v3)
               (coe
                  MAlonzo.Code.Algebra.Structures.du_isRingWithoutOne_2702
                  (coe v7)))))
-- Algebra.Apartness.Structures.IsHeytingField._.¬#-isEquivalence
d_'172''35''45'isEquivalence_614 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  T_IsHeytingField_464 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_'172''35''45'isEquivalence_614 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
                                 ~v8 ~v9 ~v10 ~v11
  = du_'172''35''45'isEquivalence_614
du_'172''35''45'isEquivalence_614 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
du_'172''35''45'isEquivalence_614
  = coe du_'172''35''45'isEquivalence_462
