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

module MAlonzo.Code.Function.Construct.Symmetry where

import Data.Text qualified
import MAlonzo.Code.Agda.Builtin.Sigma qualified
import MAlonzo.Code.Agda.Primitive qualified
import MAlonzo.Code.Data.Product.Base qualified
import MAlonzo.Code.Function.Bundles qualified
import MAlonzo.Code.Function.Structures qualified
import MAlonzo.Code.Relation.Binary.Bundles qualified
import MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties qualified
import MAlonzo.Code.Relation.Binary.Structures qualified
import MAlonzo.RTE (AgdaAny, add64, addInt, coe, eq64, eqInt, erased, geqInt, lt64, ltInt, mul64,
                    mulInt, quot64, quotInt, rem64, remInt, sub64, subInt, word64FromNat,
                    word64ToNat)
import MAlonzo.RTE qualified

-- Function.Construct.Symmetry._.f⁻¹
d_f'8315''185'_48 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> AgdaAny -> AgdaAny
d_f'8315''185'_48 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9 v10
  = du_f'8315''185'_48 v9 v10
du_f'8315''185'_48 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> AgdaAny -> AgdaAny
du_f'8315''185'_48 v0 v1
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
      (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 v0 v1)
-- Function.Construct.Symmetry._.f∘f⁻¹≡id
d_f'8728'f'8315''185''8801'id_50 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_f'8728'f'8315''185''8801'id_50 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
                                 ~v8 v9 v10
  = du_f'8728'f'8315''185''8801'id_50 v9 v10
du_f'8728'f'8315''185''8801'id_50 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_f'8728'f'8315''185''8801'id_50 v0 v1
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
      (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 v0 v1)
-- Function.Construct.Symmetry._.injective
d_injective_52 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_injective_52 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 v9 v10 v11 v12
               v13 v14 v15 v16
  = du_injective_52 v8 v9 v10 v11 v12 v13 v14 v15 v16
du_injective_52 ::
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_injective_52 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = coe
      v4 v6 (coe v0 (coe du_f'8315''185'_48 (coe v1) (coe v7))) v7
      (coe
         v4 v6
         (coe
            v0
            (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
               (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 v1 v6)))
         (coe v0 (coe du_f'8315''185'_48 (coe v1) (coe v7)))
         (coe
            v3
            (coe
               v0
               (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                  (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 v1 v6)))
            v6
            (coe
               du_f'8728'f'8315''185''8801'id_50 v1 v6
               (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                  (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 v1 v6))
               (coe
                  v2
                  (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                     (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 v1 v6)))))
         (coe
            v5 (coe du_f'8315''185'_48 (coe v1) (coe v6))
            (coe du_f'8315''185'_48 (coe v1) (coe v7)) v8))
      (coe
         du_f'8728'f'8315''185''8801'id_50 v1 v7
         (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
            (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 v1 v7))
         (coe
            v2
            (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
               (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 v1 v7))))
-- Function.Construct.Symmetry._.surjective
d_surjective_64 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_surjective_64 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 v9 v10 v11 v12
  = du_surjective_64 v8 v9 v10 v11 v12
du_surjective_64 ::
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_surjective_64 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0 v4)
      (coe
         (\ v5 v6 ->
            coe
              MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 v1
              (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                 (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 v1 v5))
              v4
              (coe
                 v3
                 (coe
                    v0
                    (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                       (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 v1 v5)))
                 v5 (coe v0 v4)
                 (coe
                    du_f'8728'f'8315''185''8801'id_50 v1 v5
                    (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                       (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 v1 v5))
                    (coe
                       v2
                       (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                          (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 v1 v5))))
                 v6)))
-- Function.Construct.Symmetry._.bijective
d_bijective_72 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_bijective_72 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 v9 v10 v11 v12
               v13
  = du_bijective_72 v8 v9 v10 v11 v12 v13
du_bijective_72 ::
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_bijective_72 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         du_injective_52 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
         (coe v5))
      (coe du_surjective_64 (coe v0) (coe v1) (coe v2) (coe v4))
-- Function.Construct.Symmetry._.inverseʳ
d_inverse'691'_102 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_inverse'691'_102 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10 v11
                   v12
  = du_inverse'691'_102 v10 v11 v12
du_inverse'691'_102 ::
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_inverse'691'_102 v0 v1 v2 = coe v0 v1 v2
-- Function.Construct.Symmetry._.inverseˡ
d_inverse'737'_106 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_inverse'737'_106 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10 v11
                   v12
  = du_inverse'737'_106 v10 v11 v12
du_inverse'737'_106 ::
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_inverse'737'_106 v0 v1 v2 = coe v0 v1 v2
-- Function.Construct.Symmetry._.inverseᵇ
d_inverse'7495'_110 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inverse'7495'_110 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10
  = du_inverse'7495'_110 v10
du_inverse'7495'_110 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_inverse'7495'_110 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v1 v2
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Function.Construct.Symmetry._.f⁻¹
d_f'8315''185'_206 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsBijection_238 ->
  AgdaAny -> AgdaAny
d_f'8315''185'_206 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9 v10
  = du_f'8315''185'_206 v9 v10
du_f'8315''185'_206 ::
  MAlonzo.Code.Function.Structures.T_IsBijection_238 ->
  AgdaAny -> AgdaAny
du_f'8315''185'_206 v0 v1
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
      (coe MAlonzo.Code.Function.Structures.d_surjective_248 v0 v1)
-- Function.Construct.Symmetry._.isBijection
d_isBijection_208 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsBijection_238 ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsBijection_238
d_isBijection_208 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 v9 v10
  = du_isBijection_208 v8 v9 v10
du_isBijection_208 ::
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsBijection_238 ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsBijection_238
du_isBijection_208 v0 v1 v2
  = coe
      MAlonzo.Code.Function.Structures.C_IsBijection'46'constructor_10113
      (coe
         MAlonzo.Code.Function.Structures.C_IsInjection'46'constructor_3997
         (coe
            MAlonzo.Code.Function.Structures.C_IsCongruent'46'constructor_985
            (coe v2)
            (let v3
                   = MAlonzo.Code.Function.Structures.d_isInjection_246 (coe v1) in
             coe
               (let v4
                      = MAlonzo.Code.Function.Structures.d_isCongruent_100 (coe v3) in
                coe
                  (coe
                     MAlonzo.Code.Function.Structures.d_isEquivalence'8322'_36
                     (coe v4))))
            (let v3
                   = MAlonzo.Code.Function.Structures.d_isInjection_246 (coe v1) in
             coe
               (let v4
                      = MAlonzo.Code.Function.Structures.d_isCongruent_100 (coe v3) in
                coe
                  (coe
                     MAlonzo.Code.Function.Structures.d_isEquivalence'8321'_34
                     (coe v4)))))
         (coe
            du_injective_52 (coe v0)
            (coe MAlonzo.Code.Function.Structures.du_bijective_310 (coe v1))
            (let v3
                   = MAlonzo.Code.Function.Structures.d_isInjection_246 (coe v1) in
             coe
               (let v4
                      = MAlonzo.Code.Function.Structures.d_isCongruent_100 (coe v3) in
                coe
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                     (coe
                        MAlonzo.Code.Function.Structures.d_isEquivalence'8321'_34
                        (coe v4)))))
            (let v3
                   = MAlonzo.Code.Function.Structures.d_isInjection_246 (coe v1) in
             coe
               (let v4
                      = MAlonzo.Code.Function.Structures.d_isCongruent_100 (coe v3) in
                coe
                  (let v5
                         = coe MAlonzo.Code.Function.Structures.du_setoid_66 (coe v4) in
                   coe
                     (coe
                        MAlonzo.Code.Relation.Binary.Structures.d_sym_36
                        (coe
                           MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                           (coe v5))))))
            (let v3
                   = MAlonzo.Code.Function.Structures.d_isInjection_246 (coe v1) in
             coe
               (let v4
                      = MAlonzo.Code.Function.Structures.d_isCongruent_100 (coe v3) in
                coe
                  (let v5
                         = coe MAlonzo.Code.Function.Structures.du_setoid_66 (coe v4) in
                   coe
                     (coe
                        MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                        (coe
                           MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                           (coe v5))))))
            (coe
               MAlonzo.Code.Function.Structures.d_cong_32
               (coe
                  MAlonzo.Code.Function.Structures.d_isCongruent_100
                  (coe
                     MAlonzo.Code.Function.Structures.d_isInjection_246 (coe v1))))))
      (coe
         du_surjective_64 (coe v0)
         (coe MAlonzo.Code.Function.Structures.du_bijective_310 (coe v1))
         (let v3
                = MAlonzo.Code.Function.Structures.d_isInjection_246 (coe v1) in
          coe
            (let v4
                   = MAlonzo.Code.Function.Structures.d_isCongruent_100 (coe v3) in
             coe
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                  (coe
                     MAlonzo.Code.Function.Structures.d_isEquivalence'8321'_34
                     (coe v4)))))
         (let v3
                = MAlonzo.Code.Function.Structures.d_isInjection_246 (coe v1) in
          coe
            (let v4
                   = MAlonzo.Code.Function.Structures.d_isCongruent_100 (coe v3) in
             coe
               (let v5
                      = coe MAlonzo.Code.Function.Structures.du_setoid_66 (coe v4) in
                coe
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                     (coe
                        MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                        (coe v5)))))))
-- Function.Construct.Symmetry._.isBijection-≡
d_isBijection'45''8801'_228 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsBijection_238 ->
  MAlonzo.Code.Function.Structures.T_IsBijection_238
d_isBijection'45''8801'_228 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7
  = du_isBijection'45''8801'_228 v6 v7
du_isBijection'45''8801'_228 ::
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsBijection_238 ->
  MAlonzo.Code.Function.Structures.T_IsBijection_238
du_isBijection'45''8801'_228 v0 v1
  = coe
      du_isBijection_208 (coe v0) (coe v1)
      (coe
         (\ v2 v3 v4 ->
            let v5
                  = MAlonzo.Code.Function.Structures.d_isInjection_246 (coe v1) in
            coe
              (let v6
                     = MAlonzo.Code.Function.Structures.d_isCongruent_100 (coe v5) in
               coe
                 (let v7
                        = coe MAlonzo.Code.Function.Structures.du_setoid_40 (coe v6) in
                  coe
                    (coe
                       MAlonzo.Code.Relation.Binary.Structures.du_reflexive_40
                       (coe
                          MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v7))
                       (coe du_f'8315''185'_206 (coe v1) (coe v2)))))))
-- Function.Construct.Symmetry._.isCongruent
d_isCongruent_324 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsCongruent_22 ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsCongruent_22
d_isCongruent_324 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10 v11
  = du_isCongruent_324 v10 v11
du_isCongruent_324 ::
  MAlonzo.Code.Function.Structures.T_IsCongruent_22 ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsCongruent_22
du_isCongruent_324 v0 v1
  = coe
      MAlonzo.Code.Function.Structures.C_IsCongruent'46'constructor_985
      (coe v1)
      (coe
         MAlonzo.Code.Function.Structures.d_isEquivalence'8322'_36 (coe v0))
      (coe
         MAlonzo.Code.Function.Structures.d_isEquivalence'8321'_34 (coe v0))
-- Function.Construct.Symmetry._.isLeftInverse
d_isLeftInverse_390 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsRightInverse_408 ->
  MAlonzo.Code.Function.Structures.T_IsLeftInverse_322
d_isLeftInverse_390 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10
  = du_isLeftInverse_390 v10
du_isLeftInverse_390 ::
  MAlonzo.Code.Function.Structures.T_IsRightInverse_408 ->
  MAlonzo.Code.Function.Structures.T_IsLeftInverse_322
du_isLeftInverse_390 v0
  = coe
      MAlonzo.Code.Function.Structures.C_IsLeftInverse'46'constructor_14363
      (coe
         du_isCongruent_324
         (coe MAlonzo.Code.Function.Structures.d_isCongruent_420 (coe v0))
         (coe MAlonzo.Code.Function.Structures.d_from'45'cong_422 (coe v0)))
      (coe
         MAlonzo.Code.Function.Structures.d_cong_32
         (coe MAlonzo.Code.Function.Structures.d_isCongruent_420 (coe v0)))
      (coe
         du_inverse'737'_106
         (coe MAlonzo.Code.Function.Structures.d_inverse'691'_424 (coe v0)))
-- Function.Construct.Symmetry._.isRightInverse
d_isRightInverse_462 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsLeftInverse_322 ->
  MAlonzo.Code.Function.Structures.T_IsRightInverse_408
d_isRightInverse_462 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10
  = du_isRightInverse_462 v10
du_isRightInverse_462 ::
  MAlonzo.Code.Function.Structures.T_IsLeftInverse_322 ->
  MAlonzo.Code.Function.Structures.T_IsRightInverse_408
du_isRightInverse_462 v0
  = coe
      MAlonzo.Code.Function.Structures.C_IsRightInverse'46'constructor_18837
      (coe
         du_isCongruent_324
         (coe MAlonzo.Code.Function.Structures.d_isCongruent_334 (coe v0))
         (coe MAlonzo.Code.Function.Structures.d_from'45'cong_336 (coe v0)))
      (coe
         MAlonzo.Code.Function.Structures.d_cong_32
         (coe MAlonzo.Code.Function.Structures.d_isCongruent_334 (coe v0)))
      (coe
         du_inverse'691'_102
         (coe MAlonzo.Code.Function.Structures.d_inverse'737'_338 (coe v0)))
-- Function.Construct.Symmetry._.isInverse
d_isInverse_536 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsInverse_490 ->
  MAlonzo.Code.Function.Structures.T_IsInverse_490
d_isInverse_536 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 v10
  = du_isInverse_536 v10
du_isInverse_536 ::
  MAlonzo.Code.Function.Structures.T_IsInverse_490 ->
  MAlonzo.Code.Function.Structures.T_IsInverse_490
du_isInverse_536 v0
  = coe
      MAlonzo.Code.Function.Structures.C_IsInverse'46'constructor_22449
      (coe
         du_isLeftInverse_390
         (coe
            MAlonzo.Code.Function.Structures.du_isRightInverse_570 (coe v0)))
      (coe
         du_inverse'691'_102
         (coe
            MAlonzo.Code.Function.Structures.d_inverse'737'_338
            (coe
               MAlonzo.Code.Function.Structures.d_isLeftInverse_500 (coe v0))))
-- Function.Construct.Symmetry._.IB.Eq₁._≈_
d__'8776'__666 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Function.Bundles.T_Bijection_926 ->
  AgdaAny -> AgdaAny -> ()
d__'8776'__666 = erased
-- Function.Construct.Symmetry._.IB.Eq₂._≈_
d__'8776'__690 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Function.Bundles.T_Bijection_926 ->
  AgdaAny -> AgdaAny -> ()
d__'8776'__690 = erased
-- Function.Construct.Symmetry._.from
d_from_712 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Function.Bundles.T_Bijection_926 -> AgdaAny -> AgdaAny
d_from_712 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 = du_from_712 v6 v7
du_from_712 ::
  MAlonzo.Code.Function.Bundles.T_Bijection_926 -> AgdaAny -> AgdaAny
du_from_712 v0 v1
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
      (coe MAlonzo.Code.Function.Bundles.du_surjective_942 v0 v1)
-- Function.Construct.Symmetry._.bijection
d_bijection_714 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Function.Bundles.T_Bijection_926 ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Bundles.T_Bijection_926
d_bijection_714 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7
  = du_bijection_714 v4 v5 v6 v7
du_bijection_714 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Function.Bundles.T_Bijection_926 ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Bundles.T_Bijection_926
du_bijection_714 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Function.Bundles.C_Bijection'46'constructor_15277
      (coe du_from_712 (coe v2)) (coe v3)
      (coe
         du_bijective_72
         (coe MAlonzo.Code.Function.Bundles.d_to_934 (coe v2))
         (coe MAlonzo.Code.Function.Bundles.d_bijective_938 (coe v2))
         (let v4
                = coe
                    MAlonzo.Code.Function.Bundles.du_isBijection_960 (coe v0) (coe v1)
                    (coe v2) in
          coe
            (let v5
                   = MAlonzo.Code.Function.Structures.d_isInjection_246 (coe v4) in
             coe
               (let v6
                      = MAlonzo.Code.Function.Structures.d_isCongruent_100 (coe v5) in
                coe
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                     (coe
                        MAlonzo.Code.Function.Structures.d_isEquivalence'8321'_34
                        (coe v6))))))
         (let v4
                = coe
                    MAlonzo.Code.Function.Bundles.du_isBijection_960 (coe v0) (coe v1)
                    (coe v2) in
          coe
            (let v5
                   = MAlonzo.Code.Function.Structures.d_isInjection_246 (coe v4) in
             coe
               (let v6
                      = MAlonzo.Code.Function.Structures.d_isCongruent_100 (coe v5) in
                coe
                  (let v7
                         = coe MAlonzo.Code.Function.Structures.du_setoid_66 (coe v6) in
                   coe
                     (coe
                        MAlonzo.Code.Relation.Binary.Structures.d_sym_36
                        (coe
                           MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                           (coe v7)))))))
         (let v4
                = coe
                    MAlonzo.Code.Function.Bundles.du_isBijection_960 (coe v0) (coe v1)
                    (coe v2) in
          coe
            (let v5
                   = MAlonzo.Code.Function.Structures.d_isInjection_246 (coe v4) in
             coe
               (let v6
                      = MAlonzo.Code.Function.Structures.d_isCongruent_100 (coe v5) in
                coe
                  (let v7
                         = coe MAlonzo.Code.Function.Structures.du_setoid_66 (coe v6) in
                   coe
                     (coe
                        MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                        (coe
                           MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                           (coe v7)))))))
         (coe MAlonzo.Code.Function.Bundles.d_cong_936 (coe v2)))
-- Function.Construct.Symmetry.bijection-≡
d_bijection'45''8801'_722 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  () ->
  MAlonzo.Code.Function.Bundles.T_Bijection_926 ->
  MAlonzo.Code.Function.Bundles.T_Bijection_926
d_bijection'45''8801'_722 ~v0 ~v1 ~v2 v3 ~v4 v5
  = du_bijection'45''8801'_722 v3 v5
du_bijection'45''8801'_722 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Function.Bundles.T_Bijection_926 ->
  MAlonzo.Code.Function.Bundles.T_Bijection_926
du_bijection'45''8801'_722 v0 v1
  = coe
      du_bijection_714 (coe v0)
      (coe
         MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties.du_setoid_402)
      (coe v1)
      (coe
         (\ v2 v3 v4 ->
            let v5
                  = coe
                      MAlonzo.Code.Function.Bundles.du_isBijection_960 (coe v0)
                      (coe
                         MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties.du_setoid_402)
                      (coe v1) in
            coe
              (let v6
                     = MAlonzo.Code.Function.Structures.d_isInjection_246 (coe v5) in
               coe
                 (let v7
                        = MAlonzo.Code.Function.Structures.d_isCongruent_100 (coe v6) in
                  coe
                    (let v8
                           = coe MAlonzo.Code.Function.Structures.du_setoid_40 (coe v7) in
                     coe
                       (coe
                          MAlonzo.Code.Relation.Binary.Structures.du_reflexive_40
                          (coe
                             MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v8))
                          (coe du_from_712 (coe v1) (coe v2))))))))
-- Function.Construct.Symmetry._.equivalence
d_equivalence_820 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Function.Bundles.T_Equivalence_1714 ->
  MAlonzo.Code.Function.Bundles.T_Equivalence_1714
d_equivalence_820 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_equivalence_820 v6
du_equivalence_820 ::
  MAlonzo.Code.Function.Bundles.T_Equivalence_1714 ->
  MAlonzo.Code.Function.Bundles.T_Equivalence_1714
du_equivalence_820 v0
  = coe
      MAlonzo.Code.Function.Bundles.C_Equivalence'46'constructor_25797
      (coe MAlonzo.Code.Function.Bundles.d_from_1726 (coe v0))
      (coe MAlonzo.Code.Function.Bundles.d_to_1724 (coe v0))
      (coe MAlonzo.Code.Function.Bundles.d_from'45'cong_1730 (coe v0))
      (coe MAlonzo.Code.Function.Bundles.d_to'45'cong_1728 (coe v0))
-- Function.Construct.Symmetry._.rightInverse
d_rightInverse_894 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Function.Bundles.T_LeftInverse_1792 ->
  MAlonzo.Code.Function.Bundles.T_RightInverse_1880
d_rightInverse_894 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_rightInverse_894 v6
du_rightInverse_894 ::
  MAlonzo.Code.Function.Bundles.T_LeftInverse_1792 ->
  MAlonzo.Code.Function.Bundles.T_RightInverse_1880
du_rightInverse_894 v0
  = coe
      MAlonzo.Code.Function.Bundles.C_RightInverse'46'constructor_34573
      (coe MAlonzo.Code.Function.Bundles.d_from_1806 (coe v0))
      (coe MAlonzo.Code.Function.Bundles.d_to_1804 (coe v0))
      (coe MAlonzo.Code.Function.Bundles.d_from'45'cong_1810 (coe v0))
      (coe MAlonzo.Code.Function.Bundles.d_to'45'cong_1808 (coe v0))
      (coe MAlonzo.Code.Function.Bundles.d_inverse'737'_1812 (coe v0))
-- Function.Construct.Symmetry._.leftInverse
d_leftInverse_976 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Function.Bundles.T_RightInverse_1880 ->
  MAlonzo.Code.Function.Bundles.T_LeftInverse_1792
d_leftInverse_976 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_leftInverse_976 v6
du_leftInverse_976 ::
  MAlonzo.Code.Function.Bundles.T_RightInverse_1880 ->
  MAlonzo.Code.Function.Bundles.T_LeftInverse_1792
du_leftInverse_976 v0
  = coe
      MAlonzo.Code.Function.Bundles.C_LeftInverse'46'constructor_29775
      (coe MAlonzo.Code.Function.Bundles.d_from_1894 (coe v0))
      (coe MAlonzo.Code.Function.Bundles.d_to_1892 (coe v0))
      (coe MAlonzo.Code.Function.Bundles.d_from'45'cong_1898 (coe v0))
      (coe MAlonzo.Code.Function.Bundles.d_to'45'cong_1896 (coe v0))
      (coe MAlonzo.Code.Function.Bundles.d_inverse'691'_1900 (coe v0))
-- Function.Construct.Symmetry._.inverse
d_inverse_1052 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Function.Bundles.T_Inverse_1960 ->
  MAlonzo.Code.Function.Bundles.T_Inverse_1960
d_inverse_1052 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 = du_inverse_1052 v6
du_inverse_1052 ::
  MAlonzo.Code.Function.Bundles.T_Inverse_1960 ->
  MAlonzo.Code.Function.Bundles.T_Inverse_1960
du_inverse_1052 v0
  = coe
      MAlonzo.Code.Function.Bundles.C_Inverse'46'constructor_38621
      (coe MAlonzo.Code.Function.Bundles.d_from_1974 (coe v0))
      (coe MAlonzo.Code.Function.Bundles.d_to_1972 (coe v0))
      (coe MAlonzo.Code.Function.Bundles.d_from'45'cong_1978 (coe v0))
      (coe MAlonzo.Code.Function.Bundles.d_to'45'cong_1976 (coe v0))
      (coe
         MAlonzo.Code.Data.Product.Base.du_swap_370
         (coe MAlonzo.Code.Function.Bundles.d_inverse_1980 (coe v0)))
-- Function.Construct.Symmetry.⤖-sym
d_'10518''45'sym_1138 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Function.Bundles.T_Bijection_926 ->
  MAlonzo.Code.Function.Bundles.T_Bijection_926
d_'10518''45'sym_1138 ~v0 ~v1 ~v2 ~v3 v4
  = du_'10518''45'sym_1138 v4
du_'10518''45'sym_1138 ::
  MAlonzo.Code.Function.Bundles.T_Bijection_926 ->
  MAlonzo.Code.Function.Bundles.T_Bijection_926
du_'10518''45'sym_1138 v0
  = coe
      du_bijection_714
      (coe
         MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties.du_setoid_402)
      (coe
         MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties.du_setoid_402)
      (coe v0) erased
-- Function.Construct.Symmetry.⇔-sym
d_'8660''45'sym_1142 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Function.Bundles.T_Equivalence_1714 ->
  MAlonzo.Code.Function.Bundles.T_Equivalence_1714
d_'8660''45'sym_1142 ~v0 ~v1 ~v2 ~v3 = du_'8660''45'sym_1142
du_'8660''45'sym_1142 ::
  MAlonzo.Code.Function.Bundles.T_Equivalence_1714 ->
  MAlonzo.Code.Function.Bundles.T_Equivalence_1714
du_'8660''45'sym_1142 = coe du_equivalence_820
-- Function.Construct.Symmetry.↩-sym
d_'8617''45'sym_1144 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Function.Bundles.T_LeftInverse_1792 ->
  MAlonzo.Code.Function.Bundles.T_RightInverse_1880
d_'8617''45'sym_1144 ~v0 ~v1 ~v2 ~v3 = du_'8617''45'sym_1144
du_'8617''45'sym_1144 ::
  MAlonzo.Code.Function.Bundles.T_LeftInverse_1792 ->
  MAlonzo.Code.Function.Bundles.T_RightInverse_1880
du_'8617''45'sym_1144 = coe du_rightInverse_894
-- Function.Construct.Symmetry.↪-sym
d_'8618''45'sym_1146 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Function.Bundles.T_RightInverse_1880 ->
  MAlonzo.Code.Function.Bundles.T_LeftInverse_1792
d_'8618''45'sym_1146 ~v0 ~v1 ~v2 ~v3 = du_'8618''45'sym_1146
du_'8618''45'sym_1146 ::
  MAlonzo.Code.Function.Bundles.T_RightInverse_1880 ->
  MAlonzo.Code.Function.Bundles.T_LeftInverse_1792
du_'8618''45'sym_1146 = coe du_leftInverse_976
-- Function.Construct.Symmetry.↔-sym
d_'8596''45'sym_1148 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Function.Bundles.T_Inverse_1960 ->
  MAlonzo.Code.Function.Bundles.T_Inverse_1960
d_'8596''45'sym_1148 ~v0 ~v1 ~v2 ~v3 = du_'8596''45'sym_1148
du_'8596''45'sym_1148 ::
  MAlonzo.Code.Function.Bundles.T_Inverse_1960 ->
  MAlonzo.Code.Function.Bundles.T_Inverse_1960
du_'8596''45'sym_1148 = coe du_inverse_1052
-- Function.Construct.Symmetry.sym-⤖
d_sym'45''10518'_1150 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Function.Bundles.T_Bijection_926 ->
  MAlonzo.Code.Function.Bundles.T_Bijection_926
d_sym'45''10518'_1150 v0 v1 v2 v3 v4
  = coe du_'10518''45'sym_1138 v4
-- Function.Construct.Symmetry.sym-⇔
d_sym'45''8660'_1152 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Function.Bundles.T_Equivalence_1714 ->
  MAlonzo.Code.Function.Bundles.T_Equivalence_1714
d_sym'45''8660'_1152 v0 v1 v2 v3 = coe du_'8660''45'sym_1142
-- Function.Construct.Symmetry.sym-↩
d_sym'45''8617'_1154 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Function.Bundles.T_LeftInverse_1792 ->
  MAlonzo.Code.Function.Bundles.T_RightInverse_1880
d_sym'45''8617'_1154 v0 v1 v2 v3 = coe du_'8617''45'sym_1144
-- Function.Construct.Symmetry.sym-↪
d_sym'45''8618'_1156 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Function.Bundles.T_RightInverse_1880 ->
  MAlonzo.Code.Function.Bundles.T_LeftInverse_1792
d_sym'45''8618'_1156 v0 v1 v2 v3 = coe du_'8618''45'sym_1146
-- Function.Construct.Symmetry.sym-↔
d_sym'45''8596'_1158 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Function.Bundles.T_Inverse_1960 ->
  MAlonzo.Code.Function.Bundles.T_Inverse_1960
d_sym'45''8596'_1158 v0 v1 v2 v3 = coe du_'8596''45'sym_1148
