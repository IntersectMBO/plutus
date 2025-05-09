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

module MAlonzo.Code.Function.Construct.Composition where

import Data.Text qualified
import MAlonzo.Code.Agda.Builtin.Sigma qualified
import MAlonzo.Code.Agda.Primitive qualified
import MAlonzo.Code.Data.Product.Base qualified
import MAlonzo.Code.Function.Bundles qualified
import MAlonzo.Code.Function.Structures qualified
import MAlonzo.Code.Relation.Binary.Bundles qualified
import MAlonzo.RTE (AgdaAny, add64, addInt, coe, eq64, eqInt, erased, geqInt, lt64, ltInt, mul64,
                    mulInt, quot64, quotInt, rem64, remInt, sub64, subInt, word64FromNat,
                    word64ToNat)
import MAlonzo.RTE qualified

-- Function.Construct.Composition._.congruent
d_congruent_50 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_congruent_50 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11
               v12 ~v13 v14 v15 v16 v17 v18
  = du_congruent_50 v12 v14 v15 v16 v17 v18
du_congruent_50 ::
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_congruent_50 v0 v1 v2 v3 v4 v5
  = coe v2 (coe v0 v3) (coe v0 v4) (coe v1 v3 v4 v5)
-- Function.Construct.Composition._.injective
d_injective_56 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_injective_56 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11
               v12 ~v13 v14 v15 v16 v17 v18
  = du_injective_56 v12 v14 v15 v16 v17 v18
du_injective_56 ::
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_injective_56 v0 v1 v2 v3 v4 v5
  = coe v1 v3 v4 (coe v2 (coe v0 v3) (coe v0 v4) v5)
-- Function.Construct.Composition._.surjective
d_surjective_62 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_surjective_62 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11
                v12 ~v13 v14 v15 v16
  = du_surjective_62 v12 v14 v15 v16
du_surjective_62 ::
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_surjective_62 v0 v1 v2 v3
  = let v4 = coe v2 v3 in
    coe
      (case coe v4 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
           -> let v7 = coe v1 v5 in
              coe
                (case coe v7 of
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9
                     -> coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v8)
                          (coe (\ v10 v11 -> coe v6 (coe v0 v10) (coe v9 v10 v11)))
                   _ -> MAlonzo.RTE.mazUnreachableError)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Function.Construct.Composition._.bijective
d_bijective_102 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_bijective_102 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11
                v12 ~v13
  = du_bijective_102 v12
du_bijective_102 ::
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_bijective_102 v0
  = coe
      MAlonzo.Code.Data.Product.Base.du_zip'8242'_312
      (coe du_injective_56 (coe v0)) (coe du_surjective_62 (coe v0))
-- Function.Construct.Composition._.inverseˡ
d_inverse'737'_134 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_inverse'737'_134 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
                   ~v11 v12 ~v13 ~v14 v15 v16 v17 v18 v19 v20
  = du_inverse'737'_134 v12 v15 v16 v17 v18 v19 v20
du_inverse'737'_134 ::
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_inverse'737'_134 v0 v1 v2 v3 v4 v5 v6
  = coe v3 v4 (coe v0 v5) (coe v2 (coe v1 v4) v5 v6)
-- Function.Construct.Composition._.inverseʳ
d_inverse'691'_140 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_inverse'691'_140 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
                   ~v11 v12 ~v13 ~v14 v15 v16 v17 v18 v19 v20
  = du_inverse'691'_140 v12 v15 v16 v17 v18 v19 v20
du_inverse'691'_140 ::
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_inverse'691'_140 v0 v1 v2 v3 v4 v5 v6
  = coe v2 v4 (coe v1 v5) (coe v3 (coe v0 v4) v5 v6)
-- Function.Construct.Composition._.inverseᵇ
d_inverse'7495'_146 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inverse'7495'_146 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
                    ~v11 v12 ~v13 ~v14 v15
  = du_inverse'7495'_146 v12 v15
du_inverse'7495'_146 ::
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_inverse'7495'_146 v0 v1
  = coe
      MAlonzo.Code.Data.Product.Base.du_zip'8242'_312
      (coe du_inverse'737'_134 (coe v0) (coe v1))
      (coe du_inverse'691'_140 (coe v0) (coe v1))
-- Function.Construct.Composition._.isCongruent
d_isCongruent_174 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsCongruent_22 ->
  MAlonzo.Code.Function.Structures.T_IsCongruent_22 ->
  MAlonzo.Code.Function.Structures.T_IsCongruent_22
d_isCongruent_174 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11
                  v12 ~v13 v14 v15
  = du_isCongruent_174 v12 v14 v15
du_isCongruent_174 ::
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsCongruent_22 ->
  MAlonzo.Code.Function.Structures.T_IsCongruent_22 ->
  MAlonzo.Code.Function.Structures.T_IsCongruent_22
du_isCongruent_174 v0 v1 v2
  = coe
      MAlonzo.Code.Function.Structures.C_IsCongruent'46'constructor_985
      (coe
         (\ v3 v4 v5 ->
            coe
              MAlonzo.Code.Function.Structures.d_cong_32 v2 (coe v0 v3)
              (coe v0 v4)
              (coe MAlonzo.Code.Function.Structures.d_cong_32 v1 v3 v4 v5)))
      (coe
         MAlonzo.Code.Function.Structures.d_isEquivalence'8321'_34 (coe v1))
      (coe
         MAlonzo.Code.Function.Structures.d_isEquivalence'8322'_36 (coe v2))
-- Function.Construct.Composition._.isInjection
d_isInjection_296 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsInjection_92 ->
  MAlonzo.Code.Function.Structures.T_IsInjection_92 ->
  MAlonzo.Code.Function.Structures.T_IsInjection_92
d_isInjection_296 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11
                  v12 ~v13 v14 v15
  = du_isInjection_296 v12 v14 v15
du_isInjection_296 ::
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsInjection_92 ->
  MAlonzo.Code.Function.Structures.T_IsInjection_92 ->
  MAlonzo.Code.Function.Structures.T_IsInjection_92
du_isInjection_296 v0 v1 v2
  = coe
      MAlonzo.Code.Function.Structures.C_IsInjection'46'constructor_3997
      (coe
         du_isCongruent_174 (coe v0)
         (coe MAlonzo.Code.Function.Structures.d_isCongruent_100 (coe v1))
         (coe MAlonzo.Code.Function.Structures.d_isCongruent_100 (coe v2)))
      (coe
         du_injective_56 (coe v0)
         (coe MAlonzo.Code.Function.Structures.d_injective_102 (coe v1))
         (coe MAlonzo.Code.Function.Structures.d_injective_102 (coe v2)))
-- Function.Construct.Composition._.isSurjection
d_isSurjection_426 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsSurjection_162 ->
  MAlonzo.Code.Function.Structures.T_IsSurjection_162 ->
  MAlonzo.Code.Function.Structures.T_IsSurjection_162
d_isSurjection_426 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
                   ~v11 v12 ~v13 v14 v15
  = du_isSurjection_426 v12 v14 v15
du_isSurjection_426 ::
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsSurjection_162 ->
  MAlonzo.Code.Function.Structures.T_IsSurjection_162 ->
  MAlonzo.Code.Function.Structures.T_IsSurjection_162
du_isSurjection_426 v0 v1 v2
  = coe
      MAlonzo.Code.Function.Structures.C_IsSurjection'46'constructor_6463
      (coe
         du_isCongruent_174 (coe v0)
         (coe MAlonzo.Code.Function.Structures.d_isCongruent_170 (coe v1))
         (coe MAlonzo.Code.Function.Structures.d_isCongruent_170 (coe v2)))
      (coe
         du_surjective_62 (coe v0)
         (coe MAlonzo.Code.Function.Structures.d_surjective_172 (coe v1))
         (coe MAlonzo.Code.Function.Structures.d_surjective_172 (coe v2)))
-- Function.Construct.Composition._.isBijection
d_isBijection_560 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsBijection_238 ->
  MAlonzo.Code.Function.Structures.T_IsBijection_238 ->
  MAlonzo.Code.Function.Structures.T_IsBijection_238
d_isBijection_560 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11
                  v12 ~v13 v14 v15
  = du_isBijection_560 v12 v14 v15
du_isBijection_560 ::
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsBijection_238 ->
  MAlonzo.Code.Function.Structures.T_IsBijection_238 ->
  MAlonzo.Code.Function.Structures.T_IsBijection_238
du_isBijection_560 v0 v1 v2
  = coe
      MAlonzo.Code.Function.Structures.C_IsBijection'46'constructor_10113
      (coe
         du_isInjection_296 (coe v0)
         (coe MAlonzo.Code.Function.Structures.d_isInjection_246 (coe v1))
         (coe MAlonzo.Code.Function.Structures.d_isInjection_246 (coe v2)))
      (coe
         du_surjective_62 (coe v0)
         (coe MAlonzo.Code.Function.Structures.d_surjective_248 (coe v1))
         (coe MAlonzo.Code.Function.Structures.d_surjective_248 (coe v2)))
-- Function.Construct.Composition._.isLeftInverse
d_isLeftInverse_740 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsLeftInverse_322 ->
  MAlonzo.Code.Function.Structures.T_IsLeftInverse_322 ->
  MAlonzo.Code.Function.Structures.T_IsLeftInverse_322
d_isLeftInverse_740 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
                    ~v11 v12 ~v13 ~v14 v15 v16 v17
  = du_isLeftInverse_740 v12 v15 v16 v17
du_isLeftInverse_740 ::
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsLeftInverse_322 ->
  MAlonzo.Code.Function.Structures.T_IsLeftInverse_322 ->
  MAlonzo.Code.Function.Structures.T_IsLeftInverse_322
du_isLeftInverse_740 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Function.Structures.C_IsLeftInverse'46'constructor_14363
      (coe
         du_isCongruent_174 (coe v0)
         (coe MAlonzo.Code.Function.Structures.d_isCongruent_334 (coe v2))
         (coe MAlonzo.Code.Function.Structures.d_isCongruent_334 (coe v3)))
      (coe
         du_congruent_50 (coe v1)
         (coe MAlonzo.Code.Function.Structures.d_from'45'cong_336 (coe v3))
         (coe MAlonzo.Code.Function.Structures.d_from'45'cong_336 (coe v2)))
      (coe
         du_inverse'737'_134 (coe v0) (coe v1)
         (coe MAlonzo.Code.Function.Structures.d_inverse'737'_338 (coe v2))
         (coe MAlonzo.Code.Function.Structures.d_inverse'737'_338 (coe v3)))
-- Function.Construct.Composition._.isRightInverse
d_isRightInverse_882 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsRightInverse_408 ->
  MAlonzo.Code.Function.Structures.T_IsRightInverse_408 ->
  MAlonzo.Code.Function.Structures.T_IsRightInverse_408
d_isRightInverse_882 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
                     ~v11 v12 ~v13 ~v14 v15 v16 v17
  = du_isRightInverse_882 v12 v15 v16 v17
du_isRightInverse_882 ::
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsRightInverse_408 ->
  MAlonzo.Code.Function.Structures.T_IsRightInverse_408 ->
  MAlonzo.Code.Function.Structures.T_IsRightInverse_408
du_isRightInverse_882 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Function.Structures.C_IsRightInverse'46'constructor_18837
      (coe
         du_isCongruent_174 (coe v0)
         (coe MAlonzo.Code.Function.Structures.d_isCongruent_420 (coe v2))
         (coe MAlonzo.Code.Function.Structures.d_isCongruent_420 (coe v3)))
      (coe
         du_congruent_50 (coe v1)
         (coe MAlonzo.Code.Function.Structures.d_from'45'cong_422 (coe v3))
         (coe MAlonzo.Code.Function.Structures.d_from'45'cong_422 (coe v2)))
      (coe
         du_inverse'691'_140 (coe v0) (coe v1)
         (coe MAlonzo.Code.Function.Structures.d_inverse'691'_424 (coe v2))
         (coe MAlonzo.Code.Function.Structures.d_inverse'691'_424 (coe v3)))
-- Function.Construct.Composition._.isInverse
d_isInverse_1020 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsInverse_490 ->
  MAlonzo.Code.Function.Structures.T_IsInverse_490 ->
  MAlonzo.Code.Function.Structures.T_IsInverse_490
d_isInverse_1020 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11
                 v12 ~v13 ~v14 v15 v16 v17
  = du_isInverse_1020 v12 v15 v16 v17
du_isInverse_1020 ::
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsInverse_490 ->
  MAlonzo.Code.Function.Structures.T_IsInverse_490 ->
  MAlonzo.Code.Function.Structures.T_IsInverse_490
du_isInverse_1020 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Function.Structures.C_IsInverse'46'constructor_22449
      (coe
         du_isLeftInverse_740 (coe v0) (coe v1)
         (coe MAlonzo.Code.Function.Structures.d_isLeftInverse_500 (coe v2))
         (coe
            MAlonzo.Code.Function.Structures.d_isLeftInverse_500 (coe v3)))
      (coe
         du_inverse'691'_140 (coe v0) (coe v1)
         (coe MAlonzo.Code.Function.Structures.d_inverse'691'_502 (coe v2))
         (coe MAlonzo.Code.Function.Structures.d_inverse'691'_502 (coe v3)))
-- Function.Construct.Composition._.function
d_function_1204 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Function.Bundles.T_Func_714 ->
  MAlonzo.Code.Function.Bundles.T_Func_714 ->
  MAlonzo.Code.Function.Bundles.T_Func_714
d_function_1204 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9 v10
  = du_function_1204 v9 v10
du_function_1204 ::
  MAlonzo.Code.Function.Bundles.T_Func_714 ->
  MAlonzo.Code.Function.Bundles.T_Func_714 ->
  MAlonzo.Code.Function.Bundles.T_Func_714
du_function_1204 v0 v1
  = coe
      MAlonzo.Code.Function.Bundles.C_Func'46'constructor_6307
      (coe
         (\ v2 ->
            coe
              MAlonzo.Code.Function.Bundles.d_to_720 v1
              (coe MAlonzo.Code.Function.Bundles.d_to_720 v0 v2)))
      (coe
         du_congruent_50
         (coe MAlonzo.Code.Function.Bundles.d_to_720 (coe v0))
         (coe MAlonzo.Code.Function.Bundles.d_cong_722 (coe v0))
         (coe MAlonzo.Code.Function.Bundles.d_cong_722 (coe v1)))
-- Function.Construct.Composition._.injection
d_injection_1326 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Function.Bundles.T_Injection_776 ->
  MAlonzo.Code.Function.Bundles.T_Injection_776 ->
  MAlonzo.Code.Function.Bundles.T_Injection_776
d_injection_1326 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9 v10
  = du_injection_1326 v9 v10
du_injection_1326 ::
  MAlonzo.Code.Function.Bundles.T_Injection_776 ->
  MAlonzo.Code.Function.Bundles.T_Injection_776 ->
  MAlonzo.Code.Function.Bundles.T_Injection_776
du_injection_1326 v0 v1
  = coe
      MAlonzo.Code.Function.Bundles.C_Injection'46'constructor_8675
      (coe
         (\ v2 ->
            coe
              MAlonzo.Code.Function.Bundles.d_to_784 v1
              (coe MAlonzo.Code.Function.Bundles.d_to_784 v0 v2)))
      (coe
         du_congruent_50
         (coe MAlonzo.Code.Function.Bundles.d_to_784 (coe v0))
         (coe MAlonzo.Code.Function.Bundles.d_cong_786 (coe v0))
         (coe MAlonzo.Code.Function.Bundles.d_cong_786 (coe v1)))
      (coe
         du_injective_56
         (coe MAlonzo.Code.Function.Bundles.d_to_784 (coe v0))
         (coe MAlonzo.Code.Function.Bundles.d_injective_788 (coe v0))
         (coe MAlonzo.Code.Function.Bundles.d_injective_788 (coe v1)))
-- Function.Construct.Composition._.surjection
d_surjection_1460 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Function.Bundles.T_Surjection_846 ->
  MAlonzo.Code.Function.Bundles.T_Surjection_846 ->
  MAlonzo.Code.Function.Bundles.T_Surjection_846
d_surjection_1460 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9 v10
  = du_surjection_1460 v9 v10
du_surjection_1460 ::
  MAlonzo.Code.Function.Bundles.T_Surjection_846 ->
  MAlonzo.Code.Function.Bundles.T_Surjection_846 ->
  MAlonzo.Code.Function.Bundles.T_Surjection_846
du_surjection_1460 v0 v1
  = coe
      MAlonzo.Code.Function.Bundles.C_Surjection'46'constructor_11197
      (coe
         (\ v2 ->
            coe
              MAlonzo.Code.Function.Bundles.d_to_854 v1
              (coe MAlonzo.Code.Function.Bundles.d_to_854 v0 v2)))
      (coe
         du_congruent_50
         (coe MAlonzo.Code.Function.Bundles.d_to_854 (coe v0))
         (coe MAlonzo.Code.Function.Bundles.d_cong_856 (coe v0))
         (coe MAlonzo.Code.Function.Bundles.d_cong_856 (coe v1)))
      (coe
         du_surjective_62
         (coe MAlonzo.Code.Function.Bundles.d_to_854 (coe v0))
         (coe MAlonzo.Code.Function.Bundles.d_surjective_858 (coe v0))
         (coe MAlonzo.Code.Function.Bundles.d_surjective_858 (coe v1)))
-- Function.Construct.Composition._.bijection
d_bijection_1606 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Function.Bundles.T_Bijection_926 ->
  MAlonzo.Code.Function.Bundles.T_Bijection_926 ->
  MAlonzo.Code.Function.Bundles.T_Bijection_926
d_bijection_1606 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9 v10
  = du_bijection_1606 v9 v10
du_bijection_1606 ::
  MAlonzo.Code.Function.Bundles.T_Bijection_926 ->
  MAlonzo.Code.Function.Bundles.T_Bijection_926 ->
  MAlonzo.Code.Function.Bundles.T_Bijection_926
du_bijection_1606 v0 v1
  = coe
      MAlonzo.Code.Function.Bundles.C_Bijection'46'constructor_15277
      (coe
         (\ v2 ->
            coe
              MAlonzo.Code.Function.Bundles.d_to_934 v1
              (coe MAlonzo.Code.Function.Bundles.d_to_934 v0 v2)))
      (coe
         du_congruent_50
         (coe MAlonzo.Code.Function.Bundles.d_to_934 (coe v0))
         (coe MAlonzo.Code.Function.Bundles.d_cong_936 (coe v0))
         (coe MAlonzo.Code.Function.Bundles.d_cong_936 (coe v1)))
      (coe
         du_bijective_102 (MAlonzo.Code.Function.Bundles.d_to_934 (coe v0))
         (MAlonzo.Code.Function.Bundles.d_bijective_938 (coe v0))
         (MAlonzo.Code.Function.Bundles.d_bijective_938 (coe v1)))
-- Function.Construct.Composition._.equivalence
d_equivalence_1764 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Function.Bundles.T_Equivalence_1714 ->
  MAlonzo.Code.Function.Bundles.T_Equivalence_1714 ->
  MAlonzo.Code.Function.Bundles.T_Equivalence_1714
d_equivalence_1764 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9 v10
  = du_equivalence_1764 v9 v10
du_equivalence_1764 ::
  MAlonzo.Code.Function.Bundles.T_Equivalence_1714 ->
  MAlonzo.Code.Function.Bundles.T_Equivalence_1714 ->
  MAlonzo.Code.Function.Bundles.T_Equivalence_1714
du_equivalence_1764 v0 v1
  = coe
      MAlonzo.Code.Function.Bundles.C_Equivalence'46'constructor_25797
      (coe
         (\ v2 ->
            coe
              MAlonzo.Code.Function.Bundles.d_to_1724 v1
              (coe MAlonzo.Code.Function.Bundles.d_to_1724 v0 v2)))
      (coe
         (\ v2 ->
            coe
              MAlonzo.Code.Function.Bundles.d_from_1726 v0
              (coe MAlonzo.Code.Function.Bundles.d_from_1726 v1 v2)))
      (coe
         du_congruent_50
         (coe MAlonzo.Code.Function.Bundles.d_to_1724 (coe v0))
         (coe MAlonzo.Code.Function.Bundles.d_to'45'cong_1728 (coe v0))
         (coe MAlonzo.Code.Function.Bundles.d_to'45'cong_1728 (coe v1)))
      (coe
         du_congruent_50
         (coe MAlonzo.Code.Function.Bundles.d_from_1726 (coe v1))
         (coe MAlonzo.Code.Function.Bundles.d_from'45'cong_1730 (coe v1))
         (coe MAlonzo.Code.Function.Bundles.d_from'45'cong_1730 (coe v0)))
-- Function.Construct.Composition._.leftInverse
d_leftInverse_1906 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Function.Bundles.T_LeftInverse_1792 ->
  MAlonzo.Code.Function.Bundles.T_LeftInverse_1792 ->
  MAlonzo.Code.Function.Bundles.T_LeftInverse_1792
d_leftInverse_1906 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9 v10
  = du_leftInverse_1906 v9 v10
du_leftInverse_1906 ::
  MAlonzo.Code.Function.Bundles.T_LeftInverse_1792 ->
  MAlonzo.Code.Function.Bundles.T_LeftInverse_1792 ->
  MAlonzo.Code.Function.Bundles.T_LeftInverse_1792
du_leftInverse_1906 v0 v1
  = coe
      MAlonzo.Code.Function.Bundles.C_LeftInverse'46'constructor_29775
      (coe
         (\ v2 ->
            coe
              MAlonzo.Code.Function.Bundles.d_to_1804 v1
              (coe MAlonzo.Code.Function.Bundles.d_to_1804 v0 v2)))
      (coe
         (\ v2 ->
            coe
              MAlonzo.Code.Function.Bundles.d_from_1806 v0
              (coe MAlonzo.Code.Function.Bundles.d_from_1806 v1 v2)))
      (coe
         du_congruent_50
         (coe MAlonzo.Code.Function.Bundles.d_to_1804 (coe v0))
         (coe MAlonzo.Code.Function.Bundles.d_to'45'cong_1808 (coe v0))
         (coe MAlonzo.Code.Function.Bundles.d_to'45'cong_1808 (coe v1)))
      (coe
         du_congruent_50
         (coe MAlonzo.Code.Function.Bundles.d_from_1806 (coe v1))
         (coe MAlonzo.Code.Function.Bundles.d_from'45'cong_1810 (coe v1))
         (coe MAlonzo.Code.Function.Bundles.d_from'45'cong_1810 (coe v0)))
      (coe
         du_inverse'737'_134
         (coe MAlonzo.Code.Function.Bundles.d_to_1804 (coe v0))
         (coe MAlonzo.Code.Function.Bundles.d_from_1806 (coe v1))
         (coe MAlonzo.Code.Function.Bundles.d_inverse'737'_1812 (coe v0))
         (coe MAlonzo.Code.Function.Bundles.d_inverse'737'_1812 (coe v1)))
-- Function.Construct.Composition._.rightInverse
d_rightInverse_2064 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Function.Bundles.T_RightInverse_1880 ->
  MAlonzo.Code.Function.Bundles.T_RightInverse_1880 ->
  MAlonzo.Code.Function.Bundles.T_RightInverse_1880
d_rightInverse_2064 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9 v10
  = du_rightInverse_2064 v9 v10
du_rightInverse_2064 ::
  MAlonzo.Code.Function.Bundles.T_RightInverse_1880 ->
  MAlonzo.Code.Function.Bundles.T_RightInverse_1880 ->
  MAlonzo.Code.Function.Bundles.T_RightInverse_1880
du_rightInverse_2064 v0 v1
  = coe
      MAlonzo.Code.Function.Bundles.C_RightInverse'46'constructor_34573
      (coe
         (\ v2 ->
            coe
              MAlonzo.Code.Function.Bundles.d_to_1892 v1
              (coe MAlonzo.Code.Function.Bundles.d_to_1892 v0 v2)))
      (coe
         (\ v2 ->
            coe
              MAlonzo.Code.Function.Bundles.d_from_1894 v0
              (coe MAlonzo.Code.Function.Bundles.d_from_1894 v1 v2)))
      (coe
         du_congruent_50
         (coe MAlonzo.Code.Function.Bundles.d_to_1892 (coe v0))
         (coe MAlonzo.Code.Function.Bundles.d_to'45'cong_1896 (coe v0))
         (coe MAlonzo.Code.Function.Bundles.d_to'45'cong_1896 (coe v1)))
      (coe
         du_congruent_50
         (coe MAlonzo.Code.Function.Bundles.d_from_1894 (coe v1))
         (coe MAlonzo.Code.Function.Bundles.d_from'45'cong_1898 (coe v1))
         (coe MAlonzo.Code.Function.Bundles.d_from'45'cong_1898 (coe v0)))
      (coe
         du_inverse'691'_140
         (coe MAlonzo.Code.Function.Bundles.d_to_1892 (coe v0))
         (coe MAlonzo.Code.Function.Bundles.d_from_1894 (coe v1))
         (coe MAlonzo.Code.Function.Bundles.d_inverse'691'_1900 (coe v0))
         (coe MAlonzo.Code.Function.Bundles.d_inverse'691'_1900 (coe v1)))
-- Function.Construct.Composition._.inverse
d_inverse_2210 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Function.Bundles.T_Inverse_1960 ->
  MAlonzo.Code.Function.Bundles.T_Inverse_1960 ->
  MAlonzo.Code.Function.Bundles.T_Inverse_1960
d_inverse_2210 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9 v10
  = du_inverse_2210 v9 v10
du_inverse_2210 ::
  MAlonzo.Code.Function.Bundles.T_Inverse_1960 ->
  MAlonzo.Code.Function.Bundles.T_Inverse_1960 ->
  MAlonzo.Code.Function.Bundles.T_Inverse_1960
du_inverse_2210 v0 v1
  = coe
      MAlonzo.Code.Function.Bundles.C_Inverse'46'constructor_38621
      (coe
         (\ v2 ->
            coe
              MAlonzo.Code.Function.Bundles.d_to_1972 v1
              (coe MAlonzo.Code.Function.Bundles.d_to_1972 v0 v2)))
      (coe
         (\ v2 ->
            coe
              MAlonzo.Code.Function.Bundles.d_from_1974 v0
              (coe MAlonzo.Code.Function.Bundles.d_from_1974 v1 v2)))
      (coe
         du_congruent_50
         (coe MAlonzo.Code.Function.Bundles.d_to_1972 (coe v0))
         (coe MAlonzo.Code.Function.Bundles.d_to'45'cong_1976 (coe v0))
         (coe MAlonzo.Code.Function.Bundles.d_to'45'cong_1976 (coe v1)))
      (coe
         du_congruent_50
         (coe MAlonzo.Code.Function.Bundles.d_from_1974 (coe v1))
         (coe MAlonzo.Code.Function.Bundles.d_from'45'cong_1978 (coe v1))
         (coe MAlonzo.Code.Function.Bundles.d_from'45'cong_1978 (coe v0)))
      (coe
         du_inverse'7495'_146
         (MAlonzo.Code.Function.Bundles.d_to_1972 (coe v0))
         (MAlonzo.Code.Function.Bundles.d_from_1974 (coe v1))
         (MAlonzo.Code.Function.Bundles.d_inverse_1980 (coe v0))
         (MAlonzo.Code.Function.Bundles.d_inverse_1980 (coe v1)))
-- Function.Construct.Composition._⟶-∘_
d__'10230''45''8728'__2376 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Function.Bundles.T_Func_714 ->
  MAlonzo.Code.Function.Bundles.T_Func_714 ->
  MAlonzo.Code.Function.Bundles.T_Func_714
d__'10230''45''8728'__2376 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7
  = du__'10230''45''8728'__2376 v6 v7
du__'10230''45''8728'__2376 ::
  MAlonzo.Code.Function.Bundles.T_Func_714 ->
  MAlonzo.Code.Function.Bundles.T_Func_714 ->
  MAlonzo.Code.Function.Bundles.T_Func_714
du__'10230''45''8728'__2376 v0 v1
  = coe du_function_1204 (coe v1) (coe v0)
-- Function.Construct.Composition._↣-∘_
d__'8611''45''8728'__2378 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Function.Bundles.T_Injection_776 ->
  MAlonzo.Code.Function.Bundles.T_Injection_776 ->
  MAlonzo.Code.Function.Bundles.T_Injection_776
d__'8611''45''8728'__2378 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7
  = du__'8611''45''8728'__2378 v6 v7
du__'8611''45''8728'__2378 ::
  MAlonzo.Code.Function.Bundles.T_Injection_776 ->
  MAlonzo.Code.Function.Bundles.T_Injection_776 ->
  MAlonzo.Code.Function.Bundles.T_Injection_776
du__'8611''45''8728'__2378 v0 v1
  = coe du_injection_1326 (coe v1) (coe v0)
-- Function.Construct.Composition._↠-∘_
d__'8608''45''8728'__2380 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Function.Bundles.T_Surjection_846 ->
  MAlonzo.Code.Function.Bundles.T_Surjection_846 ->
  MAlonzo.Code.Function.Bundles.T_Surjection_846
d__'8608''45''8728'__2380 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7
  = du__'8608''45''8728'__2380 v6 v7
du__'8608''45''8728'__2380 ::
  MAlonzo.Code.Function.Bundles.T_Surjection_846 ->
  MAlonzo.Code.Function.Bundles.T_Surjection_846 ->
  MAlonzo.Code.Function.Bundles.T_Surjection_846
du__'8608''45''8728'__2380 v0 v1
  = coe du_surjection_1460 (coe v1) (coe v0)
-- Function.Construct.Composition._⤖-∘_
d__'10518''45''8728'__2382 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Function.Bundles.T_Bijection_926 ->
  MAlonzo.Code.Function.Bundles.T_Bijection_926 ->
  MAlonzo.Code.Function.Bundles.T_Bijection_926
d__'10518''45''8728'__2382 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7
  = du__'10518''45''8728'__2382 v6 v7
du__'10518''45''8728'__2382 ::
  MAlonzo.Code.Function.Bundles.T_Bijection_926 ->
  MAlonzo.Code.Function.Bundles.T_Bijection_926 ->
  MAlonzo.Code.Function.Bundles.T_Bijection_926
du__'10518''45''8728'__2382 v0 v1
  = coe du_bijection_1606 (coe v1) (coe v0)
-- Function.Construct.Composition._⇔-∘_
d__'8660''45''8728'__2384 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Function.Bundles.T_Equivalence_1714 ->
  MAlonzo.Code.Function.Bundles.T_Equivalence_1714 ->
  MAlonzo.Code.Function.Bundles.T_Equivalence_1714
d__'8660''45''8728'__2384 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7
  = du__'8660''45''8728'__2384 v6 v7
du__'8660''45''8728'__2384 ::
  MAlonzo.Code.Function.Bundles.T_Equivalence_1714 ->
  MAlonzo.Code.Function.Bundles.T_Equivalence_1714 ->
  MAlonzo.Code.Function.Bundles.T_Equivalence_1714
du__'8660''45''8728'__2384 v0 v1
  = coe du_equivalence_1764 (coe v1) (coe v0)
-- Function.Construct.Composition._↩-∘_
d__'8617''45''8728'__2386 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Function.Bundles.T_LeftInverse_1792 ->
  MAlonzo.Code.Function.Bundles.T_LeftInverse_1792 ->
  MAlonzo.Code.Function.Bundles.T_LeftInverse_1792
d__'8617''45''8728'__2386 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7
  = du__'8617''45''8728'__2386 v6 v7
du__'8617''45''8728'__2386 ::
  MAlonzo.Code.Function.Bundles.T_LeftInverse_1792 ->
  MAlonzo.Code.Function.Bundles.T_LeftInverse_1792 ->
  MAlonzo.Code.Function.Bundles.T_LeftInverse_1792
du__'8617''45''8728'__2386 v0 v1
  = coe du_leftInverse_1906 (coe v1) (coe v0)
-- Function.Construct.Composition._↪-∘_
d__'8618''45''8728'__2388 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Function.Bundles.T_RightInverse_1880 ->
  MAlonzo.Code.Function.Bundles.T_RightInverse_1880 ->
  MAlonzo.Code.Function.Bundles.T_RightInverse_1880
d__'8618''45''8728'__2388 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7
  = du__'8618''45''8728'__2388 v6 v7
du__'8618''45''8728'__2388 ::
  MAlonzo.Code.Function.Bundles.T_RightInverse_1880 ->
  MAlonzo.Code.Function.Bundles.T_RightInverse_1880 ->
  MAlonzo.Code.Function.Bundles.T_RightInverse_1880
du__'8618''45''8728'__2388 v0 v1
  = coe du_rightInverse_2064 (coe v1) (coe v0)
-- Function.Construct.Composition._↔-∘_
d__'8596''45''8728'__2390 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Function.Bundles.T_Inverse_1960 ->
  MAlonzo.Code.Function.Bundles.T_Inverse_1960 ->
  MAlonzo.Code.Function.Bundles.T_Inverse_1960
d__'8596''45''8728'__2390 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7
  = du__'8596''45''8728'__2390 v6 v7
du__'8596''45''8728'__2390 ::
  MAlonzo.Code.Function.Bundles.T_Inverse_1960 ->
  MAlonzo.Code.Function.Bundles.T_Inverse_1960 ->
  MAlonzo.Code.Function.Bundles.T_Inverse_1960
du__'8596''45''8728'__2390 v0 v1
  = coe du_inverse_2210 (coe v1) (coe v0)
-- Function.Construct.Composition._∘-⟶_
d__'8728''45''10230'__2392 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Function.Bundles.T_Func_714 ->
  MAlonzo.Code.Function.Bundles.T_Func_714 ->
  MAlonzo.Code.Function.Bundles.T_Func_714
d__'8728''45''10230'__2392 v0 v1 v2 v3 v4 v5 v6 v7
  = coe du__'10230''45''8728'__2376 v6 v7
-- Function.Construct.Composition._∘-↣_
d__'8728''45''8611'__2394 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Function.Bundles.T_Injection_776 ->
  MAlonzo.Code.Function.Bundles.T_Injection_776 ->
  MAlonzo.Code.Function.Bundles.T_Injection_776
d__'8728''45''8611'__2394 v0 v1 v2 v3 v4 v5 v6 v7
  = coe du__'8611''45''8728'__2378 v6 v7
-- Function.Construct.Composition._∘-↠_
d__'8728''45''8608'__2396 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Function.Bundles.T_Surjection_846 ->
  MAlonzo.Code.Function.Bundles.T_Surjection_846 ->
  MAlonzo.Code.Function.Bundles.T_Surjection_846
d__'8728''45''8608'__2396 v0 v1 v2 v3 v4 v5 v6 v7
  = coe du__'8608''45''8728'__2380 v6 v7
-- Function.Construct.Composition._∘-⤖_
d__'8728''45''10518'__2398 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Function.Bundles.T_Bijection_926 ->
  MAlonzo.Code.Function.Bundles.T_Bijection_926 ->
  MAlonzo.Code.Function.Bundles.T_Bijection_926
d__'8728''45''10518'__2398 v0 v1 v2 v3 v4 v5 v6 v7
  = coe du__'10518''45''8728'__2382 v6 v7
-- Function.Construct.Composition._∘-⇔_
d__'8728''45''8660'__2400 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Function.Bundles.T_Equivalence_1714 ->
  MAlonzo.Code.Function.Bundles.T_Equivalence_1714 ->
  MAlonzo.Code.Function.Bundles.T_Equivalence_1714
d__'8728''45''8660'__2400 v0 v1 v2 v3 v4 v5 v6 v7
  = coe du__'8660''45''8728'__2384 v6 v7
-- Function.Construct.Composition._∘-↩_
d__'8728''45''8617'__2402 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Function.Bundles.T_LeftInverse_1792 ->
  MAlonzo.Code.Function.Bundles.T_LeftInverse_1792 ->
  MAlonzo.Code.Function.Bundles.T_LeftInverse_1792
d__'8728''45''8617'__2402 v0 v1 v2 v3 v4 v5 v6 v7
  = coe du__'8617''45''8728'__2386 v6 v7
-- Function.Construct.Composition._∘-↪_
d__'8728''45''8618'__2404 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Function.Bundles.T_RightInverse_1880 ->
  MAlonzo.Code.Function.Bundles.T_RightInverse_1880 ->
  MAlonzo.Code.Function.Bundles.T_RightInverse_1880
d__'8728''45''8618'__2404 v0 v1 v2 v3 v4 v5 v6 v7
  = coe du__'8618''45''8728'__2388 v6 v7
-- Function.Construct.Composition._∘-↔_
d__'8728''45''8596'__2406 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Function.Bundles.T_Inverse_1960 ->
  MAlonzo.Code.Function.Bundles.T_Inverse_1960 ->
  MAlonzo.Code.Function.Bundles.T_Inverse_1960
d__'8728''45''8596'__2406 v0 v1 v2 v3 v4 v5 v6 v7
  = coe du__'8596''45''8728'__2390 v6 v7
