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

module MAlonzo.Code.Function.Construct.Composition where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Data.Product.Base
import qualified MAlonzo.Code.Function.Bundles
import qualified MAlonzo.Code.Function.Structures
import qualified MAlonzo.Code.Relation.Binary.Bundles

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
      MAlonzo.Code.Function.Structures.C_constructor_94
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
d_isInjection_304 ::
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
  MAlonzo.Code.Function.Structures.T_IsInjection_98 ->
  MAlonzo.Code.Function.Structures.T_IsInjection_98 ->
  MAlonzo.Code.Function.Structures.T_IsInjection_98
d_isInjection_304 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11
                  v12 ~v13 v14 v15
  = du_isInjection_304 v12 v14 v15
du_isInjection_304 ::
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsInjection_98 ->
  MAlonzo.Code.Function.Structures.T_IsInjection_98 ->
  MAlonzo.Code.Function.Structures.T_IsInjection_98
du_isInjection_304 v0 v1 v2
  = coe
      MAlonzo.Code.Function.Structures.C_constructor_170
      (coe
         du_isCongruent_174 (coe v0)
         (coe MAlonzo.Code.Function.Structures.d_isCongruent_106 (coe v1))
         (coe MAlonzo.Code.Function.Structures.d_isCongruent_106 (coe v2)))
      (coe
         du_injective_56 (coe v0)
         (coe MAlonzo.Code.Function.Structures.d_injective_108 (coe v1))
         (coe MAlonzo.Code.Function.Structures.d_injective_108 (coe v2)))
-- Function.Construct.Composition._.isSurjection
d_isSurjection_442 ::
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
  MAlonzo.Code.Function.Structures.T_IsSurjection_174 ->
  MAlonzo.Code.Function.Structures.T_IsSurjection_174 ->
  MAlonzo.Code.Function.Structures.T_IsSurjection_174
d_isSurjection_442 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
                   ~v11 v12 ~v13 v14 v15
  = du_isSurjection_442 v12 v14 v15
du_isSurjection_442 ::
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsSurjection_174 ->
  MAlonzo.Code.Function.Structures.T_IsSurjection_174 ->
  MAlonzo.Code.Function.Structures.T_IsSurjection_174
du_isSurjection_442 v0 v1 v2
  = coe
      MAlonzo.Code.Function.Structures.C_constructor_252
      (coe
         du_isCongruent_174 (coe v0)
         (coe MAlonzo.Code.Function.Structures.d_isCongruent_182 (coe v1))
         (coe MAlonzo.Code.Function.Structures.d_isCongruent_182 (coe v2)))
      (coe
         du_surjective_62 (coe v0)
         (coe MAlonzo.Code.Function.Structures.d_surjective_184 (coe v1))
         (coe MAlonzo.Code.Function.Structures.d_surjective_184 (coe v2)))
-- Function.Construct.Composition._.isBijection
d_isBijection_584 ::
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
  MAlonzo.Code.Function.Structures.T_IsBijection_256 ->
  MAlonzo.Code.Function.Structures.T_IsBijection_256 ->
  MAlonzo.Code.Function.Structures.T_IsBijection_256
d_isBijection_584 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11
                  v12 ~v13 v14 v15
  = du_isBijection_584 v12 v14 v15
du_isBijection_584 ::
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsBijection_256 ->
  MAlonzo.Code.Function.Structures.T_IsBijection_256 ->
  MAlonzo.Code.Function.Structures.T_IsBijection_256
du_isBijection_584 v0 v1 v2
  = coe
      MAlonzo.Code.Function.Structures.C_constructor_340
      (coe
         du_isInjection_304 (coe v0)
         (coe MAlonzo.Code.Function.Structures.d_isInjection_264 (coe v1))
         (coe MAlonzo.Code.Function.Structures.d_isInjection_264 (coe v2)))
      (coe
         du_surjective_62 (coe v0)
         (coe MAlonzo.Code.Function.Structures.d_surjective_266 (coe v1))
         (coe MAlonzo.Code.Function.Structures.d_surjective_266 (coe v2)))
-- Function.Construct.Composition._.isLeftInverse
d_isLeftInverse_772 ::
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
  MAlonzo.Code.Function.Structures.T_IsLeftInverse_346 ->
  MAlonzo.Code.Function.Structures.T_IsLeftInverse_346 ->
  MAlonzo.Code.Function.Structures.T_IsLeftInverse_346
d_isLeftInverse_772 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
                    ~v11 v12 ~v13 ~v14 v15 v16 v17
  = du_isLeftInverse_772 v12 v15 v16 v17
du_isLeftInverse_772 ::
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsLeftInverse_346 ->
  MAlonzo.Code.Function.Structures.T_IsLeftInverse_346 ->
  MAlonzo.Code.Function.Structures.T_IsLeftInverse_346
du_isLeftInverse_772 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Function.Structures.C_constructor_432
      (coe
         du_isCongruent_174 (coe v0)
         (coe MAlonzo.Code.Function.Structures.d_isCongruent_358 (coe v2))
         (coe MAlonzo.Code.Function.Structures.d_isCongruent_358 (coe v3)))
      (coe
         du_congruent_50 (coe v1)
         (coe MAlonzo.Code.Function.Structures.d_from'45'cong_360 (coe v3))
         (coe MAlonzo.Code.Function.Structures.d_from'45'cong_360 (coe v2)))
      (coe
         du_inverse'737'_134 (coe v0) (coe v1)
         (coe MAlonzo.Code.Function.Structures.d_inverse'737'_362 (coe v2))
         (coe MAlonzo.Code.Function.Structures.d_inverse'737'_362 (coe v3)))
-- Function.Construct.Composition._.isRightInverse
d_isRightInverse_922 ::
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
  MAlonzo.Code.Function.Structures.T_IsRightInverse_438 ->
  MAlonzo.Code.Function.Structures.T_IsRightInverse_438 ->
  MAlonzo.Code.Function.Structures.T_IsRightInverse_438
d_isRightInverse_922 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
                     ~v11 v12 ~v13 ~v14 v15 v16 v17
  = du_isRightInverse_922 v12 v15 v16 v17
du_isRightInverse_922 ::
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsRightInverse_438 ->
  MAlonzo.Code.Function.Structures.T_IsRightInverse_438 ->
  MAlonzo.Code.Function.Structures.T_IsRightInverse_438
du_isRightInverse_922 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Function.Structures.C_constructor_520
      (coe
         du_isCongruent_174 (coe v0)
         (coe MAlonzo.Code.Function.Structures.d_isCongruent_450 (coe v2))
         (coe MAlonzo.Code.Function.Structures.d_isCongruent_450 (coe v3)))
      (coe
         du_congruent_50 (coe v1)
         (coe MAlonzo.Code.Function.Structures.d_from'45'cong_452 (coe v3))
         (coe MAlonzo.Code.Function.Structures.d_from'45'cong_452 (coe v2)))
      (coe
         du_inverse'691'_140 (coe v0) (coe v1)
         (coe MAlonzo.Code.Function.Structures.d_inverse'691'_454 (coe v2))
         (coe MAlonzo.Code.Function.Structures.d_inverse'691'_454 (coe v3)))
-- Function.Construct.Composition._.isInverse
d_isInverse_1068 ::
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
  MAlonzo.Code.Function.Structures.T_IsInverse_526 ->
  MAlonzo.Code.Function.Structures.T_IsInverse_526 ->
  MAlonzo.Code.Function.Structures.T_IsInverse_526
d_isInverse_1068 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11
                 v12 ~v13 ~v14 v15 v16 v17
  = du_isInverse_1068 v12 v15 v16 v17
du_isInverse_1068 ::
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Structures.T_IsInverse_526 ->
  MAlonzo.Code.Function.Structures.T_IsInverse_526 ->
  MAlonzo.Code.Function.Structures.T_IsInverse_526
du_isInverse_1068 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Function.Structures.C_constructor_618
      (coe
         du_isLeftInverse_772 (coe v0) (coe v1)
         (coe MAlonzo.Code.Function.Structures.d_isLeftInverse_536 (coe v2))
         (coe
            MAlonzo.Code.Function.Structures.d_isLeftInverse_536 (coe v3)))
      (coe
         du_inverse'691'_140 (coe v0) (coe v1)
         (coe MAlonzo.Code.Function.Structures.d_inverse'691'_538 (coe v2))
         (coe MAlonzo.Code.Function.Structures.d_inverse'691'_538 (coe v3)))
-- Function.Construct.Composition._.function
d_function_1260 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Function.Bundles.T_Func_774 ->
  MAlonzo.Code.Function.Bundles.T_Func_774 ->
  MAlonzo.Code.Function.Bundles.T_Func_774
d_function_1260 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9 v10
  = du_function_1260 v9 v10
du_function_1260 ::
  MAlonzo.Code.Function.Bundles.T_Func_774 ->
  MAlonzo.Code.Function.Bundles.T_Func_774 ->
  MAlonzo.Code.Function.Bundles.T_Func_774
du_function_1260 v0 v1
  = coe
      MAlonzo.Code.Function.Bundles.C_constructor_840
      (coe
         (\ v2 ->
            coe
              MAlonzo.Code.Function.Bundles.d_to_780 v1
              (coe MAlonzo.Code.Function.Bundles.d_to_780 v0 v2)))
      (coe
         du_congruent_50
         (coe MAlonzo.Code.Function.Bundles.d_to_780 (coe v0))
         (coe MAlonzo.Code.Function.Bundles.d_cong_782 (coe v0))
         (coe MAlonzo.Code.Function.Bundles.d_cong_782 (coe v1)))
-- Function.Construct.Composition._.injection
d_injection_1390 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Function.Bundles.T_Injection_842 ->
  MAlonzo.Code.Function.Bundles.T_Injection_842 ->
  MAlonzo.Code.Function.Bundles.T_Injection_842
d_injection_1390 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9 v10
  = du_injection_1390 v9 v10
du_injection_1390 ::
  MAlonzo.Code.Function.Bundles.T_Injection_842 ->
  MAlonzo.Code.Function.Bundles.T_Injection_842 ->
  MAlonzo.Code.Function.Bundles.T_Injection_842
du_injection_1390 v0 v1
  = coe
      MAlonzo.Code.Function.Bundles.C_constructor_916
      (coe
         (\ v2 ->
            coe
              MAlonzo.Code.Function.Bundles.d_to_850 v1
              (coe MAlonzo.Code.Function.Bundles.d_to_850 v0 v2)))
      (coe
         du_congruent_50
         (coe MAlonzo.Code.Function.Bundles.d_to_850 (coe v0))
         (coe MAlonzo.Code.Function.Bundles.d_cong_852 (coe v0))
         (coe MAlonzo.Code.Function.Bundles.d_cong_852 (coe v1)))
      (coe
         du_injective_56
         (coe MAlonzo.Code.Function.Bundles.d_to_850 (coe v0))
         (coe MAlonzo.Code.Function.Bundles.d_injective_854 (coe v0))
         (coe MAlonzo.Code.Function.Bundles.d_injective_854 (coe v1)))
-- Function.Construct.Composition._.surjection
d_surjection_1532 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Function.Bundles.T_Surjection_918 ->
  MAlonzo.Code.Function.Bundles.T_Surjection_918 ->
  MAlonzo.Code.Function.Bundles.T_Surjection_918
d_surjection_1532 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9 v10
  = du_surjection_1532 v9 v10
du_surjection_1532 ::
  MAlonzo.Code.Function.Bundles.T_Surjection_918 ->
  MAlonzo.Code.Function.Bundles.T_Surjection_918 ->
  MAlonzo.Code.Function.Bundles.T_Surjection_918
du_surjection_1532 v0 v1
  = coe
      MAlonzo.Code.Function.Bundles.C_constructor_1002
      (coe
         (\ v2 ->
            coe
              MAlonzo.Code.Function.Bundles.d_to_926 v1
              (coe MAlonzo.Code.Function.Bundles.d_to_926 v0 v2)))
      (coe
         du_congruent_50
         (coe MAlonzo.Code.Function.Bundles.d_to_926 (coe v0))
         (coe MAlonzo.Code.Function.Bundles.d_cong_928 (coe v0))
         (coe MAlonzo.Code.Function.Bundles.d_cong_928 (coe v1)))
      (coe
         du_surjective_62
         (coe MAlonzo.Code.Function.Bundles.d_to_926 (coe v0))
         (coe MAlonzo.Code.Function.Bundles.d_surjective_930 (coe v0))
         (coe MAlonzo.Code.Function.Bundles.d_surjective_930 (coe v1)))
-- Function.Construct.Composition._.bijection
d_bijection_1686 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Function.Bundles.T_Bijection_1004 ->
  MAlonzo.Code.Function.Bundles.T_Bijection_1004 ->
  MAlonzo.Code.Function.Bundles.T_Bijection_1004
d_bijection_1686 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9 v10
  = du_bijection_1686 v9 v10
du_bijection_1686 ::
  MAlonzo.Code.Function.Bundles.T_Bijection_1004 ->
  MAlonzo.Code.Function.Bundles.T_Bijection_1004 ->
  MAlonzo.Code.Function.Bundles.T_Bijection_1004
du_bijection_1686 v0 v1
  = coe
      MAlonzo.Code.Function.Bundles.C_constructor_1094
      (coe
         (\ v2 ->
            coe
              MAlonzo.Code.Function.Bundles.d_to_1012 v1
              (coe MAlonzo.Code.Function.Bundles.d_to_1012 v0 v2)))
      (coe
         du_congruent_50
         (coe MAlonzo.Code.Function.Bundles.d_to_1012 (coe v0))
         (coe MAlonzo.Code.Function.Bundles.d_cong_1014 (coe v0))
         (coe MAlonzo.Code.Function.Bundles.d_cong_1014 (coe v1)))
      (coe
         du_bijective_102 (MAlonzo.Code.Function.Bundles.d_to_1012 (coe v0))
         (MAlonzo.Code.Function.Bundles.d_bijective_1016 (coe v0))
         (MAlonzo.Code.Function.Bundles.d_bijective_1016 (coe v1)))
-- Function.Construct.Composition._.equivalence
d_equivalence_1852 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Function.Bundles.T_Equivalence_1858 ->
  MAlonzo.Code.Function.Bundles.T_Equivalence_1858 ->
  MAlonzo.Code.Function.Bundles.T_Equivalence_1858
d_equivalence_1852 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9 v10
  = du_equivalence_1852 v9 v10
du_equivalence_1852 ::
  MAlonzo.Code.Function.Bundles.T_Equivalence_1858 ->
  MAlonzo.Code.Function.Bundles.T_Equivalence_1858 ->
  MAlonzo.Code.Function.Bundles.T_Equivalence_1858
du_equivalence_1852 v0 v1
  = coe
      MAlonzo.Code.Function.Bundles.C_constructor_1940
      (coe
         (\ v2 ->
            coe
              MAlonzo.Code.Function.Bundles.d_to_1868 v1
              (coe MAlonzo.Code.Function.Bundles.d_to_1868 v0 v2)))
      (coe
         (\ v2 ->
            coe
              MAlonzo.Code.Function.Bundles.d_from_1870 v0
              (coe MAlonzo.Code.Function.Bundles.d_from_1870 v1 v2)))
      (coe
         du_congruent_50
         (coe MAlonzo.Code.Function.Bundles.d_to_1868 (coe v0))
         (coe MAlonzo.Code.Function.Bundles.d_to'45'cong_1872 (coe v0))
         (coe MAlonzo.Code.Function.Bundles.d_to'45'cong_1872 (coe v1)))
      (coe
         du_congruent_50
         (coe MAlonzo.Code.Function.Bundles.d_from_1870 (coe v1))
         (coe MAlonzo.Code.Function.Bundles.d_from'45'cong_1874 (coe v1))
         (coe MAlonzo.Code.Function.Bundles.d_from'45'cong_1874 (coe v0)))
-- Function.Construct.Composition._.leftInverse
d_leftInverse_2002 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Function.Bundles.T_LeftInverse_1942 ->
  MAlonzo.Code.Function.Bundles.T_LeftInverse_1942 ->
  MAlonzo.Code.Function.Bundles.T_LeftInverse_1942
d_leftInverse_2002 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9 v10
  = du_leftInverse_2002 v9 v10
du_leftInverse_2002 ::
  MAlonzo.Code.Function.Bundles.T_LeftInverse_1942 ->
  MAlonzo.Code.Function.Bundles.T_LeftInverse_1942 ->
  MAlonzo.Code.Function.Bundles.T_LeftInverse_1942
du_leftInverse_2002 v0 v1
  = coe
      MAlonzo.Code.Function.Bundles.C_constructor_2034
      (coe
         (\ v2 ->
            coe
              MAlonzo.Code.Function.Bundles.d_to_1954 v1
              (coe MAlonzo.Code.Function.Bundles.d_to_1954 v0 v2)))
      (coe
         (\ v2 ->
            coe
              MAlonzo.Code.Function.Bundles.d_from_1956 v0
              (coe MAlonzo.Code.Function.Bundles.d_from_1956 v1 v2)))
      (coe
         du_congruent_50
         (coe MAlonzo.Code.Function.Bundles.d_to_1954 (coe v0))
         (coe MAlonzo.Code.Function.Bundles.d_to'45'cong_1958 (coe v0))
         (coe MAlonzo.Code.Function.Bundles.d_to'45'cong_1958 (coe v1)))
      (coe
         du_congruent_50
         (coe MAlonzo.Code.Function.Bundles.d_from_1956 (coe v1))
         (coe MAlonzo.Code.Function.Bundles.d_from'45'cong_1960 (coe v1))
         (coe MAlonzo.Code.Function.Bundles.d_from'45'cong_1960 (coe v0)))
      (coe
         du_inverse'737'_134
         (coe MAlonzo.Code.Function.Bundles.d_to_1954 (coe v0))
         (coe MAlonzo.Code.Function.Bundles.d_from_1956 (coe v1))
         (coe MAlonzo.Code.Function.Bundles.d_inverse'737'_1962 (coe v0))
         (coe MAlonzo.Code.Function.Bundles.d_inverse'737'_1962 (coe v1)))
-- Function.Construct.Composition._.rightInverse
d_rightInverse_2168 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Function.Bundles.T_RightInverse_2036 ->
  MAlonzo.Code.Function.Bundles.T_RightInverse_2036 ->
  MAlonzo.Code.Function.Bundles.T_RightInverse_2036
d_rightInverse_2168 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9 v10
  = du_rightInverse_2168 v9 v10
du_rightInverse_2168 ::
  MAlonzo.Code.Function.Bundles.T_RightInverse_2036 ->
  MAlonzo.Code.Function.Bundles.T_RightInverse_2036 ->
  MAlonzo.Code.Function.Bundles.T_RightInverse_2036
du_rightInverse_2168 v0 v1
  = coe
      MAlonzo.Code.Function.Bundles.C_constructor_2120
      (coe
         (\ v2 ->
            coe
              MAlonzo.Code.Function.Bundles.d_to_2048 v1
              (coe MAlonzo.Code.Function.Bundles.d_to_2048 v0 v2)))
      (coe
         (\ v2 ->
            coe
              MAlonzo.Code.Function.Bundles.d_from_2050 v0
              (coe MAlonzo.Code.Function.Bundles.d_from_2050 v1 v2)))
      (coe
         du_congruent_50
         (coe MAlonzo.Code.Function.Bundles.d_to_2048 (coe v0))
         (coe MAlonzo.Code.Function.Bundles.d_to'45'cong_2052 (coe v0))
         (coe MAlonzo.Code.Function.Bundles.d_to'45'cong_2052 (coe v1)))
      (coe
         du_congruent_50
         (coe MAlonzo.Code.Function.Bundles.d_from_2050 (coe v1))
         (coe MAlonzo.Code.Function.Bundles.d_from'45'cong_2054 (coe v1))
         (coe MAlonzo.Code.Function.Bundles.d_from'45'cong_2054 (coe v0)))
      (coe
         du_inverse'691'_140
         (coe MAlonzo.Code.Function.Bundles.d_to_2048 (coe v0))
         (coe MAlonzo.Code.Function.Bundles.d_from_2050 (coe v1))
         (coe MAlonzo.Code.Function.Bundles.d_inverse'691'_2056 (coe v0))
         (coe MAlonzo.Code.Function.Bundles.d_inverse'691'_2056 (coe v1)))
-- Function.Construct.Composition._.inverse
d_inverse_2322 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Function.Bundles.T_Inverse_2122 ->
  MAlonzo.Code.Function.Bundles.T_Inverse_2122 ->
  MAlonzo.Code.Function.Bundles.T_Inverse_2122
d_inverse_2322 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9 v10
  = du_inverse_2322 v9 v10
du_inverse_2322 ::
  MAlonzo.Code.Function.Bundles.T_Inverse_2122 ->
  MAlonzo.Code.Function.Bundles.T_Inverse_2122 ->
  MAlonzo.Code.Function.Bundles.T_Inverse_2122
du_inverse_2322 v0 v1
  = coe
      MAlonzo.Code.Function.Bundles.C_constructor_2220
      (coe
         (\ v2 ->
            coe
              MAlonzo.Code.Function.Bundles.d_to_2134 v1
              (coe MAlonzo.Code.Function.Bundles.d_to_2134 v0 v2)))
      (coe
         (\ v2 ->
            coe
              MAlonzo.Code.Function.Bundles.d_from_2136 v0
              (coe MAlonzo.Code.Function.Bundles.d_from_2136 v1 v2)))
      (coe
         du_congruent_50
         (coe MAlonzo.Code.Function.Bundles.d_to_2134 (coe v0))
         (coe MAlonzo.Code.Function.Bundles.d_to'45'cong_2138 (coe v0))
         (coe MAlonzo.Code.Function.Bundles.d_to'45'cong_2138 (coe v1)))
      (coe
         du_congruent_50
         (coe MAlonzo.Code.Function.Bundles.d_from_2136 (coe v1))
         (coe MAlonzo.Code.Function.Bundles.d_from'45'cong_2140 (coe v1))
         (coe MAlonzo.Code.Function.Bundles.d_from'45'cong_2140 (coe v0)))
      (coe
         du_inverse'7495'_146
         (MAlonzo.Code.Function.Bundles.d_to_2134 (coe v0))
         (MAlonzo.Code.Function.Bundles.d_from_2136 (coe v1))
         (MAlonzo.Code.Function.Bundles.d_inverse_2142 (coe v0))
         (MAlonzo.Code.Function.Bundles.d_inverse_2142 (coe v1)))
-- Function.Construct.Composition._⟶-∘_
d__'10230''45''8728'__2496 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Function.Bundles.T_Func_774 ->
  MAlonzo.Code.Function.Bundles.T_Func_774 ->
  MAlonzo.Code.Function.Bundles.T_Func_774
d__'10230''45''8728'__2496 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7
  = du__'10230''45''8728'__2496 v6 v7
du__'10230''45''8728'__2496 ::
  MAlonzo.Code.Function.Bundles.T_Func_774 ->
  MAlonzo.Code.Function.Bundles.T_Func_774 ->
  MAlonzo.Code.Function.Bundles.T_Func_774
du__'10230''45''8728'__2496 v0 v1
  = coe du_function_1260 (coe v1) (coe v0)
-- Function.Construct.Composition._↣-∘_
d__'8611''45''8728'__2498 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Function.Bundles.T_Injection_842 ->
  MAlonzo.Code.Function.Bundles.T_Injection_842 ->
  MAlonzo.Code.Function.Bundles.T_Injection_842
d__'8611''45''8728'__2498 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7
  = du__'8611''45''8728'__2498 v6 v7
du__'8611''45''8728'__2498 ::
  MAlonzo.Code.Function.Bundles.T_Injection_842 ->
  MAlonzo.Code.Function.Bundles.T_Injection_842 ->
  MAlonzo.Code.Function.Bundles.T_Injection_842
du__'8611''45''8728'__2498 v0 v1
  = coe du_injection_1390 (coe v1) (coe v0)
-- Function.Construct.Composition._↠-∘_
d__'8608''45''8728'__2500 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Function.Bundles.T_Surjection_918 ->
  MAlonzo.Code.Function.Bundles.T_Surjection_918 ->
  MAlonzo.Code.Function.Bundles.T_Surjection_918
d__'8608''45''8728'__2500 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7
  = du__'8608''45''8728'__2500 v6 v7
du__'8608''45''8728'__2500 ::
  MAlonzo.Code.Function.Bundles.T_Surjection_918 ->
  MAlonzo.Code.Function.Bundles.T_Surjection_918 ->
  MAlonzo.Code.Function.Bundles.T_Surjection_918
du__'8608''45''8728'__2500 v0 v1
  = coe du_surjection_1532 (coe v1) (coe v0)
-- Function.Construct.Composition._⤖-∘_
d__'10518''45''8728'__2502 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Function.Bundles.T_Bijection_1004 ->
  MAlonzo.Code.Function.Bundles.T_Bijection_1004 ->
  MAlonzo.Code.Function.Bundles.T_Bijection_1004
d__'10518''45''8728'__2502 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7
  = du__'10518''45''8728'__2502 v6 v7
du__'10518''45''8728'__2502 ::
  MAlonzo.Code.Function.Bundles.T_Bijection_1004 ->
  MAlonzo.Code.Function.Bundles.T_Bijection_1004 ->
  MAlonzo.Code.Function.Bundles.T_Bijection_1004
du__'10518''45''8728'__2502 v0 v1
  = coe du_bijection_1686 (coe v1) (coe v0)
-- Function.Construct.Composition._⇔-∘_
d__'8660''45''8728'__2504 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Function.Bundles.T_Equivalence_1858 ->
  MAlonzo.Code.Function.Bundles.T_Equivalence_1858 ->
  MAlonzo.Code.Function.Bundles.T_Equivalence_1858
d__'8660''45''8728'__2504 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7
  = du__'8660''45''8728'__2504 v6 v7
du__'8660''45''8728'__2504 ::
  MAlonzo.Code.Function.Bundles.T_Equivalence_1858 ->
  MAlonzo.Code.Function.Bundles.T_Equivalence_1858 ->
  MAlonzo.Code.Function.Bundles.T_Equivalence_1858
du__'8660''45''8728'__2504 v0 v1
  = coe du_equivalence_1852 (coe v1) (coe v0)
-- Function.Construct.Composition._↩-∘_
d__'8617''45''8728'__2506 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Function.Bundles.T_LeftInverse_1942 ->
  MAlonzo.Code.Function.Bundles.T_LeftInverse_1942 ->
  MAlonzo.Code.Function.Bundles.T_LeftInverse_1942
d__'8617''45''8728'__2506 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7
  = du__'8617''45''8728'__2506 v6 v7
du__'8617''45''8728'__2506 ::
  MAlonzo.Code.Function.Bundles.T_LeftInverse_1942 ->
  MAlonzo.Code.Function.Bundles.T_LeftInverse_1942 ->
  MAlonzo.Code.Function.Bundles.T_LeftInverse_1942
du__'8617''45''8728'__2506 v0 v1
  = coe du_leftInverse_2002 (coe v1) (coe v0)
-- Function.Construct.Composition._↪-∘_
d__'8618''45''8728'__2508 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Function.Bundles.T_RightInverse_2036 ->
  MAlonzo.Code.Function.Bundles.T_RightInverse_2036 ->
  MAlonzo.Code.Function.Bundles.T_RightInverse_2036
d__'8618''45''8728'__2508 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7
  = du__'8618''45''8728'__2508 v6 v7
du__'8618''45''8728'__2508 ::
  MAlonzo.Code.Function.Bundles.T_RightInverse_2036 ->
  MAlonzo.Code.Function.Bundles.T_RightInverse_2036 ->
  MAlonzo.Code.Function.Bundles.T_RightInverse_2036
du__'8618''45''8728'__2508 v0 v1
  = coe du_rightInverse_2168 (coe v1) (coe v0)
-- Function.Construct.Composition._↔-∘_
d__'8596''45''8728'__2510 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Function.Bundles.T_Inverse_2122 ->
  MAlonzo.Code.Function.Bundles.T_Inverse_2122 ->
  MAlonzo.Code.Function.Bundles.T_Inverse_2122
d__'8596''45''8728'__2510 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7
  = du__'8596''45''8728'__2510 v6 v7
du__'8596''45''8728'__2510 ::
  MAlonzo.Code.Function.Bundles.T_Inverse_2122 ->
  MAlonzo.Code.Function.Bundles.T_Inverse_2122 ->
  MAlonzo.Code.Function.Bundles.T_Inverse_2122
du__'8596''45''8728'__2510 v0 v1
  = coe du_inverse_2322 (coe v1) (coe v0)
-- Function.Construct.Composition._∘-⟶_
d__'8728''45''10230'__2512 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Function.Bundles.T_Func_774 ->
  MAlonzo.Code.Function.Bundles.T_Func_774 ->
  MAlonzo.Code.Function.Bundles.T_Func_774
d__'8728''45''10230'__2512 v0 v1 v2 v3 v4 v5 v6 v7
  = coe du__'10230''45''8728'__2496 v6 v7
-- Function.Construct.Composition._∘-↣_
d__'8728''45''8611'__2514 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Function.Bundles.T_Injection_842 ->
  MAlonzo.Code.Function.Bundles.T_Injection_842 ->
  MAlonzo.Code.Function.Bundles.T_Injection_842
d__'8728''45''8611'__2514 v0 v1 v2 v3 v4 v5 v6 v7
  = coe du__'8611''45''8728'__2498 v6 v7
-- Function.Construct.Composition._∘-↠_
d__'8728''45''8608'__2516 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Function.Bundles.T_Surjection_918 ->
  MAlonzo.Code.Function.Bundles.T_Surjection_918 ->
  MAlonzo.Code.Function.Bundles.T_Surjection_918
d__'8728''45''8608'__2516 v0 v1 v2 v3 v4 v5 v6 v7
  = coe du__'8608''45''8728'__2500 v6 v7
-- Function.Construct.Composition._∘-⤖_
d__'8728''45''10518'__2518 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Function.Bundles.T_Bijection_1004 ->
  MAlonzo.Code.Function.Bundles.T_Bijection_1004 ->
  MAlonzo.Code.Function.Bundles.T_Bijection_1004
d__'8728''45''10518'__2518 v0 v1 v2 v3 v4 v5 v6 v7
  = coe du__'10518''45''8728'__2502 v6 v7
-- Function.Construct.Composition._∘-⇔_
d__'8728''45''8660'__2520 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Function.Bundles.T_Equivalence_1858 ->
  MAlonzo.Code.Function.Bundles.T_Equivalence_1858 ->
  MAlonzo.Code.Function.Bundles.T_Equivalence_1858
d__'8728''45''8660'__2520 v0 v1 v2 v3 v4 v5 v6 v7
  = coe du__'8660''45''8728'__2504 v6 v7
-- Function.Construct.Composition._∘-↩_
d__'8728''45''8617'__2522 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Function.Bundles.T_LeftInverse_1942 ->
  MAlonzo.Code.Function.Bundles.T_LeftInverse_1942 ->
  MAlonzo.Code.Function.Bundles.T_LeftInverse_1942
d__'8728''45''8617'__2522 v0 v1 v2 v3 v4 v5 v6 v7
  = coe du__'8617''45''8728'__2506 v6 v7
-- Function.Construct.Composition._∘-↪_
d__'8728''45''8618'__2524 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Function.Bundles.T_RightInverse_2036 ->
  MAlonzo.Code.Function.Bundles.T_RightInverse_2036 ->
  MAlonzo.Code.Function.Bundles.T_RightInverse_2036
d__'8728''45''8618'__2524 v0 v1 v2 v3 v4 v5 v6 v7
  = coe du__'8618''45''8728'__2508 v6 v7
-- Function.Construct.Composition._∘-↔_
d__'8728''45''8596'__2526 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Function.Bundles.T_Inverse_2122 ->
  MAlonzo.Code.Function.Bundles.T_Inverse_2122 ->
  MAlonzo.Code.Function.Bundles.T_Inverse_2122
d__'8728''45''8596'__2526 v0 v1 v2 v3 v4 v5 v6 v7
  = coe du__'8596''45''8728'__2510 v6 v7
