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

module MAlonzo.Code.Data.Product.Relation.Binary.Pointwise.NonDependent where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Data.Product.Base
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Function.Bundles
import qualified MAlonzo.Code.Relation.Binary.Bundles
import qualified MAlonzo.Code.Relation.Binary.Structures
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core

-- Data.Product.Relation.Binary.Pointwise.NonDependent.Pointwise
d_Pointwise_40 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> ()
d_Pointwise_40 = erased
-- Data.Product.Relation.Binary.Pointwise.NonDependent.×-reflexive
d_'215''45'reflexive_54 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'215''45'reflexive_54 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                        ~v10 ~v11 v12 v13 v14 v15
  = du_'215''45'reflexive_54 v12 v13 v14 v15
du_'215''45'reflexive_54 ::
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'215''45'reflexive_54 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Data.Product.Base.du_map_128
      (coe
         v0 (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v2))
         (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v3)))
      (coe
         (\ v4 ->
            coe
              v1 (MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v2))
              (MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v3))))
-- Data.Product.Relation.Binary.Pointwise.NonDependent.×-refl
d_'215''45'refl_60 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'215''45'refl_60 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 v9 v10
  = du_'215''45'refl_60 v8 v9 v10
du_'215''45'refl_60 ::
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'215''45'refl_60 v0 v1 v2
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe v0 (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v2)))
      (coe v1 (MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v2)))
-- Data.Product.Relation.Binary.Pointwise.NonDependent.×-irreflexive₁
d_'215''45'irreflexive'8321'_66 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'215''45'irreflexive'8321'_66 = erased
-- Data.Product.Relation.Binary.Pointwise.NonDependent.×-irreflexive₂
d_'215''45'irreflexive'8322'_74 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'215''45'irreflexive'8322'_74 = erased
-- Data.Product.Relation.Binary.Pointwise.NonDependent.×-symmetric
d_'215''45'symmetric_82 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'215''45'symmetric_82 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 v9 v10
                        v11
  = du_'215''45'symmetric_82 v8 v9 v10 v11
du_'215''45'symmetric_82 ::
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'215''45'symmetric_82 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Data.Product.Base.du_map_128
      (coe
         v0 (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v2))
         (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v3)))
      (coe
         (\ v4 ->
            coe
              v1 (MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v2))
              (MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v3))))
-- Data.Product.Relation.Binary.Pointwise.NonDependent.×-transitive
d_'215''45'transitive_88 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'215''45'transitive_88 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 v9 v10
                         v11 v12
  = du_'215''45'transitive_88 v8 v9 v10 v11 v12
du_'215''45'transitive_88 ::
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'215''45'transitive_88 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Data.Product.Base.du_zip_198
      (coe
         v0 (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v2))
         (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v3))
         (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v4)))
      (coe
         (\ v5 v6 ->
            coe
              v1 (MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v2))
              (MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v3))
              (MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v4))))
-- Data.Product.Relation.Binary.Pointwise.NonDependent.×-antisymmetric
d_'215''45'antisymmetric_94 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'215''45'antisymmetric_94 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                            ~v10 ~v11 v12 v13 v14 v15
  = du_'215''45'antisymmetric_94 v12 v13 v14 v15
du_'215''45'antisymmetric_94 ::
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'215''45'antisymmetric_94 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Data.Product.Base.du_zip_198
      (coe
         v0 (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v2))
         (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v3)))
      (coe
         (\ v4 v5 ->
            coe
              v1 (MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v2))
              (MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v3))))
-- Data.Product.Relation.Binary.Pointwise.NonDependent.×-asymmetric₁
d_'215''45'asymmetric'8321'_100 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'215''45'asymmetric'8321'_100 = erased
-- Data.Product.Relation.Binary.Pointwise.NonDependent.×-asymmetric₂
d_'215''45'asymmetric'8322'_108 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'215''45'asymmetric'8322'_108 = erased
-- Data.Product.Relation.Binary.Pointwise.NonDependent.×-respectsʳ
d_'215''45'respects'691'_116 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'215''45'respects'691'_116 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8
                             ~v9 ~v10 ~v11 v12 v13 v14 v15 v16
  = du_'215''45'respects'691'_116 v12 v13 v14 v15 v16
du_'215''45'respects'691'_116 ::
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'215''45'respects'691'_116 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Data.Product.Base.du_zip_198
      (coe
         v0 (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v2))
         (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v3))
         (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v4)))
      (coe
         (\ v5 v6 ->
            coe
              v1 (MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v2))
              (MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v3))
              (MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v4))))
-- Data.Product.Relation.Binary.Pointwise.NonDependent.×-respectsˡ
d_'215''45'respects'737'_122 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'215''45'respects'737'_122 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8
                             ~v9 ~v10 ~v11 v12 v13 v14 v15 v16
  = du_'215''45'respects'737'_122 v12 v13 v14 v15 v16
du_'215''45'respects'737'_122 ::
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'215''45'respects'737'_122 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Data.Product.Base.du_zip_198
      (coe
         v0 (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v2))
         (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v3))
         (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v4)))
      (coe
         (\ v5 v6 ->
            coe
              v1 (MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v2))
              (MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v3))
              (MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v4))))
-- Data.Product.Relation.Binary.Pointwise.NonDependent.×-respects₂
d_'215''45'respects'8322'_128 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'215''45'respects'8322'_128 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8
                              ~v9 ~v10 ~v11
  = du_'215''45'respects'8322'_128
du_'215''45'respects'8322'_128 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'215''45'respects'8322'_128
  = coe
      MAlonzo.Code.Data.Product.Base.du_zip_198
      (coe du_'215''45'respects'691'_116)
      (coe (\ v0 v1 -> coe du_'215''45'respects'737'_122))
-- Data.Product.Relation.Binary.Pointwise.NonDependent.×-total
d_'215''45'total_130 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30) ->
  (AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_'215''45'total_130 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 v9 v10 v11
                     v12
  = du_'215''45'total_130 v8 v9 v10 v11 v12
du_'215''45'total_130 ::
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30) ->
  (AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_'215''45'total_130 v0 v1 v2 v3 v4
  = case coe v3 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
        -> case coe v4 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
               -> let v9 = coe v1 v5 v7 in
                  coe
                    (let v10 = coe v2 v6 v8 in
                     coe
                       (case coe v9 of
                          MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v11
                            -> case coe v10 of
                                 MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v12
                                   -> coe
                                        MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                                        (coe
                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v11)
                                           (coe v12))
                                 MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v12
                                   -> coe
                                        MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                                        (coe
                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                           (coe v0 v5 v7 v11) (coe v12))
                                 _ -> MAlonzo.RTE.mazUnreachableError
                          MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v11
                            -> case coe v10 of
                                 MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v12
                                   -> coe
                                        MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                                        (coe
                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                           (coe v0 v7 v5 v11) (coe v12))
                                 MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v12
                                   -> coe
                                        MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                                        (coe
                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v11)
                                           (coe v12))
                                 _ -> MAlonzo.RTE.mazUnreachableError
                          _ -> MAlonzo.RTE.mazUnreachableError))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Product.Relation.Binary.Pointwise.NonDependent.×-decidable
d_'215''45'decidable_222 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_'215''45'decidable_222 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 v9 v10
                         v11
  = du_'215''45'decidable_222 v8 v9 v10 v11
du_'215''45'decidable_222 ::
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du_'215''45'decidable_222 v0 v1 v2 v3
  = case coe v2 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
        -> case coe v3 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.du__'215''45'dec__84
                    (coe v0 v4 v6) (coe v1 v5 v7)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Product.Relation.Binary.Pointwise.NonDependent.×-isEquivalence
d_'215''45'isEquivalence_236 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_'215''45'isEquivalence_236 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 v9
  = du_'215''45'isEquivalence_236 v8 v9
du_'215''45'isEquivalence_236 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
du_'215''45'isEquivalence_236 v0 v1
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_constructor_46
      (coe
         du_'215''45'refl_60
         (coe MAlonzo.Code.Relation.Binary.Structures.d_refl_36 (coe v0))
         (coe MAlonzo.Code.Relation.Binary.Structures.d_refl_36 (coe v1)))
      (coe
         du_'215''45'symmetric_82
         (coe MAlonzo.Code.Relation.Binary.Structures.d_sym_38 (coe v0))
         (coe MAlonzo.Code.Relation.Binary.Structures.d_sym_38 (coe v1)))
      (coe
         du_'215''45'transitive_88
         (coe MAlonzo.Code.Relation.Binary.Structures.d_trans_40 (coe v0))
         (coe MAlonzo.Code.Relation.Binary.Structures.d_trans_40 (coe v1)))
-- Data.Product.Relation.Binary.Pointwise.NonDependent.×-isDecEquivalence
d_'215''45'isDecEquivalence_250 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecEquivalence_48 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecEquivalence_48 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecEquivalence_48
d_'215''45'isDecEquivalence_250 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
                                v9
  = du_'215''45'isDecEquivalence_250 v8 v9
du_'215''45'isDecEquivalence_250 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecEquivalence_48 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecEquivalence_48 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecEquivalence_48
du_'215''45'isDecEquivalence_250 v0 v1
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_constructor_70
      (coe
         du_'215''45'isEquivalence_236
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_54
            (coe v0))
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_54
            (coe v1)))
      (coe
         du_'215''45'decidable_222
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d__'8799'__56 (coe v0))
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d__'8799'__56 (coe v1)))
-- Data.Product.Relation.Binary.Pointwise.NonDependent.×-isPreorder
d_'215''45'isPreorder_260 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPreorder_76 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPreorder_76 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPreorder_76
d_'215''45'isPreorder_260 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                          ~v10 ~v11 v12 v13
  = du_'215''45'isPreorder_260 v12 v13
du_'215''45'isPreorder_260 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsPreorder_76 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPreorder_76 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPreorder_76
du_'215''45'isPreorder_260 v0 v1
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_constructor_126
      (coe
         du_'215''45'isEquivalence_236
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_86
            (coe v0))
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_86
            (coe v1)))
      (coe
         du_'215''45'reflexive_54
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_reflexive_88 (coe v0))
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_reflexive_88 (coe v1)))
      (coe
         du_'215''45'transitive_88
         (coe MAlonzo.Code.Relation.Binary.Structures.d_trans_90 (coe v0))
         (coe MAlonzo.Code.Relation.Binary.Structures.d_trans_90 (coe v1)))
-- Data.Product.Relation.Binary.Pointwise.NonDependent.×-isPartialOrder
d_'215''45'isPartialOrder_274 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialOrder_248 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialOrder_248 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialOrder_248
d_'215''45'isPartialOrder_274 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8
                              ~v9 ~v10 ~v11 v12 v13
  = du_'215''45'isPartialOrder_274 v12 v13
du_'215''45'isPartialOrder_274 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialOrder_248 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialOrder_248 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialOrder_248
du_'215''45'isPartialOrder_274 v0 v1
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_constructor_294
      (coe
         du_'215''45'isPreorder_260
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256 (coe v0))
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256 (coe v1)))
      (coe
         du_'215''45'antisymmetric_94
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_antisym_258 (coe v0))
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_antisym_258 (coe v1)))
-- Data.Product.Relation.Binary.Pointwise.NonDependent.×-isStrictPartialOrder
d_'215''45'isStrictPartialOrder_288 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsStrictPartialOrder_370 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsStrictPartialOrder_370 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsStrictPartialOrder_370
d_'215''45'isStrictPartialOrder_288 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
                                    ~v8 ~v9 ~v10 ~v11 v12 v13
  = du_'215''45'isStrictPartialOrder_288 v12 v13
du_'215''45'isStrictPartialOrder_288 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsStrictPartialOrder_370 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsStrictPartialOrder_370 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsStrictPartialOrder_370
du_'215''45'isStrictPartialOrder_288 v0 v1
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_constructor_412
      (coe
         du_'215''45'isEquivalence_236
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_382
            (coe v0))
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_382
            (coe v1)))
      (coe
         du_'215''45'transitive_88
         (coe MAlonzo.Code.Relation.Binary.Structures.d_trans_386 (coe v0))
         (coe MAlonzo.Code.Relation.Binary.Structures.d_trans_386 (coe v1)))
      (coe
         du_'215''45'respects'8322'_128
         (MAlonzo.Code.Relation.Binary.Structures.d_'60''45'resp'45''8776'_388
            (coe v0))
         (MAlonzo.Code.Relation.Binary.Structures.d_'60''45'resp'45''8776'_388
            (coe v1)))
-- Data.Product.Relation.Binary.Pointwise.NonDependent.×-setoid
d_'215''45'setoid_304 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_'215''45'setoid_304 ~v0 ~v1 ~v2 ~v3 v4 v5
  = du_'215''45'setoid_304 v4 v5
du_'215''45'setoid_304 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
du_'215''45'setoid_304 v0 v1
  = coe
      MAlonzo.Code.Relation.Binary.Bundles.C_constructor_84
      (coe
         du_'215''45'isEquivalence_236
         (coe
            MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62 (coe v0))
         (coe
            MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62 (coe v1)))
-- Data.Product.Relation.Binary.Pointwise.NonDependent.×-decSetoid
d_'215''45'decSetoid_314 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_DecSetoid_90 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_DecSetoid_90 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_DecSetoid_90
d_'215''45'decSetoid_314 ~v0 ~v1 ~v2 ~v3 v4 v5
  = du_'215''45'decSetoid_314 v4 v5
du_'215''45'decSetoid_314 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_DecSetoid_90 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_DecSetoid_90 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_DecSetoid_90
du_'215''45'decSetoid_314 v0 v1
  = coe
      MAlonzo.Code.Relation.Binary.Bundles.C_constructor_134
      (coe
         du_'215''45'isDecEquivalence_250
         (coe
            MAlonzo.Code.Relation.Binary.Bundles.d_isDecEquivalence_106
            (coe v0))
         (coe
            MAlonzo.Code.Relation.Binary.Bundles.d_isDecEquivalence_106
            (coe v1)))
-- Data.Product.Relation.Binary.Pointwise.NonDependent.×-preorder
d_'215''45'preorder_324 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Preorder_142 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Preorder_142 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Preorder_142
d_'215''45'preorder_324 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7
  = du_'215''45'preorder_324 v6 v7
du_'215''45'preorder_324 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Preorder_142 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Preorder_142 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Preorder_142
du_'215''45'preorder_324 v0 v1
  = coe
      MAlonzo.Code.Relation.Binary.Bundles.C_constructor_232
      (coe
         du_'215''45'isPreorder_260
         (coe
            MAlonzo.Code.Relation.Binary.Bundles.d_isPreorder_164 (coe v0))
         (coe
            MAlonzo.Code.Relation.Binary.Bundles.d_isPreorder_164 (coe v1)))
-- Data.Product.Relation.Binary.Pointwise.NonDependent.×-poset
d_'215''45'poset_334 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Poset_492 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Poset_492 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Poset_492
d_'215''45'poset_334 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7
  = du_'215''45'poset_334 v6 v7
du_'215''45'poset_334 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Poset_492 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Poset_492 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Poset_492
du_'215''45'poset_334 v0 v1
  = coe
      MAlonzo.Code.Relation.Binary.Bundles.C_constructor_588
      (coe
         du_'215''45'isPartialOrder_274
         (coe
            MAlonzo.Code.Relation.Binary.Bundles.d_isPartialOrder_514 (coe v0))
         (coe
            MAlonzo.Code.Relation.Binary.Bundles.d_isPartialOrder_514
            (coe v1)))
-- Data.Product.Relation.Binary.Pointwise.NonDependent.×-strictPartialOrder
d_'215''45'strictPartialOrder_344 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictPartialOrder_760 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictPartialOrder_760 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictPartialOrder_760
d_'215''45'strictPartialOrder_344 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7
  = du_'215''45'strictPartialOrder_344 v6 v7
du_'215''45'strictPartialOrder_344 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictPartialOrder_760 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictPartialOrder_760 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictPartialOrder_760
du_'215''45'strictPartialOrder_344 v0 v1
  = coe
      MAlonzo.Code.Relation.Binary.Bundles.C_constructor_842
      (coe
         du_'215''45'isStrictPartialOrder_288
         (coe
            MAlonzo.Code.Relation.Binary.Bundles.d_isStrictPartialOrder_782
            (coe v0))
         (coe
            MAlonzo.Code.Relation.Binary.Bundles.d_isStrictPartialOrder_782
            (coe v1)))
-- Data.Product.Relation.Binary.Pointwise.NonDependent._×ₛ_
d__'215''8347'__354 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d__'215''8347'__354 ~v0 ~v1 ~v2 ~v3 = du__'215''8347'__354
du__'215''8347'__354 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
du__'215''8347'__354 = coe du_'215''45'setoid_304
-- Data.Product.Relation.Binary.Pointwise.NonDependent.≡×≡⇒≡
d_'8801''215''8801''8658''8801'_356 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8801''215''8801''8658''8801'_356 = erased
-- Data.Product.Relation.Binary.Pointwise.NonDependent.≡⇒≡×≡
d_'8801''8658''8801''215''8801'_358 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8801''8658''8801''215''8801'_358 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6
  = du_'8801''8658''8801''215''8801'_358
du_'8801''8658''8801''215''8801'_358 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8801''8658''8801''215''8801'_358
  = coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased
-- Data.Product.Relation.Binary.Pointwise.NonDependent.Pointwise-≡↔≡
d_Pointwise'45''8801''8596''8801'_360 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> MAlonzo.Code.Function.Bundles.T_Inverse_2122
d_Pointwise'45''8801''8596''8801'_360 ~v0 ~v1 ~v2 ~v3
  = du_Pointwise'45''8801''8596''8801'_360
du_Pointwise'45''8801''8596''8801'_360 ::
  MAlonzo.Code.Function.Bundles.T_Inverse_2122
du_Pointwise'45''8801''8596''8801'_360
  = coe
      MAlonzo.Code.Function.Bundles.C_constructor_2220 (coe (\ v0 -> v0))
      (coe (\ v0 -> v0)) erased
      (\ v0 v1 v2 -> coe du_'8801''8658''8801''215''8801'_358)
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
         (coe (\ v0 v1 v2 -> coe du_'8801''8658''8801''215''8801'_358)))
