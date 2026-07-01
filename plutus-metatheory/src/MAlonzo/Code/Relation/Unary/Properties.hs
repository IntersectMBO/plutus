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

module MAlonzo.Code.Relation.Unary.Properties where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Bool
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.Unit
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Data.Product.Base
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core
import qualified MAlonzo.Code.Relation.Nullary.Reflects

-- Relation.Unary.Properties.∅?
d_'8709''63'_22 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  AgdaAny -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_'8709''63'_22 ~v0 ~v1 ~v2 = du_'8709''63'_22
du_'8709''63'_22 ::
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du_'8709''63'_22
  = coe
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
      (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
      (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
-- Relation.Unary.Properties.∅-Empty
d_'8709''45'Empty_24 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  AgdaAny ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'8709''45'Empty_24 = erased
-- Relation.Unary.Properties.∁∅-Universal
d_'8705''8709''45'Universal_28 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  AgdaAny ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'8705''8709''45'Universal_28 = erased
-- Relation.Unary.Properties.U?
d_U'63'_34 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  AgdaAny -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_U'63'_34 ~v0 ~v1 ~v2 = du_U'63'_34
du_U'63'_34 ::
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du_U'63'_34
  = coe
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
      (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
      (coe
         MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
         (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
-- Relation.Unary.Properties.U-Universal
d_U'45'Universal_36 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6
d_U'45'Universal_36 ~v0 ~v1 ~v2 = du_U'45'Universal_36
du_U'45'Universal_36 :: MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6
du_U'45'Universal_36 = coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
-- Relation.Unary.Properties.∁U-Empty
d_'8705'U'45'Empty_40 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  AgdaAny ->
  (MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'8705'U'45'Empty_40 = erased
-- Relation.Unary.Properties.∅-⊆
d_'8709''45''8838'_48 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20 -> AgdaAny
d_'8709''45''8838'_48 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_'8709''45''8838'_48
du_'8709''45''8838'_48 :: AgdaAny
du_'8709''45''8838'_48 = MAlonzo.RTE.mazUnreachableError
-- Relation.Unary.Properties.⊆-U
d_'8838''45'U_54 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6
d_'8838''45'U_54 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 = du_'8838''45'U_54
du_'8838''45'U_54 :: MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6
du_'8838''45'U_54 = coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
-- Relation.Unary.Properties.⊆-refl
d_'8838''45'refl_58 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) -> AgdaAny -> AgdaAny -> AgdaAny
d_'8838''45'refl_58 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_'8838''45'refl_58 v5
du_'8838''45'refl_58 :: AgdaAny -> AgdaAny
du_'8838''45'refl_58 v0 = coe v0
-- Relation.Unary.Properties.⊆-reflexive
d_'8838''45'reflexive_62 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  (AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_'8838''45'reflexive_62 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7
  = du_'8838''45'reflexive_62 v6 v7
du_'8838''45'reflexive_62 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  AgdaAny -> AgdaAny -> AgdaAny
du_'8838''45'reflexive_62 v0 v1
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v2 v3 -> coe v2 v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Relation.Unary.Properties.⊆-trans
d_'8838''45'trans_68 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  (AgdaAny -> ()) ->
  (AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny -> AgdaAny
d_'8838''45'trans_68 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 v9 v10 v11
  = du_'8838''45'trans_68 v8 v9 v10 v11
du_'8838''45'trans_68 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny -> AgdaAny
du_'8838''45'trans_68 v0 v1 v2 v3 = coe v1 v2 (coe v0 v2 v3)
-- Relation.Unary.Properties.⊆-antisym
d_'8838''45'antisym_76 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  (AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8838''45'antisym_76 ~v0 ~v1 ~v2 ~v3 ~v4
  = du_'8838''45'antisym_76
du_'8838''45'antisym_76 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8838''45'antisym_76
  = coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
-- Relation.Unary.Properties.⊆-min
d_'8838''45'min_78 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20 -> AgdaAny
d_'8838''45'min_78 ~v0 ~v1 ~v2 = du_'8838''45'min_78
du_'8838''45'min_78 ::
  (AgdaAny -> ()) ->
  AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20 -> AgdaAny
du_'8838''45'min_78 v0 v1 v2 = coe du_'8709''45''8838'_48
-- Relation.Unary.Properties.⊆-max
d_'8838''45'max_80 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6
d_'8838''45'max_80 ~v0 ~v1 ~v2 = du_'8838''45'max_80
du_'8838''45'max_80 ::
  (AgdaAny -> ()) ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6
du_'8838''45'max_80 v0 v1 v2 = coe du_'8838''45'U_54
-- Relation.Unary.Properties.⊂⇒⊆
d_'8834''8658''8838'_82 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  (AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_'8834''8658''8838'_82 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_'8834''8658''8838'_82 v6
du_'8834''8658''8838'_82 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  AgdaAny -> AgdaAny -> AgdaAny
du_'8834''8658''8838'_82 v0
  = coe MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v0)
-- Relation.Unary.Properties.⊂-trans
d_'8834''45'trans_84 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  (AgdaAny -> ()) ->
  (AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8834''45'trans_84 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 v9
  = du_'8834''45'trans_84 v8 v9
du_'8834''45'trans_84 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8834''45'trans_84 v0 v1
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe (\ v6 v7 -> coe v4 v6 (coe v2 v6 v7)))
                    (coe (\ v6 -> coe v5 (\ v7 v8 -> coe v2 v7 (coe v6 v7 v8))))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Relation.Unary.Properties.⊂-⊆-trans
d_'8834''45''8838''45'trans_100 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  (AgdaAny -> ()) ->
  (AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8834''45''8838''45'trans_100 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
                                v9
  = du_'8834''45''8838''45'trans_100 v8 v9
du_'8834''45''8838''45'trans_100 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8834''45''8838''45'trans_100 v0 v1
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v2 v3
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe (\ v4 v5 -> coe v1 v4 (coe v2 v4 v5)))
             (coe (\ v4 -> coe v3 (\ v5 v6 -> coe v4 v5 (coe v1 v5 v6))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Relation.Unary.Properties.⊆-⊂-trans
d_'8838''45''8834''45'trans_114 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  (AgdaAny -> ()) ->
  (AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8838''45''8834''45'trans_114 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
                                v9
  = du_'8838''45''8834''45'trans_114 v8 v9
du_'8838''45''8834''45'trans_114 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8838''45''8834''45'trans_114 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v2 v3
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe (\ v4 v5 -> coe v2 v4 (coe v0 v4 v5)))
             (coe (\ v4 -> coe v3 (\ v5 v6 -> coe v0 v5 (coe v4 v5 v6))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Relation.Unary.Properties.⊂-respʳ-≐
d_'8834''45'resp'691''45''8784'_128 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  (AgdaAny -> ()) ->
  (AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8834''45'resp'691''45''8784'_128 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
                                    v8
  = du_'8834''45'resp'691''45''8784'_128 v7 v8
du_'8834''45'resp'691''45''8784'_128 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8834''45'resp'691''45''8784'_128 v0 v1
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v2 v3
        -> coe du_'8834''45''8838''45'trans_100 (coe v1) (coe v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Relation.Unary.Properties.⊂-respˡ-≐
d_'8834''45'resp'737''45''8784'_134 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  (AgdaAny -> ()) ->
  (AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8834''45'resp'737''45''8784'_134 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7
                                    v8
  = du_'8834''45'resp'737''45''8784'_134 v7 v8
du_'8834''45'resp'737''45''8784'_134 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8834''45'resp'737''45''8784'_134 v0 v1
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v2 v3
        -> coe du_'8838''45''8834''45'trans_114 (coe v3) (coe v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Relation.Unary.Properties.⊂-resp-≐
d_'8834''45'resp'45''8784'_140 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8834''45'resp'45''8784'_140 ~v0 ~v1 ~v2
  = du_'8834''45'resp'45''8784'_140
du_'8834''45'resp'45''8784'_140 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8834''45'resp'45''8784'_140
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (\ v0 v1 v2 v3 v4 ->
         coe du_'8834''45'resp'691''45''8784'_128 v3 v4)
      (\ v0 v1 v2 v3 v4 ->
         coe du_'8834''45'resp'737''45''8784'_134 v3 v4)
-- Relation.Unary.Properties.⊂-irrefl
d_'8834''45'irrefl_142 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  (AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'8834''45'irrefl_142 = erased
-- Relation.Unary.Properties.⊂-antisym
d_'8834''45'antisym_148 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  (AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8834''45'antisym_148 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6
  = du_'8834''45'antisym_148 v5 v6
du_'8834''45'antisym_148 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8834''45'antisym_148 v0 v1
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> coe du_'8838''45'antisym_76 v2 v4
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Relation.Unary.Properties.⊂-asym
d_'8834''45'asym_154 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  (AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'8834''45'asym_154 = erased
-- Relation.Unary.Properties.∅-⊆′
d_'8709''45''8838''8242'_160 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20 -> AgdaAny
d_'8709''45''8838''8242'_160 = erased
-- Relation.Unary.Properties.⊆′-U
d_'8838''8242''45'U_164 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6
d_'8838''8242''45'U_164 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_'8838''8242''45'U_164
du_'8838''8242''45'U_164 ::
  MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6
du_'8838''8242''45'U_164
  = coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
-- Relation.Unary.Properties.⊆′-refl
d_'8838''8242''45'refl_166 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) -> AgdaAny -> AgdaAny -> AgdaAny
d_'8838''8242''45'refl_166 ~v0 ~v1 ~v2 ~v3 ~v4 v5
  = du_'8838''8242''45'refl_166 v5
du_'8838''8242''45'refl_166 :: AgdaAny -> AgdaAny
du_'8838''8242''45'refl_166 v0 = coe v0
-- Relation.Unary.Properties.⊆′-reflexive
d_'8838''8242''45'reflexive_172 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  (AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_'8838''8242''45'reflexive_172 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_'8838''8242''45'reflexive_172 v6
du_'8838''8242''45'reflexive_172 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  AgdaAny -> AgdaAny -> AgdaAny
du_'8838''8242''45'reflexive_172 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Relation.Unary.Properties.⊆′-trans
d_'8838''8242''45'trans_178 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  (AgdaAny -> ()) ->
  (AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny -> AgdaAny
d_'8838''8242''45'trans_178 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 v9
                            v10 v11
  = du_'8838''8242''45'trans_178 v8 v9 v10 v11
du_'8838''8242''45'trans_178 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny -> AgdaAny
du_'8838''8242''45'trans_178 v0 v1 v2 v3 = coe v1 v2 (coe v0 v2 v3)
-- Relation.Unary.Properties.⊆′-antisym
d_'8838''8242''45'antisym_188 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  (AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8838''8242''45'antisym_188 ~v0 ~v1 ~v2 ~v3 ~v4
  = du_'8838''8242''45'antisym_188
du_'8838''8242''45'antisym_188 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8838''8242''45'antisym_188
  = coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
-- Relation.Unary.Properties.⊆′-min
d_'8838''8242''45'min_190 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20 -> AgdaAny
d_'8838''8242''45'min_190 v0 ~v1 v2
  = du_'8838''8242''45'min_190 v0 v2
du_'8838''8242''45'min_190 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20 -> AgdaAny
du_'8838''8242''45'min_190 v0 v1
  = coe d_'8709''45''8838''8242'_160 v0 erased v1
-- Relation.Unary.Properties.⊆′-max
d_'8838''8242''45'max_192 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6
d_'8838''8242''45'max_192 ~v0 ~v1 ~v2 = du_'8838''8242''45'max_192
du_'8838''8242''45'max_192 ::
  (AgdaAny -> ()) ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6
du_'8838''8242''45'max_192 v0 v1 v2 = coe du_'8838''8242''45'U_164
-- Relation.Unary.Properties.⊂′⇒⊆′
d_'8834''8242''8658''8838''8242'_194 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  (AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_'8834''8242''8658''8838''8242'_194 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_'8834''8242''8658''8838''8242'_194 v6
du_'8834''8242''8658''8838''8242'_194 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  AgdaAny -> AgdaAny -> AgdaAny
du_'8834''8242''8658''8838''8242'_194 v0
  = coe MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v0)
-- Relation.Unary.Properties.⊂′-trans
d_'8834''8242''45'trans_196 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  (AgdaAny -> ()) ->
  (AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8834''8242''45'trans_196 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 v9
  = du_'8834''8242''45'trans_196 v8 v9
du_'8834''8242''45'trans_196 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8834''8242''45'trans_196 v0 v1
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe du_'8838''8242''45'trans_178 (coe v2) (coe v4))
                    (coe
                       (\ v6 ->
                          coe v5 (coe du_'8838''8242''45'trans_178 (coe v6) (coe v2))))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Relation.Unary.Properties.⊂′-⊆′-trans
d_'8834''8242''45''8838''8242''45'trans_208 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  (AgdaAny -> ()) ->
  (AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8834''8242''45''8838''8242''45'trans_208 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
                                            ~v6 ~v7 v8 v9
  = du_'8834''8242''45''8838''8242''45'trans_208 v8 v9
du_'8834''8242''45''8838''8242''45'trans_208 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8834''8242''45''8838''8242''45'trans_208 v0 v1
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v2 v3
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe du_'8838''8242''45'trans_178 (coe v2) (coe v1))
             (coe
                (\ v4 ->
                   coe v3 (coe du_'8838''8242''45'trans_178 (coe v1) (coe v4))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Relation.Unary.Properties.⊆′-⊂′-trans
d_'8838''8242''45''8834''8242''45'trans_218 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  (AgdaAny -> ()) ->
  (AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8838''8242''45''8834''8242''45'trans_218 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
                                            ~v6 ~v7 v8 v9
  = du_'8838''8242''45''8834''8242''45'trans_218 v8 v9
du_'8838''8242''45''8834''8242''45'trans_218 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8838''8242''45''8834''8242''45'trans_218 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v2 v3
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe du_'8838''8242''45'trans_178 (coe v0) (coe v2))
             (coe
                (\ v4 ->
                   coe v3 (coe du_'8838''8242''45'trans_178 (coe v4) (coe v0))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Relation.Unary.Properties.⊂′-respʳ-≐′
d_'8834''8242''45'resp'691''45''8784''8242'_228 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  (AgdaAny -> ()) ->
  (AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8834''8242''45'resp'691''45''8784''8242'_228 ~v0 ~v1 ~v2 ~v3 ~v4
                                                ~v5 ~v6 v7 v8
  = du_'8834''8242''45'resp'691''45''8784''8242'_228 v7 v8
du_'8834''8242''45'resp'691''45''8784''8242'_228 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8834''8242''45'resp'691''45''8784''8242'_228 v0 v1
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v2 v3
        -> coe
             du_'8834''8242''45''8838''8242''45'trans_208 (coe v1) (coe v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Relation.Unary.Properties.⊂′-respˡ-≐′
d_'8834''8242''45'resp'737''45''8784''8242'_234 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  (AgdaAny -> ()) ->
  (AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8834''8242''45'resp'737''45''8784''8242'_234 ~v0 ~v1 ~v2 ~v3 ~v4
                                                ~v5 ~v6 v7 v8
  = du_'8834''8242''45'resp'737''45''8784''8242'_234 v7 v8
du_'8834''8242''45'resp'737''45''8784''8242'_234 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8834''8242''45'resp'737''45''8784''8242'_234 v0 v1
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v2 v3
        -> coe
             du_'8838''8242''45''8834''8242''45'trans_218 (coe v3) (coe v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Relation.Unary.Properties.⊂′-resp-≐′
d_'8834''8242''45'resp'45''8784''8242'_240 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8834''8242''45'resp'45''8784''8242'_240 ~v0 ~v1 ~v2
  = du_'8834''8242''45'resp'45''8784''8242'_240
du_'8834''8242''45'resp'45''8784''8242'_240 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8834''8242''45'resp'45''8784''8242'_240
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (\ v0 v1 v2 v3 v4 ->
         coe du_'8834''8242''45'resp'691''45''8784''8242'_228 v3 v4)
      (\ v0 v1 v2 v3 v4 ->
         coe du_'8834''8242''45'resp'737''45''8784''8242'_234 v3 v4)
-- Relation.Unary.Properties.⊂′-irrefl
d_'8834''8242''45'irrefl_242 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  (AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'8834''8242''45'irrefl_242 = erased
-- Relation.Unary.Properties.⊂′-antisym
d_'8834''8242''45'antisym_248 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  (AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8834''8242''45'antisym_248 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6
  = du_'8834''8242''45'antisym_248 v5 v6
du_'8834''8242''45'antisym_248 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8834''8242''45'antisym_248 v0 v1
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> coe du_'8838''8242''45'antisym_188 v2 v4
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Relation.Unary.Properties.⊆⇒⊆′
d_'8838''8658''8838''8242'_254 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  (AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny -> AgdaAny
d_'8838''8658''8838''8242'_254 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 v8
  = du_'8838''8658''8838''8242'_254 v6 v7 v8
du_'8838''8658''8838''8242'_254 ::
  (AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny -> AgdaAny
du_'8838''8658''8838''8242'_254 v0 v1 v2 = coe v0 v1 v2
-- Relation.Unary.Properties.⊆′⇒⊆
d_'8838''8242''8658''8838'_260 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  (AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny -> AgdaAny
d_'8838''8242''8658''8838'_260 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 v8
  = du_'8838''8242''8658''8838'_260 v6 v7 v8
du_'8838''8242''8658''8838'_260 ::
  (AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny -> AgdaAny
du_'8838''8242''8658''8838'_260 v0 v1 v2 = coe v0 v1 v2
-- Relation.Unary.Properties.⊂⇒⊂′
d_'8834''8658''8834''8242'_266 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  (AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8834''8658''8834''8242'_266 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_'8834''8658''8834''8242'_266
du_'8834''8658''8834''8242'_266 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8834''8658''8834''8242'_266
  = coe
      MAlonzo.Code.Data.Product.Base.du_map_128
      (coe du_'8838''8658''8838''8242'_254)
      (coe
         (\ v0 v1 v2 ->
            coe v1 (coe du_'8838''8242''8658''8838'_260 (coe v2))))
-- Relation.Unary.Properties.⊂′⇒⊂
d_'8834''8242''8658''8834'_270 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  (AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8834''8242''8658''8834'_270 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_'8834''8242''8658''8834'_270
du_'8834''8242''8658''8834'_270 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8834''8242''8658''8834'_270
  = coe
      MAlonzo.Code.Data.Product.Base.du_map_128
      (coe du_'8838''8242''8658''8838'_260)
      (coe
         (\ v0 v1 v2 ->
            coe v1 (coe du_'8838''8658''8838''8242'_254 (coe v2))))
-- Relation.Unary.Properties.≐-refl
d_'8784''45'refl_274 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8784''45'refl_274 ~v0 ~v1 ~v2 ~v3 = du_'8784''45'refl_274
du_'8784''45'refl_274 :: MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8784''45'refl_274
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (\ v0 v1 -> v1))
      (coe (\ v0 v1 -> v1))
-- Relation.Unary.Properties.≐-sym
d_'8784''45'sym_276 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  (AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8784''45'sym_276 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 = du_'8784''45'sym_276
du_'8784''45'sym_276 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8784''45'sym_276
  = coe MAlonzo.Code.Data.Product.Base.du_swap_370
-- Relation.Unary.Properties.≐-trans
d_'8784''45'trans_278 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  (AgdaAny -> ()) ->
  (AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8784''45'trans_278 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
  = du_'8784''45'trans_278
du_'8784''45'trans_278 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8784''45'trans_278
  = coe
      MAlonzo.Code.Data.Product.Base.du_zip'8242'_312
      (coe (\ v0 v1 v2 v3 -> coe v1 v2 (coe v0 v2 v3)))
      (coe (\ v0 v1 v2 v3 -> coe v0 v2 (coe v1 v2 v3)))
-- Relation.Unary.Properties.≐′-refl
d_'8784''8242''45'refl_292 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8784''8242''45'refl_292 ~v0 ~v1 ~v2 ~v3
  = du_'8784''8242''45'refl_292
du_'8784''8242''45'refl_292 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8784''8242''45'refl_292
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (\ v0 v1 -> v1))
      (coe (\ v0 v1 -> v1))
-- Relation.Unary.Properties.≐′-sym
d_'8784''8242''45'sym_298 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  (AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8784''8242''45'sym_298 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_'8784''8242''45'sym_298
du_'8784''8242''45'sym_298 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8784''8242''45'sym_298
  = coe MAlonzo.Code.Data.Product.Base.du_swap_370
-- Relation.Unary.Properties.≐′-trans
d_'8784''8242''45'trans_300 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  (AgdaAny -> ()) ->
  (AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8784''8242''45'trans_300 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
  = du_'8784''8242''45'trans_300
du_'8784''8242''45'trans_300 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8784''8242''45'trans_300
  = coe
      MAlonzo.Code.Data.Product.Base.du_zip'8242'_312
      (coe (\ v0 v1 v2 v3 -> coe v1 v2 (coe v0 v2 v3)))
      (coe (\ v0 v1 v2 v3 -> coe v0 v2 (coe v1 v2 v3)))
-- Relation.Unary.Properties.≐⇒≐′
d_'8784''8658''8784''8242'_318 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  (AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8784''8658''8784''8242'_318 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_'8784''8658''8784''8242'_318
du_'8784''8658''8784''8242'_318 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8784''8658''8784''8242'_318
  = coe
      MAlonzo.Code.Data.Product.Base.du_map_128
      (coe du_'8838''8658''8838''8242'_254)
      (coe (\ v0 -> coe du_'8838''8658''8838''8242'_254))
-- Relation.Unary.Properties.≐′⇒≐
d_'8784''8242''8658''8784'_320 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  (AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8784''8242''8658''8784'_320 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_'8784''8242''8658''8784'_320
du_'8784''8242''8658''8784'_320 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8784''8242''8658''8784'_320
  = coe
      MAlonzo.Code.Data.Product.Base.du_map_128
      (coe du_'8838''8242''8658''8838'_260)
      (coe (\ v0 -> coe du_'8838''8242''8658''8838'_260))
-- Relation.Unary.Properties.≬-symmetric
d_'8812''45'symmetric_322 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  (AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8812''45'symmetric_322 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_'8812''45'symmetric_322
du_'8812''45'symmetric_322 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8812''45'symmetric_322
  = coe
      MAlonzo.Code.Data.Product.Base.du_map'8322'_150
      (coe (\ v0 -> coe MAlonzo.Code.Data.Product.Base.du_swap_370))
-- Relation.Unary.Properties.⊥-symmetric
d_'8869''45'symmetric_324 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  (AgdaAny -> ()) ->
  (AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'8869''45'symmetric_324 = erased
-- Relation.Unary.Properties.≬-sym
d_'8812''45'sym_328 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  (AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8812''45'sym_328 ~v0 ~v1 ~v2 ~v3 ~v4 = du_'8812''45'sym_328
du_'8812''45'sym_328 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8812''45'sym_328 = coe du_'8812''45'symmetric_322
-- Relation.Unary.Properties.⊥-sym
d_'8869''45'sym_330 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  (AgdaAny -> ()) ->
  (AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'8869''45'sym_330 = erased
-- Relation.Unary.Properties.≬⇒¬⊥
d_'8812''8658''172''8869'_332 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  (AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  (AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'8812''8658''172''8869'_332 = erased
-- Relation.Unary.Properties.⊥⇒¬≬
d_'8869''8658''172''8812'_338 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  (AgdaAny -> ()) ->
  (AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'8869''8658''172''8812'_338 = erased
-- Relation.Unary.Properties.map
d_map_346 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  (AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  (AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  AgdaAny -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_map_346 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 v8 = du_map_346 v6 v7 v8
du_map_346 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  (AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  AgdaAny -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du_map_346 v0 v1 v2
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
        -> coe
             MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
             (coe v3 v2) (coe v4 v2) (coe v1 v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Relation.Unary.Properties.∁?
d_'8705''63'_358 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  (AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  AgdaAny -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_'8705''63'_358 ~v0 ~v1 ~v2 ~v3 v4 v5 = du_'8705''63'_358 v4 v5
du_'8705''63'_358 ::
  (AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  AgdaAny -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du_'8705''63'_358 v0 v1
  = coe
      MAlonzo.Code.Relation.Nullary.Decidable.Core.du_'172''63'_76
      (coe v0 v1)
-- Relation.Unary.Properties._∪?_
d__'8746''63'__368 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  (AgdaAny -> ()) ->
  (AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  (AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  AgdaAny -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8746''63'__368 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 v8
  = du__'8746''63'__368 v6 v7 v8
du__'8746''63'__368 ::
  (AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  (AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  AgdaAny -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du__'8746''63'__368 v0 v1 v2
  = coe
      MAlonzo.Code.Relation.Nullary.Decidable.Core.du__'8846''45'dec__96
      (coe v0 v2) (coe v1 v2)
-- Relation.Unary.Properties._∩?_
d__'8745''63'__380 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  (AgdaAny -> ()) ->
  (AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  (AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  AgdaAny -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8745''63'__380 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 v8
  = du__'8745''63'__380 v6 v7 v8
du__'8745''63'__380 ::
  (AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  (AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  AgdaAny -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du__'8745''63'__380 v0 v1 v2
  = coe
      MAlonzo.Code.Relation.Nullary.Decidable.Core.du__'215''45'dec__84
      (coe v0 v2) (coe v1 v2)
-- Relation.Unary.Properties._×?_
d__'215''63'__392 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  (AgdaAny -> ()) ->
  (AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  (AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'215''63'__392 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 v9 v10
  = du__'215''63'__392 v8 v9 v10
du__'215''63'__392 ::
  (AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  (AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du__'215''63'__392 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
        -> coe
             MAlonzo.Code.Relation.Nullary.Decidable.Core.du__'215''45'dec__84
             (coe v0 v3) (coe v1 v4)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Relation.Unary.Properties._⊙?_
d__'8857''63'__406 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  (AgdaAny -> ()) ->
  (AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  (AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8857''63'__406 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 v9 v10
  = du__'8857''63'__406 v8 v9 v10
du__'8857''63'__406 ::
  (AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  (AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du__'8857''63'__406 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
        -> coe
             MAlonzo.Code.Relation.Nullary.Decidable.Core.du__'8846''45'dec__96
             (coe v0 v3) (coe v1 v4)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Relation.Unary.Properties._⊎?_
d__'8846''63'__420 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> ()) ->
  (AgdaAny -> ()) ->
  (AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  (AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8846''63'__420 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 v8 v9
  = du__'8846''63'__420 v7 v8 v9
du__'8846''63'__420 ::
  (AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  (AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du__'8846''63'__420 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v3 -> coe v0 v3
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v3 -> coe v1 v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Relation.Unary.Properties._~?
d__'126''63'_436 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> ()) ->
  (MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'126''63'_436 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7
  = du__'126''63'_436 v6 v7
du__'126''63'_436 ::
  (MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du__'126''63'_436 v0 v1
  = coe v0 (coe MAlonzo.Code.Data.Product.Base.du_swap_370 (coe v1))
-- Relation.Unary.Properties.does-≡
d_does'45''8801'_446 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  (AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  (AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_does'45''8801'_446 = erased
-- Relation.Unary.Properties.does-≐
d_does'45''8784'_462 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  (AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  (AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  (AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_does'45''8784'_462 = erased
-- Relation.Unary.Properties.U-irrelevant
d_U'45'irrelevant_468 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6 ->
  MAlonzo.Code.Agda.Builtin.Unit.T_'8868'_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_U'45'irrelevant_468 = erased
-- Relation.Unary.Properties.∁-irrelevant
d_'8705''45'irrelevant_476 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  AgdaAny ->
  (AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  (AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8705''45'irrelevant_476 = erased
