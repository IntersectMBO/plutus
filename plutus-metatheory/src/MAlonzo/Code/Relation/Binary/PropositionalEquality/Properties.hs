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

module MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Relation.Binary.Bundles
import qualified MAlonzo.Code.Relation.Binary.Properties.Setoid
import qualified MAlonzo.Code.Relation.Binary.Structures
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core

-- Relation.Binary.PropositionalEquality.Properties.J
d_J_34 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  AgdaAny ->
  (AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> ()) ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> AgdaAny
d_J_34 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 = du_J_34 v7
du_J_34 :: AgdaAny -> AgdaAny
du_J_34 v0 = coe v0
-- Relation.Binary.PropositionalEquality.Properties.dcong
d_dcong_54 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_dcong_54 = erased
-- Relation.Binary.PropositionalEquality.Properties.dcong₂
d_dcong'8322'_78 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> ()) ->
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_dcong'8322'_78 = erased
-- Relation.Binary.PropositionalEquality.Properties.dsubst₂
d_dsubst'8322'_100 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> AgdaAny
d_dsubst'8322'_100 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10
                   ~v11 v12
  = du_dsubst'8322'_100 v12
du_dsubst'8322'_100 :: AgdaAny -> AgdaAny
du_dsubst'8322'_100 v0 = coe v0
-- Relation.Binary.PropositionalEquality.Properties.ddcong₂
d_ddcong'8322'_132 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_ddcong'8322'_132 = erased
-- Relation.Binary.PropositionalEquality.Properties.trans-reflʳ
d_trans'45'refl'691'_142 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trans'45'refl'691'_142 = erased
-- Relation.Binary.PropositionalEquality.Properties.trans-assoc
d_trans'45'assoc_158 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trans'45'assoc_158 = erased
-- Relation.Binary.PropositionalEquality.Properties.trans-symˡ
d_trans'45'sym'737'_166 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trans'45'sym'737'_166 = erased
-- Relation.Binary.PropositionalEquality.Properties.trans-symʳ
d_trans'45'sym'691'_174 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trans'45'sym'691'_174 = erased
-- Relation.Binary.PropositionalEquality.Properties.trans-injectiveˡ
d_trans'45'injective'737'_188 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trans'45'injective'737'_188 = erased
-- Relation.Binary.PropositionalEquality.Properties.trans-injectiveʳ
d_trans'45'injective'691'_202 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trans'45'injective'691'_202 = erased
-- Relation.Binary.PropositionalEquality.Properties.cong-id
d_cong'45'id_212 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_cong'45'id_212 = erased
-- Relation.Binary.PropositionalEquality.Properties.cong-∘
d_cong'45''8728'_224 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  AgdaAny ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_cong'45''8728'_224 = erased
-- Relation.Binary.PropositionalEquality.Properties.sym-cong
d_sym'45'cong_234 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  AgdaAny ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sym'45'cong_234 = erased
-- Relation.Binary.PropositionalEquality.Properties.trans-cong
d_trans'45'cong_248 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trans'45'cong_248 = erased
-- Relation.Binary.PropositionalEquality.Properties.cong₂-reflˡ
d_cong'8322''45'refl'737'_262 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_cong'8322''45'refl'737'_262 = erased
-- Relation.Binary.PropositionalEquality.Properties.cong₂-reflʳ
d_cong'8322''45'refl'691'_276 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_cong'8322''45'refl'691'_276 = erased
-- Relation.Binary.PropositionalEquality.Properties._.subst-injective
d_subst'45'injective_298 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_subst'45'injective_298 = erased
-- Relation.Binary.PropositionalEquality.Properties._.subst-subst
d_subst'45'subst_310 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_subst'45'subst_310 = erased
-- Relation.Binary.PropositionalEquality.Properties._.subst-subst-sym
d_subst'45'subst'45'sym_316 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_subst'45'subst'45'sym_316 = erased
-- Relation.Binary.PropositionalEquality.Properties._.subst-sym-subst
d_subst'45'sym'45'subst_322 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_subst'45'sym'45'subst_322 = erased
-- Relation.Binary.PropositionalEquality.Properties.subst-∘
d_subst'45''8728'_336 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  AgdaAny ->
  AgdaAny ->
  (AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_subst'45''8728'_336 = erased
-- Relation.Binary.PropositionalEquality.Properties.subst-application′
d_subst'45'application'8242'_362 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> ()) ->
  (AgdaAny -> ()) ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_subst'45'application'8242'_362 = erased
-- Relation.Binary.PropositionalEquality.Properties.subst-application
d_subst'45'application_394 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  () ->
  (AgdaAny -> ()) ->
  (AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_subst'45'application_394 = erased
-- Relation.Binary.PropositionalEquality.Properties.isEquivalence
d_isEquivalence_396 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_396 ~v0 ~v1 = du_isEquivalence_396
du_isEquivalence_396 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
du_isEquivalence_396
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_constructor_46 erased
      erased erased
-- Relation.Binary.PropositionalEquality.Properties.isDecEquivalence
d_isDecEquivalence_398 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecEquivalence_48
d_isDecEquivalence_398 ~v0 ~v1 v2 = du_isDecEquivalence_398 v2
du_isDecEquivalence_398 ::
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecEquivalence_48
du_isDecEquivalence_398 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_constructor_70
      (coe du_isEquivalence_396) (coe v0)
-- Relation.Binary.PropositionalEquality.Properties.setoid
d_setoid_402 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_setoid_402 ~v0 ~v1 = du_setoid_402
du_setoid_402 :: MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
du_setoid_402
  = coe
      MAlonzo.Code.Relation.Binary.Bundles.C_constructor_84
      (coe du_isEquivalence_396)
-- Relation.Binary.PropositionalEquality.Properties.decSetoid
d_decSetoid_406 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  MAlonzo.Code.Relation.Binary.Bundles.T_DecSetoid_90
d_decSetoid_406 ~v0 ~v1 v2 = du_decSetoid_406 v2
du_decSetoid_406 ::
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  MAlonzo.Code.Relation.Binary.Bundles.T_DecSetoid_90
du_decSetoid_406 v0
  = coe
      MAlonzo.Code.Relation.Binary.Bundles.C_constructor_134
      (coe du_isDecEquivalence_398 (coe v0))
-- Relation.Binary.PropositionalEquality.Properties.isPreorder
d_isPreorder_410 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> MAlonzo.Code.Relation.Binary.Structures.T_IsPreorder_76
d_isPreorder_410 ~v0 ~v1 = du_isPreorder_410
du_isPreorder_410 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsPreorder_76
du_isPreorder_410
  = coe
      MAlonzo.Code.Relation.Binary.Properties.Setoid.du_'8776''45'isPreorder_40
      (coe du_setoid_402)
-- Relation.Binary.PropositionalEquality.Properties.isPartialOrder
d_isPartialOrder_412 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> MAlonzo.Code.Relation.Binary.Structures.T_IsPartialOrder_248
d_isPartialOrder_412 ~v0 ~v1 = du_isPartialOrder_412
du_isPartialOrder_412 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialOrder_248
du_isPartialOrder_412
  = coe
      MAlonzo.Code.Relation.Binary.Properties.Setoid.du_'8776''45'isPartialOrder_42
      (coe du_setoid_402)
-- Relation.Binary.PropositionalEquality.Properties.preorder
d_preorder_414 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> MAlonzo.Code.Relation.Binary.Bundles.T_Preorder_142
d_preorder_414 ~v0 ~v1 = du_preorder_414
du_preorder_414 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Preorder_142
du_preorder_414
  = coe
      MAlonzo.Code.Relation.Binary.Properties.Setoid.du_'8776''45'preorder_50
      (coe du_setoid_402)
-- Relation.Binary.PropositionalEquality.Properties.poset
d_poset_418 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> MAlonzo.Code.Relation.Binary.Bundles.T_Poset_492
d_poset_418 ~v0 ~v1 = du_poset_418
du_poset_418 :: MAlonzo.Code.Relation.Binary.Bundles.T_Poset_492
du_poset_418
  = coe
      MAlonzo.Code.Relation.Binary.Properties.Setoid.du_'8776''45'poset_52
      (coe du_setoid_402)
-- Relation.Binary.PropositionalEquality.Properties.≡-Reasoning._.begin_
d_begin__430 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_begin__430 = erased
-- Relation.Binary.PropositionalEquality.Properties.≡-Reasoning._.step-≡
d_step'45''8801'_434 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_step'45''8801'_434 = erased
-- Relation.Binary.PropositionalEquality.Properties.≡-Reasoning._.step-≡-∣
d_step'45''8801''45''8739'_436 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_step'45''8801''45''8739'_436 = erased
-- Relation.Binary.PropositionalEquality.Properties.≡-Reasoning._.step-≡-⟨
d_step'45''8801''45''10216'_438 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_step'45''8801''45''10216'_438 = erased
-- Relation.Binary.PropositionalEquality.Properties.≡-Reasoning._.step-≡-⟩
d_step'45''8801''45''10217'_440 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_step'45''8801''45''10217'_440 = erased
-- Relation.Binary.PropositionalEquality.Properties.≡-Reasoning._.step-≡˘
d_step'45''8801''728'_442 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_step'45''8801''728'_442 = erased
-- Relation.Binary.PropositionalEquality.Properties.≡-Reasoning._._∎
d__'8718'_446 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d__'8718'_446 = erased
