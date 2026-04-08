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

module MAlonzo.Code.Relation.Binary.HeterogeneousEquality where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Function.Bundles
import qualified MAlonzo.Code.Relation.Binary.Bundles
import qualified MAlonzo.Code.Relation.Binary.Consequences
import qualified MAlonzo.Code.Relation.Binary.HeterogeneousEquality.Core
import qualified MAlonzo.Code.Relation.Binary.Indexed.Heterogeneous.Bundles
import qualified MAlonzo.Code.Relation.Binary.Indexed.Heterogeneous.Structures
import qualified MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties
import qualified MAlonzo.Code.Relation.Binary.Structures
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core

-- Relation.Binary.HeterogeneousEquality._≇_
d__'8775'__28 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> AgdaAny -> () -> AgdaAny -> ()
d__'8775'__28 = erased
-- Relation.Binary.HeterogeneousEquality.≅-to-type-≡
d_'8773''45'to'45'type'45''8801'_42 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  () ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Relation.Binary.HeterogeneousEquality.Core.T__'8773'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8773''45'to'45'type'45''8801'_42 = erased
-- Relation.Binary.HeterogeneousEquality.≅-to-subst-≡
d_'8773''45'to'45'subst'45''8801'_56 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  () ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Relation.Binary.HeterogeneousEquality.Core.T__'8773'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8773''45'to'45'subst'45''8801'_56 = erased
-- Relation.Binary.HeterogeneousEquality.reflexive
d_reflexive_62 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Relation.Binary.HeterogeneousEquality.Core.T__'8773'__22
d_reflexive_62 = erased
-- Relation.Binary.HeterogeneousEquality.sym
d_sym_68 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Relation.Binary.HeterogeneousEquality.Core.T__'8773'__22 ->
  MAlonzo.Code.Relation.Binary.HeterogeneousEquality.Core.T__'8773'__22
d_sym_68 = erased
-- Relation.Binary.HeterogeneousEquality.trans
d_trans_76 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Relation.Binary.HeterogeneousEquality.Core.T__'8773'__22 ->
  MAlonzo.Code.Relation.Binary.HeterogeneousEquality.Core.T__'8773'__22 ->
  MAlonzo.Code.Relation.Binary.HeterogeneousEquality.Core.T__'8773'__22
d_trans_76 = erased
-- Relation.Binary.HeterogeneousEquality.subst
d_subst_84 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Relation.Binary.HeterogeneousEquality.Core.T__'8773'__22 ->
  AgdaAny -> AgdaAny
d_subst_84 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 = du_subst_84 v7
du_subst_84 :: AgdaAny -> AgdaAny
du_subst_84 v0 = coe v0
-- Relation.Binary.HeterogeneousEquality.subst₂
d_subst'8322'_100 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Relation.Binary.HeterogeneousEquality.Core.T__'8773'__22 ->
  MAlonzo.Code.Relation.Binary.HeterogeneousEquality.Core.T__'8773'__22 ->
  AgdaAny -> AgdaAny
d_subst'8322'_100 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11
                  v12
  = du_subst'8322'_100 v12
du_subst'8322'_100 :: AgdaAny -> AgdaAny
du_subst'8322'_100 v0 = coe v0
-- Relation.Binary.HeterogeneousEquality.subst-removable
d_subst'45'removable_116 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Relation.Binary.HeterogeneousEquality.Core.T__'8773'__22 ->
  AgdaAny ->
  MAlonzo.Code.Relation.Binary.HeterogeneousEquality.Core.T__'8773'__22
d_subst'45'removable_116 = erased
-- Relation.Binary.HeterogeneousEquality.subst₂-removable
d_subst'8322''45'removable_138 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Relation.Binary.HeterogeneousEquality.Core.T__'8773'__22 ->
  MAlonzo.Code.Relation.Binary.HeterogeneousEquality.Core.T__'8773'__22 ->
  AgdaAny ->
  MAlonzo.Code.Relation.Binary.HeterogeneousEquality.Core.T__'8773'__22
d_subst'8322''45'removable_138 = erased
-- Relation.Binary.HeterogeneousEquality.≡-subst-removable
d_'8801''45'subst'45'removable_154 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  MAlonzo.Code.Relation.Binary.HeterogeneousEquality.Core.T__'8773'__22
d_'8801''45'subst'45'removable_154 = erased
-- Relation.Binary.HeterogeneousEquality.cong
d_cong_172 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> ()) ->
  AgdaAny ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Relation.Binary.HeterogeneousEquality.Core.T__'8773'__22 ->
  MAlonzo.Code.Relation.Binary.HeterogeneousEquality.Core.T__'8773'__22
d_cong_172 = erased
-- Relation.Binary.HeterogeneousEquality.cong-app
d_cong'45'app_188 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Relation.Binary.HeterogeneousEquality.Core.T__'8773'__22 ->
  AgdaAny ->
  MAlonzo.Code.Relation.Binary.HeterogeneousEquality.Core.T__'8773'__22
d_cong'45'app_188 = erased
-- Relation.Binary.HeterogeneousEquality.cong₂
d_cong'8322'_214 ::
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
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Relation.Binary.HeterogeneousEquality.Core.T__'8773'__22 ->
  MAlonzo.Code.Relation.Binary.HeterogeneousEquality.Core.T__'8773'__22 ->
  MAlonzo.Code.Relation.Binary.HeterogeneousEquality.Core.T__'8773'__22
d_cong'8322'_214 = erased
-- Relation.Binary.HeterogeneousEquality.resp₂
d_resp'8322'_224 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_resp'8322'_224 ~v0 ~v1 ~v2 ~v3 = du_resp'8322'_224
du_resp'8322'_224 :: MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_resp'8322'_224
  = coe
      MAlonzo.Code.Relation.Binary.Consequences.du_subst'8658'resp'8322'_60
      (coe (\ v0 v1 v2 v3 v4 -> v4))
-- Relation.Binary.HeterogeneousEquality._.icong
d_icong_260 ::
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
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Relation.Binary.HeterogeneousEquality.Core.T__'8773'__22 ->
  MAlonzo.Code.Relation.Binary.HeterogeneousEquality.Core.T__'8773'__22
d_icong_260 = erased
-- Relation.Binary.HeterogeneousEquality._.icong₂
d_icong'8322'_288 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> AgdaAny -> ()) ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Relation.Binary.HeterogeneousEquality.Core.T__'8773'__22 ->
  MAlonzo.Code.Relation.Binary.HeterogeneousEquality.Core.T__'8773'__22 ->
  MAlonzo.Code.Relation.Binary.HeterogeneousEquality.Core.T__'8773'__22
d_icong'8322'_288 = erased
-- Relation.Binary.HeterogeneousEquality._.icong-subst-removable
d_icong'45'subst'45'removable_304 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Relation.Binary.HeterogeneousEquality.Core.T__'8773'__22 ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  MAlonzo.Code.Relation.Binary.HeterogeneousEquality.Core.T__'8773'__22
d_icong'45'subst'45'removable_304 = erased
-- Relation.Binary.HeterogeneousEquality._.icong-≡-subst-removable
d_icong'45''8801''45'subst'45'removable_320 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  MAlonzo.Code.Relation.Binary.HeterogeneousEquality.Core.T__'8773'__22
d_icong'45''8801''45'subst'45'removable_320 = erased
-- Relation.Binary.HeterogeneousEquality.≅-irrelevant
d_'8773''45'irrelevant_330 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  () ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Relation.Binary.HeterogeneousEquality.Core.T__'8773'__22 ->
  MAlonzo.Code.Relation.Binary.HeterogeneousEquality.Core.T__'8773'__22 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8773''45'irrelevant_330 = erased
-- Relation.Binary.HeterogeneousEquality._.≅-heterogeneous-irrelevant
d_'8773''45'heterogeneous'45'irrelevant_360 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  () ->
  () ->
  () ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Relation.Binary.HeterogeneousEquality.Core.T__'8773'__22 ->
  MAlonzo.Code.Relation.Binary.HeterogeneousEquality.Core.T__'8773'__22 ->
  MAlonzo.Code.Relation.Binary.HeterogeneousEquality.Core.T__'8773'__22 ->
  MAlonzo.Code.Relation.Binary.HeterogeneousEquality.Core.T__'8773'__22
d_'8773''45'heterogeneous'45'irrelevant_360 = erased
-- Relation.Binary.HeterogeneousEquality._.≅-heterogeneous-irrelevantˡ
d_'8773''45'heterogeneous'45'irrelevant'737'_366 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  () ->
  () ->
  () ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Relation.Binary.HeterogeneousEquality.Core.T__'8773'__22 ->
  MAlonzo.Code.Relation.Binary.HeterogeneousEquality.Core.T__'8773'__22 ->
  MAlonzo.Code.Relation.Binary.HeterogeneousEquality.Core.T__'8773'__22 ->
  MAlonzo.Code.Relation.Binary.HeterogeneousEquality.Core.T__'8773'__22
d_'8773''45'heterogeneous'45'irrelevant'737'_366 = erased
-- Relation.Binary.HeterogeneousEquality._.≅-heterogeneous-irrelevantʳ
d_'8773''45'heterogeneous'45'irrelevant'691'_372 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  () ->
  () ->
  () ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Relation.Binary.HeterogeneousEquality.Core.T__'8773'__22 ->
  MAlonzo.Code.Relation.Binary.HeterogeneousEquality.Core.T__'8773'__22 ->
  MAlonzo.Code.Relation.Binary.HeterogeneousEquality.Core.T__'8773'__22 ->
  MAlonzo.Code.Relation.Binary.HeterogeneousEquality.Core.T__'8773'__22
d_'8773''45'heterogeneous'45'irrelevant'691'_372 = erased
-- Relation.Binary.HeterogeneousEquality.isEquivalence
d_isEquivalence_378 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_378 ~v0 ~v1 = du_isEquivalence_378
du_isEquivalence_378 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
du_isEquivalence_378
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_constructor_46 erased
      erased erased
-- Relation.Binary.HeterogeneousEquality.setoid
d_setoid_380 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_setoid_380 ~v0 ~v1 = du_setoid_380
du_setoid_380 :: MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
du_setoid_380
  = coe
      MAlonzo.Code.Relation.Binary.Bundles.C_constructor_84
      (coe du_isEquivalence_378)
-- Relation.Binary.HeterogeneousEquality.indexedSetoid
d_indexedSetoid_388 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  MAlonzo.Code.Relation.Binary.Indexed.Heterogeneous.Bundles.T_IndexedSetoid_18
d_indexedSetoid_388 ~v0 ~v1 ~v2 ~v3 = du_indexedSetoid_388
du_indexedSetoid_388 ::
  MAlonzo.Code.Relation.Binary.Indexed.Heterogeneous.Bundles.T_IndexedSetoid_18
du_indexedSetoid_388
  = coe
      MAlonzo.Code.Relation.Binary.Indexed.Heterogeneous.Bundles.C_constructor_50
      (coe
         MAlonzo.Code.Relation.Binary.Indexed.Heterogeneous.Structures.C_constructor_40
         erased erased erased)
-- Relation.Binary.HeterogeneousEquality.≡↔≅
d_'8801''8596''8773'_402 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> ()) ->
  AgdaAny -> MAlonzo.Code.Function.Bundles.T_Inverse_2122
d_'8801''8596''8773'_402 ~v0 ~v1 ~v2 ~v3 ~v4
  = du_'8801''8596''8773'_402
du_'8801''8596''8773'_402 ::
  MAlonzo.Code.Function.Bundles.T_Inverse_2122
du_'8801''8596''8773'_402
  = coe
      MAlonzo.Code.Function.Bundles.C_constructor_2220 (coe (\ v0 -> v0))
      (coe (\ v0 -> v0)) erased erased
      (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased)
-- Relation.Binary.HeterogeneousEquality.decSetoid
d_decSetoid_414 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  MAlonzo.Code.Relation.Binary.Bundles.T_DecSetoid_90
d_decSetoid_414 ~v0 ~v1 v2 = du_decSetoid_414 v2
du_decSetoid_414 ::
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  MAlonzo.Code.Relation.Binary.Bundles.T_DecSetoid_90
du_decSetoid_414 v0
  = coe
      MAlonzo.Code.Relation.Binary.Bundles.C_constructor_134
      (coe
         MAlonzo.Code.Relation.Binary.Structures.C_constructor_70
         (coe du_isEquivalence_378) (coe v0))
-- Relation.Binary.HeterogeneousEquality.isPreorder
d_isPreorder_430 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> MAlonzo.Code.Relation.Binary.Structures.T_IsPreorder_76
d_isPreorder_430 ~v0 ~v1 = du_isPreorder_430
du_isPreorder_430 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsPreorder_76
du_isPreorder_430
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_constructor_126
      (coe du_isEquivalence_378) (coe (\ v0 v1 v2 -> v2)) erased
-- Relation.Binary.HeterogeneousEquality.isPreorder-≡
d_isPreorder'45''8801'_436 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> MAlonzo.Code.Relation.Binary.Structures.T_IsPreorder_76
d_isPreorder'45''8801'_436 ~v0 ~v1 = du_isPreorder'45''8801'_436
du_isPreorder'45''8801'_436 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsPreorder_76
du_isPreorder'45''8801'_436
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_constructor_126
      (coe
         MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties.du_isEquivalence_396)
      erased erased
-- Relation.Binary.HeterogeneousEquality.preorder
d_preorder_438 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> MAlonzo.Code.Relation.Binary.Bundles.T_Preorder_142
d_preorder_438 ~v0 ~v1 = du_preorder_438
du_preorder_438 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Preorder_142
du_preorder_438
  = coe
      MAlonzo.Code.Relation.Binary.Bundles.C_constructor_232
      (coe du_isPreorder'45''8801'_436)
-- Relation.Binary.HeterogeneousEquality.≅-Reasoning._IsRelatedTo_
d__IsRelatedTo__460 a0 a1 a2 a3 a4 a5 = ()
data T__IsRelatedTo__460 = C_relTo_472
-- Relation.Binary.HeterogeneousEquality.≅-Reasoning.start
d_start_478 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  AgdaAny ->
  AgdaAny ->
  T__IsRelatedTo__460 ->
  MAlonzo.Code.Relation.Binary.HeterogeneousEquality.Core.T__'8773'__22
d_start_478 = erased
-- Relation.Binary.HeterogeneousEquality.≅-Reasoning.≡-go
d_'8801''45'go_486 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  () ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T__IsRelatedTo__460 -> T__IsRelatedTo__460
d_'8801''45'go_486 = erased
-- Relation.Binary.HeterogeneousEquality.≅-Reasoning._._.begin_
d_begin__506 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  () ->
  AgdaAny ->
  AgdaAny ->
  T__IsRelatedTo__460 ->
  MAlonzo.Code.Relation.Binary.HeterogeneousEquality.Core.T__'8773'__22
d_begin__506 = erased
-- Relation.Binary.HeterogeneousEquality.≅-Reasoning._._.step-≡
d_step'45''8801'_510 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  () ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  T__IsRelatedTo__460 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T__IsRelatedTo__460
d_step'45''8801'_510 = erased
-- Relation.Binary.HeterogeneousEquality.≅-Reasoning._._.step-≡-∣
d_step'45''8801''45''8739'_512 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  () ->
  AgdaAny -> AgdaAny -> T__IsRelatedTo__460 -> T__IsRelatedTo__460
d_step'45''8801''45''8739'_512 = erased
-- Relation.Binary.HeterogeneousEquality.≅-Reasoning._._.step-≡-⟨
d_step'45''8801''45''10216'_514 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  () ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  T__IsRelatedTo__460 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T__IsRelatedTo__460
d_step'45''8801''45''10216'_514 = erased
-- Relation.Binary.HeterogeneousEquality.≅-Reasoning._._.step-≡-⟩
d_step'45''8801''45''10217'_516 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  () ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  T__IsRelatedTo__460 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T__IsRelatedTo__460
d_step'45''8801''45''10217'_516 = erased
-- Relation.Binary.HeterogeneousEquality.≅-Reasoning._._.step-≡˘
d_step'45''8801''728'_518 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  () ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  T__IsRelatedTo__460 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T__IsRelatedTo__460
d_step'45''8801''728'_518 = erased
-- Relation.Binary.HeterogeneousEquality.≅-Reasoning._._._∎
d__'8718'_530 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> AgdaAny -> T__IsRelatedTo__460
d__'8718'_530 = erased
-- Relation.Binary.HeterogeneousEquality.≅-Reasoning._≅⟨_⟩_
d__'8773''10216'_'10217'__538 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Relation.Binary.HeterogeneousEquality.Core.T__'8773'__22 ->
  T__IsRelatedTo__460 -> T__IsRelatedTo__460
d__'8773''10216'_'10217'__538 = erased
-- Relation.Binary.HeterogeneousEquality.≅-Reasoning._≅⟨_⟨_
d__'8773''10216'_'10216'__550 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Relation.Binary.HeterogeneousEquality.Core.T__'8773'__22 ->
  T__IsRelatedTo__460 -> T__IsRelatedTo__460
d__'8773''10216'_'10216'__550 = erased
-- Relation.Binary.HeterogeneousEquality.≅-Reasoning._≅˘⟨_⟩_
d__'8773''728''10216'_'10217'__556 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Relation.Binary.HeterogeneousEquality.Core.T__'8773'__22 ->
  T__IsRelatedTo__460 -> T__IsRelatedTo__460
d__'8773''728''10216'_'10217'__556 = erased
-- Relation.Binary.HeterogeneousEquality.Reveal_·_is_
d_Reveal_'183'_is__574 a0 a1 a2 a3 a4 a5 a6 = ()
data T_Reveal_'183'_is__574 = C_'91'_'93'_590
-- Relation.Binary.HeterogeneousEquality.Reveal_·_is_.eq
d_eq_588 ::
  T_Reveal_'183'_is__574 ->
  MAlonzo.Code.Relation.Binary.HeterogeneousEquality.Core.T__'8773'__22
d_eq_588 = erased
-- Relation.Binary.HeterogeneousEquality.inspect
d_inspect_602 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> T_Reveal_'183'_is__574
d_inspect_602 = erased
