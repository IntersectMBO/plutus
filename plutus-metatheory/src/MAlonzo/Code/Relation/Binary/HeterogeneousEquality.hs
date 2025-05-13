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

module MAlonzo.Code.Relation.Binary.HeterogeneousEquality where

import Data.Text qualified
import MAlonzo.Code.Agda.Builtin.Equality qualified
import MAlonzo.Code.Agda.Builtin.Sigma qualified
import MAlonzo.Code.Agda.Primitive qualified
import MAlonzo.Code.Function.Bundles qualified
import MAlonzo.Code.Relation.Binary.Bundles qualified
import MAlonzo.Code.Relation.Binary.Consequences qualified
import MAlonzo.Code.Relation.Binary.HeterogeneousEquality.Core qualified
import MAlonzo.Code.Relation.Binary.Indexed.Heterogeneous.Bundles qualified
import MAlonzo.Code.Relation.Binary.Indexed.Heterogeneous.Structures qualified
import MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties qualified
import MAlonzo.Code.Relation.Binary.Structures qualified
import MAlonzo.Code.Relation.Nullary.Decidable.Core qualified
import MAlonzo.RTE (AgdaAny, add64, addInt, coe, eq64, eqInt, erased, geqInt, lt64, ltInt, mul64,
                    mulInt, quot64, quotInt, rem64, remInt, sub64, subInt, word64FromNat,
                    word64ToNat)
import MAlonzo.RTE qualified

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
      MAlonzo.Code.Relation.Binary.Consequences.du_subst'8658'resp'8322'_58
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
  () -> MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_378 ~v0 ~v1 = du_isEquivalence_378
du_isEquivalence_378 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
du_isEquivalence_378
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_IsEquivalence'46'constructor_745
      erased erased erased
-- Relation.Binary.HeterogeneousEquality.setoid
d_setoid_380 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
d_setoid_380 ~v0 ~v1 = du_setoid_380
du_setoid_380 :: MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
du_setoid_380
  = coe
      MAlonzo.Code.Relation.Binary.Bundles.C_Setoid'46'constructor_733
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
      MAlonzo.Code.Relation.Binary.Indexed.Heterogeneous.Bundles.C_IndexedSetoid'46'constructor_445
      (coe
         MAlonzo.Code.Relation.Binary.Indexed.Heterogeneous.Structures.C_IsIndexedEquivalence'46'constructor_1089
         erased erased erased)
-- Relation.Binary.HeterogeneousEquality.≡↔≅
d_'8801''8596''8773'_402 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> ()) ->
  AgdaAny -> MAlonzo.Code.Function.Bundles.T_Inverse_1960
d_'8801''8596''8773'_402 ~v0 ~v1 ~v2 ~v3 ~v4
  = du_'8801''8596''8773'_402
du_'8801''8596''8773'_402 ::
  MAlonzo.Code.Function.Bundles.T_Inverse_1960
du_'8801''8596''8773'_402
  = coe
      MAlonzo.Code.Function.Bundles.C_Inverse'46'constructor_38621
      (coe (\ v0 -> v0)) (coe (\ v0 -> v0)) erased erased
      (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased)
-- Relation.Binary.HeterogeneousEquality.decSetoid
d_decSetoid_414 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  MAlonzo.Code.Relation.Binary.Bundles.T_DecSetoid_84
d_decSetoid_414 ~v0 ~v1 v2 = du_decSetoid_414 v2
du_decSetoid_414 ::
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  MAlonzo.Code.Relation.Binary.Bundles.T_DecSetoid_84
du_decSetoid_414 v0
  = coe
      MAlonzo.Code.Relation.Binary.Bundles.C_DecSetoid'46'constructor_1389
      (coe
         MAlonzo.Code.Relation.Binary.Structures.C_IsDecEquivalence'46'constructor_3083
         (coe du_isEquivalence_378) (coe v0))
-- Relation.Binary.HeterogeneousEquality.isPreorder
d_isPreorder_430 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> MAlonzo.Code.Relation.Binary.Structures.T_IsPreorder_70
d_isPreorder_430 ~v0 ~v1 = du_isPreorder_430
du_isPreorder_430 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsPreorder_70
du_isPreorder_430
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_IsPreorder'46'constructor_4003
      (coe du_isEquivalence_378) (coe (\ v0 v1 v2 -> v2)) erased
-- Relation.Binary.HeterogeneousEquality.isPreorder-≡
d_isPreorder'45''8801'_436 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> MAlonzo.Code.Relation.Binary.Structures.T_IsPreorder_70
d_isPreorder'45''8801'_436 ~v0 ~v1 = du_isPreorder'45''8801'_436
du_isPreorder'45''8801'_436 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsPreorder_70
du_isPreorder'45''8801'_436
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_IsPreorder'46'constructor_4003
      (coe
         MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties.du_isEquivalence_396)
      erased erased
-- Relation.Binary.HeterogeneousEquality.preorder
d_preorder_438 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> MAlonzo.Code.Relation.Binary.Bundles.T_Preorder_132
d_preorder_438 ~v0 ~v1 = du_preorder_438
du_preorder_438 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Preorder_132
du_preorder_438
  = coe
      MAlonzo.Code.Relation.Binary.Bundles.C_Preorder'46'constructor_2267
      (coe du_isPreorder'45''8801'_436)
-- Relation.Binary.HeterogeneousEquality.≅-Reasoning._IsRelatedTo_
d__IsRelatedTo__458 a0 a1 a2 a3 a4 = ()
data T__IsRelatedTo__458 = C_relTo_470
-- Relation.Binary.HeterogeneousEquality.≅-Reasoning.start
d_start_476 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  () ->
  AgdaAny ->
  AgdaAny ->
  T__IsRelatedTo__458 ->
  MAlonzo.Code.Relation.Binary.HeterogeneousEquality.Core.T__'8773'__22
d_start_476 = erased
-- Relation.Binary.HeterogeneousEquality.≅-Reasoning.≡-go
d_'8801''45'go_482 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T__IsRelatedTo__458 -> T__IsRelatedTo__458
d_'8801''45'go_482 = erased
-- Relation.Binary.HeterogeneousEquality.≅-Reasoning._._.begin_
d_begin__500 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  () ->
  AgdaAny ->
  AgdaAny ->
  T__IsRelatedTo__458 ->
  MAlonzo.Code.Relation.Binary.HeterogeneousEquality.Core.T__'8773'__22
d_begin__500 = erased
-- Relation.Binary.HeterogeneousEquality.≅-Reasoning._._.step-≡
d_step'45''8801'_512 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  T__IsRelatedTo__458 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T__IsRelatedTo__458
d_step'45''8801'_512 = erased
-- Relation.Binary.HeterogeneousEquality.≅-Reasoning._._.step-≡-∣
d_step'45''8801''45''8739'_514 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  AgdaAny -> AgdaAny -> T__IsRelatedTo__458 -> T__IsRelatedTo__458
d_step'45''8801''45''8739'_514 = erased
-- Relation.Binary.HeterogeneousEquality.≅-Reasoning._._.step-≡-⟨
d_step'45''8801''45''10216'_516 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  T__IsRelatedTo__458 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T__IsRelatedTo__458
d_step'45''8801''45''10216'_516 = erased
-- Relation.Binary.HeterogeneousEquality.≅-Reasoning._._.step-≡-⟩
d_step'45''8801''45''10217'_518 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  T__IsRelatedTo__458 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T__IsRelatedTo__458
d_step'45''8801''45''10217'_518 = erased
-- Relation.Binary.HeterogeneousEquality.≅-Reasoning._._.step-≡˘
d_step'45''8801''728'_520 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  T__IsRelatedTo__458 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T__IsRelatedTo__458
d_step'45''8801''728'_520 = erased
-- Relation.Binary.HeterogeneousEquality.≅-Reasoning._._._∎
d__'8718'_524 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> AgdaAny -> T__IsRelatedTo__458
d__'8718'_524 = erased
-- Relation.Binary.HeterogeneousEquality.≅-Reasoning._≅⟨_⟩_
d__'8773''10216'_'10217'__532 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  () ->
  () ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Relation.Binary.HeterogeneousEquality.Core.T__'8773'__22 ->
  T__IsRelatedTo__458 -> T__IsRelatedTo__458
d__'8773''10216'_'10217'__532 = erased
-- Relation.Binary.HeterogeneousEquality.≅-Reasoning._≅⟨_⟨_
d__'8773''10216'_'10216'__544 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  () ->
  () ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Relation.Binary.HeterogeneousEquality.Core.T__'8773'__22 ->
  T__IsRelatedTo__458 -> T__IsRelatedTo__458
d__'8773''10216'_'10216'__544 = erased
-- Relation.Binary.HeterogeneousEquality.≅-Reasoning._≅˘⟨_⟩_
d__'8773''728''10216'_'10217'__550 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  () ->
  () ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Relation.Binary.HeterogeneousEquality.Core.T__'8773'__22 ->
  T__IsRelatedTo__458 -> T__IsRelatedTo__458
d__'8773''728''10216'_'10217'__550 = erased
-- Relation.Binary.HeterogeneousEquality.Reveal_·_is_
d_Reveal_'183'_is__568 a0 a1 a2 a3 a4 a5 a6 = ()
data T_Reveal_'183'_is__568 = C_'91'_'93'_584
-- Relation.Binary.HeterogeneousEquality.Reveal_·_is_.eq
d_eq_582 ::
  T_Reveal_'183'_is__568 ->
  MAlonzo.Code.Relation.Binary.HeterogeneousEquality.Core.T__'8773'__22
d_eq_582 = erased
-- Relation.Binary.HeterogeneousEquality.inspect
d_inspect_596 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> T_Reveal_'183'_is__568
d_inspect_596 = erased
