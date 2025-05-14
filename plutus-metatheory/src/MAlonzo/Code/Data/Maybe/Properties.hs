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

module MAlonzo.Code.Data.Maybe.Properties where

import Data.Text qualified
import MAlonzo.Code.Agda.Builtin.Bool qualified
import MAlonzo.Code.Agda.Builtin.Equality qualified
import MAlonzo.Code.Agda.Builtin.Maybe qualified
import MAlonzo.Code.Agda.Builtin.Sigma qualified
import MAlonzo.Code.Agda.Primitive qualified
import MAlonzo.Code.Algebra.Bundles qualified
import MAlonzo.Code.Algebra.Structures qualified
import MAlonzo.Code.Data.Maybe.Base qualified
import MAlonzo.Code.Data.Maybe.Relation.Unary.All qualified
import MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties qualified
import MAlonzo.Code.Relation.Binary.Structures qualified
import MAlonzo.Code.Relation.Nullary.Decidable.Core qualified
import MAlonzo.Code.Relation.Nullary.Reflects qualified
import MAlonzo.RTE (AgdaAny, add64, addInt, coe, eq64, eqInt, erased, geqInt, lt64, ltInt, mul64,
                    mulInt, quot64, quotInt, rem64, remInt, sub64, subInt, word64FromNat,
                    word64ToNat)
import MAlonzo.RTE qualified

-- Data.Maybe.Properties.just-injective
d_just'45'injective_22 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_just'45'injective_22 = erased
-- Data.Maybe.Properties.≡-dec
d_'8801''45'dec_24 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  Maybe AgdaAny ->
  Maybe AgdaAny ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_'8801''45'dec_24 ~v0 ~v1 v2 v3 v4 = du_'8801''45'dec_24 v2 v3 v4
du_'8801''45'dec_24 ::
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  Maybe AgdaAny ->
  Maybe AgdaAny ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du_'8801''45'dec_24 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_168
                    erased erased (coe v0 v3 v4)
             MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 erased)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Maybe.Properties.map-id
d_map'45'id_42 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  Maybe AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_map'45'id_42 = erased
-- Data.Maybe.Properties.map-id-local
d_map'45'id'45'local_52 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  Maybe AgdaAny ->
  MAlonzo.Code.Data.Maybe.Relation.Unary.All.T_All_18 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_map'45'id'45'local_52 = erased
-- Data.Maybe.Properties.map-<∣>
d_map'45''60''8739''62'_62 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  Maybe AgdaAny ->
  Maybe AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_map'45''60''8739''62'_62 = erased
-- Data.Maybe.Properties.map-cong
d_map'45'cong_78 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  Maybe AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_map'45'cong_78 = erased
-- Data.Maybe.Properties.map-cong-local
d_map'45'cong'45'local_94 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  Maybe AgdaAny ->
  MAlonzo.Code.Data.Maybe.Relation.Unary.All.T_All_18 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_map'45'cong'45'local_94 = erased
-- Data.Maybe.Properties.map-injective
d_map'45'injective_100 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  Maybe AgdaAny ->
  Maybe AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_map'45'injective_100 = erased
-- Data.Maybe.Properties.map-∘
d_map'45''8728'_118 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  Maybe AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_map'45''8728'_118 = erased
-- Data.Maybe.Properties.map-nothing
d_map'45'nothing_126 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  Maybe AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_map'45'nothing_126 = erased
-- Data.Maybe.Properties.map-just
d_map'45'just_134 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  Maybe AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_map'45'just_134 = erased
-- Data.Maybe.Properties.maybe-map
d_maybe'45'map_148 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (Maybe AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  Maybe AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_maybe'45'map_148 = erased
-- Data.Maybe.Properties.maybe′-map
d_maybe'8242''45'map_172 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) ->
  Maybe AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_maybe'8242''45'map_172 = erased
-- Data.Maybe.Properties._._.Associative
d_Associative_206 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> (Maybe AgdaAny -> Maybe AgdaAny -> Maybe AgdaAny) -> ()
d_Associative_206 = erased
-- Data.Maybe.Properties._._.Idempotent
d_Idempotent_220 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> (Maybe AgdaAny -> Maybe AgdaAny -> Maybe AgdaAny) -> ()
d_Idempotent_220 = erased
-- Data.Maybe.Properties._._.Identity
d_Identity_226 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  Maybe AgdaAny ->
  (Maybe AgdaAny -> Maybe AgdaAny -> Maybe AgdaAny) -> ()
d_Identity_226 = erased
-- Data.Maybe.Properties._._.LeftIdentity
d_LeftIdentity_252 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  Maybe AgdaAny ->
  (Maybe AgdaAny -> Maybe AgdaAny -> Maybe AgdaAny) -> ()
d_LeftIdentity_252 = erased
-- Data.Maybe.Properties._._.RightIdentity
d_RightIdentity_282 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  Maybe AgdaAny ->
  (Maybe AgdaAny -> Maybe AgdaAny -> Maybe AgdaAny) -> ()
d_RightIdentity_282 = erased
-- Data.Maybe.Properties._.<∣>-assoc
d_'60''8739''62''45'assoc_312 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  Maybe AgdaAny ->
  Maybe AgdaAny ->
  Maybe AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'60''8739''62''45'assoc_312 = erased
-- Data.Maybe.Properties._.<∣>-identityˡ
d_'60''8739''62''45'identity'737'_324 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  Maybe AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'60''8739''62''45'identity'737'_324 = erased
-- Data.Maybe.Properties._.<∣>-identityʳ
d_'60''8739''62''45'identity'691'_328 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  Maybe AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'60''8739''62''45'identity'691'_328 = erased
-- Data.Maybe.Properties._.<∣>-identity
d_'60''8739''62''45'identity_332 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'60''8739''62''45'identity_332 ~v0 ~v1
  = du_'60''8739''62''45'identity_332
du_'60''8739''62''45'identity_332 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'60''8739''62''45'identity_332
  = coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased
-- Data.Maybe.Properties._.<∣>-idem
d_'60''8739''62''45'idem_334 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  Maybe AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'60''8739''62''45'idem_334 = erased
-- Data.Maybe.Properties._._.IsMagma
d_IsMagma_392 a0 a1 a2 = ()
-- Data.Maybe.Properties._._.IsMonoid
d_IsMonoid_398 a0 a1 a2 a3 = ()
-- Data.Maybe.Properties._._.IsSemigroup
d_IsSemigroup_420 a0 a1 a2 = ()
-- Data.Maybe.Properties._._.IsMagma.isEquivalence
d_isEquivalence_1692 ::
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_1692 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isEquivalence_184 (coe v0)
-- Data.Maybe.Properties._._.IsMagma.∙-cong
d_'8729''45'cong_1706 ::
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176 ->
  Maybe AgdaAny ->
  Maybe AgdaAny ->
  Maybe AgdaAny ->
  Maybe AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8729''45'cong_1706 = erased
-- Data.Maybe.Properties._._.IsMonoid.identity
d_identity_1802 ::
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_686 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_identity_1802 v0
  = coe MAlonzo.Code.Algebra.Structures.d_identity_698 (coe v0)
-- Data.Maybe.Properties._._.IsMonoid.isSemigroup
d_isSemigroup_1814 ::
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_686 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_472
d_isSemigroup_1814 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isSemigroup_696 (coe v0)
-- Data.Maybe.Properties._._.IsSemigroup.assoc
d_assoc_2546 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_472 ->
  Maybe AgdaAny ->
  Maybe AgdaAny ->
  Maybe AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_assoc_2546 = erased
-- Data.Maybe.Properties._._.IsSemigroup.isMagma
d_isMagma_2550 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_472 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176
d_isMagma_2550 v0
  = coe MAlonzo.Code.Algebra.Structures.d_isMagma_480 (coe v0)
-- Data.Maybe.Properties._.<∣>-isMagma
d_'60''8739''62''45'isMagma_2860 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> MAlonzo.Code.Algebra.Structures.T_IsMagma_176
d_'60''8739''62''45'isMagma_2860 ~v0 ~v1
  = du_'60''8739''62''45'isMagma_2860
du_'60''8739''62''45'isMagma_2860 ::
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176
du_'60''8739''62''45'isMagma_2860
  = coe
      MAlonzo.Code.Algebra.Structures.C_IsMagma'46'constructor_1867
      (coe
         MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties.du_isEquivalence_396)
      erased
-- Data.Maybe.Properties._.<∣>-isSemigroup
d_'60''8739''62''45'isSemigroup_2862 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> MAlonzo.Code.Algebra.Structures.T_IsSemigroup_472
d_'60''8739''62''45'isSemigroup_2862 ~v0 ~v1
  = du_'60''8739''62''45'isSemigroup_2862
du_'60''8739''62''45'isSemigroup_2862 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_472
du_'60''8739''62''45'isSemigroup_2862
  = coe
      MAlonzo.Code.Algebra.Structures.C_IsSemigroup'46'constructor_10417
      (coe du_'60''8739''62''45'isMagma_2860) erased
-- Data.Maybe.Properties._.<∣>-isMonoid
d_'60''8739''62''45'isMonoid_2864 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> MAlonzo.Code.Algebra.Structures.T_IsMonoid_686
d_'60''8739''62''45'isMonoid_2864 ~v0 ~v1
  = du_'60''8739''62''45'isMonoid_2864
du_'60''8739''62''45'isMonoid_2864 ::
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_686
du_'60''8739''62''45'isMonoid_2864
  = coe
      MAlonzo.Code.Algebra.Structures.C_IsMonoid'46'constructor_15873
      (coe du_'60''8739''62''45'isSemigroup_2862)
      (coe du_'60''8739''62''45'identity_332)
-- Data.Maybe.Properties._.<∣>-semigroup
d_'60''8739''62''45'semigroup_2866 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> MAlonzo.Code.Algebra.Bundles.T_Semigroup_536
d_'60''8739''62''45'semigroup_2866 ~v0 ~v1
  = du_'60''8739''62''45'semigroup_2866
du_'60''8739''62''45'semigroup_2866 ::
  MAlonzo.Code.Algebra.Bundles.T_Semigroup_536
du_'60''8739''62''45'semigroup_2866
  = coe
      MAlonzo.Code.Algebra.Bundles.C_Semigroup'46'constructor_9793
      (coe MAlonzo.Code.Data.Maybe.Base.du__'60''8739''62'__80)
      (coe du_'60''8739''62''45'isSemigroup_2862)
-- Data.Maybe.Properties._.<∣>-monoid
d_'60''8739''62''45'monoid_2868 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> MAlonzo.Code.Algebra.Bundles.T_Monoid_882
d_'60''8739''62''45'monoid_2868 ~v0 ~v1
  = du_'60''8739''62''45'monoid_2868
du_'60''8739''62''45'monoid_2868 ::
  MAlonzo.Code.Algebra.Bundles.T_Monoid_882
du_'60''8739''62''45'monoid_2868
  = coe
      MAlonzo.Code.Algebra.Bundles.C_Monoid'46'constructor_16157
      (coe MAlonzo.Code.Data.Maybe.Base.du__'60''8739''62'__80)
      (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18)
      (coe du_'60''8739''62''45'isMonoid_2864)
-- Data.Maybe.Properties.map-id₂
d_map'45'id'8322'_2870 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  Maybe AgdaAny ->
  MAlonzo.Code.Data.Maybe.Relation.Unary.All.T_All_18 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_map'45'id'8322'_2870 = erased
-- Data.Maybe.Properties.map-cong₂
d_map'45'cong'8322'_2872 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  Maybe AgdaAny ->
  MAlonzo.Code.Data.Maybe.Relation.Unary.All.T_All_18 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_map'45'cong'8322'_2872 = erased
-- Data.Maybe.Properties.map-compose
d_map'45'compose_2874 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  Maybe AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_map'45'compose_2874 = erased
-- Data.Maybe.Properties.map-<∣>-commute
d_map'45''60''8739''62''45'commute_2876 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  Maybe AgdaAny ->
  Maybe AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_map'45''60''8739''62''45'commute_2876 = erased
