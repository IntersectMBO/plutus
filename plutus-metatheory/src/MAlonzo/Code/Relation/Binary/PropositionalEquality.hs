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

module MAlonzo.Code.Relation.Binary.PropositionalEquality where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Function.Dependent.Bundles
import qualified MAlonzo.Code.Function.Indexed.Relation.Binary.Equality
import qualified MAlonzo.Code.Relation.Binary.Bundles
import qualified MAlonzo.Code.Relation.Binary.Indexed.Heterogeneous.Bundles
import qualified MAlonzo.Code.Relation.Binary.Indexed.Heterogeneous.Construct.Trivial
import qualified MAlonzo.Code.Relation.Binary.Indexed.Heterogeneous.Structures
import qualified MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core

-- Relation.Binary.PropositionalEquality._→-setoid_
d__'8594''45'setoid__26 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> () -> MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d__'8594''45'setoid__26 ~v0 ~v1 ~v2 ~v3 = du__'8594''45'setoid__26
du__'8594''45'setoid__26 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
du__'8594''45'setoid__26
  = coe
      MAlonzo.Code.Function.Indexed.Relation.Binary.Equality.du_'8801''45'setoid_18
      (coe
         MAlonzo.Code.Relation.Binary.Indexed.Heterogeneous.Construct.Trivial.du_indexedSetoid_106
         (coe
            MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties.du_setoid_402))
-- Relation.Binary.PropositionalEquality.:→-to-Π
d_'58''8594''45'to'45'Π_38 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Relation.Binary.Indexed.Heterogeneous.Bundles.T_IndexedSetoid_18 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Dependent.Bundles.T_Func_42
d_'58''8594''45'to'45'Π_38 ~v0 ~v1 ~v2 ~v3 v4 v5
  = du_'58''8594''45'to'45'Π_38 v4 v5
du_'58''8594''45'to'45'Π_38 ::
  MAlonzo.Code.Relation.Binary.Indexed.Heterogeneous.Bundles.T_IndexedSetoid_18 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Dependent.Bundles.T_Func_42
du_'58''8594''45'to'45'Π_38 v0 v1
  = coe
      MAlonzo.Code.Function.Dependent.Bundles.C_constructor_64 (coe v1)
      (\ v2 v3 v4 -> coe du_'46'extendedlambda0_44 (coe v0) (coe v1) v2)
-- Relation.Binary.PropositionalEquality..extendedlambda0
d_'46'extendedlambda0_44 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Relation.Binary.Indexed.Heterogeneous.Bundles.T_IndexedSetoid_18 ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny
d_'46'extendedlambda0_44 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 ~v7 ~v8
  = du_'46'extendedlambda0_44 v4 v5 v6
du_'46'extendedlambda0_44 ::
  MAlonzo.Code.Relation.Binary.Indexed.Heterogeneous.Bundles.T_IndexedSetoid_18 ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du_'46'extendedlambda0_44 v0 v1 v2
  = coe
      MAlonzo.Code.Relation.Binary.Indexed.Heterogeneous.Structures.d_refl_30
      (MAlonzo.Code.Relation.Binary.Indexed.Heterogeneous.Bundles.d_isEquivalence_38
         (coe v0))
      v2 (coe v1 v2)
-- Relation.Binary.PropositionalEquality.→-to-⟶
d_'8594''45'to'45''10230'_50 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Dependent.Bundles.T_Func_42
d_'8594''45'to'45''10230'_50 ~v0 ~v1 ~v2 ~v3 v4
  = du_'8594''45'to'45''10230'_50 v4
du_'8594''45'to'45''10230'_50 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  (AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Function.Dependent.Bundles.T_Func_42
du_'8594''45'to'45''10230'_50 v0
  = coe
      du_'58''8594''45'to'45'Π_38
      (coe
         MAlonzo.Code.Relation.Binary.Indexed.Heterogeneous.Bundles.C_constructor_50
         (coe
            MAlonzo.Code.Relation.Binary.Indexed.Heterogeneous.Construct.Trivial.du_isIndexedEquivalence_32
            (coe
               MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62 (coe v0))))
-- Relation.Binary.PropositionalEquality.naturality
d_naturality_66 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_naturality_66 = erased
-- Relation.Binary.PropositionalEquality.cong-≡id
d_cong'45''8801'id_84 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_cong'45''8801'id_84 = erased
-- Relation.Binary.PropositionalEquality._.fx≡x
d_fx'8801'x_96 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_fx'8801'x_96 = erased
-- Relation.Binary.PropositionalEquality._.f²x≡x
d_f'178'x'8801'x_98 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_f'178'x'8801'x_98 = erased
-- Relation.Binary.PropositionalEquality._.≡-≟-identity
d_'8801''45''8799''45'identity_118 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8801''45''8799''45'identity_118 = erased
-- Relation.Binary.PropositionalEquality._.≢-≟-identity
d_'8802''45''8799''45'identity_124 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  AgdaAny ->
  AgdaAny ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8802''45''8799''45'identity_124 = erased
-- Relation.Binary.PropositionalEquality.Reveal_·_is_
d_Reveal_'183'_is__142 a0 a1 a2 a3 a4 a5 a6 = ()
data T_Reveal_'183'_is__142 = C_'91'_'93'_158
-- Relation.Binary.PropositionalEquality.Reveal_·_is_.eq
d_eq_156 ::
  T_Reveal_'183'_is__142 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_eq_156 = erased
-- Relation.Binary.PropositionalEquality.inspect
d_inspect_170 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> T_Reveal_'183'_is__142
d_inspect_170 = erased
-- Relation.Binary.PropositionalEquality.isPropositional
d_isPropositional_176 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> ()
d_isPropositional_176 = erased
