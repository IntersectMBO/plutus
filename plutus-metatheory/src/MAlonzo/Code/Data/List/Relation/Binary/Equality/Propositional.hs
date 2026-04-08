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

module MAlonzo.Code.Data.List.Relation.Binary.Equality.Propositional where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Data.Fin.Base
import qualified MAlonzo.Code.Data.List.Relation.Binary.Equality.Setoid
import qualified MAlonzo.Code.Data.List.Relation.Binary.Pointwise
import qualified MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base
import qualified MAlonzo.Code.Data.List.Relation.Unary.All
import qualified MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Core
import qualified MAlonzo.Code.Data.List.Relation.Unary.Any
import qualified MAlonzo.Code.Relation.Binary.Bundles
import qualified MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties
import qualified MAlonzo.Code.Relation.Binary.Structures
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core

-- Data.List.Relation.Binary.Equality.Propositional._._≋_
d__'8779'__18 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> [AgdaAny] -> [AgdaAny] -> ()
d__'8779'__18 = erased
-- Data.List.Relation.Binary.Equality.Propositional._.++-cancelʳ
d_'43''43''45'cancel'691'_20 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48
d_'43''43''45'cancel'691'_20 ~v0 ~v1
  = du_'43''43''45'cancel'691'_20
du_'43''43''45'cancel'691'_20 ::
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48
du_'43''43''45'cancel'691'_20 v0
  = coe
      MAlonzo.Code.Data.List.Relation.Binary.Equality.Setoid.du_'43''43''45'cancel'691'_188
-- Data.List.Relation.Binary.Equality.Propositional._.++-cancelˡ
d_'43''43''45'cancel'737'_22 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48
d_'43''43''45'cancel'737'_22 ~v0 ~v1
  = du_'43''43''45'cancel'737'_22
du_'43''43''45'cancel'737'_22 ::
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48
du_'43''43''45'cancel'737'_22 v0 v1 v2
  = coe
      MAlonzo.Code.Data.List.Relation.Binary.Equality.Setoid.du_'43''43''45'cancel'737'_178
      v0
-- Data.List.Relation.Binary.Equality.Propositional._.++⁺
d_'43''43''8314'_24 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48
d_'43''43''8314'_24 ~v0 ~v1 = du_'43''43''8314'_24
du_'43''43''8314'_24 ::
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48
du_'43''43''8314'_24 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Data.List.Relation.Binary.Equality.Setoid.du_'43''43''8314'_158
      v0 v1
-- Data.List.Relation.Binary.Equality.Propositional._.++⁺ʳ
d_'43''43''8314''691'_26 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48
d_'43''43''8314''691'_26 ~v0 ~v1 = du_'43''43''8314''691'_26
du_'43''43''8314''691'_26 ::
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48
du_'43''43''8314''691'_26
  = coe
      MAlonzo.Code.Data.List.Relation.Binary.Equality.Setoid.du_'43''43''8314''691'_168
      (coe
         MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties.du_setoid_402)
-- Data.List.Relation.Binary.Equality.Propositional._.++⁺ˡ
d_'43''43''8314''737'_28 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48
d_'43''43''8314''737'_28 ~v0 ~v1 = du_'43''43''8314''737'_28
du_'43''43''8314''737'_28 ::
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48
du_'43''43''8314''737'_28 v0 v1 v2
  = coe
      MAlonzo.Code.Data.List.Relation.Binary.Equality.Setoid.du_'43''43''8314''737'_162
      (coe
         MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties.du_setoid_402)
      v2
-- Data.List.Relation.Binary.Equality.Propositional._.Unique-resp-≋
d_Unique'45'resp'45''8779'_30 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Core.T_AllPairs_20 ->
  MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Core.T_AllPairs_20
d_Unique'45'resp'45''8779'_30 ~v0 ~v1
  = du_Unique'45'resp'45''8779'_30
du_Unique'45'resp'45''8779'_30 ::
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Core.T_AllPairs_20 ->
  MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Core.T_AllPairs_20
du_Unique'45'resp'45''8779'_30
  = coe
      MAlonzo.Code.Data.List.Relation.Binary.Equality.Setoid.du_Unique'45'resp'45''8779'_92
-- Data.List.Relation.Binary.Equality.Propositional._.concat⁺
d_concat'8314'_32 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  [[AgdaAny]] ->
  [[AgdaAny]] ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48
d_concat'8314'_32 ~v0 ~v1 = du_concat'8314'_32
du_concat'8314'_32 ::
  [[AgdaAny]] ->
  [[AgdaAny]] ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48
du_concat'8314'_32
  = coe
      MAlonzo.Code.Data.List.Relation.Binary.Equality.Setoid.du_concat'8314'_190
-- Data.List.Relation.Binary.Equality.Propositional._.filter⁺
d_filter'8314'_34 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  (AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   AgdaAny -> AgdaAny) ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48
d_filter'8314'_34 ~v0 ~v1 = du_filter'8314'_34
du_filter'8314'_34 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  (AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   AgdaAny -> AgdaAny) ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48
du_filter'8314'_34 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Data.List.Relation.Binary.Equality.Setoid.du_filter'8314'_222
      v2 v4 v5 v6
-- Data.List.Relation.Binary.Equality.Propositional._.foldr⁺
d_foldr'8314'_36 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  [AgdaAny] ->
  [AgdaAny] ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_foldr'8314'_36 = erased
-- Data.List.Relation.Binary.Equality.Propositional._.map⁺
d_map'8314'_38 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny) ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48
d_map'8314'_38 ~v0 ~v1 = du_map'8314'_38
du_map'8314'_38 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny) ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48
du_map'8314'_38 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Data.List.Relation.Binary.Equality.Setoid.du_map'8314'_122
      v4 v5 v6 v7
-- Data.List.Relation.Binary.Equality.Propositional._.Pointwise.Pointwise
d_Pointwise_39 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 = ()
-- Data.List.Relation.Binary.Equality.Propositional._.reverse⁺
d_reverse'8314'_40 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48
d_reverse'8314'_40 ~v0 ~v1 = du_reverse'8314'_40
du_reverse'8314'_40 ::
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48
du_reverse'8314'_40
  = coe
      MAlonzo.Code.Data.List.Relation.Binary.Equality.Setoid.du_reverse'8314'_228
-- Data.List.Relation.Binary.Equality.Propositional._.tabulate⁺
d_tabulate'8314'_42 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> AgdaAny) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> AgdaAny) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48
d_tabulate'8314'_42 ~v0 ~v1 = du_tabulate'8314'_42
du_tabulate'8314'_42 ::
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> AgdaAny) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> AgdaAny) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48
du_tabulate'8314'_42 v0 v1 v2
  = coe
      MAlonzo.Code.Data.List.Relation.Binary.Equality.Setoid.du_tabulate'8314'_204
      v0
-- Data.List.Relation.Binary.Equality.Propositional._.tabulate⁻
d_tabulate'8315'_44 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> AgdaAny) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> AgdaAny) ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_tabulate'8315'_44 = erased
-- Data.List.Relation.Binary.Equality.Propositional._.ʳ++⁺
d_'691''43''43''8314'_46 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48
d_'691''43''43''8314'_46 ~v0 ~v1 = du_'691''43''43''8314'_46
du_'691''43''43''8314'_46 ::
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48
du_'691''43''43''8314'_46 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Data.List.Relation.Binary.Equality.Setoid.du_'691''43''43''8314'_226
      v0 v1
-- Data.List.Relation.Binary.Equality.Propositional._.isEquivalence
d_isEquivalence_48 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_48 ~v0 ~v1 = du_isEquivalence_48
du_isEquivalence_48 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
du_isEquivalence_48
  = let v0
          = coe
              MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties.du_setoid_402 in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62
         (coe
            MAlonzo.Code.Data.List.Relation.Binary.Equality.Setoid.du_'8779''45'setoid_78
            (coe v0)))
-- Data.List.Relation.Binary.Equality.Propositional._.≋-length
d_'8779''45'length_50 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8779''45'length_50 = erased
-- Data.List.Relation.Binary.Equality.Propositional._.refl
d_refl_52 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48
d_refl_52 ~v0 ~v1 = du_refl_52
du_refl_52 ::
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48
du_refl_52
  = let v0
          = coe
              MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties.du_setoid_402 in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_refl_36
         (coe
            MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62
            (coe
               MAlonzo.Code.Data.List.Relation.Binary.Equality.Setoid.du_'8779''45'setoid_78
               (coe v0))))
-- Data.List.Relation.Binary.Equality.Propositional._.reflexive
d_reflexive_54 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48
d_reflexive_54 ~v0 ~v1 = du_reflexive_54
du_reflexive_54 ::
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48
du_reflexive_54
  = let v0
          = coe
              MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties.du_setoid_402 in
    coe
      (let v1
             = coe
                 MAlonzo.Code.Data.List.Relation.Binary.Equality.Setoid.du_'8779''45'setoid_78
                 (coe v0) in
       coe
         (\ v2 v3 v4 ->
            coe
              MAlonzo.Code.Relation.Binary.Structures.du_reflexive_42
              (coe
                 MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62 (coe v1))
              v2))
-- Data.List.Relation.Binary.Equality.Propositional._.≋-setoid
d_'8779''45'setoid_56 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_'8779''45'setoid_56 ~v0 ~v1 = du_'8779''45'setoid_56
du_'8779''45'setoid_56 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
du_'8779''45'setoid_56
  = coe
      MAlonzo.Code.Data.List.Relation.Binary.Equality.Setoid.du_'8779''45'setoid_78
      (coe
         MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties.du_setoid_402)
-- Data.List.Relation.Binary.Equality.Propositional._.sym
d_sym_58 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48
d_sym_58 ~v0 ~v1 = du_sym_58
du_sym_58 ::
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48
du_sym_58
  = let v0
          = coe
              MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties.du_setoid_402 in
    coe
      (let v1
             = coe
                 MAlonzo.Code.Data.List.Relation.Binary.Equality.Setoid.du_'8779''45'setoid_78
                 (coe v0) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_sym_38
            (coe
               MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62 (coe v1))))
-- Data.List.Relation.Binary.Equality.Propositional._.trans
d_trans_60 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48
d_trans_60 ~v0 ~v1 = du_trans_60
du_trans_60 ::
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48
du_trans_60
  = let v0
          = coe
              MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties.du_setoid_402 in
    coe
      (let v1
             = coe
                 MAlonzo.Code.Data.List.Relation.Binary.Equality.Setoid.du_'8779''45'setoid_78
                 (coe v0) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_trans_40
            (coe
               MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62 (coe v1))))
-- Data.List.Relation.Binary.Equality.Propositional._.Pointwise.All-resp-Pointwise
d_All'45'resp'45'Pointwise_68 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_All'45'resp'45'Pointwise_68 ~v0 ~v1
  = du_All'45'resp'45'Pointwise_68
du_All'45'resp'45'Pointwise_68 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_All'45'resp'45'Pointwise_68 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = coe
      MAlonzo.Code.Data.List.Relation.Binary.Pointwise.du_All'45'resp'45'Pointwise_206
      v6 v7 v8 v9 v10
-- Data.List.Relation.Binary.Equality.Propositional._.Pointwise.AllPairs-resp-Pointwise
d_AllPairs'45'resp'45'Pointwise_70 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Core.T_AllPairs_20 ->
  MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Core.T_AllPairs_20
d_AllPairs'45'resp'45'Pointwise_70 ~v0 ~v1
  = du_AllPairs'45'resp'45'Pointwise_70
du_AllPairs'45'resp'45'Pointwise_70 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Core.T_AllPairs_20 ->
  MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Core.T_AllPairs_20
du_AllPairs'45'resp'45'Pointwise_70 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
                                    v10
  = coe
      MAlonzo.Code.Data.List.Relation.Binary.Pointwise.du_AllPairs'45'resp'45'Pointwise_240
      v6 v7 v8 v9 v10
-- Data.List.Relation.Binary.Equality.Propositional._.Pointwise.Any-resp-Pointwise
d_Any'45'resp'45'Pointwise_72 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
d_Any'45'resp'45'Pointwise_72 ~v0 ~v1
  = du_Any'45'resp'45'Pointwise_72
du_Any'45'resp'45'Pointwise_72 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
du_Any'45'resp'45'Pointwise_72 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = coe
      MAlonzo.Code.Data.List.Relation.Binary.Pointwise.du_Any'45'resp'45'Pointwise_222
      v6 v7 v8 v9 v10
-- Data.List.Relation.Binary.Equality.Propositional.≋⇒≡
d_'8779''8658''8801'_76 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8779''8658''8801'_76 = erased
-- Data.List.Relation.Binary.Equality.Propositional.≡⇒≋
d_'8801''8658''8779'_82 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48
d_'8801''8658''8779'_82 ~v0 ~v1 v2 ~v3 ~v4
  = du_'8801''8658''8779'_82 v2
du_'8801''8658''8779'_82 ::
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48
du_'8801''8658''8779'_82 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_refl_36
      (MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62
         (coe
            MAlonzo.Code.Data.List.Relation.Binary.Equality.Setoid.du_'8779''45'setoid_78
            (coe
               MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties.du_setoid_402)))
      v0
