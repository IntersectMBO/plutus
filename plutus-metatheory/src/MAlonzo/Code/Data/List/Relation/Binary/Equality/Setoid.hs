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

module MAlonzo.Code.Data.List.Relation.Binary.Equality.Setoid where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Data.Fin.Base
import qualified MAlonzo.Code.Data.List.Relation.Binary.Pointwise
import qualified MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base
import qualified MAlonzo.Code.Data.List.Relation.Unary.All
import qualified MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Core
import qualified MAlonzo.Code.Relation.Binary.Bundles
import qualified MAlonzo.Code.Relation.Binary.Properties.Setoid
import qualified MAlonzo.Code.Relation.Binary.Structures
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core

-- Data.List.Relation.Binary.Equality.Setoid._.AllPairs
d_AllPairs_20 a0 a1 a2 a3 = ()
-- Data.List.Relation.Binary.Equality.Setoid._≋_
d__'8779'__76 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  [AgdaAny] -> [AgdaAny] -> ()
d__'8779'__76 = erased
-- Data.List.Relation.Binary.Equality.Setoid.≋-setoid
d_'8779''45'setoid_78 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_'8779''45'setoid_78 ~v0 ~v1 v2 = du_'8779''45'setoid_78 v2
du_'8779''45'setoid_78 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
du_'8779''45'setoid_78 v0
  = coe
      MAlonzo.Code.Data.List.Relation.Binary.Pointwise.du_setoid_188
      (coe v0)
-- Data.List.Relation.Binary.Equality.Setoid._.isEquivalence
d_isEquivalence_82 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_82 ~v0 ~v1 v2 = du_isEquivalence_82 v2
du_isEquivalence_82 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
du_isEquivalence_82 v0
  = coe
      MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62
      (coe du_'8779''45'setoid_78 (coe v0))
-- Data.List.Relation.Binary.Equality.Setoid._.refl
d_refl_84 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48
d_refl_84 ~v0 ~v1 v2 = du_refl_84 v2
du_refl_84 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48
du_refl_84 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_refl_36
      (coe
         MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62
         (coe du_'8779''45'setoid_78 (coe v0)))
-- Data.List.Relation.Binary.Equality.Setoid._.reflexive
d_reflexive_86 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48
d_reflexive_86 ~v0 ~v1 v2 = du_reflexive_86 v2
du_reflexive_86 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48
du_reflexive_86 v0
  = let v1 = coe du_'8779''45'setoid_78 (coe v0) in
    coe
      (\ v2 v3 v4 ->
         coe
           MAlonzo.Code.Relation.Binary.Structures.du_reflexive_42
           (coe
              MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62 (coe v1))
           v2)
-- Data.List.Relation.Binary.Equality.Setoid._.sym
d_sym_88 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48
d_sym_88 ~v0 ~v1 v2 = du_sym_88 v2
du_sym_88 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48
du_sym_88 v0
  = let v1 = coe du_'8779''45'setoid_78 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_sym_38
         (coe
            MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62 (coe v1)))
-- Data.List.Relation.Binary.Equality.Setoid._.trans
d_trans_90 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48
d_trans_90 ~v0 ~v1 v2 = du_trans_90 v2
du_trans_90 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48
du_trans_90 v0
  = let v1 = coe du_'8779''45'setoid_78 (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_trans_40
         (coe
            MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62 (coe v1)))
-- Data.List.Relation.Binary.Equality.Setoid.Unique-resp-≋
d_Unique'45'resp'45''8779'_92 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Core.T_AllPairs_20 ->
  MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Core.T_AllPairs_20
d_Unique'45'resp'45''8779'_92 ~v0 ~v1 ~v2 v3 v4
  = du_Unique'45'resp'45''8779'_92 v3 v4
du_Unique'45'resp'45''8779'_92 ::
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Core.T_AllPairs_20 ->
  MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Core.T_AllPairs_20
du_Unique'45'resp'45''8779'_92 v0 v1
  = coe
      MAlonzo.Code.Data.List.Relation.Binary.Pointwise.du_AllPairs'45'resp'45'Pointwise_240
      (coe
         MAlonzo.Code.Relation.Binary.Properties.Setoid.du_'8777''45'resp'8322'_72)
      (coe v0) (coe v1)
-- Data.List.Relation.Binary.Equality.Setoid.≋-length
d_'8779''45'length_98 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8779''45'length_98 = erased
-- Data.List.Relation.Binary.Equality.Setoid._._≋′_
d__'8779''8242'__114 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  [AgdaAny] -> [AgdaAny] -> ()
d__'8779''8242'__114 = erased
-- Data.List.Relation.Binary.Equality.Setoid._.map⁺
d_map'8314'_122 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48
d_map'8314'_122 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 v8 v9 v10
  = du_map'8314'_122 v7 v8 v9 v10
du_map'8314'_122 ::
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48
du_map'8314'_122 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Data.List.Relation.Binary.Pointwise.du_map'8314'_414
      (coe v1) (coe v2)
      (coe
         MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.du_map_120
         (coe v0) (coe v1) (coe v2) (coe v3))
-- Data.List.Relation.Binary.Equality.Setoid.foldr⁺
d_foldr'8314'_150 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny ->
   AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  [AgdaAny] ->
  [AgdaAny] ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  AgdaAny
d_foldr'8314'_150 ~v0 ~v1 ~v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
  = du_foldr'8314'_150 v3 v4 v5 v6 v7 v8 v9 v10 v11
du_foldr'8314'_150 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny ->
   AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  [AgdaAny] ->
  [AgdaAny] ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  AgdaAny
du_foldr'8314'_150 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = coe
      MAlonzo.Code.Data.List.Relation.Binary.Pointwise.du_foldr'8314'_466
      (coe v3) (coe v4) (coe v0) (coe v1) (coe v2) (coe v5) (coe v6)
      (coe v7) (coe v8)
-- Data.List.Relation.Binary.Equality.Setoid.++⁺
d_'43''43''8314'_158 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48
d_'43''43''8314'_158 ~v0 ~v1 ~v2 v3 v4 ~v5 ~v6
  = du_'43''43''8314'_158 v3 v4
du_'43''43''8314'_158 ::
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48
du_'43''43''8314'_158 v0 v1
  = coe
      MAlonzo.Code.Data.List.Relation.Binary.Pointwise.du_'43''43''8314'_296
      (coe v0) (coe v1)
-- Data.List.Relation.Binary.Equality.Setoid.++⁺ˡ
d_'43''43''8314''737'_162 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48
d_'43''43''8314''737'_162 ~v0 ~v1 v2 ~v3 ~v4 v5
  = du_'43''43''8314''737'_162 v2 v5
du_'43''43''8314''737'_162 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48
du_'43''43''8314''737'_162 v0 v1
  = coe
      MAlonzo.Code.Data.List.Relation.Binary.Pointwise.du_'43''43''8314''737'_364
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_refl_36
         (coe
            MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62 (coe v0)))
      (coe v1)
-- Data.List.Relation.Binary.Equality.Setoid.++⁺ʳ
d_'43''43''8314''691'_168 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48
d_'43''43''8314''691'_168 ~v0 ~v1 v2 v3 v4 v5
  = du_'43''43''8314''691'_168 v2 v3 v4 v5
du_'43''43''8314''691'_168 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48
du_'43''43''8314''691'_168 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Data.List.Relation.Binary.Pointwise.du_'43''43''8314''691'_372
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_refl_36
         (coe
            MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62 (coe v0)))
      (coe v3) (coe v1) (coe v2)
-- Data.List.Relation.Binary.Equality.Setoid.++-cancelˡ
d_'43''43''45'cancel'737'_178 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48
d_'43''43''45'cancel'737'_178 ~v0 ~v1 ~v2 v3 ~v4 ~v5
  = du_'43''43''45'cancel'737'_178 v3
du_'43''43''45'cancel'737'_178 ::
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48
du_'43''43''45'cancel'737'_178 v0
  = coe
      MAlonzo.Code.Data.List.Relation.Binary.Pointwise.du_'43''43''45'cancel'737'_308
      (coe v0)
-- Data.List.Relation.Binary.Equality.Setoid.++-cancelʳ
d_'43''43''45'cancel'691'_188 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48
d_'43''43''45'cancel'691'_188 ~v0 ~v1 ~v2 ~v3
  = du_'43''43''45'cancel'691'_188
du_'43''43''45'cancel'691'_188 ::
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48
du_'43''43''45'cancel'691'_188
  = coe
      MAlonzo.Code.Data.List.Relation.Binary.Pointwise.du_'43''43''45'cancel'691'_322
-- Data.List.Relation.Binary.Equality.Setoid.concat⁺
d_concat'8314'_190 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  [[AgdaAny]] ->
  [[AgdaAny]] ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48
d_concat'8314'_190 ~v0 ~v1 ~v2 v3 v4 = du_concat'8314'_190 v3 v4
du_concat'8314'_190 ::
  [[AgdaAny]] ->
  [[AgdaAny]] ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48
du_concat'8314'_190 v0 v1
  = coe
      MAlonzo.Code.Data.List.Relation.Binary.Pointwise.du_concat'8314'_382
      (coe v0) (coe v1)
-- Data.List.Relation.Binary.Equality.Setoid._.tabulate⁺
d_tabulate'8314'_204 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> AgdaAny) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> AgdaAny) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> AgdaAny) ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48
d_tabulate'8314'_204 ~v0 ~v1 ~v2 v3 ~v4 ~v5
  = du_tabulate'8314'_204 v3
du_tabulate'8314'_204 ::
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> AgdaAny) ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48
du_tabulate'8314'_204 v0
  = coe
      MAlonzo.Code.Data.List.Relation.Binary.Pointwise.du_tabulate'8314'_264
      (coe v0)
-- Data.List.Relation.Binary.Equality.Setoid._.tabulate⁻
d_tabulate'8315'_208 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> AgdaAny) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> AgdaAny) ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> AgdaAny
d_tabulate'8315'_208 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_tabulate'8315'_208
du_tabulate'8315'_208 ::
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> AgdaAny
du_tabulate'8315'_208
  = coe
      MAlonzo.Code.Data.List.Relation.Binary.Pointwise.du_tabulate'8315'_280
-- Data.List.Relation.Binary.Equality.Setoid._.filter⁺
d_filter'8314'_222 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  (AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48
d_filter'8314'_222 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 v7 v8 v9
  = du_filter'8314'_222 v5 v7 v8 v9
du_filter'8314'_222 ::
  (AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48
du_filter'8314'_222 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Data.List.Relation.Binary.Pointwise.du_filter'8314'_512
      (coe v0) (coe v0) (coe v1) (coe v2) (coe v3)
-- Data.List.Relation.Binary.Equality.Setoid.ʳ++⁺
d_'691''43''43''8314'_226 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48
d_'691''43''43''8314'_226 ~v0 ~v1 ~v2 v3 v4 ~v5 ~v6
  = du_'691''43''43''8314'_226 v3 v4
du_'691''43''43''8314'_226 ::
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48
du_'691''43''43''8314'_226 v0 v1
  = coe
      MAlonzo.Code.Data.List.Relation.Binary.Pointwise.du_'691''43''43''8314'_398
      (coe v0) (coe v1)
-- Data.List.Relation.Binary.Equality.Setoid.reverse⁺
d_reverse'8314'_228 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48
d_reverse'8314'_228 ~v0 ~v1 ~v2 v3 v4 = du_reverse'8314'_228 v3 v4
du_reverse'8314'_228 ::
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48
du_reverse'8314'_228 v0 v1
  = coe
      MAlonzo.Code.Data.List.Relation.Binary.Pointwise.du_reverse'8314'_404
      (coe v0) (coe v1)
