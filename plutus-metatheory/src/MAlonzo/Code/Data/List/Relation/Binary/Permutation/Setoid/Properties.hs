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

module MAlonzo.Code.Data.List.Relation.Binary.Permutation.Setoid.Properties where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Bool
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Algebra.Bundles
import qualified MAlonzo.Code.Algebra.Consequences.Base
import qualified MAlonzo.Code.Algebra.Structures
import qualified MAlonzo.Code.Data.Fin.Base
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Data.List.Relation.Binary.Equality.Setoid
import qualified MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous
import qualified MAlonzo.Code.Data.List.Relation.Binary.Permutation.Setoid
import qualified MAlonzo.Code.Data.List.Relation.Binary.Pointwise
import qualified MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base
import qualified MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Properties
import qualified MAlonzo.Code.Data.List.Relation.Unary.All
import qualified MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Core
import qualified MAlonzo.Code.Data.List.Relation.Unary.Any
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Data.Nat.Properties
import qualified MAlonzo.Code.Function.Base
import qualified MAlonzo.Code.Function.Bundles
import qualified MAlonzo.Code.Relation.Binary.Bundles
import qualified MAlonzo.Code.Relation.Binary.Properties.Setoid
import qualified MAlonzo.Code.Relation.Binary.Reasoning.Base.Single
import qualified MAlonzo.Code.Relation.Binary.Reasoning.Syntax
import qualified MAlonzo.Code.Relation.Binary.Structures
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core
import qualified MAlonzo.Code.Relation.Nullary.Negation.Core
import qualified MAlonzo.Code.Relation.Nullary.Reflects

-- Data.List.Relation.Binary.Permutation.Setoid.Properties._._↭_
d__'8621'__38 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  [AgdaAny] -> [AgdaAny] -> ()
d__'8621'__38 = erased
-- Data.List.Relation.Binary.Permutation.Setoid.Properties._.steps
d_steps_40 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.T_Permutation_32 ->
  Integer
d_steps_40 ~v0 ~v1 ~v2 = du_steps_40
du_steps_40 ::
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.T_Permutation_32 ->
  Integer
du_steps_40
  = coe
      MAlonzo.Code.Data.List.Relation.Binary.Permutation.Setoid.du_steps_58
-- Data.List.Relation.Binary.Permutation.Setoid.Properties._.Homogeneous.onIndices
d_onIndices_144 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.T_Permutation_32 ->
  MAlonzo.Code.Function.Bundles.T_Inverse_2068
d_onIndices_144 ~v0 ~v1 ~v2 = du_onIndices_144
du_onIndices_144 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.T_Permutation_32 ->
  MAlonzo.Code.Function.Bundles.T_Inverse_2068
du_onIndices_144 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.du_onIndices_166
      v4 v5 v6
-- Data.List.Relation.Binary.Permutation.Setoid.Properties._._∈_
d__'8712'__158 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  AgdaAny -> [AgdaAny] -> ()
d__'8712'__158 = erased
-- Data.List.Relation.Binary.Permutation.Setoid.Properties._.Permutation.Permutation
d_Permutation_171 a0 a1 a2 a3 a4 a5 a6 a7 a8 = ()
-- Data.List.Relation.Binary.Permutation.Setoid.Properties._.AllPairs
d_AllPairs_174 a0 a1 a2 a3 = ()
-- Data.List.Relation.Binary.Permutation.Setoid.Properties.≋._≋_
d__'8779'__184 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  [AgdaAny] -> [AgdaAny] -> ()
d__'8779'__184 = erased
-- Data.List.Relation.Binary.Permutation.Setoid.Properties.≋.++-cancelʳ
d_'43''43''45'cancel'691'_186 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48
d_'43''43''45'cancel'691'_186 ~v0 ~v1 ~v2
  = du_'43''43''45'cancel'691'_186
du_'43''43''45'cancel'691'_186 ::
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48
du_'43''43''45'cancel'691'_186 v0
  = coe
      MAlonzo.Code.Data.List.Relation.Binary.Equality.Setoid.du_'43''43''45'cancel'691'_188
-- Data.List.Relation.Binary.Permutation.Setoid.Properties.≋.++-cancelˡ
d_'43''43''45'cancel'737'_188 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48
d_'43''43''45'cancel'737'_188 ~v0 ~v1 ~v2
  = du_'43''43''45'cancel'737'_188
du_'43''43''45'cancel'737'_188 ::
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48
du_'43''43''45'cancel'737'_188 v0 v1 v2
  = coe
      MAlonzo.Code.Data.List.Relation.Binary.Equality.Setoid.du_'43''43''45'cancel'737'_178
      v0
-- Data.List.Relation.Binary.Permutation.Setoid.Properties.≋.++⁺
d_'43''43''8314'_190 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48
d_'43''43''8314'_190 ~v0 ~v1 ~v2 = du_'43''43''8314'_190
du_'43''43''8314'_190 ::
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48
du_'43''43''8314'_190 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Data.List.Relation.Binary.Equality.Setoid.du_'43''43''8314'_158
      v0 v1
-- Data.List.Relation.Binary.Permutation.Setoid.Properties.≋.++⁺ʳ
d_'43''43''8314''691'_192 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48
d_'43''43''8314''691'_192 ~v0 ~v1 v2
  = du_'43''43''8314''691'_192 v2
du_'43''43''8314''691'_192 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48
du_'43''43''8314''691'_192 v0
  = coe
      MAlonzo.Code.Data.List.Relation.Binary.Equality.Setoid.du_'43''43''8314''691'_168
      (coe v0)
-- Data.List.Relation.Binary.Permutation.Setoid.Properties.≋.++⁺ˡ
d_'43''43''8314''737'_194 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48
d_'43''43''8314''737'_194 ~v0 ~v1 v2
  = du_'43''43''8314''737'_194 v2
du_'43''43''8314''737'_194 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48
du_'43''43''8314''737'_194 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Data.List.Relation.Binary.Equality.Setoid.du_'43''43''8314''737'_162
      (coe v0) v3
-- Data.List.Relation.Binary.Permutation.Setoid.Properties.≋.Unique-resp-≋
d_Unique'45'resp'45''8779'_196 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Core.T_AllPairs_20 ->
  MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Core.T_AllPairs_20
d_Unique'45'resp'45''8779'_196 ~v0 ~v1 ~v2
  = du_Unique'45'resp'45''8779'_196
du_Unique'45'resp'45''8779'_196 ::
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Core.T_AllPairs_20 ->
  MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Core.T_AllPairs_20
du_Unique'45'resp'45''8779'_196
  = coe
      MAlonzo.Code.Data.List.Relation.Binary.Equality.Setoid.du_Unique'45'resp'45''8779'_92
-- Data.List.Relation.Binary.Permutation.Setoid.Properties.≋.concat⁺
d_concat'8314'_198 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  [[AgdaAny]] ->
  [[AgdaAny]] ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48
d_concat'8314'_198 ~v0 ~v1 ~v2 = du_concat'8314'_198
du_concat'8314'_198 ::
  [[AgdaAny]] ->
  [[AgdaAny]] ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48
du_concat'8314'_198
  = coe
      MAlonzo.Code.Data.List.Relation.Binary.Equality.Setoid.du_concat'8314'_190
-- Data.List.Relation.Binary.Permutation.Setoid.Properties.≋.filter⁺
d_filter'8314'_200 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  (AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48
d_filter'8314'_200 ~v0 ~v1 ~v2 = du_filter'8314'_200
du_filter'8314'_200 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  (AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48
du_filter'8314'_200 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Data.List.Relation.Binary.Equality.Setoid.du_filter'8314'_222
      v2 v4 v5 v6
-- Data.List.Relation.Binary.Permutation.Setoid.Properties.≋.foldr⁺
d_foldr'8314'_202 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
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
d_foldr'8314'_202 ~v0 ~v1 ~v2 = du_foldr'8314'_202
du_foldr'8314'_202 ::
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
du_foldr'8314'_202
  = coe
      MAlonzo.Code.Data.List.Relation.Binary.Equality.Setoid.du_foldr'8314'_150
-- Data.List.Relation.Binary.Permutation.Setoid.Properties.≋.map⁺
d_map'8314'_204 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48
d_map'8314'_204 ~v0 ~v1 ~v2 = du_map'8314'_204
du_map'8314'_204 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48
du_map'8314'_204 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Data.List.Relation.Binary.Equality.Setoid.du_map'8314'_122
      v4 v5 v6 v7
-- Data.List.Relation.Binary.Permutation.Setoid.Properties.≋.reverse⁺
d_reverse'8314'_206 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48
d_reverse'8314'_206 ~v0 ~v1 ~v2 = du_reverse'8314'_206
du_reverse'8314'_206 ::
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48
du_reverse'8314'_206
  = coe
      MAlonzo.Code.Data.List.Relation.Binary.Equality.Setoid.du_reverse'8314'_228
-- Data.List.Relation.Binary.Permutation.Setoid.Properties.≋.tabulate⁺
d_tabulate'8314'_208 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> AgdaAny) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> AgdaAny) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> AgdaAny) ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48
d_tabulate'8314'_208 ~v0 ~v1 ~v2 = du_tabulate'8314'_208
du_tabulate'8314'_208 ::
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> AgdaAny) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> AgdaAny) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> AgdaAny) ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48
du_tabulate'8314'_208 v0 v1 v2
  = coe
      MAlonzo.Code.Data.List.Relation.Binary.Equality.Setoid.du_tabulate'8314'_204
      v0
-- Data.List.Relation.Binary.Permutation.Setoid.Properties.≋.tabulate⁻
d_tabulate'8315'_210 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> AgdaAny) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> AgdaAny) ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> AgdaAny
d_tabulate'8315'_210 ~v0 ~v1 ~v2 = du_tabulate'8315'_210
du_tabulate'8315'_210 ::
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> AgdaAny) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> AgdaAny) ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> AgdaAny
du_tabulate'8315'_210 v0 v1 v2
  = coe
      MAlonzo.Code.Data.List.Relation.Binary.Equality.Setoid.du_tabulate'8315'_208
-- Data.List.Relation.Binary.Permutation.Setoid.Properties.≋.ʳ++⁺
d_'691''43''43''8314'_212 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48
d_'691''43''43''8314'_212 ~v0 ~v1 ~v2 = du_'691''43''43''8314'_212
du_'691''43''43''8314'_212 ::
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48
du_'691''43''43''8314'_212 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Data.List.Relation.Binary.Equality.Setoid.du_'691''43''43''8314'_226
      v0 v1
-- Data.List.Relation.Binary.Permutation.Setoid.Properties.≋.isEquivalence
d_isEquivalence_214 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_214 ~v0 ~v1 v2 = du_isEquivalence_214 v2
du_isEquivalence_214 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
du_isEquivalence_214 v0
  = coe
      MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
      (coe
         MAlonzo.Code.Data.List.Relation.Binary.Equality.Setoid.du_'8779''45'setoid_78
         (coe v0))
-- Data.List.Relation.Binary.Permutation.Setoid.Properties.≋.≋-length
d_'8779''45'length_216 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8779''45'length_216 = erased
-- Data.List.Relation.Binary.Permutation.Setoid.Properties.≋.refl
d_refl_218 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48
d_refl_218 ~v0 ~v1 v2 = du_refl_218 v2
du_refl_218 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48
du_refl_218 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.d_refl_34
      (coe
         MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
         (coe
            MAlonzo.Code.Data.List.Relation.Binary.Equality.Setoid.du_'8779''45'setoid_78
            (coe v0)))
-- Data.List.Relation.Binary.Permutation.Setoid.Properties.≋.reflexive
d_reflexive_220 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48
d_reflexive_220 ~v0 ~v1 v2 = du_reflexive_220 v2
du_reflexive_220 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48
du_reflexive_220 v0
  = let v1
          = coe
              MAlonzo.Code.Data.List.Relation.Binary.Equality.Setoid.du_'8779''45'setoid_78
              (coe v0) in
    coe
      (\ v2 v3 v4 ->
         coe
           MAlonzo.Code.Relation.Binary.Structures.du_reflexive_40
           (coe
              MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v1))
           v2)
-- Data.List.Relation.Binary.Permutation.Setoid.Properties.≋.≋-setoid
d_'8779''45'setoid_222 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
d_'8779''45'setoid_222 ~v0 ~v1 v2 = du_'8779''45'setoid_222 v2
du_'8779''45'setoid_222 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
du_'8779''45'setoid_222 v0
  = coe
      MAlonzo.Code.Data.List.Relation.Binary.Equality.Setoid.du_'8779''45'setoid_78
      (coe v0)
-- Data.List.Relation.Binary.Permutation.Setoid.Properties.≋.sym
d_sym_224 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48
d_sym_224 ~v0 ~v1 v2 = du_sym_224 v2
du_sym_224 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48
du_sym_224 v0
  = let v1
          = coe
              MAlonzo.Code.Data.List.Relation.Binary.Equality.Setoid.du_'8779''45'setoid_78
              (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_sym_36
         (coe
            MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v1)))
-- Data.List.Relation.Binary.Permutation.Setoid.Properties.≋.trans
d_trans_226 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48
d_trans_226 ~v0 ~v1 v2 = du_trans_226 v2
du_trans_226 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48
du_trans_226 v0
  = let v1
          = coe
              MAlonzo.Code.Data.List.Relation.Binary.Equality.Setoid.du_'8779''45'setoid_78
              (coe v0) in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_trans_38
         (coe
            MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v1)))
-- Data.List.Relation.Binary.Permutation.Setoid.Properties.≋.Pointwise.All-resp-Pointwise
d_All'45'resp'45'Pointwise_234 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
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
d_All'45'resp'45'Pointwise_234 ~v0 ~v1 ~v2
  = du_All'45'resp'45'Pointwise_234
du_All'45'resp'45'Pointwise_234 ::
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
du_All'45'resp'45'Pointwise_234 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = coe
      MAlonzo.Code.Data.List.Relation.Binary.Pointwise.du_All'45'resp'45'Pointwise_206
      v6 v7 v8 v9 v10
-- Data.List.Relation.Binary.Permutation.Setoid.Properties.≋.Pointwise.AllPairs-resp-Pointwise
d_AllPairs'45'resp'45'Pointwise_236 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
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
d_AllPairs'45'resp'45'Pointwise_236 ~v0 ~v1 ~v2
  = du_AllPairs'45'resp'45'Pointwise_236
du_AllPairs'45'resp'45'Pointwise_236 ::
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
du_AllPairs'45'resp'45'Pointwise_236 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
                                     v10
  = coe
      MAlonzo.Code.Data.List.Relation.Binary.Pointwise.du_AllPairs'45'resp'45'Pointwise_240
      v6 v7 v8 v9 v10
-- Data.List.Relation.Binary.Permutation.Setoid.Properties.≋.Pointwise.Any-resp-Pointwise
d_Any'45'resp'45'Pointwise_238 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
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
d_Any'45'resp'45'Pointwise_238 ~v0 ~v1 ~v2
  = du_Any'45'resp'45'Pointwise_238
du_Any'45'resp'45'Pointwise_238 ::
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
du_Any'45'resp'45'Pointwise_238 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10
  = coe
      MAlonzo.Code.Data.List.Relation.Binary.Pointwise.du_Any'45'resp'45'Pointwise_222
      v6 v7 v8 v9 v10
-- Data.List.Relation.Binary.Permutation.Setoid.Properties.All-resp-↭
d_All'45'resp'45''8621'_272 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.T_Permutation_32 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_All'45'resp'45''8621'_272 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6 v7 v8 v9
  = du_All'45'resp'45''8621'_272 v5 v6 v7 v8 v9
du_All'45'resp'45''8621'_272 ::
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.T_Permutation_32 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44 ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_All'45'resp'45''8621'_272 v0 v1 v2 v3 v4
  = case coe v3 of
      MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.C_refl_42 v7
        -> coe
             MAlonzo.Code.Data.List.Relation.Binary.Pointwise.du_All'45'resp'45'Pointwise_206
             (coe v0) (coe v1) (coe v2) (coe v7) (coe v4)
      MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.C_prep_54 v9 v10
        -> case coe v1 of
             (:) v11 v12
               -> case coe v2 of
                    (:) v13 v14
                      -> case coe v4 of
                           MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 v17 v18
                             -> coe
                                  MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                  (coe v0 v11 v13 v9 v17)
                                  (coe
                                     du_All'45'resp'45''8621'_272 (coe v0) (coe v12) (coe v14)
                                     (coe v10) (coe v18))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.C_swap_72 v11 v12 v13
        -> case coe v1 of
             (:) v14 v15
               -> case coe v15 of
                    (:) v16 v17
                      -> case coe v2 of
                           (:) v18 v19
                             -> case coe v19 of
                                  (:) v20 v21
                                    -> case coe v4 of
                                         MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 v24 v25
                                           -> case coe v25 of
                                                MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 v28 v29
                                                  -> coe
                                                       MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                       (coe v0 v16 v18 v12 v28)
                                                       (coe
                                                          MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                          (coe v0 v14 v20 v11 v24)
                                                          (coe
                                                             du_All'45'resp'45''8621'_272 (coe v0)
                                                             (coe v17) (coe v21) (coe v13)
                                                             (coe v29)))
                                                _ -> MAlonzo.RTE.mazUnreachableError
                                         _ -> MAlonzo.RTE.mazUnreachableError
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.C_trans_80 v6 v8 v9
        -> coe
             du_All'45'resp'45''8621'_272 (coe v0) (coe v6) (coe v2) (coe v9)
             (coe
                du_All'45'resp'45''8621'_272 (coe v0) (coe v1) (coe v6) (coe v8)
                (coe v4))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.List.Relation.Binary.Permutation.Setoid.Properties.Any-resp-↭
d_Any'45'resp'45''8621'_312 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.T_Permutation_32 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
d_Any'45'resp'45''8621'_312 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6 v7 v8 v9
  = du_Any'45'resp'45''8621'_312 v5 v6 v7 v8 v9
du_Any'45'resp'45''8621'_312 ::
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.T_Permutation_32 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
du_Any'45'resp'45''8621'_312 v0 v1 v2 v3 v4
  = case coe v3 of
      MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.C_refl_42 v7
        -> coe
             MAlonzo.Code.Data.List.Relation.Binary.Pointwise.du_Any'45'resp'45'Pointwise_222
             (coe v0) (coe v1) (coe v2) (coe v7) (coe v4)
      MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.C_prep_54 v9 v10
        -> case coe v1 of
             (:) v11 v12
               -> case coe v2 of
                    (:) v13 v14
                      -> case coe v4 of
                           MAlonzo.Code.Data.List.Relation.Unary.Any.C_here_46 v17
                             -> coe
                                  MAlonzo.Code.Data.List.Relation.Unary.Any.C_here_46
                                  (coe v0 v11 v13 v9 v17)
                           MAlonzo.Code.Data.List.Relation.Unary.Any.C_there_54 v17
                             -> coe
                                  MAlonzo.Code.Data.List.Relation.Unary.Any.C_there_54
                                  (coe
                                     du_Any'45'resp'45''8621'_312 (coe v0) (coe v12) (coe v14)
                                     (coe v10) (coe v17))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.C_swap_72 v11 v12 v13
        -> case coe v1 of
             (:) v14 v15
               -> case coe v15 of
                    (:) v16 v17
                      -> case coe v2 of
                           (:) v18 v19
                             -> case coe v19 of
                                  (:) v20 v21
                                    -> case coe v4 of
                                         MAlonzo.Code.Data.List.Relation.Unary.Any.C_here_46 v24
                                           -> coe
                                                MAlonzo.Code.Data.List.Relation.Unary.Any.C_there_54
                                                (coe
                                                   MAlonzo.Code.Data.List.Relation.Unary.Any.C_here_46
                                                   (coe v0 v14 v20 v11 v24))
                                         MAlonzo.Code.Data.List.Relation.Unary.Any.C_there_54 v24
                                           -> case coe v24 of
                                                MAlonzo.Code.Data.List.Relation.Unary.Any.C_here_46 v27
                                                  -> coe
                                                       MAlonzo.Code.Data.List.Relation.Unary.Any.C_here_46
                                                       (coe v0 v16 v18 v12 v27)
                                                MAlonzo.Code.Data.List.Relation.Unary.Any.C_there_54 v27
                                                  -> coe
                                                       MAlonzo.Code.Data.List.Relation.Unary.Any.C_there_54
                                                       (coe
                                                          MAlonzo.Code.Data.List.Relation.Unary.Any.C_there_54
                                                          (coe
                                                             du_Any'45'resp'45''8621'_312 (coe v0)
                                                             (coe v17) (coe v21) (coe v13)
                                                             (coe v27)))
                                                _ -> MAlonzo.RTE.mazUnreachableError
                                         _ -> MAlonzo.RTE.mazUnreachableError
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.C_trans_80 v6 v8 v9
        -> coe
             du_Any'45'resp'45''8621'_312 (coe v0) (coe v6) (coe v2) (coe v9)
             (coe
                du_Any'45'resp'45''8621'_312 (coe v0) (coe v1) (coe v6) (coe v8)
                (coe v4))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.List.Relation.Binary.Permutation.Setoid.Properties.AllPairs-resp-↭
d_AllPairs'45'resp'45''8621'_374 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.T_Permutation_32 ->
  MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Core.T_AllPairs_20 ->
  MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Core.T_AllPairs_20
d_AllPairs'45'resp'45''8621'_374 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6 v7 v8 v9
                                 v10
  = du_AllPairs'45'resp'45''8621'_374 v5 v6 v7 v8 v9 v10
du_AllPairs'45'resp'45''8621'_374 ::
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.T_Permutation_32 ->
  MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Core.T_AllPairs_20 ->
  MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Core.T_AllPairs_20
du_AllPairs'45'resp'45''8621'_374 v0 v1 v2 v3 v4 v5
  = case coe v4 of
      MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.C_refl_42 v8
        -> coe
             MAlonzo.Code.Data.List.Relation.Binary.Pointwise.du_AllPairs'45'resp'45'Pointwise_240
             (coe v1) (coe v2) (coe v3) (coe v8) (coe v5)
      MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.C_prep_54 v10 v11
        -> case coe v2 of
             (:) v12 v13
               -> case coe v3 of
                    (:) v14 v15
                      -> case coe v5 of
                           MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Core.C__'8759'__28 v18 v19
                             -> coe
                                  MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Core.C__'8759'__28
                                  (coe
                                     du_All'45'resp'45''8621'_272
                                     (coe MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 v1 v14) (coe v13)
                                     (coe v15) (coe v11)
                                     (coe
                                        MAlonzo.Code.Data.List.Relation.Unary.All.du_map_164
                                        (coe
                                           (\ v20 ->
                                              coe
                                                MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 v1 v20 v12
                                                v14 v10))
                                        (coe v13) (coe v18)))
                                  (coe
                                     du_AllPairs'45'resp'45''8621'_374 (coe v0) (coe v1) (coe v13)
                                     (coe v15) (coe v11) (coe v19))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.C_swap_72 v12 v13 v14
        -> case coe v2 of
             (:) v15 v16
               -> case coe v16 of
                    (:) v17 v18
                      -> case coe v3 of
                           (:) v19 v20
                             -> case coe v20 of
                                  (:) v21 v22
                                    -> case coe v1 of
                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v23 v24
                                           -> case coe v5 of
                                                MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Core.C__'8759'__28 v27 v28
                                                  -> case coe v27 of
                                                       MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 v31 v32
                                                         -> case coe v28 of
                                                              MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Core.C__'8759'__28 v35 v36
                                                                -> coe
                                                                     MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Core.C__'8759'__28
                                                                     (coe
                                                                        MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                                        (coe
                                                                           v0 v21 v19
                                                                           (coe
                                                                              v23 v21 v17 v19 v13
                                                                              (coe
                                                                                 v24 v17 v15 v21 v12
                                                                                 v31)))
                                                                        (coe
                                                                           du_All'45'resp'45''8621'_272
                                                                           (coe v23 v19) (coe v18)
                                                                           (coe v22) (coe v14)
                                                                           (coe
                                                                              MAlonzo.Code.Data.List.Relation.Unary.All.du_map_164
                                                                              (coe
                                                                                 (\ v37 ->
                                                                                    coe
                                                                                      v24 v37 v17
                                                                                      v19 v13))
                                                                              (coe v18) (coe v35))))
                                                                     (coe
                                                                        MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Core.C__'8759'__28
                                                                        (coe
                                                                           du_All'45'resp'45''8621'_272
                                                                           (coe v23 v21) (coe v18)
                                                                           (coe v22) (coe v14)
                                                                           (coe
                                                                              MAlonzo.Code.Data.List.Relation.Unary.All.du_map_164
                                                                              (coe
                                                                                 (\ v37 ->
                                                                                    coe
                                                                                      v24 v37 v15
                                                                                      v21 v12))
                                                                              (coe v18) (coe v32)))
                                                                        (coe
                                                                           du_AllPairs'45'resp'45''8621'_374
                                                                           (coe v0) (coe v1)
                                                                           (coe v18) (coe v22)
                                                                           (coe v14) (coe v36)))
                                                              _ -> MAlonzo.RTE.mazUnreachableError
                                                       _ -> MAlonzo.RTE.mazUnreachableError
                                                _ -> MAlonzo.RTE.mazUnreachableError
                                         _ -> MAlonzo.RTE.mazUnreachableError
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.C_trans_80 v7 v9 v10
        -> coe
             du_AllPairs'45'resp'45''8621'_374 (coe v0) (coe v1) (coe v7)
             (coe v3) (coe v10)
             (coe
                du_AllPairs'45'resp'45''8621'_374 (coe v0) (coe v1) (coe v2)
                (coe v7) (coe v9) (coe v5))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.List.Relation.Binary.Permutation.Setoid.Properties.∈-resp-↭
d_'8712''45'resp'45''8621'_430 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  AgdaAny ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.T_Permutation_32 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
d_'8712''45'resp'45''8621'_430 ~v0 ~v1 v2 v3 v4 v5
  = du_'8712''45'resp'45''8621'_430 v2 v3 v4 v5
du_'8712''45'resp'45''8621'_430 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  AgdaAny ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.T_Permutation_32 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
  MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34
du_'8712''45'resp'45''8621'_430 v0 v1 v2 v3
  = coe
      du_Any'45'resp'45''8621'_312
      (coe
         (\ v4 v5 v6 v7 ->
            coe
              MAlonzo.Code.Relation.Binary.Structures.d_trans_38
              (MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v0))
              v1 v4 v5 v7 v6))
      (coe v2) (coe v3)
-- Data.List.Relation.Binary.Permutation.Setoid.Properties.Unique-resp-↭
d_Unique'45'resp'45''8621'_432 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.T_Permutation_32 ->
  MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Core.T_AllPairs_20 ->
  MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Core.T_AllPairs_20
d_Unique'45'resp'45''8621'_432 ~v0 ~v1 v2 v3 v4
  = du_Unique'45'resp'45''8621'_432 v2 v3 v4
du_Unique'45'resp'45''8621'_432 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.T_Permutation_32 ->
  MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Core.T_AllPairs_20 ->
  MAlonzo.Code.Data.List.Relation.Unary.AllPairs.Core.T_AllPairs_20
du_Unique'45'resp'45''8621'_432 v0 v1 v2
  = coe
      du_AllPairs'45'resp'45''8621'_374
      (coe
         (\ v3 v4 v5 v6 ->
            coe
              v5
              (coe
                 MAlonzo.Code.Relation.Binary.Structures.d_sym_36
                 (MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v0))
                 v4 v3 v6)))
      (coe
         MAlonzo.Code.Relation.Binary.Properties.Setoid.du_'8777''45'resp'8322'_72)
      (coe v1) (coe v2)
-- Data.List.Relation.Binary.Permutation.Setoid.Properties.xs↭ys⇒|xs|≡|ys|
d_xs'8621'ys'8658''124'xs'124''8801''124'ys'124'_440 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.T_Permutation_32 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_xs'8621'ys'8658''124'xs'124''8801''124'ys'124'_440 = erased
-- Data.List.Relation.Binary.Permutation.Setoid.Properties.¬x∷xs↭[]
d_'172'x'8759'xs'8621''91''93'_462 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  AgdaAny ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.T_Permutation_32 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'172'x'8759'xs'8621''91''93'_462 = erased
-- Data.List.Relation.Binary.Permutation.Setoid.Properties.shift
d_shift_468 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.T_Permutation_32
d_shift_468 ~v0 ~v1 v2 v3 v4 v5 v6 v7
  = du_shift_468 v2 v3 v4 v5 v6 v7
du_shift_468 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.T_Permutation_32
du_shift_468 v0 v1 v2 v3 v4 v5
  = case coe v4 of
      []
        -> coe
             MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.C_prep_54
             v3
             (coe
                MAlonzo.Code.Data.List.Relation.Binary.Permutation.Setoid.du_'8621''45'refl_94
                (coe v0)
                (coe
                   MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v4) (coe v5)))
      (:) v6 v7
        -> coe
             MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
             (\ v8 v9 v10 ->
                coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_start_36 v10)
             (coe
                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v6)
                (coe
                   MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v7)
                   (coe
                      MAlonzo.Code.Data.List.Base.du__'43''43'__32
                      (coe MAlonzo.Code.Data.List.Base.du_'91'_'93'_270 (coe v1))
                      (coe v5))))
             (coe
                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v2)
                (coe
                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v6)
                   (coe
                      MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v7) (coe v5))))
             (coe
                MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8621''45''10217'_416
                (coe
                   MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                   (coe
                      (\ v8 v9 v10 ->
                         coe
                           MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.C_trans_80
                           (coe v9))))
                (coe
                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v6)
                   (coe
                      MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v7)
                      (coe
                         MAlonzo.Code.Data.List.Base.du__'43''43'__32
                         (coe MAlonzo.Code.Data.List.Base.du_'91'_'93'_270 (coe v1))
                         (coe v5))))
                (coe
                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v6)
                   (coe
                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v2)
                      (coe
                         MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v7) (coe v5))))
                (coe
                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v2)
                   (coe
                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v6)
                      (coe
                         MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v7) (coe v5))))
                (coe
                   MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8621''45''10217'_416
                   (coe
                      MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                      (coe
                         (\ v8 v9 v10 ->
                            coe
                              MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.C_trans_80
                              (coe v9))))
                   (coe
                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v6)
                      (coe
                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v2)
                         (coe
                            MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v7) (coe v5))))
                   (coe
                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v2)
                      (coe
                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v6)
                         (coe
                            MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v7) (coe v5))))
                   (coe
                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v2)
                      (coe
                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v6)
                         (coe
                            MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v7) (coe v5))))
                   (let v8
                          = coe
                              MAlonzo.Code.Data.List.Relation.Binary.Permutation.Setoid.du_'8621''45'setoid_178
                              (coe v0) in
                    coe
                      (let v9
                             = MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                                 (coe
                                    MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                                    (coe v8)) in
                       coe
                         (coe
                            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                            (coe
                               MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_stop_54
                               (coe v9))
                            (coe
                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v2)
                               (coe
                                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v6)
                                  (coe
                                     MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v7)
                                     (coe v5)))))))
                   (coe
                      MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.C_swap_72
                      (coe
                         MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                         (MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v0))
                         v6)
                      (coe
                         MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                         (MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v0))
                         v2)
                      (coe
                         MAlonzo.Code.Data.List.Relation.Binary.Permutation.Setoid.du_'8621''45'refl_94
                         (coe v0)
                         (coe
                            MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v7) (coe v5)))))
                (coe
                   MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.C_prep_54
                   (coe
                      MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                      (MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v0))
                      v6)
                   (coe
                      du_shift_468 (coe v0) (coe v1) (coe v2) (coe v3) (coe v7)
                      (coe v5))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.List.Relation.Binary.Permutation.Setoid.Properties.↭-split
d_'8621''45'split_504 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  [AgdaAny] ->
  AgdaAny ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.T_Permutation_32 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8621''45'split_504 ~v0 ~v1 v2 v3 v4 v5 v6 v7
  = du_'8621''45'split_504 v2 v3 v4 v5 v6 v7
du_'8621''45'split_504 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  [AgdaAny] ->
  AgdaAny ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.T_Permutation_32 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8621''45'split_504 v0 v1 v2 v3 v4 v5
  = coe
      du_helper_526 (coe v0) (coe v2) (coe v1)
      (coe
         MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v3)
         (coe
            MAlonzo.Code.Data.List.Base.du__'43''43'__32
            (coe MAlonzo.Code.Data.List.Base.du_'91'_'93'_270 (coe v2))
            (coe v4)))
      (coe v3) (coe v4) (coe v5)
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_refl_34
         (MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
            (coe
               MAlonzo.Code.Data.List.Relation.Binary.Equality.Setoid.du_'8779''45'setoid_78
               (coe v0)))
         (coe
            MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v3)
            (coe
               MAlonzo.Code.Data.List.Base.du__'43''43'__32
               (coe MAlonzo.Code.Data.List.Base.du_'91'_'93'_270 (coe v2))
               (coe v4))))
-- Data.List.Relation.Binary.Permutation.Setoid.Properties._.helper
d_helper_526 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  [AgdaAny] ->
  AgdaAny ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.T_Permutation_32 ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.T_Permutation_32 ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_helper_526 ~v0 ~v1 v2 ~v3 v4 ~v5 ~v6 ~v7 v8 v9 v10 v11 v12 v13
  = du_helper_526 v2 v4 v8 v9 v10 v11 v12 v13
du_helper_526 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  AgdaAny ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.T_Permutation_32 ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_helper_526 v0 v1 v2 v3 v4 v5 v6 v7
  = case coe v6 of
      MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.C_refl_42 v10
        -> case coe v4 of
             []
               -> case coe v10 of
                    MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.C__'8759'__62 v15 v16
                      -> case coe v2 of
                           (:) v17 v18
                             -> case coe v3 of
                                  (:) v19 v20
                                    -> case coe v7 of
                                         MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.C__'8759'__62 v25 v26
                                           -> coe
                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v4)
                                                (coe
                                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                   (coe v18)
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                      (coe
                                                         MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.C__'8759'__62
                                                         (coe
                                                            MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                                                            (MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                                                               (coe v0))
                                                            v17 v19 v1 v15 v25)
                                                         (coe
                                                            MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                                                            (MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                                                               (coe
                                                                  MAlonzo.Code.Data.List.Relation.Binary.Equality.Setoid.du_'8779''45'setoid_78
                                                                  (coe v0)))
                                                            v18))
                                                      (coe
                                                         MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.C_refl_42
                                                         (let v27
                                                                = coe
                                                                    MAlonzo.Code.Data.List.Relation.Binary.Equality.Setoid.du_'8779''45'setoid_78
                                                                    (coe v0) in
                                                          coe
                                                            (coe
                                                               MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                                                               (MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                                                                  (coe v27))
                                                               v18 v20
                                                               (coe
                                                                  MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                                                  (coe v4) (coe v5))
                                                               v16 v26)))))
                                         _ -> MAlonzo.RTE.mazUnreachableError
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             (:) v11 v12
               -> case coe v10 of
                    MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.C__'8759'__62 v17 v18
                      -> case coe v2 of
                           (:) v19 v20
                             -> case coe v3 of
                                  (:) v21 v22
                                    -> case coe v7 of
                                         MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.C__'8759'__62 v27 v28
                                           -> coe
                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v4)
                                                (coe
                                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                   (coe v5)
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                      (coe
                                                         MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.C__'8759'__62
                                                         (coe
                                                            MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                                                            (MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                                                               (coe v0))
                                                            v19 v21 v11 v17 v27)
                                                         (let v29
                                                                = coe
                                                                    MAlonzo.Code.Data.List.Relation.Binary.Equality.Setoid.du_'8779''45'setoid_78
                                                                    (coe v0) in
                                                          coe
                                                            (coe
                                                               MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                                                               (MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                                                                  (coe v29))
                                                               v20 v22
                                                               (coe
                                                                  MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                                                  (coe v12)
                                                                  (coe
                                                                     MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                                                     (coe
                                                                        MAlonzo.Code.Data.List.Base.du_'91'_'93'_270
                                                                        (coe v1))
                                                                     (coe v5)))
                                                               v18 v28)))
                                                      (coe
                                                         MAlonzo.Code.Data.List.Relation.Binary.Permutation.Setoid.du_'8621''45'refl_94
                                                         (coe v0)
                                                         (coe
                                                            MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                                            (coe v4) (coe v5)))))
                                         _ -> MAlonzo.RTE.mazUnreachableError
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.C_prep_54 v12 v13
        -> case coe v2 of
             (:) v14 v15
               -> case coe v3 of
                    (:) v16 v17
                      -> case coe v4 of
                           []
                             -> case coe v7 of
                                  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.C__'8759'__62 v22 v23
                                    -> coe
                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v4)
                                         (coe
                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v15)
                                            (coe
                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                               (coe
                                                  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.C__'8759'__62
                                                  (coe
                                                     MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                                                     (MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                                                        (coe v0))
                                                     v14 v16 v1 v12 v22)
                                                  (coe
                                                     MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                                                     (MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                                                        (coe
                                                           MAlonzo.Code.Data.List.Relation.Binary.Equality.Setoid.du_'8779''45'setoid_78
                                                           (coe v0)))
                                                     v15))
                                               (coe
                                                  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Setoid.du_'8621''45'trans'691''45''8779'_130
                                                  (coe v0) (coe v15) (coe v17)
                                                  (coe
                                                     MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                                     (coe v4) (coe v5))
                                                  (coe v13) (coe v23))))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           (:) v18 v19
                             -> case coe v7 of
                                  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.C__'8759'__62 v24 v25
                                    -> let v26
                                             = coe
                                                 du_helper_526 (coe v0) (coe v1) (coe v15) (coe v17)
                                                 (coe v19) (coe v5) (coe v13) (coe v25) in
                                       coe
                                         (case coe v26 of
                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v27 v28
                                              -> case coe v28 of
                                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v29 v30
                                                     -> case coe v30 of
                                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v31 v32
                                                            -> coe
                                                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                 (coe
                                                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                    (coe v18) (coe v27))
                                                                 (coe
                                                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                    (coe v29)
                                                                    (coe
                                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                       (coe
                                                                          MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.C__'8759'__62
                                                                          (coe
                                                                             MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                                                                             (MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                                                                                (coe v0))
                                                                             v14 v16 v18 v12 v24)
                                                                          v31)
                                                                       (coe
                                                                          MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.C_prep_54
                                                                          (coe
                                                                             MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                                                                             (MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                                                                                (coe v0))
                                                                             v18)
                                                                          v32)))
                                                          _ -> MAlonzo.RTE.mazUnreachableError
                                                   _ -> MAlonzo.RTE.mazUnreachableError
                                            _ -> MAlonzo.RTE.mazUnreachableError)
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.C_swap_72 v14 v15 v16
        -> case coe v2 of
             (:) v17 v18
               -> case coe v18 of
                    (:) v19 v20
                      -> case coe v3 of
                           (:) v21 v22
                             -> case coe v22 of
                                  (:) v23 v24
                                    -> case coe v4 of
                                         []
                                           -> case coe v5 of
                                                (:) v25 v26
                                                  -> case coe v7 of
                                                       MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.C__'8759'__62 v31 v32
                                                         -> case coe v32 of
                                                              MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.C__'8759'__62 v37 v38
                                                                -> coe
                                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                     (coe
                                                                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                        (coe v25) (coe v4))
                                                                     (coe
                                                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                        (coe v20)
                                                                        (coe
                                                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                           (coe
                                                                              MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.C__'8759'__62
                                                                              (coe
                                                                                 MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                                                                                 (MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                                                                                    (coe v0))
                                                                                 v17 v23 v25 v14
                                                                                 v37)
                                                                              (coe
                                                                                 MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.C__'8759'__62
                                                                                 (coe
                                                                                    MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                                                                                    (MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                                                                                       (coe v0))
                                                                                    v19 v21 v1 v15
                                                                                    v31)
                                                                                 (coe
                                                                                    MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                                                                                    (MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                                                                                       (coe
                                                                                          MAlonzo.Code.Data.List.Relation.Binary.Equality.Setoid.du_'8779''45'setoid_78
                                                                                          (coe v0)))
                                                                                    v20)))
                                                                           (coe
                                                                              MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.C_prep_54
                                                                              (coe
                                                                                 MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                                                                                 (MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                                                                                    (coe v0))
                                                                                 v25)
                                                                              (coe
                                                                                 MAlonzo.Code.Data.List.Relation.Binary.Permutation.Setoid.du_'8621''45'trans'691''45''8779'_130
                                                                                 (coe v0) (coe v20)
                                                                                 (coe v24) (coe v26)
                                                                                 (coe v16)
                                                                                 (coe v38)))))
                                                              _ -> MAlonzo.RTE.mazUnreachableError
                                                       _ -> MAlonzo.RTE.mazUnreachableError
                                                _ -> MAlonzo.RTE.mazUnreachableError
                                         (:) v25 v26
                                           -> case coe v26 of
                                                []
                                                  -> case coe v7 of
                                                       MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.C__'8759'__62 v31 v32
                                                         -> case coe v32 of
                                                              MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.C__'8759'__62 v37 v38
                                                                -> coe
                                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                     (coe v26)
                                                                     (coe
                                                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                        (coe
                                                                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                           (coe v25) (coe v20))
                                                                        (coe
                                                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                           (coe
                                                                              MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.C__'8759'__62
                                                                              (coe
                                                                                 MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                                                                                 (MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                                                                                    (coe v0))
                                                                                 v17 v23 v1 v14 v37)
                                                                              (coe
                                                                                 MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.C__'8759'__62
                                                                                 (coe
                                                                                    MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                                                                                    (MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                                                                                       (coe v0))
                                                                                    v19 v21 v25 v15
                                                                                    v31)
                                                                                 (coe
                                                                                    MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                                                                                    (MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                                                                                       (coe
                                                                                          MAlonzo.Code.Data.List.Relation.Binary.Equality.Setoid.du_'8779''45'setoid_78
                                                                                          (coe v0)))
                                                                                    v20)))
                                                                           (coe
                                                                              MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.C_prep_54
                                                                              (coe
                                                                                 MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                                                                                 (MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                                                                                    (coe v0))
                                                                                 v25)
                                                                              (coe
                                                                                 MAlonzo.Code.Data.List.Relation.Binary.Permutation.Setoid.du_'8621''45'trans'691''45''8779'_130
                                                                                 (coe v0) (coe v20)
                                                                                 (coe v24)
                                                                                 (coe
                                                                                    MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                                                                    (coe v26)
                                                                                    (coe v5))
                                                                                 (coe v16)
                                                                                 (coe v38)))))
                                                              _ -> MAlonzo.RTE.mazUnreachableError
                                                       _ -> MAlonzo.RTE.mazUnreachableError
                                                (:) v27 v28
                                                  -> case coe v7 of
                                                       MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.C__'8759'__62 v33 v34
                                                         -> case coe v34 of
                                                              MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.C__'8759'__62 v39 v40
                                                                -> let v41
                                                                         = coe
                                                                             du_helper_526 (coe v0)
                                                                             (coe v1) (coe v20)
                                                                             (coe v24) (coe v28)
                                                                             (coe v5) (coe v16)
                                                                             (coe v40) in
                                                                   coe
                                                                     (case coe v41 of
                                                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v42 v43
                                                                          -> case coe v43 of
                                                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v44 v45
                                                                                 -> case coe v45 of
                                                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v46 v47
                                                                                        -> coe
                                                                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                             (coe
                                                                                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                                (coe
                                                                                                   v27)
                                                                                                (coe
                                                                                                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                                   (coe
                                                                                                      v25)
                                                                                                   (coe
                                                                                                      v42)))
                                                                                             (coe
                                                                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                (coe
                                                                                                   v44)
                                                                                                (coe
                                                                                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                   (coe
                                                                                                      MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.C__'8759'__62
                                                                                                      (coe
                                                                                                         MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                                                                                                         (MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                                                                                                            (coe
                                                                                                               v0))
                                                                                                         v17
                                                                                                         v23
                                                                                                         v27
                                                                                                         v14
                                                                                                         v39)
                                                                                                      (coe
                                                                                                         MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.C__'8759'__62
                                                                                                         (coe
                                                                                                            MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                                                                                                            (MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                                                                                                               (coe
                                                                                                                  v0))
                                                                                                            v19
                                                                                                            v21
                                                                                                            v25
                                                                                                            v15
                                                                                                            v33)
                                                                                                         v46))
                                                                                                   (coe
                                                                                                      MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.C_swap_72
                                                                                                      (coe
                                                                                                         MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                                                                                                         (MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                                                                                                            (coe
                                                                                                               v0))
                                                                                                         v27)
                                                                                                      (coe
                                                                                                         MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                                                                                                         (MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                                                                                                            (coe
                                                                                                               v0))
                                                                                                         v25)
                                                                                                      v47)))
                                                                                      _ -> MAlonzo.RTE.mazUnreachableError
                                                                               _ -> MAlonzo.RTE.mazUnreachableError
                                                                        _ -> MAlonzo.RTE.mazUnreachableError)
                                                              _ -> MAlonzo.RTE.mazUnreachableError
                                                       _ -> MAlonzo.RTE.mazUnreachableError
                                                _ -> MAlonzo.RTE.mazUnreachableError
                                         _ -> MAlonzo.RTE.mazUnreachableError
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.C_trans_80 v9 v11 v12
        -> let v13
                 = coe
                     du_helper_526 (coe v0) (coe v1) (coe v9) (coe v3) (coe v4) (coe v5)
                     (coe v12) (coe v7) in
           coe
             (case coe v13 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v14 v15
                  -> case coe v15 of
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v16 v17
                         -> case coe v17 of
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v18 v19
                                -> let v20
                                         = coe
                                             du_helper_526 (coe v0) (coe v1) (coe v2) (coe v9)
                                             (coe v14) (coe v16) (coe v11) (coe v18) in
                                   coe
                                     (case coe v20 of
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v21 v22
                                          -> case coe v22 of
                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v23 v24
                                                 -> case coe v24 of
                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v25 v26
                                                        -> coe
                                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                             (coe v21)
                                                             (coe
                                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                (coe v23)
                                                                (coe
                                                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                   (coe v25)
                                                                   (coe
                                                                      MAlonzo.Code.Data.List.Relation.Binary.Permutation.Setoid.du_'8621''45'trans'8242'_162
                                                                      (coe v0)
                                                                      (coe
                                                                         MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                                                         (coe v21) (coe v23))
                                                                      (coe
                                                                         MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                                                         (coe v14) (coe v16))
                                                                      (coe
                                                                         MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                                                         (coe v4) (coe v5))
                                                                      (coe v26) (coe v19))))
                                                      _ -> MAlonzo.RTE.mazUnreachableError
                                               _ -> MAlonzo.RTE.mazUnreachableError
                                        _ -> MAlonzo.RTE.mazUnreachableError)
                              _ -> MAlonzo.RTE.mazUnreachableError
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.List.Relation.Binary.Permutation.Setoid.Properties._._._↭_
d__'8621'__700 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  [AgdaAny] -> [AgdaAny] -> ()
d__'8621'__700 = erased
-- Data.List.Relation.Binary.Permutation.Setoid.Properties._.map⁺
d_map'8314'_704 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.T_Permutation_32 ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.T_Permutation_32
d_map'8314'_704 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 v8 v9 v10
  = du_map'8314'_704 v6 v7 v8 v9 v10
du_map'8314'_704 ::
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.T_Permutation_32 ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.T_Permutation_32
du_map'8314'_704 v0 v1 v2 v3 v4
  = case coe v4 of
      MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.C_refl_42 v7
        -> coe
             MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.C_refl_42
             (coe
                MAlonzo.Code.Data.List.Relation.Binary.Pointwise.du_map'8314'_414
                (coe v2) (coe v3)
                (coe
                   MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.du_map_120
                   (coe v1) (coe v2) (coe v3) (coe v7)))
      MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.C_prep_54 v9 v10
        -> case coe v2 of
             (:) v11 v12
               -> case coe v3 of
                    (:) v13 v14
                      -> coe
                           MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.C_prep_54
                           (coe v1 v11 v13 v9)
                           (coe
                              du_map'8314'_704 (coe v0) (coe v1) (coe v12) (coe v14) (coe v10))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.C_swap_72 v11 v12 v13
        -> case coe v2 of
             (:) v14 v15
               -> case coe v15 of
                    (:) v16 v17
                      -> case coe v3 of
                           (:) v18 v19
                             -> case coe v19 of
                                  (:) v20 v21
                                    -> coe
                                         MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.C_swap_72
                                         (coe v1 v14 v20 v11) (coe v1 v16 v18 v12)
                                         (coe
                                            du_map'8314'_704 (coe v0) (coe v1) (coe v17) (coe v21)
                                            (coe v13))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.C_trans_80 v6 v8 v9
        -> coe
             MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.C_trans_80
             (coe
                MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                (\ v10 v11 -> v11)
                (coe MAlonzo.Code.Data.List.Base.du_map_22 (coe v0)) v2 v6)
             (coe du_map'8314'_704 (coe v0) (coe v1) (coe v2) (coe v6) (coe v8))
             (coe du_map'8314'_704 (coe v0) (coe v1) (coe v6) (coe v3) (coe v9))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.List.Relation.Binary.Permutation.Setoid.Properties._.filter⁺
d_filter'8314'_744 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  (AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.T_Permutation_32 ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.T_Permutation_32
d_filter'8314'_744 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 v7 v8 v9
  = du_filter'8314'_744 v5 v7 v8 v9
du_filter'8314'_744 ::
  (AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.T_Permutation_32 ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.T_Permutation_32
du_filter'8314'_744 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.C_refl_42 v6
        -> coe
             MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.C_refl_42
             (coe
                MAlonzo.Code.Data.List.Relation.Binary.Equality.Setoid.du_filter'8314'_222
                (coe v0) (coe v1) (coe v2) (coe v6))
      MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.C_prep_54 v8 v9
        -> case coe v1 of
             (:) v10 v11
               -> case coe v2 of
                    (:) v12 v13
                      -> let v14 = coe v0 v10 in
                         coe
                           (let v15 = coe v0 v12 in
                            coe
                              (case coe v14 of
                                 MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v16 v17
                                   -> if coe v16
                                        then coe
                                               seq (coe v17)
                                               (case coe v15 of
                                                  MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v18 v19
                                                    -> if coe v18
                                                         then coe
                                                                seq (coe v19)
                                                                (coe
                                                                   MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.C_prep_54
                                                                   v8
                                                                   (coe
                                                                      du_filter'8314'_744 (coe v0)
                                                                      (coe v11) (coe v13) (coe v9)))
                                                         else coe
                                                                seq (coe v19)
                                                                (coe
                                                                   MAlonzo.Code.Relation.Nullary.Negation.Core.du_contradiction_44
                                                                   erased)
                                                  _ -> MAlonzo.RTE.mazUnreachableError)
                                        else coe
                                               seq (coe v17)
                                               (case coe v15 of
                                                  MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v18 v19
                                                    -> if coe v18
                                                         then coe
                                                                seq (coe v19)
                                                                (coe
                                                                   MAlonzo.Code.Relation.Nullary.Negation.Core.du_contradiction_44
                                                                   erased)
                                                         else coe
                                                                seq (coe v19)
                                                                (coe
                                                                   du_filter'8314'_744 (coe v0)
                                                                   (coe v11) (coe v13) (coe v9))
                                                  _ -> MAlonzo.RTE.mazUnreachableError)
                                 _ -> MAlonzo.RTE.mazUnreachableError))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.C_swap_72 v10 v11 v12
        -> case coe v1 of
             (:) v13 v14
               -> case coe v14 of
                    (:) v15 v16
                      -> case coe v2 of
                           (:) v17 v18
                             -> case coe v18 of
                                  (:) v19 v20
                                    -> let v21 = coe v0 v13 in
                                       coe
                                         (let v22 = coe v0 v17 in
                                          coe
                                            (case coe v21 of
                                               MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v23 v24
                                                 -> if coe v23
                                                      then coe
                                                             seq (coe v24)
                                                             (case coe v22 of
                                                                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v25 v26
                                                                  -> if coe v25
                                                                       then case coe v26 of
                                                                              MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v27
                                                                                -> let v28
                                                                                         = coe
                                                                                             v0
                                                                                             v19 in
                                                                                   coe
                                                                                     (let v29
                                                                                            = coe
                                                                                                v0
                                                                                                v15 in
                                                                                      coe
                                                                                        (let v30
                                                                                               = case coe
                                                                                                        v29 of
                                                                                                   MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v30 v31
                                                                                                     -> coe
                                                                                                          seq
                                                                                                          (coe
                                                                                                             v30)
                                                                                                          (coe
                                                                                                             seq
                                                                                                             (coe
                                                                                                                v31)
                                                                                                             (coe
                                                                                                                MAlonzo.Code.Relation.Nullary.Negation.Core.du_contradiction_44
                                                                                                                erased))
                                                                                                   _ -> MAlonzo.RTE.mazUnreachableError in
                                                                                         coe
                                                                                           (case coe
                                                                                                   v28 of
                                                                                              MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v31 v32
                                                                                                -> let v33
                                                                                                         = case coe
                                                                                                                  v29 of
                                                                                                             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v33 v34
                                                                                                               -> case coe
                                                                                                                         v33 of
                                                                                                                    MAlonzo.Code.Agda.Builtin.Bool.C_false_8
                                                                                                                      -> case coe
                                                                                                                                v34 of
                                                                                                                           MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26
                                                                                                                             -> coe
                                                                                                                                  MAlonzo.Code.Relation.Nullary.Negation.Core.du_contradiction_44
                                                                                                                                  erased
                                                                                                                           _ -> coe
                                                                                                                                  v30
                                                                                                                    _ -> coe
                                                                                                                           v30
                                                                                                             _ -> MAlonzo.RTE.mazUnreachableError in
                                                                                                   coe
                                                                                                     (if coe
                                                                                                           v31
                                                                                                        then case coe
                                                                                                                    v29 of
                                                                                                               MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v34 v35
                                                                                                                 -> if coe
                                                                                                                         v34
                                                                                                                      then case coe
                                                                                                                                  v32 of
                                                                                                                             MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v36
                                                                                                                               -> case coe
                                                                                                                                         v35 of
                                                                                                                                    MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v37
                                                                                                                                      -> coe
                                                                                                                                           MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.C_swap_72
                                                                                                                                           v10
                                                                                                                                           v11
                                                                                                                                           (coe
                                                                                                                                              du_filter'8314'_744
                                                                                                                                              (coe
                                                                                                                                                 v0)
                                                                                                                                              (coe
                                                                                                                                                 v16)
                                                                                                                                              (coe
                                                                                                                                                 v20)
                                                                                                                                              (coe
                                                                                                                                                 v12))
                                                                                                                                    _ -> coe
                                                                                                                                           v33
                                                                                                                             _ -> coe
                                                                                                                                    v33
                                                                                                                      else (case coe
                                                                                                                                   v35 of
                                                                                                                              MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26
                                                                                                                                -> coe
                                                                                                                                     MAlonzo.Code.Relation.Nullary.Negation.Core.du_contradiction_44
                                                                                                                                     erased
                                                                                                                              _ -> coe
                                                                                                                                     v33)
                                                                                                               _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                        else (let v34
                                                                                                                    = case coe
                                                                                                                             v29 of
                                                                                                                        MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v34 v35
                                                                                                                          -> case coe
                                                                                                                                    v34 of
                                                                                                                               MAlonzo.Code.Agda.Builtin.Bool.C_false_8
                                                                                                                                 -> case coe
                                                                                                                                           v35 of
                                                                                                                                      MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26
                                                                                                                                        -> coe
                                                                                                                                             MAlonzo.Code.Relation.Nullary.Negation.Core.du_contradiction_44
                                                                                                                                             erased
                                                                                                                                      _ -> coe
                                                                                                                                             v33
                                                                                                                               _ -> coe
                                                                                                                                      v33
                                                                                                                        _ -> MAlonzo.RTE.mazUnreachableError in
                                                                                                              coe
                                                                                                                (case coe
                                                                                                                        v32 of
                                                                                                                   MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26
                                                                                                                     -> coe
                                                                                                                          MAlonzo.Code.Relation.Nullary.Negation.Core.du_contradiction_44
                                                                                                                          erased
                                                                                                                   _ -> coe
                                                                                                                          v34)))
                                                                                              _ -> MAlonzo.RTE.mazUnreachableError)))
                                                                              _ -> MAlonzo.RTE.mazUnreachableError
                                                                       else (case coe v26 of
                                                                               MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26
                                                                                 -> let v28
                                                                                          = coe
                                                                                              v0
                                                                                              v19 in
                                                                                    coe
                                                                                      (let v29
                                                                                             = coe
                                                                                                 v0
                                                                                                 v15 in
                                                                                       coe
                                                                                         (let v30
                                                                                                = case coe
                                                                                                         v29 of
                                                                                                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v30 v31
                                                                                                      -> coe
                                                                                                           seq
                                                                                                           (coe
                                                                                                              v30)
                                                                                                           (coe
                                                                                                              seq
                                                                                                              (coe
                                                                                                                 v31)
                                                                                                              (coe
                                                                                                                 MAlonzo.Code.Relation.Nullary.Negation.Core.du_contradiction_44
                                                                                                                 erased))
                                                                                                    _ -> MAlonzo.RTE.mazUnreachableError in
                                                                                          coe
                                                                                            (case coe
                                                                                                    v28 of
                                                                                               MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v31 v32
                                                                                                 -> let v33
                                                                                                          = case coe
                                                                                                                   v29 of
                                                                                                              MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v33 v34
                                                                                                                -> case coe
                                                                                                                          v33 of
                                                                                                                     MAlonzo.Code.Agda.Builtin.Bool.C_true_10
                                                                                                                       -> case coe
                                                                                                                                 v34 of
                                                                                                                            MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v35
                                                                                                                              -> coe
                                                                                                                                   MAlonzo.Code.Relation.Nullary.Negation.Core.du_contradiction_44
                                                                                                                                   erased
                                                                                                                            _ -> coe
                                                                                                                                   v30
                                                                                                                     _ -> coe
                                                                                                                            v30
                                                                                                              _ -> MAlonzo.RTE.mazUnreachableError in
                                                                                                    coe
                                                                                                      (if coe
                                                                                                            v31
                                                                                                         then case coe
                                                                                                                     v29 of
                                                                                                                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v34 v35
                                                                                                                  -> if coe
                                                                                                                          v34
                                                                                                                       then case coe
                                                                                                                                   v35 of
                                                                                                                              MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v36
                                                                                                                                -> coe
                                                                                                                                     MAlonzo.Code.Relation.Nullary.Negation.Core.du_contradiction_44
                                                                                                                                     erased
                                                                                                                              _ -> coe
                                                                                                                                     v33
                                                                                                                       else (case coe
                                                                                                                                    v32 of
                                                                                                                               MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v36
                                                                                                                                 -> case coe
                                                                                                                                           v35 of
                                                                                                                                      MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26
                                                                                                                                        -> coe
                                                                                                                                             MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.C_prep_54
                                                                                                                                             v10
                                                                                                                                             (coe
                                                                                                                                                du_filter'8314'_744
                                                                                                                                                (coe
                                                                                                                                                   v0)
                                                                                                                                                (coe
                                                                                                                                                   v16)
                                                                                                                                                (coe
                                                                                                                                                   v20)
                                                                                                                                                (coe
                                                                                                                                                   v12))
                                                                                                                                      _ -> coe
                                                                                                                                             v33
                                                                                                                               _ -> coe
                                                                                                                                      v33)
                                                                                                                _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                         else (let v34
                                                                                                                     = case coe
                                                                                                                              v29 of
                                                                                                                         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v34 v35
                                                                                                                           -> case coe
                                                                                                                                     v34 of
                                                                                                                                MAlonzo.Code.Agda.Builtin.Bool.C_true_10
                                                                                                                                  -> case coe
                                                                                                                                            v35 of
                                                                                                                                       MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v36
                                                                                                                                         -> coe
                                                                                                                                              MAlonzo.Code.Relation.Nullary.Negation.Core.du_contradiction_44
                                                                                                                                              erased
                                                                                                                                       _ -> coe
                                                                                                                                              v33
                                                                                                                                _ -> coe
                                                                                                                                       v33
                                                                                                                         _ -> MAlonzo.RTE.mazUnreachableError in
                                                                                                               coe
                                                                                                                 (case coe
                                                                                                                         v32 of
                                                                                                                    MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26
                                                                                                                      -> coe
                                                                                                                           MAlonzo.Code.Relation.Nullary.Negation.Core.du_contradiction_44
                                                                                                                           erased
                                                                                                                    _ -> coe
                                                                                                                           v34)))
                                                                                               _ -> MAlonzo.RTE.mazUnreachableError)))
                                                                               _ -> MAlonzo.RTE.mazUnreachableError)
                                                                _ -> MAlonzo.RTE.mazUnreachableError)
                                                      else coe
                                                             seq (coe v24)
                                                             (case coe v22 of
                                                                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v25 v26
                                                                  -> if coe v25
                                                                       then case coe v26 of
                                                                              MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v27
                                                                                -> let v28
                                                                                         = coe
                                                                                             v0
                                                                                             v19 in
                                                                                   coe
                                                                                     (let v29
                                                                                            = coe
                                                                                                v0
                                                                                                v15 in
                                                                                      coe
                                                                                        (let v30
                                                                                               = case coe
                                                                                                        v28 of
                                                                                                   MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v30 v31
                                                                                                     -> coe
                                                                                                          seq
                                                                                                          (coe
                                                                                                             v30)
                                                                                                          (coe
                                                                                                             seq
                                                                                                             (coe
                                                                                                                v31)
                                                                                                             (coe
                                                                                                                MAlonzo.Code.Relation.Nullary.Negation.Core.du_contradiction_44
                                                                                                                erased))
                                                                                                   _ -> MAlonzo.RTE.mazUnreachableError in
                                                                                         coe
                                                                                           (case coe
                                                                                                   v29 of
                                                                                              MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v31 v32
                                                                                                -> let v33
                                                                                                         = case coe
                                                                                                                  v28 of
                                                                                                             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v33 v34
                                                                                                               -> case coe
                                                                                                                         v33 of
                                                                                                                    MAlonzo.Code.Agda.Builtin.Bool.C_true_10
                                                                                                                      -> case coe
                                                                                                                                v34 of
                                                                                                                           MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v35
                                                                                                                             -> coe
                                                                                                                                  MAlonzo.Code.Relation.Nullary.Negation.Core.du_contradiction_44
                                                                                                                                  erased
                                                                                                                           _ -> coe
                                                                                                                                  v30
                                                                                                                    _ -> coe
                                                                                                                           v30
                                                                                                             _ -> MAlonzo.RTE.mazUnreachableError in
                                                                                                   coe
                                                                                                     (if coe
                                                                                                           v31
                                                                                                        then case coe
                                                                                                                    v28 of
                                                                                                               MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v34 v35
                                                                                                                 -> if coe
                                                                                                                         v34
                                                                                                                      then case coe
                                                                                                                                  v35 of
                                                                                                                             MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v36
                                                                                                                               -> coe
                                                                                                                                    MAlonzo.Code.Relation.Nullary.Negation.Core.du_contradiction_44
                                                                                                                                    erased
                                                                                                                             _ -> coe
                                                                                                                                    v33
                                                                                                                      else (case coe
                                                                                                                                   v35 of
                                                                                                                              MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26
                                                                                                                                -> case coe
                                                                                                                                          v32 of
                                                                                                                                     MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v37
                                                                                                                                       -> coe
                                                                                                                                            MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.C_prep_54
                                                                                                                                            v11
                                                                                                                                            (coe
                                                                                                                                               du_filter'8314'_744
                                                                                                                                               (coe
                                                                                                                                                  v0)
                                                                                                                                               (coe
                                                                                                                                                  v16)
                                                                                                                                               (coe
                                                                                                                                                  v20)
                                                                                                                                               (coe
                                                                                                                                                  v12))
                                                                                                                                     _ -> coe
                                                                                                                                            v33
                                                                                                                              _ -> coe
                                                                                                                                     v33)
                                                                                                               _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                        else (let v34
                                                                                                                    = case coe
                                                                                                                             v28 of
                                                                                                                        MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v34 v35
                                                                                                                          -> case coe
                                                                                                                                    v34 of
                                                                                                                               MAlonzo.Code.Agda.Builtin.Bool.C_true_10
                                                                                                                                 -> case coe
                                                                                                                                           v35 of
                                                                                                                                      MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v36
                                                                                                                                        -> coe
                                                                                                                                             MAlonzo.Code.Relation.Nullary.Negation.Core.du_contradiction_44
                                                                                                                                             erased
                                                                                                                                      _ -> coe
                                                                                                                                             v33
                                                                                                                               _ -> coe
                                                                                                                                      v33
                                                                                                                        _ -> MAlonzo.RTE.mazUnreachableError in
                                                                                                              coe
                                                                                                                (case coe
                                                                                                                        v32 of
                                                                                                                   MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26
                                                                                                                     -> coe
                                                                                                                          MAlonzo.Code.Relation.Nullary.Negation.Core.du_contradiction_44
                                                                                                                          erased
                                                                                                                   _ -> coe
                                                                                                                          v34)))
                                                                                              _ -> MAlonzo.RTE.mazUnreachableError)))
                                                                              _ -> MAlonzo.RTE.mazUnreachableError
                                                                       else (case coe v26 of
                                                                               MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26
                                                                                 -> let v28
                                                                                          = coe
                                                                                              v0
                                                                                              v19 in
                                                                                    coe
                                                                                      (let v29
                                                                                             = coe
                                                                                                 v0
                                                                                                 v15 in
                                                                                       coe
                                                                                         (let v30
                                                                                                = case coe
                                                                                                         v28 of
                                                                                                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v30 v31
                                                                                                      -> coe
                                                                                                           seq
                                                                                                           (coe
                                                                                                              v30)
                                                                                                           (coe
                                                                                                              seq
                                                                                                              (coe
                                                                                                                 v31)
                                                                                                              (coe
                                                                                                                 MAlonzo.Code.Relation.Nullary.Negation.Core.du_contradiction_44
                                                                                                                 erased))
                                                                                                    _ -> MAlonzo.RTE.mazUnreachableError in
                                                                                          coe
                                                                                            (case coe
                                                                                                    v29 of
                                                                                               MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v31 v32
                                                                                                 -> let v33
                                                                                                          = case coe
                                                                                                                   v28 of
                                                                                                              MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v33 v34
                                                                                                                -> case coe
                                                                                                                          v33 of
                                                                                                                     MAlonzo.Code.Agda.Builtin.Bool.C_true_10
                                                                                                                       -> case coe
                                                                                                                                 v34 of
                                                                                                                            MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v35
                                                                                                                              -> coe
                                                                                                                                   MAlonzo.Code.Relation.Nullary.Negation.Core.du_contradiction_44
                                                                                                                                   erased
                                                                                                                            _ -> coe
                                                                                                                                   v30
                                                                                                                     _ -> coe
                                                                                                                            v30
                                                                                                              _ -> MAlonzo.RTE.mazUnreachableError in
                                                                                                    coe
                                                                                                      (if coe
                                                                                                            v31
                                                                                                         then let v34
                                                                                                                    = case coe
                                                                                                                             v28 of
                                                                                                                        MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v34 v35
                                                                                                                          -> case coe
                                                                                                                                    v34 of
                                                                                                                               MAlonzo.Code.Agda.Builtin.Bool.C_true_10
                                                                                                                                 -> case coe
                                                                                                                                           v35 of
                                                                                                                                      MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v36
                                                                                                                                        -> coe
                                                                                                                                             MAlonzo.Code.Relation.Nullary.Negation.Core.du_contradiction_44
                                                                                                                                             erased
                                                                                                                                      _ -> coe
                                                                                                                                             v33
                                                                                                                               _ -> coe
                                                                                                                                      v33
                                                                                                                        _ -> MAlonzo.RTE.mazUnreachableError in
                                                                                                              coe
                                                                                                                (case coe
                                                                                                                        v32 of
                                                                                                                   MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v35
                                                                                                                     -> coe
                                                                                                                          MAlonzo.Code.Relation.Nullary.Negation.Core.du_contradiction_44
                                                                                                                          erased
                                                                                                                   _ -> coe
                                                                                                                          v34)
                                                                                                         else (case coe
                                                                                                                      v28 of
                                                                                                                 MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v34 v35
                                                                                                                   -> if coe
                                                                                                                           v34
                                                                                                                        then case coe
                                                                                                                                    v35 of
                                                                                                                               MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v36
                                                                                                                                 -> coe
                                                                                                                                      MAlonzo.Code.Relation.Nullary.Negation.Core.du_contradiction_44
                                                                                                                                      erased
                                                                                                                               _ -> coe
                                                                                                                                      v33
                                                                                                                        else (case coe
                                                                                                                                     v35 of
                                                                                                                                MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26
                                                                                                                                  -> case coe
                                                                                                                                            v32 of
                                                                                                                                       MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26
                                                                                                                                         -> coe
                                                                                                                                              du_filter'8314'_744
                                                                                                                                              (coe
                                                                                                                                                 v0)
                                                                                                                                              (coe
                                                                                                                                                 v16)
                                                                                                                                              (coe
                                                                                                                                                 v20)
                                                                                                                                              (coe
                                                                                                                                                 v12)
                                                                                                                                       _ -> coe
                                                                                                                                              v33
                                                                                                                                _ -> coe
                                                                                                                                       v33)
                                                                                                                 _ -> MAlonzo.RTE.mazUnreachableError))
                                                                                               _ -> MAlonzo.RTE.mazUnreachableError)))
                                                                               _ -> MAlonzo.RTE.mazUnreachableError)
                                                                _ -> MAlonzo.RTE.mazUnreachableError)
                                               _ -> MAlonzo.RTE.mazUnreachableError))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.C_trans_80 v5 v7 v8
        -> coe
             MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.C_trans_80
             (coe MAlonzo.Code.Data.List.Base.du_filter_648 (coe v0) (coe v5))
             (coe du_filter'8314'_744 (coe v0) (coe v1) (coe v5) (coe v7))
             (coe du_filter'8314'_744 (coe v0) (coe v5) (coe v2) (coe v8))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.List.Relation.Binary.Permutation.Setoid.Properties.++⁺ʳ
d_'43''43''8314''691'_1232 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.T_Permutation_32 ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.T_Permutation_32
d_'43''43''8314''691'_1232 ~v0 ~v1 v2 v3 v4 v5 v6
  = du_'43''43''8314''691'_1232 v2 v3 v4 v5 v6
du_'43''43''8314''691'_1232 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.T_Permutation_32 ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.T_Permutation_32
du_'43''43''8314''691'_1232 v0 v1 v2 v3 v4
  = case coe v4 of
      MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.C_refl_42 v7
        -> coe
             MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.C_refl_42
             (coe
                MAlonzo.Code.Data.List.Relation.Binary.Pointwise.du_'43''43''8314'_296
                (coe v1) (coe v2) (coe v7)
                (coe
                   MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                   (MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                      (coe
                         MAlonzo.Code.Data.List.Relation.Binary.Equality.Setoid.du_'8779''45'setoid_78
                         (coe v0)))
                   v3))
      MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.C_prep_54 v9 v10
        -> case coe v1 of
             (:) v11 v12
               -> case coe v2 of
                    (:) v13 v14
                      -> coe
                           MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.C_prep_54
                           v9
                           (coe
                              du_'43''43''8314''691'_1232 (coe v0) (coe v12) (coe v14) (coe v3)
                              (coe v10))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.C_swap_72 v11 v12 v13
        -> case coe v1 of
             (:) v14 v15
               -> case coe v15 of
                    (:) v16 v17
                      -> case coe v2 of
                           (:) v18 v19
                             -> case coe v19 of
                                  (:) v20 v21
                                    -> coe
                                         MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.C_swap_72
                                         v11 v12
                                         (coe
                                            du_'43''43''8314''691'_1232 (coe v0) (coe v17) (coe v21)
                                            (coe v3) (coe v13))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.C_trans_80 v6 v8 v9
        -> coe
             MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.C_trans_80
             (coe
                MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v6) (coe v3))
             (coe
                du_'43''43''8314''691'_1232 (coe v0) (coe v1) (coe v6) (coe v3)
                (coe v8))
             (coe
                du_'43''43''8314''691'_1232 (coe v0) (coe v6) (coe v2) (coe v3)
                (coe v9))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.List.Relation.Binary.Permutation.Setoid.Properties.dropMiddleElement-≋
d_dropMiddleElement'45''8779'_1268 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  AgdaAny ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.T_Permutation_32
d_dropMiddleElement'45''8779'_1268 ~v0 ~v1 v2 v3 v4 v5 v6 v7 v8
  = du_dropMiddleElement'45''8779'_1268 v2 v3 v4 v5 v6 v7 v8
du_dropMiddleElement'45''8779'_1268 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  AgdaAny ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.T_Permutation_32
du_dropMiddleElement'45''8779'_1268 v0 v1 v2 v3 v4 v5 v6
  = case coe v2 of
      []
        -> case coe v3 of
             []
               -> case coe v6 of
                    MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.C__'8759'__62 v11 v12
                      -> coe
                           MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.C_refl_42
                           v12
                    _ -> MAlonzo.RTE.mazUnreachableError
             (:) v7 v8
               -> case coe v6 of
                    MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.C__'8759'__62 v13 v14
                      -> coe
                           MAlonzo.Code.Data.List.Relation.Binary.Permutation.Setoid.du_'8621''45'trans'737''45''8779'_98
                           (coe v0)
                           (coe
                              MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v2) (coe v4))
                           (coe
                              MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v8)
                              (coe
                                 MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                 (coe MAlonzo.Code.Data.List.Base.du_'91'_'93'_270 (coe v1))
                                 (coe v5)))
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v7)
                              (coe
                                 MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v8) (coe v5)))
                           (coe v14)
                           (coe
                              du_shift_468 (coe v0) (coe v1) (coe v7) (coe v13) (coe v8)
                              (coe v5))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      (:) v7 v8
        -> case coe v3 of
             []
               -> case coe v6 of
                    MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.C__'8759'__62 v13 v14
                      -> coe
                           MAlonzo.Code.Data.List.Relation.Binary.Permutation.Setoid.du_'8621''45'trans'691''45''8779'_130
                           (coe v0)
                           (coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v7)
                              (coe
                                 MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v8) (coe v4)))
                           (coe
                              MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v8)
                              (coe
                                 MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                 (coe MAlonzo.Code.Data.List.Base.du_'91'_'93'_270 (coe v1))
                                 (coe v4)))
                           (coe
                              MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v3) (coe v5))
                           (coe
                              MAlonzo.Code.Data.List.Relation.Binary.Permutation.Setoid.du_'8621''45'sym_96
                              v0
                              (coe
                                 MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v8)
                                 (coe
                                    MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                    (coe MAlonzo.Code.Data.List.Base.du_'91'_'93'_270 (coe v1))
                                    (coe v4)))
                              (coe
                                 MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v7)
                                 (coe
                                    MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v8) (coe v4)))
                              (coe
                                 du_shift_468 (coe v0) (coe v1) (coe v7)
                                 (coe
                                    MAlonzo.Code.Relation.Binary.Structures.d_sym_36
                                    (MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                                       (coe v0))
                                    v7 v1 v13)
                                 (coe v8) (coe v4)))
                           (coe v14)
                    _ -> MAlonzo.RTE.mazUnreachableError
             (:) v9 v10
               -> case coe v6 of
                    MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.C__'8759'__62 v15 v16
                      -> coe
                           MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.C_prep_54
                           v15
                           (coe
                              du_dropMiddleElement'45''8779'_1268 (coe v0) (coe v1) (coe v8)
                              (coe v10) (coe v4) (coe v5) (coe v16))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.List.Relation.Binary.Permutation.Setoid.Properties.≋.Pointwise.Pointwise
d_Pointwise_1281 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 = ()
-- Data.List.Relation.Binary.Permutation.Setoid.Properties.↭-shift
d_'8621''45'shift_1306 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  AgdaAny ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.T_Permutation_32
d_'8621''45'shift_1306 ~v0 ~v1 v2 v3
  = du_'8621''45'shift_1306 v2 v3
du_'8621''45'shift_1306 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  AgdaAny ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.T_Permutation_32
du_'8621''45'shift_1306 v0 v1
  = coe
      du_shift_468 (coe v0) (coe v1) (coe v1)
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_refl_34
         (MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v0))
         v1)
-- Data.List.Relation.Binary.Permutation.Setoid.Properties.++⁺ˡ
d_'43''43''8314''737'_1314 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.T_Permutation_32 ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.T_Permutation_32
d_'43''43''8314''737'_1314 ~v0 ~v1 v2 v3 ~v4 ~v5 v6
  = du_'43''43''8314''737'_1314 v2 v3 v6
du_'43''43''8314''737'_1314 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.T_Permutation_32 ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.T_Permutation_32
du_'43''43''8314''737'_1314 v0 v1 v2
  = case coe v1 of
      [] -> coe v2
      (:) v3 v4
        -> coe
             MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.C_prep_54
             (coe
                MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                (MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v0))
                v3)
             (coe du_'43''43''8314''737'_1314 (coe v0) (coe v4) (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.List.Relation.Binary.Permutation.Setoid.Properties.++⁺
d_'43''43''8314'_1324 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.T_Permutation_32 ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.T_Permutation_32 ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.T_Permutation_32
d_'43''43''8314'_1324 ~v0 ~v1 v2 v3 v4 v5 ~v6 v7 v8
  = du_'43''43''8314'_1324 v2 v3 v4 v5 v7 v8
du_'43''43''8314'_1324 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.T_Permutation_32 ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.T_Permutation_32 ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.T_Permutation_32
du_'43''43''8314'_1324 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.C_trans_80
      (coe
         MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v2) (coe v3))
      (coe
         du_'43''43''8314''691'_1232 (coe v0) (coe v1) (coe v2) (coe v3)
         (coe v4))
      (coe du_'43''43''8314''737'_1314 (coe v0) (coe v2) (coe v5))
-- Data.List.Relation.Binary.Permutation.Setoid.Properties.zoom
d_zoom_1338 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.T_Permutation_32 ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.T_Permutation_32
d_zoom_1338 ~v0 ~v1 v2 v3 v4 v5 v6 v7
  = du_zoom_1338 v2 v3 v4 v5 v6 v7
du_zoom_1338 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.T_Permutation_32 ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.T_Permutation_32
du_zoom_1338 v0 v1 v2 v3 v4 v5
  = coe
      du_'43''43''8314''737'_1314 (coe v0) (coe v1)
      (coe
         du_'43''43''8314''691'_1232 (coe v0) (coe v3) (coe v4) (coe v2)
         (coe v5))
-- Data.List.Relation.Binary.Permutation.Setoid.Properties.inject
d_inject_1354 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  AgdaAny ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.T_Permutation_32 ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.T_Permutation_32 ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.T_Permutation_32
d_inject_1354 ~v0 ~v1 v2 v3 v4 ~v5 v6 v7 v8 v9
  = du_inject_1354 v2 v3 v4 v6 v7 v8 v9
du_inject_1354 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  AgdaAny ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.T_Permutation_32 ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.T_Permutation_32 ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.T_Permutation_32
du_inject_1354 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.C_trans_80
      (coe
         MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v2)
         (coe
            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v1) (coe v4)))
      (coe
         du_'43''43''8314''737'_1314 (coe v0) (coe v2)
         (coe
            MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.C_prep_54
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_refl_34
               (MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v0))
               v1)
            v6))
      (coe
         du_'43''43''8314''691'_1232 (coe v0) (coe v2) (coe v3)
         (coe
            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v1) (coe v4))
         (coe v5))
-- Data.List.Relation.Binary.Permutation.Setoid.Properties.++-identityˡ
d_'43''43''45'identity'737'_1362 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.T_Permutation_32
d_'43''43''45'identity'737'_1362 ~v0 ~v1 v2 v3
  = du_'43''43''45'identity'737'_1362 v2 v3
du_'43''43''45'identity'737'_1362 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.T_Permutation_32
du_'43''43''45'identity'737'_1362 v0 v1
  = coe
      MAlonzo.Code.Data.List.Relation.Binary.Permutation.Setoid.du_'8621''45'refl_94
      (coe v0)
      (coe
         MAlonzo.Code.Data.List.Base.du__'43''43'__32
         (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16) (coe v1))
-- Data.List.Relation.Binary.Permutation.Setoid.Properties.++-identityʳ
d_'43''43''45'identity'691'_1366 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.T_Permutation_32
d_'43''43''45'identity'691'_1366 ~v0 ~v1 v2 v3
  = du_'43''43''45'identity'691'_1366 v2 v3
du_'43''43''45'identity'691'_1366 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.T_Permutation_32
du_'43''43''45'identity'691'_1366 v0 v1
  = coe
      MAlonzo.Code.Data.List.Relation.Binary.Permutation.Setoid.du_'8621''45'reflexive_92
      (coe v0)
      (coe
         MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v1)
         (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
-- Data.List.Relation.Binary.Permutation.Setoid.Properties.++-identity
d_'43''43''45'identity_1370 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'43''43''45'identity_1370 ~v0 ~v1 v2
  = du_'43''43''45'identity_1370 v2
du_'43''43''45'identity_1370 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'43''43''45'identity_1370 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe du_'43''43''45'identity'737'_1362 (coe v0))
      (coe du_'43''43''45'identity'691'_1366 (coe v0))
-- Data.List.Relation.Binary.Permutation.Setoid.Properties.++-assoc
d_'43''43''45'assoc_1372 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.T_Permutation_32
d_'43''43''45'assoc_1372 ~v0 ~v1 v2 v3 v4 v5
  = du_'43''43''45'assoc_1372 v2 v3 v4 v5
du_'43''43''45'assoc_1372 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.T_Permutation_32
du_'43''43''45'assoc_1372 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Data.List.Relation.Binary.Permutation.Setoid.du_'8621''45'reflexive_92
      (coe v0)
      (coe
         MAlonzo.Code.Data.List.Base.du__'43''43'__32
         (coe
            MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v1) (coe v2))
         (coe v3))
-- Data.List.Relation.Binary.Permutation.Setoid.Properties.++-comm
d_'43''43''45'comm_1380 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.T_Permutation_32
d_'43''43''45'comm_1380 ~v0 ~v1 v2 v3 v4
  = du_'43''43''45'comm_1380 v2 v3 v4
du_'43''43''45'comm_1380 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.T_Permutation_32
du_'43''43''45'comm_1380 v0 v1 v2
  = case coe v1 of
      []
        -> coe
             MAlonzo.Code.Data.List.Relation.Binary.Permutation.Setoid.du_'8621''45'sym_96
             v0
             (coe
                MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v2) (coe v1))
             v2 (coe du_'43''43''45'identity'691'_1366 (coe v0) (coe v2))
      (:) v3 v4
        -> coe
             MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
             (\ v5 v6 v7 ->
                coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_start_36 v7)
             (coe
                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v3)
                (coe
                   MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v4) (coe v2)))
             (coe
                MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v2) (coe v1))
             (coe
                MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8621''45''10217'_416
                (coe
                   MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                   (coe
                      (\ v5 v6 v7 ->
                         coe
                           MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.C_trans_80
                           (coe v6))))
                (coe
                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v3)
                   (coe
                      MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v4) (coe v2)))
                (coe
                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v3)
                   (coe
                      MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v2) (coe v4)))
                (coe
                   MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v2) (coe v1))
                (coe
                   MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8621''45''10216'_418
                   (coe
                      MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                      (coe
                         (\ v5 v6 v7 ->
                            coe
                              MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.C_trans_80
                              (coe v6))))
                   (coe
                      MAlonzo.Code.Data.List.Relation.Binary.Permutation.Setoid.du_'8621''45'sym_96
                      (coe v0))
                   (coe
                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v3)
                      (coe
                         MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v2) (coe v4)))
                   (coe
                      MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v2) (coe v1))
                   (coe
                      MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v2) (coe v1))
                   (let v5
                          = coe
                              MAlonzo.Code.Data.List.Relation.Binary.Permutation.Setoid.du_'8621''45'setoid_178
                              (coe v0) in
                    coe
                      (let v6
                             = MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                                 (coe
                                    MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                                    (coe v5)) in
                       coe
                         (coe
                            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                            (coe
                               MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_stop_54
                               (coe v6))
                            (coe
                               MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v2) (coe v1)))))
                   (coe du_'8621''45'shift_1306 v0 v3 v2 v4))
                (coe
                   MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.C_prep_54
                   (coe
                      MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                      (MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v0))
                      v3)
                   (coe du_'43''43''45'comm_1380 (coe v0) (coe v4) (coe v2))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.List.Relation.Binary.Permutation.Setoid.Properties.shifts
d_shifts_1400 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.T_Permutation_32
d_shifts_1400 ~v0 ~v1 v2 v3 v4 v5 = du_shifts_1400 v2 v3 v4 v5
du_shifts_1400 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.T_Permutation_32
du_shifts_1400 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
      (\ v4 v5 v6 ->
         coe
           MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_start_36 v6)
      (coe
         MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v1)
         (coe
            MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v2) (coe v3)))
      (coe
         MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v2)
         (coe
            MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v1) (coe v3)))
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8621''45''10216'_418
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
            (coe
               (\ v4 v5 v6 ->
                  coe
                    MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.C_trans_80
                    (coe v5))))
         (coe
            MAlonzo.Code.Data.List.Relation.Binary.Permutation.Setoid.du_'8621''45'sym_96
            (coe v0))
         (coe
            MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v1)
            (coe
               MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v2) (coe v3)))
         (coe
            MAlonzo.Code.Data.List.Base.du__'43''43'__32
            (coe
               MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v1) (coe v2))
            (coe v3))
         (coe
            MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v2)
            (coe
               MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v1) (coe v3)))
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8621''45''10217'_416
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
               (coe
                  (\ v4 v5 v6 ->
                     coe
                       MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.C_trans_80
                       (coe v5))))
            (coe
               MAlonzo.Code.Data.List.Base.du__'43''43'__32
               (coe
                  MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v1) (coe v2))
               (coe v3))
            (coe
               MAlonzo.Code.Data.List.Base.du__'43''43'__32
               (coe
                  MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v2) (coe v1))
               (coe v3))
            (coe
               MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v2)
               (coe
                  MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v1) (coe v3)))
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8621''45''10217'_416
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                  (coe
                     (\ v4 v5 v6 ->
                        coe
                          MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.C_trans_80
                          (coe v5))))
               (coe
                  MAlonzo.Code.Data.List.Base.du__'43''43'__32
                  (coe
                     MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v2) (coe v1))
                  (coe v3))
               (coe
                  MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v2)
                  (coe
                     MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v1) (coe v3)))
               (coe
                  MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v2)
                  (coe
                     MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v1) (coe v3)))
               (let v4
                      = coe
                          MAlonzo.Code.Data.List.Relation.Binary.Permutation.Setoid.du_'8621''45'setoid_178
                          (coe v0) in
                coe
                  (let v5
                         = MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                             (coe
                                MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                                (coe v4)) in
                   coe
                     (coe
                        MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                        (coe
                           MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_stop_54
                           (coe v5))
                        (coe
                           MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v2)
                           (coe
                              MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v1) (coe v3))))))
               (coe
                  du_'43''43''45'assoc_1372 (coe v0) (coe v2) (coe v1) (coe v3)))
            (coe
               du_'43''43''8314''691'_1232 (coe v0)
               (coe
                  MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v1) (coe v2))
               (coe
                  MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v2) (coe v1))
               (coe v3)
               (coe du_'43''43''45'comm_1380 (coe v0) (coe v1) (coe v2))))
         (coe
            du_'43''43''45'assoc_1372 (coe v0) (coe v1) (coe v2) (coe v3)))
-- Data.List.Relation.Binary.Permutation.Setoid.Properties.++-isMagma
d_'43''43''45'isMagma_1412 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176
d_'43''43''45'isMagma_1412 ~v0 ~v1 v2
  = du_'43''43''45'isMagma_1412 v2
du_'43''43''45'isMagma_1412 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176
du_'43''43''45'isMagma_1412 v0
  = coe
      MAlonzo.Code.Algebra.Structures.C_IsMagma'46'constructor_1867
      (coe
         MAlonzo.Code.Data.List.Relation.Binary.Permutation.Setoid.du_'8621''45'isEquivalence_176
         (coe v0))
      (\ v1 v2 v3 v4 v5 v6 ->
         coe du_'43''43''8314'_1324 (coe v0) v1 v2 v3 v5 v6)
-- Data.List.Relation.Binary.Permutation.Setoid.Properties.++-isSemigroup
d_'43''43''45'isSemigroup_1414 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_470
d_'43''43''45'isSemigroup_1414 ~v0 ~v1 v2
  = du_'43''43''45'isSemigroup_1414 v2
du_'43''43''45'isSemigroup_1414 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_470
du_'43''43''45'isSemigroup_1414 v0
  = coe
      MAlonzo.Code.Algebra.Structures.C_IsSemigroup'46'constructor_9889
      (coe du_'43''43''45'isMagma_1412 (coe v0))
      (coe du_'43''43''45'assoc_1372 (coe v0))
-- Data.List.Relation.Binary.Permutation.Setoid.Properties.++-isMonoid
d_'43''43''45'isMonoid_1416 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_684
d_'43''43''45'isMonoid_1416 ~v0 ~v1 v2
  = du_'43''43''45'isMonoid_1416 v2
du_'43''43''45'isMonoid_1416 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_684
du_'43''43''45'isMonoid_1416 v0
  = coe
      MAlonzo.Code.Algebra.Structures.C_IsMonoid'46'constructor_15345
      (coe du_'43''43''45'isSemigroup_1414 (coe v0))
      (coe du_'43''43''45'identity_1370 (coe v0))
-- Data.List.Relation.Binary.Permutation.Setoid.Properties.++-isCommutativeMonoid
d_'43''43''45'isCommutativeMonoid_1418 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_734
d_'43''43''45'isCommutativeMonoid_1418 ~v0 ~v1 v2
  = du_'43''43''45'isCommutativeMonoid_1418 v2
du_'43''43''45'isCommutativeMonoid_1418 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_734
du_'43''43''45'isCommutativeMonoid_1418 v0
  = coe
      MAlonzo.Code.Algebra.Structures.C_IsCommutativeMonoid'46'constructor_17167
      (coe du_'43''43''45'isMonoid_1416 (coe v0))
      (coe du_'43''43''45'comm_1380 (coe v0))
-- Data.List.Relation.Binary.Permutation.Setoid.Properties.++-magma
d_'43''43''45'magma_1420 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Algebra.Bundles.T_Magma_72
d_'43''43''45'magma_1420 ~v0 ~v1 v2 = du_'43''43''45'magma_1420 v2
du_'43''43''45'magma_1420 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Algebra.Bundles.T_Magma_72
du_'43''43''45'magma_1420 v0
  = coe
      MAlonzo.Code.Algebra.Bundles.C_Magma'46'constructor_1323
      (coe MAlonzo.Code.Data.List.Base.du__'43''43'__32)
      (coe du_'43''43''45'isMagma_1412 (coe v0))
-- Data.List.Relation.Binary.Permutation.Setoid.Properties.++-semigroup
d_'43''43''45'semigroup_1422 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Algebra.Bundles.T_Semigroup_540
d_'43''43''45'semigroup_1422 ~v0 ~v1 v2
  = du_'43''43''45'semigroup_1422 v2
du_'43''43''45'semigroup_1422 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Algebra.Bundles.T_Semigroup_540
du_'43''43''45'semigroup_1422 v0
  = coe
      MAlonzo.Code.Algebra.Bundles.C_Semigroup'46'constructor_9837
      (coe MAlonzo.Code.Data.List.Base.du__'43''43'__32)
      (coe du_'43''43''45'isSemigroup_1414 (coe v0))
-- Data.List.Relation.Binary.Permutation.Setoid.Properties.++-monoid
d_'43''43''45'monoid_1424 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Algebra.Bundles.T_Monoid_886
d_'43''43''45'monoid_1424 ~v0 ~v1 v2
  = du_'43''43''45'monoid_1424 v2
du_'43''43''45'monoid_1424 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Algebra.Bundles.T_Monoid_886
du_'43''43''45'monoid_1424 v0
  = coe
      MAlonzo.Code.Algebra.Bundles.C_Monoid'46'constructor_16201
      (coe MAlonzo.Code.Data.List.Base.du__'43''43'__32)
      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      (coe du_'43''43''45'isMonoid_1416 (coe v0))
-- Data.List.Relation.Binary.Permutation.Setoid.Properties.++-commutativeMonoid
d_'43''43''45'commutativeMonoid_1426 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Algebra.Bundles.T_CommutativeMonoid_966
d_'43''43''45'commutativeMonoid_1426 ~v0 ~v1 v2
  = du_'43''43''45'commutativeMonoid_1426 v2
du_'43''43''45'commutativeMonoid_1426 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Algebra.Bundles.T_CommutativeMonoid_966
du_'43''43''45'commutativeMonoid_1426 v0
  = coe
      MAlonzo.Code.Algebra.Bundles.C_CommutativeMonoid'46'constructor_17975
      (coe MAlonzo.Code.Data.List.Base.du__'43''43'__32)
      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      (coe du_'43''43''45'isCommutativeMonoid_1418 (coe v0))
-- Data.List.Relation.Binary.Permutation.Setoid.Properties.dropMiddleElement
d_dropMiddleElement_1438 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  AgdaAny ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.T_Permutation_32 ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.T_Permutation_32
d_dropMiddleElement_1438 ~v0 ~v1 v2 v3 v4 v5 v6 v7 v8
  = du_dropMiddleElement_1438 v2 v3 v4 v5 v6 v7 v8
du_dropMiddleElement_1438 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  AgdaAny ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.T_Permutation_32 ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.T_Permutation_32
du_dropMiddleElement_1438 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.C_trans_80
      (coe
         MAlonzo.Code.Data.List.Base.du__'43''43'__32
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
            (coe
               du_'8621''45'split_504 (coe v0)
               (coe
                  MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v2)
                  (coe
                     MAlonzo.Code.Data.List.Base.du__'43''43'__32
                     (coe MAlonzo.Code.Data.List.Base.du_'91'_'93'_270 (coe v1))
                     (coe v4)))
               (coe v1) (coe v3) (coe v5) (coe v6)))
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
            (coe
               MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
               (coe
                  du_helper_526 (coe v0) (coe v1)
                  (coe
                     MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v2)
                     (coe
                        MAlonzo.Code.Data.List.Base.du__'43''43'__32
                        (coe MAlonzo.Code.Data.List.Base.du_'91'_'93'_270 (coe v1))
                        (coe v4)))
                  (coe
                     MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v3)
                     (coe
                        MAlonzo.Code.Data.List.Base.du__'43''43'__32
                        (coe MAlonzo.Code.Data.List.Base.du_'91'_'93'_270 (coe v1))
                        (coe v5)))
                  (coe v3) (coe v5) (coe v6)
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                     (MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                        (coe
                           MAlonzo.Code.Data.List.Relation.Binary.Equality.Setoid.du_'8779''45'setoid_78
                           (coe v0)))
                     (coe
                        MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v3)
                        (coe
                           MAlonzo.Code.Data.List.Base.du__'43''43'__32
                           (coe MAlonzo.Code.Data.List.Base.du_'91'_'93'_270 (coe v1))
                           (coe v5))))))))
      (coe
         du_dropMiddleElement'45''8779'_1268 (coe v0) (coe v1) (coe v2)
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
            (coe
               du_'8621''45'split_504 (coe v0)
               (coe
                  MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v2)
                  (coe
                     MAlonzo.Code.Data.List.Base.du__'43''43'__32
                     (coe MAlonzo.Code.Data.List.Base.du_'91'_'93'_270 (coe v1))
                     (coe v4)))
               (coe v1) (coe v3) (coe v5) (coe v6)))
         (coe v4)
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
            (coe
               MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
               (coe
                  du_helper_526 (coe v0) (coe v1)
                  (coe
                     MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v2)
                     (coe
                        MAlonzo.Code.Data.List.Base.du__'43''43'__32
                        (coe MAlonzo.Code.Data.List.Base.du_'91'_'93'_270 (coe v1))
                        (coe v4)))
                  (coe
                     MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v3)
                     (coe
                        MAlonzo.Code.Data.List.Base.du__'43''43'__32
                        (coe MAlonzo.Code.Data.List.Base.du_'91'_'93'_270 (coe v1))
                        (coe v5)))
                  (coe v3) (coe v5) (coe v6)
                  (coe
                     MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                     (MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                        (coe
                           MAlonzo.Code.Data.List.Relation.Binary.Equality.Setoid.du_'8779''45'setoid_78
                           (coe v0)))
                     (coe
                        MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v3)
                        (coe
                           MAlonzo.Code.Data.List.Base.du__'43''43'__32
                           (coe MAlonzo.Code.Data.List.Base.du_'91'_'93'_270 (coe v1))
                           (coe v5)))))))
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
            (coe
               MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
               (coe
                  MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                  (coe
                     du_'8621''45'split_504 (coe v0)
                     (coe
                        MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v2)
                        (coe
                           MAlonzo.Code.Data.List.Base.du__'43''43'__32
                           (coe MAlonzo.Code.Data.List.Base.du_'91'_'93'_270 (coe v1))
                           (coe v4)))
                     (coe v1) (coe v3) (coe v5) (coe v6))))))
      (MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
            (coe
               MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
               (coe
                  du_'8621''45'split_504 (coe v0)
                  (coe
                     MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v2)
                     (coe
                        MAlonzo.Code.Data.List.Base.du__'43''43'__32
                        (coe MAlonzo.Code.Data.List.Base.du_'91'_'93'_270 (coe v1))
                        (coe v4)))
                  (coe v1) (coe v3) (coe v5) (coe v6)))))
-- Data.List.Relation.Binary.Permutation.Setoid.Properties.dropMiddle
d_dropMiddle_1470 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.T_Permutation_32 ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.T_Permutation_32
d_dropMiddle_1470 ~v0 ~v1 v2 v3 v4 v5 v6 v7 v8
  = du_dropMiddle_1470 v2 v3 v4 v5 v6 v7 v8
du_dropMiddle_1470 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.T_Permutation_32 ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.T_Permutation_32
du_dropMiddle_1470 v0 v1 v2 v3 v4 v5 v6
  = case coe v1 of
      [] -> coe v6
      (:) v7 v8
        -> coe
             du_dropMiddle_1470 (coe v0) (coe v8) (coe v2) (coe v3) (coe v4)
             (coe v5)
             (coe
                du_dropMiddleElement_1438 (coe v0) (coe v7) (coe v2) (coe v3)
                (coe
                   MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v8) (coe v4))
                (coe
                   MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v8) (coe v5))
                (coe v6))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.List.Relation.Binary.Permutation.Setoid.Properties.drop-∷
d_drop'45''8759'_1488 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  AgdaAny ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.T_Permutation_32 ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.T_Permutation_32
d_drop'45''8759'_1488 ~v0 ~v1 v2 v3 v4 v5
  = du_drop'45''8759'_1488 v2 v3 v4 v5
du_drop'45''8759'_1488 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  AgdaAny ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.T_Permutation_32 ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.T_Permutation_32
du_drop'45''8759'_1488 v0 v1 v2 v3
  = coe
      du_dropMiddleElement_1438 (coe v0) (coe v1)
      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16) (coe v2)
      (coe v3)
-- Data.List.Relation.Binary.Permutation.Setoid.Properties.∷↭∷ʳ
d_'8759''8621''8759''691'_1494 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  AgdaAny ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.T_Permutation_32
d_'8759''8621''8759''691'_1494 ~v0 ~v1 v2 v3 v4
  = du_'8759''8621''8759''691'_1494 v2 v3 v4
du_'8759''8621''8759''691'_1494 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  AgdaAny ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.T_Permutation_32
du_'8759''8621''8759''691'_1494 v0 v1 v2
  = coe
      MAlonzo.Code.Data.List.Relation.Binary.Permutation.Setoid.du_'8621''45'sym_96
      v0
      (coe
         MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v2)
         (coe MAlonzo.Code.Data.List.Base.du_'91'_'93'_270 (coe v1)))
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v1) (coe v2))
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
         (\ v3 v4 v5 ->
            coe
              MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_start_36 v5)
         (coe
            MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v2)
            (coe MAlonzo.Code.Data.List.Base.du_'91'_'93'_270 (coe v1)))
         (coe
            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v1) (coe v2))
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8621''45''10217'_416
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
               (coe
                  (\ v3 v4 v5 ->
                     coe
                       MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.C_trans_80
                       (coe v4))))
            (coe
               MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v2)
               (coe MAlonzo.Code.Data.List.Base.du_'91'_'93'_270 (coe v1)))
            (coe
               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v1)
               (coe
                  MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v2)
                  (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
            (coe
               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v1) (coe v2))
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_436
               (\ v3 v4 v5 v6 v7 -> v7)
               (coe
                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v1)
                  (coe
                     MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v2)
                     (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)))
               (coe
                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v1) (coe v2))
               (coe
                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v1) (coe v2))
               (let v3
                      = coe
                          MAlonzo.Code.Data.List.Relation.Binary.Permutation.Setoid.du_'8621''45'setoid_178
                          (coe v0) in
                coe
                  (let v4
                         = MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                             (coe
                                MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                                (coe v3)) in
                   coe
                     (coe
                        MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                        (coe
                           MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_stop_54
                           (coe v4))
                        (coe
                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v1) (coe v2)))))
               erased)
            (coe
               du_'8621''45'shift_1306 v0 v1 v2
               (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))
-- Data.List.Relation.Binary.Permutation.Setoid.Properties.↭-reverse
d_'8621''45'reverse_1506 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.T_Permutation_32
d_'8621''45'reverse_1506 ~v0 ~v1 v2 v3
  = du_'8621''45'reverse_1506 v2 v3
du_'8621''45'reverse_1506 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.T_Permutation_32
du_'8621''45'reverse_1506 v0 v1
  = case coe v1 of
      []
        -> coe
             MAlonzo.Code.Data.List.Relation.Binary.Permutation.Setoid.du_'8621''45'refl_94
             (coe v0) (coe MAlonzo.Code.Data.List.Base.du_reverse_444 v1)
      (:) v2 v3
        -> coe
             MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
             (\ v4 v5 v6 ->
                coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_start_36 v6)
             (coe MAlonzo.Code.Data.List.Base.du_reverse_444 v1) v1
             (coe
                MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_436
                (\ v4 v5 v6 v7 v8 -> v8)
                (coe MAlonzo.Code.Data.List.Base.du_reverse_444 v1)
                (coe
                   MAlonzo.Code.Data.List.Base.du__'8759''691'__448
                   (coe MAlonzo.Code.Data.List.Base.du_reverse_444 v3) (coe v2))
                v1
                (coe
                   MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8621''45''10216'_418
                   (coe
                      MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                      (coe
                         (\ v4 v5 v6 ->
                            coe
                              MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.C_trans_80
                              (coe v5))))
                   (coe
                      MAlonzo.Code.Data.List.Relation.Binary.Permutation.Setoid.du_'8621''45'sym_96
                      (coe v0))
                   (coe
                      MAlonzo.Code.Data.List.Base.du__'8759''691'__448
                      (coe MAlonzo.Code.Data.List.Base.du_reverse_444 v3) (coe v2))
                   (coe
                      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v2)
                      (coe MAlonzo.Code.Data.List.Base.du_reverse_444 v3))
                   v1
                   (coe
                      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8621''45''10217'_416
                      (coe
                         MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                         (coe
                            (\ v4 v5 v6 ->
                               coe
                                 MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.C_trans_80
                                 (coe v5))))
                      (coe
                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v2)
                         (coe MAlonzo.Code.Data.List.Base.du_reverse_444 v3))
                      v1 v1
                      (let v4
                             = coe
                                 MAlonzo.Code.Data.List.Relation.Binary.Permutation.Setoid.du_'8621''45'setoid_178
                                 (coe v0) in
                       coe
                         (let v5
                                = MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                                    (coe
                                       MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                                       (coe v4)) in
                          coe
                            (coe
                               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                               (coe
                                  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_stop_54
                                  (coe v5))
                               (coe v1))))
                      (coe
                         MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.C_prep_54
                         (coe
                            MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                            (MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v0))
                            v2)
                         (coe du_'8621''45'reverse_1506 (coe v0) (coe v3))))
                   (coe
                      du_'8759''8621''8759''691'_1494 (coe v0) (coe v2)
                      (coe MAlonzo.Code.Data.List.Base.du_reverse_444 v3)))
                erased)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.List.Relation.Binary.Permutation.Setoid.Properties.++↭ʳ++
d_'43''43''8621''691''43''43'_1520 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.T_Permutation_32
d_'43''43''8621''691''43''43'_1520 ~v0 ~v1 v2 v3 v4
  = du_'43''43''8621''691''43''43'_1520 v2 v3 v4
du_'43''43''8621''691''43''43'_1520 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.T_Permutation_32
du_'43''43''8621''691''43''43'_1520 v0 v1 v2
  = case coe v1 of
      []
        -> coe
             MAlonzo.Code.Data.List.Relation.Binary.Permutation.Setoid.du_'8621''45'refl_94
             (coe v0)
             (coe
                MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v1) (coe v2))
      (:) v3 v4
        -> coe
             MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.C_trans_80
             (coe
                MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v4)
                (coe
                   MAlonzo.Code.Data.List.Base.du__'43''43'__32
                   (coe MAlonzo.Code.Data.List.Base.du_'91'_'93'_270 (coe v3))
                   (coe v2)))
             (coe
                MAlonzo.Code.Data.List.Relation.Binary.Permutation.Setoid.du_'8621''45'sym_96
                v0
                (coe
                   MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v4)
                   (coe
                      MAlonzo.Code.Data.List.Base.du__'43''43'__32
                      (coe MAlonzo.Code.Data.List.Base.du_'91'_'93'_270 (coe v3))
                      (coe v2)))
                (coe
                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v3)
                   (coe
                      MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v4) (coe v2)))
                (coe du_'8621''45'shift_1306 v0 v3 v4 v2))
             (coe
                du_'43''43''8621''691''43''43'_1520 (coe v0) (coe v4)
                (coe
                   MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v3) (coe v2)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.List.Relation.Binary.Permutation.Setoid.Properties._.partition-↭
d_partition'45''8621'_1544 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  (AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.T_Permutation_32
d_partition'45''8621'_1544 ~v0 ~v1 v2 ~v3 ~v4 v5 v6
  = du_partition'45''8621'_1544 v2 v5 v6
du_partition'45''8621'_1544 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  (AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.T_Permutation_32
du_partition'45''8621'_1544 v0 v1 v2
  = case coe v2 of
      []
        -> coe
             MAlonzo.Code.Data.List.Relation.Binary.Permutation.Setoid.du_'8621''45'refl_94
             (coe v0) (coe v2)
      (:) v3 v4
        -> let v5
                 = MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
                     (coe v1 v3) in
           coe
             (if coe v5
                then coe
                       MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.C_prep_54
                       (coe
                          MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                          (MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v0))
                          v3)
                       (coe du_partition'45''8621'_1544 (coe v0) (coe v1) (coe v4))
                else coe
                       MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.C_trans_80
                       (coe
                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v3)
                          (coe
                             MAlonzo.Code.Data.List.Base.du__'43''43'__32
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                (coe
                                   MAlonzo.Code.Data.List.Base.du_partition_680 (coe v1) (coe v4)))
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                (coe
                                   MAlonzo.Code.Data.List.Base.du_partition_680 (coe v1)
                                   (coe v4)))))
                       (coe
                          MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.C_prep_54
                          (coe
                             MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                             (MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v0))
                             v3)
                          (coe du_partition'45''8621'_1544 (coe v0) (coe v1) (coe v4)))
                       (coe
                          MAlonzo.Code.Data.List.Relation.Binary.Permutation.Setoid.du_'8621''45'sym_96
                          v0
                          (coe
                             MAlonzo.Code.Data.List.Base.du__'43''43'__32
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                (coe
                                   MAlonzo.Code.Data.List.Base.du_partition_680 (coe v1) (coe v4)))
                             (coe
                                MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                (coe MAlonzo.Code.Data.List.Base.du_'91'_'93'_270 (coe v3))
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                   (coe
                                      MAlonzo.Code.Data.List.Base.du_partition_680 (coe v1)
                                      (coe v4)))))
                          (coe
                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v3)
                             (coe
                                MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                   (coe
                                      MAlonzo.Code.Data.List.Base.du_partition_680 (coe v1)
                                      (coe v4)))
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                   (coe
                                      MAlonzo.Code.Data.List.Base.du_partition_680 (coe v1)
                                      (coe v4)))))
                          (coe
                             du_'8621''45'shift_1306 v0 v3
                             (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                (coe
                                   MAlonzo.Code.Data.List.Base.du_partition_680 (coe v1) (coe v4)))
                             (MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                (coe
                                   MAlonzo.Code.Data.List.Base.du_partition_680 (coe v1)
                                   (coe v4))))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.List.Relation.Binary.Permutation.Setoid.Properties._.merge-↭
d_merge'45''8621'_1578 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.T_Permutation_32
d_merge'45''8621'_1578 ~v0 ~v1 v2 ~v3 ~v4 v5 v6 v7
  = du_merge'45''8621'_1578 v2 v5 v6 v7
du_merge'45''8621'_1578 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.T_Permutation_32
du_merge'45''8621'_1578 v0 v1 v2 v3
  = case coe v2 of
      []
        -> case coe v3 of
             []
               -> coe
                    MAlonzo.Code.Data.List.Relation.Binary.Permutation.Setoid.du_'8621''45'refl_94
                    (coe v0)
                    (coe
                       MAlonzo.Code.Data.List.Base.du_merge_192 (coe v1) (coe v3)
                       (coe v3))
             (:) v4 v5
               -> coe
                    MAlonzo.Code.Data.List.Relation.Binary.Permutation.Setoid.du_'8621''45'refl_94
                    (coe v0)
                    (coe
                       MAlonzo.Code.Data.List.Base.du_merge_192 (coe v1) (coe v2)
                       (coe v3))
             _ -> MAlonzo.RTE.mazUnreachableError
      (:) v4 v5
        -> case coe v3 of
             []
               -> coe
                    MAlonzo.Code.Data.List.Relation.Binary.Permutation.Setoid.du_'8621''45'sym_96
                    v0
                    (coe
                       MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v2) (coe v3))
                    v2 (coe du_'43''43''45'identity'691'_1366 (coe v0) (coe v2))
             (:) v6 v7
               -> let v8
                        = MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
                            (coe v1 v4 v6) in
                  coe
                    (let v9
                           = coe
                               du_merge'45''8621'_1578 (coe v0) (coe v1) (coe v5) (coe v3) in
                     coe
                       (let v10
                              = coe
                                  du_merge'45''8621'_1578 (coe v0) (coe v1) (coe v2) (coe v7) in
                        coe
                          (if coe v8
                             then coe
                                    MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.C_prep_54
                                    (coe
                                       MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                                       (MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                                          (coe v0))
                                       v4)
                                    v9
                             else coe
                                    MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
                                    (\ v11 v12 v13 ->
                                       coe
                                         MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_start_36
                                         v13)
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v6)
                                       (coe
                                          MAlonzo.Code.Data.List.Base.du_merge_192 (coe v1) (coe v2)
                                          (coe v7)))
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v4)
                                       (coe
                                          MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v5)
                                          (coe v3)))
                                    (coe
                                       MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8621''45''10217'_416
                                       (coe
                                          MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                                          (coe
                                             (\ v11 v12 v13 ->
                                                coe
                                                  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.C_trans_80
                                                  (coe v12))))
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v6)
                                          (coe
                                             MAlonzo.Code.Data.List.Base.du_merge_192 (coe v1)
                                             (coe v2) (coe v7)))
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v6)
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v4)
                                             (coe
                                                MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                                (coe v5) (coe v7))))
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v4)
                                          (coe
                                             MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v5)
                                             (coe v3)))
                                       (coe
                                          MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8621''45''10216'_418
                                          (coe
                                             MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                                             (coe
                                                (\ v11 v12 v13 ->
                                                   coe
                                                     MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.C_trans_80
                                                     (coe v12))))
                                          (coe
                                             MAlonzo.Code.Data.List.Relation.Binary.Permutation.Setoid.du_'8621''45'sym_96
                                             (coe v0))
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v6)
                                             (coe
                                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                (coe v4)
                                                (coe
                                                   MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                                   (coe v5) (coe v7))))
                                          (coe
                                             MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v2)
                                             (coe v3))
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v4)
                                             (coe
                                                MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                                (coe v5) (coe v3)))
                                          (coe
                                             MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10216'_448
                                             (\ v11 v12 v13 v14 v15 -> v15)
                                             (coe
                                                MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                                (coe v2) (coe v3))
                                             (coe
                                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                (coe v4)
                                                (coe
                                                   MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                                   (coe v5) (coe v3)))
                                             (coe
                                                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                (coe v4)
                                                (coe
                                                   MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                                   (coe v5) (coe v3)))
                                             (let v11
                                                    = coe
                                                        MAlonzo.Code.Data.List.Relation.Binary.Permutation.Setoid.du_'8621''45'setoid_178
                                                        (coe v0) in
                                              coe
                                                (let v12
                                                       = MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                                                           (coe
                                                              MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                                                              (coe v11)) in
                                                 coe
                                                   (coe
                                                      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                                                      (coe
                                                         MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_stop_54
                                                         (coe v12))
                                                      (coe
                                                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                         (coe v4)
                                                         (coe
                                                            MAlonzo.Code.Data.List.Base.du__'43''43'__32
                                                            (coe v5) (coe v3))))))
                                             erased)
                                          (coe du_'8621''45'shift_1306 v0 v6 v2 v7))
                                       (coe
                                          MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.C_prep_54
                                          (coe
                                             MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                                             (MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                                                (coe v0))
                                             v6)
                                          v10)))))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.List.Relation.Binary.Permutation.Setoid.Properties._.commutativeMonoid
d_commutativeMonoid_1634 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_734 ->
  MAlonzo.Code.Algebra.Bundles.T_CommutativeMonoid_966
d_commutativeMonoid_1634 ~v0 ~v1 ~v2 v3 v4 v5
  = du_commutativeMonoid_1634 v3 v4 v5
du_commutativeMonoid_1634 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_734 ->
  MAlonzo.Code.Algebra.Bundles.T_CommutativeMonoid_966
du_commutativeMonoid_1634 v0 v1 v2
  = coe
      MAlonzo.Code.Algebra.Bundles.C_CommutativeMonoid'46'constructor_17975
      v0 v1 v2
-- Data.List.Relation.Binary.Permutation.Setoid.Properties._.foldr-commMonoid
d_foldr'45'commMonoid_1708 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_734 ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.T_Permutation_32 ->
  AgdaAny
d_foldr'45'commMonoid_1708 ~v0 ~v1 ~v2 v3 v4 v5 v6 v7 v8
  = du_foldr'45'commMonoid_1708 v3 v4 v5 v6 v7 v8
du_foldr'45'commMonoid_1708 ::
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_734 ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.T_Permutation_32 ->
  AgdaAny
du_foldr'45'commMonoid_1708 v0 v1 v2 v3 v4 v5
  = case coe v5 of
      MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.C_refl_42 v8
        -> coe
             MAlonzo.Code.Data.List.Relation.Binary.Pointwise.du_foldr'8314'_466
             (coe v3) (coe v4) (coe v0) (coe v0)
             (coe
                MAlonzo.Code.Algebra.Structures.d_'8729''45'cong_186
                (coe
                   MAlonzo.Code.Algebra.Structures.d_isMagma_478
                   (coe
                      MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                      (coe MAlonzo.Code.Algebra.Structures.d_isMonoid_744 (coe v2)))))
             (coe v1) (coe v1)
             (coe
                MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                (MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
                   (coe
                      MAlonzo.Code.Algebra.Structures.d_isMagma_478
                      (coe
                         MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                         (coe MAlonzo.Code.Algebra.Structures.d_isMonoid_744 (coe v2)))))
                v1)
             (coe v8)
      MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.C_prep_54 v10 v11
        -> case coe v3 of
             (:) v12 v13
               -> case coe v4 of
                    (:) v14 v15
                      -> coe
                           MAlonzo.Code.Algebra.Structures.d_'8729''45'cong_186
                           (MAlonzo.Code.Algebra.Structures.d_isMagma_478
                              (coe
                                 MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                                 (coe MAlonzo.Code.Algebra.Structures.d_isMonoid_744 (coe v2))))
                           v12 v14
                           (coe
                              MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                              (coe MAlonzo.Code.Data.List.Base.du_foldr_216 (coe v0) (coe v1))
                              (\ v16 v17 -> v16) v13 v15)
                           (coe
                              MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                              (\ v16 v17 -> v17)
                              (coe MAlonzo.Code.Data.List.Base.du_foldr_216 (coe v0) (coe v1))
                              v13 v15)
                           v10
                           (coe
                              du_foldr'45'commMonoid_1708 (coe v0) (coe v1) (coe v2) (coe v13)
                              (coe v15) (coe v11))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.C_swap_72 v12 v13 v14
        -> case coe v3 of
             (:) v15 v16
               -> case coe v16 of
                    (:) v17 v18
                      -> case coe v4 of
                           (:) v19 v20
                             -> case coe v20 of
                                  (:) v21 v22
                                    -> coe
                                         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
                                         (\ v23 v24 v25 ->
                                            coe
                                              MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_start_36
                                              v25)
                                         (coe
                                            v0 v15
                                            (coe
                                               v0 v17
                                               (coe
                                                  MAlonzo.Code.Data.List.Base.du_foldr_216 (coe v0)
                                                  (coe v1) (coe v18))))
                                         (coe
                                            v0 v19
                                            (coe
                                               v0 v21
                                               (coe
                                                  MAlonzo.Code.Data.List.Base.du_foldr_216 (coe v0)
                                                  (coe v1) (coe v22))))
                                         (coe
                                            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
                                            (coe
                                               MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                                               (coe
                                                  MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                                                  (coe
                                                     MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                                                     (let v23
                                                            = MAlonzo.Code.Algebra.Structures.d_isMonoid_744
                                                                (coe v2) in
                                                      coe
                                                        (let v24
                                                               = MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                                                                   (coe v23) in
                                                         coe
                                                           (coe
                                                              MAlonzo.Code.Algebra.Structures.du_setoid_200
                                                              (coe
                                                                 MAlonzo.Code.Algebra.Structures.d_isMagma_478
                                                                 (coe v24))))))))
                                            (coe
                                               v0 v15
                                               (coe
                                                  v0 v17
                                                  (coe
                                                     MAlonzo.Code.Data.List.Base.du_foldr_216
                                                     (coe v0) (coe v1) (coe v18))))
                                            (coe
                                               v0 v15
                                               (coe
                                                  v0 v17
                                                  (coe
                                                     MAlonzo.Code.Data.List.Base.du_foldr_216
                                                     (coe v0) (coe v1) (coe v22))))
                                            (coe
                                               v0 v19
                                               (coe
                                                  v0 v21
                                                  (coe
                                                     MAlonzo.Code.Data.List.Base.du_foldr_216
                                                     (coe v0) (coe v1) (coe v22))))
                                            (coe
                                               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10216'_370
                                               (coe
                                                  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                                                  (coe
                                                     MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                                                     (coe
                                                        MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                                                        (let v23
                                                               = MAlonzo.Code.Algebra.Structures.d_isMonoid_744
                                                                   (coe v2) in
                                                         coe
                                                           (let v24
                                                                  = MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                                                                      (coe v23) in
                                                            coe
                                                              (coe
                                                                 MAlonzo.Code.Algebra.Structures.du_setoid_200
                                                                 (coe
                                                                    MAlonzo.Code.Algebra.Structures.d_isMagma_478
                                                                    (coe v24))))))))
                                               (MAlonzo.Code.Relation.Binary.Structures.d_sym_36
                                                  (coe
                                                     MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                                                     (let v23
                                                            = MAlonzo.Code.Algebra.Structures.d_isMonoid_744
                                                                (coe v2) in
                                                      coe
                                                        (let v24
                                                               = MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                                                                   (coe v23) in
                                                         coe
                                                           (coe
                                                              MAlonzo.Code.Algebra.Structures.du_setoid_200
                                                              (coe
                                                                 MAlonzo.Code.Algebra.Structures.d_isMagma_478
                                                                 (coe v24)))))))
                                               (coe
                                                  v0 v15
                                                  (coe
                                                     v0 v17
                                                     (coe
                                                        MAlonzo.Code.Data.List.Base.du_foldr_216
                                                        (coe v0) (coe v1) (coe v22))))
                                               (coe
                                                  v0 (coe v0 v15 v17)
                                                  (coe
                                                     MAlonzo.Code.Data.List.Base.du_foldr_216
                                                     (coe v0) (coe v1) (coe v22)))
                                               (coe
                                                  v0 v19
                                                  (coe
                                                     v0 v21
                                                     (coe
                                                        MAlonzo.Code.Data.List.Base.du_foldr_216
                                                        (coe v0) (coe v1) (coe v22))))
                                               (coe
                                                  MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
                                                  (coe
                                                     MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                                                     (coe
                                                        MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                                                        (coe
                                                           MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                                                           (let v23
                                                                  = MAlonzo.Code.Algebra.Structures.d_isMonoid_744
                                                                      (coe v2) in
                                                            coe
                                                              (let v24
                                                                     = MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                                                                         (coe v23) in
                                                               coe
                                                                 (coe
                                                                    MAlonzo.Code.Algebra.Structures.du_setoid_200
                                                                    (coe
                                                                       MAlonzo.Code.Algebra.Structures.d_isMagma_478
                                                                       (coe v24))))))))
                                                  (coe
                                                     v0 (coe v0 v15 v17)
                                                     (coe
                                                        MAlonzo.Code.Data.List.Base.du_foldr_216
                                                        (coe v0) (coe v1) (coe v22)))
                                                  (coe
                                                     v0 (coe v0 v17 v15)
                                                     (coe
                                                        MAlonzo.Code.Data.List.Base.du_foldr_216
                                                        (coe v0) (coe v1) (coe v22)))
                                                  (coe
                                                     v0 v19
                                                     (coe
                                                        v0 v21
                                                        (coe
                                                           MAlonzo.Code.Data.List.Base.du_foldr_216
                                                           (coe v0) (coe v1) (coe v22))))
                                                  (coe
                                                     MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
                                                     (coe
                                                        MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                                                        (coe
                                                           MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                                                           (coe
                                                              MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                                                              (let v23
                                                                     = MAlonzo.Code.Algebra.Structures.d_isMonoid_744
                                                                         (coe v2) in
                                                               coe
                                                                 (let v24
                                                                        = MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                                                                            (coe v23) in
                                                                  coe
                                                                    (coe
                                                                       MAlonzo.Code.Algebra.Structures.du_setoid_200
                                                                       (coe
                                                                          MAlonzo.Code.Algebra.Structures.d_isMagma_478
                                                                          (coe v24))))))))
                                                     (coe
                                                        v0 (coe v0 v17 v15)
                                                        (coe
                                                           MAlonzo.Code.Data.List.Base.du_foldr_216
                                                           (coe v0) (coe v1) (coe v22)))
                                                     (coe
                                                        v0 (coe v0 v19 v21)
                                                        (coe
                                                           MAlonzo.Code.Data.List.Base.du_foldr_216
                                                           (coe v0) (coe v1) (coe v22)))
                                                     (coe
                                                        v0 v19
                                                        (coe
                                                           v0 v21
                                                           (coe
                                                              MAlonzo.Code.Data.List.Base.du_foldr_216
                                                              (coe v0) (coe v1) (coe v22))))
                                                     (coe
                                                        MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
                                                        (coe
                                                           MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
                                                           (coe
                                                              MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                                                              (coe
                                                                 MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                                                                 (let v23
                                                                        = MAlonzo.Code.Algebra.Structures.d_isMonoid_744
                                                                            (coe v2) in
                                                                  coe
                                                                    (let v24
                                                                           = MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                                                                               (coe v23) in
                                                                     coe
                                                                       (coe
                                                                          MAlonzo.Code.Algebra.Structures.du_setoid_200
                                                                          (coe
                                                                             MAlonzo.Code.Algebra.Structures.d_isMagma_478
                                                                             (coe v24))))))))
                                                        (coe
                                                           v0 (coe v0 v19 v21)
                                                           (coe
                                                              MAlonzo.Code.Data.List.Base.du_foldr_216
                                                              (coe v0) (coe v1) (coe v22)))
                                                        (coe
                                                           v0 v19
                                                           (coe
                                                              v0 v21
                                                              (coe
                                                                 MAlonzo.Code.Data.List.Base.du_foldr_216
                                                                 (coe v0) (coe v1) (coe v22))))
                                                        (coe
                                                           v0 v19
                                                           (coe
                                                              v0 v21
                                                              (coe
                                                                 MAlonzo.Code.Data.List.Base.du_foldr_216
                                                                 (coe v0) (coe v1) (coe v22))))
                                                        (let v23
                                                               = MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                                                                   (coe
                                                                      MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                                                                      (let v23
                                                                             = MAlonzo.Code.Algebra.Structures.d_isMonoid_744
                                                                                 (coe v2) in
                                                                       coe
                                                                         (let v24
                                                                                = MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                                                                                    (coe v23) in
                                                                          coe
                                                                            (coe
                                                                               MAlonzo.Code.Algebra.Structures.du_setoid_200
                                                                               (coe
                                                                                  MAlonzo.Code.Algebra.Structures.d_isMagma_478
                                                                                  (coe v24)))))) in
                                                         coe
                                                           (coe
                                                              MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                                                              (coe
                                                                 MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_stop_54
                                                                 (coe v23))
                                                              (coe
                                                                 v0 v19
                                                                 (coe
                                                                    v0 v21
                                                                    (coe
                                                                       MAlonzo.Code.Data.List.Base.du_foldr_216
                                                                       (coe v0) (coe v1)
                                                                       (coe v22))))))
                                                        (coe
                                                           MAlonzo.Code.Algebra.Structures.d_assoc_480
                                                           (MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                                                              (coe
                                                                 MAlonzo.Code.Algebra.Structures.d_isMonoid_744
                                                                 (coe v2)))
                                                           v19 v21
                                                           (coe
                                                              MAlonzo.Code.Data.List.Base.du_foldr_216
                                                              (coe v0) (coe v1) (coe v22))))
                                                     (let v23
                                                            = MAlonzo.Code.Algebra.Structures.d_isMonoid_744
                                                                (coe v2) in
                                                      coe
                                                        (let v24
                                                               = MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                                                                   (coe v23) in
                                                         coe
                                                           (let v25
                                                                  = MAlonzo.Code.Algebra.Structures.d_isMagma_478
                                                                      (coe v24) in
                                                            coe
                                                              (let v26
                                                                     = coe
                                                                         MAlonzo.Code.Algebra.Structures.du_setoid_200
                                                                         (coe v25) in
                                                               coe
                                                                 (let v27
                                                                        = MAlonzo.Code.Algebra.Structures.d_'8729''45'cong_186
                                                                            (coe v25) in
                                                                  coe
                                                                    (coe
                                                                       MAlonzo.Code.Algebra.Consequences.Base.du_'8729''45'cong'691'_46
                                                                       v27
                                                                       (MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                                                                          (coe
                                                                             MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                                                                             (coe v26)))
                                                                       (coe
                                                                          MAlonzo.Code.Data.List.Base.du_foldr_216
                                                                          (coe v0) (coe v1)
                                                                          (coe v22))
                                                                       (coe v0 v17 v15)
                                                                       (coe v0 v19 v21)
                                                                       (coe
                                                                          MAlonzo.Code.Algebra.Structures.d_'8729''45'cong_186
                                                                          (MAlonzo.Code.Algebra.Structures.d_isMagma_478
                                                                             (coe
                                                                                MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                                                                                (coe
                                                                                   MAlonzo.Code.Algebra.Structures.d_isMonoid_744
                                                                                   (coe v2))))
                                                                          v17 v19 v15 v21 v13
                                                                          v12))))))))
                                                  (let v23
                                                         = MAlonzo.Code.Algebra.Structures.d_isMonoid_744
                                                             (coe v2) in
                                                   coe
                                                     (let v24
                                                            = MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                                                                (coe v23) in
                                                      coe
                                                        (let v25
                                                               = MAlonzo.Code.Algebra.Structures.d_isMagma_478
                                                                   (coe v24) in
                                                         coe
                                                           (let v26
                                                                  = coe
                                                                      MAlonzo.Code.Algebra.Structures.du_setoid_200
                                                                      (coe v25) in
                                                            coe
                                                              (let v27
                                                                     = MAlonzo.Code.Algebra.Structures.d_'8729''45'cong_186
                                                                         (coe v25) in
                                                               coe
                                                                 (coe
                                                                    MAlonzo.Code.Algebra.Consequences.Base.du_'8729''45'cong'691'_46
                                                                    v27
                                                                    (MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                                                                       (coe
                                                                          MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                                                                          (coe v26)))
                                                                    (coe
                                                                       MAlonzo.Code.Data.List.Base.du_foldr_216
                                                                       (coe v0) (coe v1) (coe v22))
                                                                    (coe v0 v15 v17)
                                                                    (coe v0 v17 v15)
                                                                    (coe
                                                                       MAlonzo.Code.Algebra.Structures.d_comm_746
                                                                       v2 v15 v17))))))))
                                               (coe
                                                  MAlonzo.Code.Algebra.Structures.d_assoc_480
                                                  (MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                                                     (coe
                                                        MAlonzo.Code.Algebra.Structures.d_isMonoid_744
                                                        (coe v2)))
                                                  v15 v17
                                                  (coe
                                                     MAlonzo.Code.Data.List.Base.du_foldr_216
                                                     (coe v0) (coe v1) (coe v22))))
                                            (let v23
                                                   = MAlonzo.Code.Algebra.Structures.d_isMonoid_744
                                                       (coe v2) in
                                             coe
                                               (let v24
                                                      = MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                                                          (coe v23) in
                                                coe
                                                  (let v25
                                                         = MAlonzo.Code.Algebra.Structures.d_isMagma_478
                                                             (coe v24) in
                                                   coe
                                                     (let v26
                                                            = coe
                                                                MAlonzo.Code.Algebra.Structures.du_setoid_200
                                                                (coe v25) in
                                                      coe
                                                        (let v27
                                                               = MAlonzo.Code.Algebra.Structures.d_'8729''45'cong_186
                                                                   (coe v25) in
                                                         coe
                                                           (coe
                                                              MAlonzo.Code.Algebra.Consequences.Base.du_'8729''45'cong'737'_42
                                                              v27
                                                              (MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                                                                 (coe
                                                                    MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                                                                    (coe v26)))
                                                              v15
                                                              (coe
                                                                 MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                                                                 (coe v0 v17) (\ v28 v29 -> v28)
                                                                 (coe
                                                                    MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                                                                    (coe
                                                                       MAlonzo.Code.Data.List.Base.du_foldr_216
                                                                       (coe v0) (coe v1))
                                                                    (\ v28 v29 -> v28) v18 v22)
                                                                 (coe
                                                                    MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                                                                    (\ v28 v29 -> v29)
                                                                    (coe
                                                                       MAlonzo.Code.Data.List.Base.du_foldr_216
                                                                       (coe v0) (coe v1))
                                                                    v18 v22))
                                                              (coe
                                                                 MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                                                                 (\ v28 v29 -> v29) (coe v0 v17)
                                                                 (coe
                                                                    MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                                                                    (coe
                                                                       MAlonzo.Code.Data.List.Base.du_foldr_216
                                                                       (coe v0) (coe v1))
                                                                    (\ v28 v29 -> v28) v18 v22)
                                                                 (coe
                                                                    MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                                                                    (\ v28 v29 -> v29)
                                                                    (coe
                                                                       MAlonzo.Code.Data.List.Base.du_foldr_216
                                                                       (coe v0) (coe v1))
                                                                    v18 v22))
                                                              (let v28
                                                                     = MAlonzo.Code.Algebra.Structures.d_isMonoid_744
                                                                         (coe v2) in
                                                               coe
                                                                 (let v29
                                                                        = MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                                                                            (coe v28) in
                                                                  coe
                                                                    (let v30
                                                                           = MAlonzo.Code.Algebra.Structures.d_isMagma_478
                                                                               (coe v29) in
                                                                     coe
                                                                       (let v31
                                                                              = coe
                                                                                  MAlonzo.Code.Algebra.Structures.du_setoid_200
                                                                                  (coe v30) in
                                                                        coe
                                                                          (let v32
                                                                                 = MAlonzo.Code.Algebra.Structures.d_'8729''45'cong_186
                                                                                     (coe v30) in
                                                                           coe
                                                                             (coe
                                                                                MAlonzo.Code.Algebra.Consequences.Base.du_'8729''45'cong'737'_42
                                                                                v32
                                                                                (MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                                                                                   (coe
                                                                                      MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                                                                                      (coe v31)))
                                                                                v17
                                                                                (coe
                                                                                   MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                                                                                   (coe
                                                                                      MAlonzo.Code.Data.List.Base.du_foldr_216
                                                                                      (coe v0)
                                                                                      (coe v1))
                                                                                   (\ v33 v34 ->
                                                                                      v33)
                                                                                   v18 v22)
                                                                                (coe
                                                                                   MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                                                                                   (\ v33 v34 ->
                                                                                      v34)
                                                                                   (coe
                                                                                      MAlonzo.Code.Data.List.Base.du_foldr_216
                                                                                      (coe v0)
                                                                                      (coe v1))
                                                                                   v18 v22)
                                                                                (coe
                                                                                   du_foldr'45'commMonoid_1708
                                                                                   (coe v0) (coe v1)
                                                                                   (coe v2)
                                                                                   (coe v18)
                                                                                   (coe v22)
                                                                                   (coe
                                                                                      v14)))))))))))))))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.C_trans_80 v7 v9 v10
        -> coe
             MAlonzo.Code.Relation.Binary.Structures.d_trans_38
             (MAlonzo.Code.Algebra.Structures.d_isEquivalence_184
                (coe
                   MAlonzo.Code.Algebra.Structures.d_isMagma_478
                   (coe
                      MAlonzo.Code.Algebra.Structures.d_isSemigroup_694
                      (coe MAlonzo.Code.Algebra.Structures.d_isMonoid_744 (coe v2)))))
             (coe
                MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                (coe MAlonzo.Code.Data.List.Base.du_foldr_216 (coe v0) (coe v1))
                (\ v11 v12 -> v11) v3 v7)
             (coe
                MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                (\ v11 v12 -> v12)
                (coe MAlonzo.Code.Data.List.Base.du_foldr_216 (coe v0) (coe v1)) v3
                v7)
             (coe
                MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                (\ v11 v12 -> v12)
                (coe MAlonzo.Code.Data.List.Base.du_foldr_216 (coe v0) (coe v1)) v7
                v4)
             (coe
                du_foldr'45'commMonoid_1708 (coe v0) (coe v1) (coe v2) (coe v3)
                (coe v7) (coe v9))
             (coe
                du_foldr'45'commMonoid_1708 (coe v0) (coe v1) (coe v2) (coe v7)
                (coe v4) (coe v10))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.List.Relation.Binary.Permutation.Setoid.Properties.onIndices-lookup
d_onIndices'45'lookup_1786 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.T_Permutation_32 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> AgdaAny
d_onIndices'45'lookup_1786 ~v0 ~v1 v2 v3 v4 v5 v6
  = du_onIndices'45'lookup_1786 v2 v3 v4 v5 v6
du_onIndices'45'lookup_1786 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.T_Permutation_32 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> AgdaAny
du_onIndices'45'lookup_1786 v0 v1 v2 v3 v4
  = case coe v3 of
      MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.C_refl_42 v7
        -> coe
             MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Properties.du_lookup'45'cast_164
             (coe v1) (coe v2) (coe v7) (coe v4)
      MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.C_prep_54 v9 v10
        -> case coe v1 of
             (:) v11 v12
               -> case coe v2 of
                    (:) v13 v14
                      -> case coe v4 of
                           MAlonzo.Code.Data.Fin.Base.C_zero_12 -> coe v9
                           MAlonzo.Code.Data.Fin.Base.C_suc_16 v16
                             -> coe
                                  du_onIndices'45'lookup_1786 (coe v0) (coe v12) (coe v14) (coe v10)
                                  (coe v16)
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.C_swap_72 v11 v12 v13
        -> case coe v1 of
             (:) v14 v15
               -> case coe v15 of
                    (:) v16 v17
                      -> case coe v2 of
                           (:) v18 v19
                             -> case coe v19 of
                                  (:) v20 v21
                                    -> case coe v4 of
                                         MAlonzo.Code.Data.Fin.Base.C_zero_12 -> coe v11
                                         MAlonzo.Code.Data.Fin.Base.C_suc_16 v23
                                           -> case coe v23 of
                                                MAlonzo.Code.Data.Fin.Base.C_zero_12 -> coe v12
                                                MAlonzo.Code.Data.Fin.Base.C_suc_16 v25
                                                  -> coe
                                                       du_onIndices'45'lookup_1786 (coe v0)
                                                       (coe v17) (coe v21) (coe v13) (coe v25)
                                                _ -> MAlonzo.RTE.mazUnreachableError
                                         _ -> MAlonzo.RTE.mazUnreachableError
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.C_trans_80 v6 v8 v9
        -> coe
             MAlonzo.Code.Relation.Binary.Structures.d_trans_38
             (MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v0))
             (coe MAlonzo.Code.Data.List.Base.du_lookup_390 (coe v1) (coe v4))
             (coe
                MAlonzo.Code.Data.List.Base.du_lookup_390 (coe v6)
                (coe
                   MAlonzo.Code.Function.Bundles.d_to_2080
                   (coe
                      MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.du_onIndices_166
                      (coe v1) (coe v6) (coe v8))
                   v4))
             (coe
                MAlonzo.Code.Data.List.Base.du_lookup_390 (coe v2)
                (coe
                   MAlonzo.Code.Function.Bundles.d_to_2080
                   (coe
                      MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.du_onIndices_166
                      (coe v6) (coe v2) (coe v9))
                   (coe
                      MAlonzo.Code.Function.Bundles.d_to_2080
                      (coe
                         MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.du_onIndices_166
                         (coe v1) (coe v6) (coe v8))
                      v4)))
             (coe
                du_onIndices'45'lookup_1786 (coe v0) (coe v1) (coe v6) (coe v8)
                (coe v4))
             (coe
                du_onIndices'45'lookup_1786 (coe v0) (coe v6) (coe v2) (coe v9)
                (coe
                   MAlonzo.Code.Function.Bundles.d_to_2080
                   (coe
                      MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.du_onIndices_166
                      (coe v1) (coe v6) (coe v8))
                   v4))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.List.Relation.Binary.Permutation.Setoid.Properties.≋⇒↭
d_'8779''8658''8621'_1818 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.T_Permutation_32
d_'8779''8658''8621'_1818 ~v0 ~v1 ~v2 = du_'8779''8658''8621'_1818
du_'8779''8658''8621'_1818 ::
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.T_Permutation_32
du_'8779''8658''8621'_1818
  = coe
      MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.C_refl_42
-- Data.List.Relation.Binary.Permutation.Setoid.Properties.↭-respʳ-≋
d_'8621''45'resp'691''45''8779'_1820 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.T_Permutation_32 ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.T_Permutation_32
d_'8621''45'resp'691''45''8779'_1820 ~v0 ~v1 v2 v3 v4 v5 v6 v7
  = du_'8621''45'resp'691''45''8779'_1820 v2 v3 v4 v5 v6 v7
du_'8621''45'resp'691''45''8779'_1820 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.T_Permutation_32 ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.T_Permutation_32
du_'8621''45'resp'691''45''8779'_1820 v0 v1 v2 v3 v4 v5
  = case coe v5 of
      MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.C_refl_42 v8
        -> coe
             MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.C_refl_42
             (let v9
                    = coe
                        MAlonzo.Code.Data.List.Relation.Binary.Equality.Setoid.du_'8779''45'setoid_78
                        (coe v0) in
              coe
                (coe
                   MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                   (MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v9))
                   v1 v2 v3 v8 v4))
      MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.C_prep_54 v10 v11
        -> case coe v1 of
             (:) v12 v13
               -> case coe v2 of
                    (:) v14 v15
                      -> case coe v4 of
                           MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.C__'8759'__62 v20 v21
                             -> case coe v3 of
                                  (:) v22 v23
                                    -> coe
                                         MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.C_prep_54
                                         (coe
                                            MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                                            (MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                                               (coe v0))
                                            v12 v14 v22 v10 v20)
                                         (coe
                                            du_'8621''45'resp'691''45''8779'_1820 (coe v0) (coe v13)
                                            (coe v15) (coe v23) (coe v21) (coe v11))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.C_swap_72 v12 v13 v14
        -> case coe v1 of
             (:) v15 v16
               -> case coe v16 of
                    (:) v17 v18
                      -> case coe v2 of
                           (:) v19 v20
                             -> case coe v20 of
                                  (:) v21 v22
                                    -> case coe v4 of
                                         MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.C__'8759'__62 v27 v28
                                           -> case coe v3 of
                                                (:) v29 v30
                                                  -> case coe v28 of
                                                       MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.C__'8759'__62 v35 v36
                                                         -> case coe v30 of
                                                              (:) v37 v38
                                                                -> coe
                                                                     MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.C_swap_72
                                                                     (coe
                                                                        MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                                                                        (MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                                                                           (coe v0))
                                                                        v15 v21 v37 v12 v35)
                                                                     (coe
                                                                        MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                                                                        (MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                                                                           (coe v0))
                                                                        v17 v19 v29 v13 v27)
                                                                     (coe
                                                                        du_'8621''45'resp'691''45''8779'_1820
                                                                        (coe v0) (coe v18) (coe v22)
                                                                        (coe v38) (coe v36)
                                                                        (coe v14))
                                                              _ -> MAlonzo.RTE.mazUnreachableError
                                                       _ -> MAlonzo.RTE.mazUnreachableError
                                                _ -> MAlonzo.RTE.mazUnreachableError
                                         _ -> MAlonzo.RTE.mazUnreachableError
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.C_trans_80 v7 v9 v10
        -> coe
             MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.C_trans_80
             v7 v9
             (coe
                du_'8621''45'resp'691''45''8779'_1820 (coe v0) (coe v7) (coe v2)
                (coe v3) (coe v4) (coe v10))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.List.Relation.Binary.Permutation.Setoid.Properties.↭-respˡ-≋
d_'8621''45'resp'737''45''8779'_1852 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.T_Permutation_32 ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.T_Permutation_32
d_'8621''45'resp'737''45''8779'_1852 ~v0 ~v1 v2 v3 v4 v5 v6 v7
  = du_'8621''45'resp'737''45''8779'_1852 v2 v3 v4 v5 v6 v7
du_'8621''45'resp'737''45''8779'_1852 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.T_Permutation_32 ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.T_Permutation_32
du_'8621''45'resp'737''45''8779'_1852 v0 v1 v2 v3 v4 v5
  = case coe v5 of
      MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.C_refl_42 v8
        -> coe
             MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.C_refl_42
             (let v9
                    = coe
                        MAlonzo.Code.Data.List.Relation.Binary.Equality.Setoid.du_'8779''45'setoid_78
                        (coe v0) in
              coe
                (coe
                   MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                   (MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v9))
                   v3 v2 v1
                   (let v10
                          = coe
                              MAlonzo.Code.Data.List.Relation.Binary.Equality.Setoid.du_'8779''45'setoid_78
                              (coe v0) in
                    coe
                      (coe
                         MAlonzo.Code.Relation.Binary.Structures.d_sym_36
                         (MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v10))
                         v2 v3 v4))
                   v8))
      MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.C_prep_54 v10 v11
        -> case coe v1 of
             (:) v12 v13
               -> case coe v2 of
                    (:) v14 v15
                      -> case coe v4 of
                           MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.C__'8759'__62 v20 v21
                             -> case coe v3 of
                                  (:) v22 v23
                                    -> coe
                                         MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.C_prep_54
                                         (coe
                                            MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                                            (MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                                               (coe v0))
                                            v22 v14 v12
                                            (coe
                                               MAlonzo.Code.Relation.Binary.Structures.d_sym_36
                                               (MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                                                  (coe v0))
                                               v14 v22 v20)
                                            v10)
                                         (coe
                                            du_'8621''45'resp'737''45''8779'_1852 (coe v0) (coe v13)
                                            (coe v15) (coe v23) (coe v21) (coe v11))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.C_swap_72 v12 v13 v14
        -> case coe v1 of
             (:) v15 v16
               -> case coe v16 of
                    (:) v17 v18
                      -> case coe v2 of
                           (:) v19 v20
                             -> case coe v20 of
                                  (:) v21 v22
                                    -> case coe v4 of
                                         MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.C__'8759'__62 v27 v28
                                           -> case coe v3 of
                                                (:) v29 v30
                                                  -> case coe v28 of
                                                       MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.C__'8759'__62 v35 v36
                                                         -> case coe v30 of
                                                              (:) v37 v38
                                                                -> coe
                                                                     MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.C_swap_72
                                                                     (coe
                                                                        MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                                                                        (MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                                                                           (coe v0))
                                                                        v29 v19 v17
                                                                        (coe
                                                                           MAlonzo.Code.Relation.Binary.Structures.d_sym_36
                                                                           (MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                                                                              (coe v0))
                                                                           v19 v29 v27)
                                                                        v12)
                                                                     (coe
                                                                        MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                                                                        (MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                                                                           (coe v0))
                                                                        v37 v21 v15
                                                                        (coe
                                                                           MAlonzo.Code.Relation.Binary.Structures.d_sym_36
                                                                           (MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                                                                              (coe v0))
                                                                           v21 v37 v35)
                                                                        v13)
                                                                     (coe
                                                                        du_'8621''45'resp'737''45''8779'_1852
                                                                        (coe v0) (coe v18) (coe v22)
                                                                        (coe v38) (coe v36)
                                                                        (coe v14))
                                                              _ -> MAlonzo.RTE.mazUnreachableError
                                                       _ -> MAlonzo.RTE.mazUnreachableError
                                                _ -> MAlonzo.RTE.mazUnreachableError
                                         _ -> MAlonzo.RTE.mazUnreachableError
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.C_trans_80 v7 v9 v10
        -> coe
             MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.C_trans_80
             v7
             (coe
                du_'8621''45'resp'737''45''8779'_1852 (coe v0) (coe v7) (coe v2)
                (coe v3) (coe v4) (coe v9))
             v10
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.List.Relation.Binary.Permutation.Setoid.Properties.0<steps
d_0'60'steps_1886 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.T_Permutation_32 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_0'60'steps_1886 ~v0 ~v1 ~v2 v3 v4 v5
  = du_0'60'steps_1886 v3 v4 v5
du_0'60'steps_1886 ::
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.T_Permutation_32 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_0'60'steps_1886 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.C_refl_42 v5
        -> coe
             MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
             (coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26)
      MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.C_prep_54 v7 v8
        -> case coe v0 of
             (:) v9 v10
               -> case coe v1 of
                    (:) v11 v12
                      -> coe
                           MAlonzo.Code.Data.Nat.Properties.du_m'60'n'8658'm'60'1'43'n_3118
                           (coe du_0'60'steps_1886 (coe v10) (coe v12) (coe v8))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.C_swap_72 v9 v10 v11
        -> case coe v0 of
             (:) v12 v13
               -> case coe v13 of
                    (:) v14 v15
                      -> case coe v1 of
                           (:) v16 v17
                             -> case coe v17 of
                                  (:) v18 v19
                                    -> coe
                                         MAlonzo.Code.Data.Nat.Properties.du_m'60'n'8658'm'60'1'43'n_3118
                                         (coe du_0'60'steps_1886 (coe v15) (coe v19) (coe v11))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.C_trans_80 v4 v6 v7
        -> coe
             MAlonzo.Code.Data.Nat.Properties.du_'60''45''8804''45'trans_3048
             (coe du_0'60'steps_1886 (coe v0) (coe v4) (coe v6))
             (coe
                MAlonzo.Code.Data.Nat.Properties.du_m'8804'm'43'n_3538
                (coe
                   MAlonzo.Code.Data.List.Relation.Binary.Permutation.Setoid.du_steps_58
                   v0 v4 v6))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.List.Relation.Binary.Permutation.Setoid.Properties.steps-respˡ
d_steps'45'resp'737'_1906 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.T_Permutation_32 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_steps'45'resp'737'_1906 = erased
-- Data.List.Relation.Binary.Permutation.Setoid.Properties.steps-respʳ
d_steps'45'resp'691'_1928 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Pointwise.Base.T_Pointwise_48 ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.T_Permutation_32 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_steps'45'resp'691'_1928 = erased
-- Data.List.Relation.Binary.Permutation.Setoid.Properties.split
d_split_1958 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  AgdaAny ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.T_Permutation_32 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_split_1958 ~v0 ~v1 v2 v3 v4 v5 v6 v7
  = du_split_1958 v2 v3 v4 v5 v6 v7
du_split_1958 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  AgdaAny ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Data.List.Relation.Binary.Permutation.Homogeneous.T_Permutation_32 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_split_1958 v0 v1 v2 v3 v4 v5
  = let v6
          = coe
              du_helper_526 (coe v0) (coe v1) (coe v4)
              (coe
                 MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v2)
                 (coe
                    MAlonzo.Code.Data.List.Base.du__'43''43'__32
                    (coe MAlonzo.Code.Data.List.Base.du_'91'_'93'_270 (coe v1))
                    (coe v3)))
              (coe v2) (coe v3) (coe v5)
              (coe
                 MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                 (MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                    (coe
                       MAlonzo.Code.Data.List.Relation.Binary.Equality.Setoid.du_'8779''45'setoid_78
                       (coe v0)))
                 (coe
                    MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v2)
                    (coe
                       MAlonzo.Code.Data.List.Base.du__'43''43'__32
                       (coe MAlonzo.Code.Data.List.Base.du_'91'_'93'_270 (coe v1))
                       (coe v3)))) in
    coe
      (case coe v6 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
           -> case coe v8 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                  -> case coe v10 of
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v11 v12
                         -> coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v7)
                              (coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v9) (coe v11))
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> MAlonzo.RTE.mazUnreachableError)
