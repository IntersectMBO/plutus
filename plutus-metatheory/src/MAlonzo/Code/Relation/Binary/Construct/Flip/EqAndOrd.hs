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

module MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Relation.Binary.Bundles
import qualified MAlonzo.Code.Relation.Binary.Definitions
import qualified MAlonzo.Code.Relation.Binary.Structures
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core

-- Relation.Binary.Construct.Flip.EqAndOrd._.refl
d_refl_44 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_refl_44 ~v0 ~v1 ~v2 ~v3 v4 v5 = du_refl_44 v4 v5
du_refl_44 :: (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du_refl_44 v0 v1 = coe v0 v1
-- Relation.Binary.Construct.Flip.EqAndOrd._.sym
d_sym_48 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_sym_48 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 = du_sym_48 v4 v5 v6
du_sym_48 ::
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_sym_48 v0 v1 v2 = coe v0 v2 v1
-- Relation.Binary.Construct.Flip.EqAndOrd._.trans
d_trans_52 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_trans_52 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 v8 v9
  = du_trans_52 v4 v5 v6 v7 v8 v9
du_trans_52 ::
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_trans_52 v0 v1 v2 v3 v4 v5 = coe v0 v3 v2 v1 v5 v4
-- Relation.Binary.Construct.Flip.EqAndOrd._.asym
d_asym_56 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_asym_56 = erased
-- Relation.Binary.Construct.Flip.EqAndOrd._.total
d_total_60 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30) ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_total_60 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 = du_total_60 v4 v5 v6
du_total_60 ::
  (AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30) ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_total_60 v0 v1 v2 = coe v0 v2 v1
-- Relation.Binary.Construct.Flip.EqAndOrd._.resp
d_resp_72 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_resp_72 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 v8 v9 v10
  = du_resp_72 v6 v7 v8 v9 v10
du_resp_72 ::
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_resp_72 v0 v1 v2 v3 v4 = coe v1 v2 v3 (coe v0 v3 v2 v4)
-- Relation.Binary.Construct.Flip.EqAndOrd._.max
d_max_82 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  AgdaAny -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_max_82 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_max_82 v5
du_max_82 :: (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du_max_82 v0 = coe v0
-- Relation.Binary.Construct.Flip.EqAndOrd._.min
d_min_88 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  AgdaAny -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_min_88 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_min_88 v5
du_min_88 :: (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du_min_88 v0 = coe v0
-- Relation.Binary.Construct.Flip.EqAndOrd._.reflexive
d_reflexive_106 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_reflexive_106 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 v8 v9 v10
  = du_reflexive_106 v6 v7 v8 v9 v10
du_reflexive_106 ::
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_reflexive_106 v0 v1 v2 v3 v4 = coe v1 v3 v2 (coe v0 v2 v3 v4)
-- Relation.Binary.Construct.Flip.EqAndOrd._.irrefl
d_irrefl_112 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_irrefl_112 = erased
-- Relation.Binary.Construct.Flip.EqAndOrd._.antisym
d_antisym_122 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_antisym_122 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 v8 v9 v10
  = du_antisym_122 v6 v7 v8 v9 v10
du_antisym_122 ::
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_antisym_122 v0 v1 v2 v3 v4 = coe v0 v1 v2 v4 v3
-- Relation.Binary.Construct.Flip.EqAndOrd._.compare
d_compare_126 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny ->
   AgdaAny -> MAlonzo.Code.Relation.Binary.Definitions.T_Tri_158) ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Relation.Binary.Definitions.T_Tri_158
d_compare_126 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 v8
  = du_compare_126 v6 v7 v8
du_compare_126 ::
  (AgdaAny ->
   AgdaAny -> MAlonzo.Code.Relation.Binary.Definitions.T_Tri_158) ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Relation.Binary.Definitions.T_Tri_158
du_compare_126 v0 v1 v2
  = let v3 = coe v0 v1 v2 in
    coe
      (case coe v3 of
         MAlonzo.Code.Relation.Binary.Definitions.C_tri'60'_172 v4
           -> coe MAlonzo.Code.Relation.Binary.Definitions.C_tri'62'_188 v4
         MAlonzo.Code.Relation.Binary.Definitions.C_tri'8776'_180 v5
           -> coe MAlonzo.Code.Relation.Binary.Definitions.C_tri'8776'_180 v5
         MAlonzo.Code.Relation.Binary.Definitions.C_tri'62'_188 v6
           -> coe MAlonzo.Code.Relation.Binary.Definitions.C_tri'60'_172 v6
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Relation.Binary.Construct.Flip.EqAndOrd._.resp₂
d_resp'8322'_188 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_resp'8322'_188 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 = du_resp'8322'_188 v6
du_resp'8322'_188 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_resp'8322'_188 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v1 v2
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Construct.Flip.EqAndOrd._.dec
d_dec_206 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_dec_206 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 v8 = du_dec_206 v6 v7 v8
du_dec_206 ::
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du_dec_206 v0 v1 v2 = coe v0 v2 v1
-- Relation.Binary.Construct.Flip.EqAndOrd.isEquivalence
d_isEquivalence_210 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_isEquivalence_210 ~v0 ~v1 ~v2 ~v3 v4 = du_isEquivalence_210 v4
du_isEquivalence_210 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
du_isEquivalence_210 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_constructor_46
      (coe
         du_refl_44
         (coe MAlonzo.Code.Relation.Binary.Structures.d_refl_36 (coe v0)))
      (coe
         du_sym_48
         (coe MAlonzo.Code.Relation.Binary.Structures.d_sym_38 (coe v0)))
      (coe
         du_trans_52
         (coe MAlonzo.Code.Relation.Binary.Structures.d_trans_40 (coe v0)))
-- Relation.Binary.Construct.Flip.EqAndOrd.isDecEquivalence
d_isDecEquivalence_232 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecEquivalence_48 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecEquivalence_48
d_isDecEquivalence_232 ~v0 ~v1 ~v2 ~v3 v4
  = du_isDecEquivalence_232 v4
du_isDecEquivalence_232 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecEquivalence_48 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecEquivalence_48
du_isDecEquivalence_232 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_constructor_70
      (coe
         du_isEquivalence_210
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_54
            (coe v0)))
      (coe
         du_dec_206
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d__'8799'__56 (coe v0)))
-- Relation.Binary.Construct.Flip.EqAndOrd.isPreorder
d_isPreorder_258 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPreorder_76 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPreorder_76
d_isPreorder_258 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 = du_isPreorder_258 v6
du_isPreorder_258 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsPreorder_76 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPreorder_76
du_isPreorder_258 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_constructor_126
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_86
         (coe v0))
      (coe
         du_reflexive_106
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_sym_38
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_86
               (coe v0)))
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_reflexive_88 (coe v0)))
      (coe
         du_trans_52
         (coe MAlonzo.Code.Relation.Binary.Structures.d_trans_90 (coe v0)))
-- Relation.Binary.Construct.Flip.EqAndOrd.isTotalPreorder
d_isTotalPreorder_304 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsTotalPreorder_132 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsTotalPreorder_132
d_isTotalPreorder_304 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_isTotalPreorder_304 v6
du_isTotalPreorder_304 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsTotalPreorder_132 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsTotalPreorder_132
du_isTotalPreorder_304 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_constructor_178
      (coe
         du_isPreorder_258
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_140 (coe v0)))
      (coe
         du_total_60
         (coe MAlonzo.Code.Relation.Binary.Structures.d_total_142 (coe v0)))
-- Relation.Binary.Construct.Flip.EqAndOrd.isPartialOrder
d_isPartialOrder_350 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialOrder_248 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialOrder_248
d_isPartialOrder_350 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_isPartialOrder_350 v6
du_isPartialOrder_350 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialOrder_248 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialOrder_248
du_isPartialOrder_350 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_constructor_294
      (coe
         du_isPreorder_258
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256 (coe v0)))
      (coe
         du_antisym_122
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_antisym_258 (coe v0)))
-- Relation.Binary.Construct.Flip.EqAndOrd.isTotalOrder
d_isTotalOrder_398 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsTotalOrder_488 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsTotalOrder_488
d_isTotalOrder_398 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_isTotalOrder_398 v6
du_isTotalOrder_398 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsTotalOrder_488 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsTotalOrder_488
du_isTotalOrder_398 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_constructor_540
      (coe
         du_isPartialOrder_350
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPartialOrder_496
            (coe v0)))
      (coe
         du_total_60
         (coe MAlonzo.Code.Relation.Binary.Structures.d_total_498 (coe v0)))
-- Relation.Binary.Construct.Flip.EqAndOrd.isDecTotalOrder
d_isDecTotalOrder_450 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecTotalOrder_546 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecTotalOrder_546
d_isDecTotalOrder_450 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_isDecTotalOrder_450 v6
du_isDecTotalOrder_450 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecTotalOrder_546 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecTotalOrder_546
du_isDecTotalOrder_450 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_constructor_618
      (coe
         du_isTotalOrder_398
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isTotalOrder_556
            (coe v0)))
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d__'8799'__558 (coe v0))
      (coe
         du_dec_206
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d__'8804''63'__560
            (coe v0)))
-- Relation.Binary.Construct.Flip.EqAndOrd.isStrictPartialOrder
d_isStrictPartialOrder_518 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsStrictPartialOrder_370 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsStrictPartialOrder_370
d_isStrictPartialOrder_518 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_isStrictPartialOrder_518 v6
du_isStrictPartialOrder_518 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsStrictPartialOrder_370 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsStrictPartialOrder_370
du_isStrictPartialOrder_518 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_constructor_412
      (MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_382
         (coe v0))
      (coe
         du_trans_52
         (coe MAlonzo.Code.Relation.Binary.Structures.d_trans_386 (coe v0)))
      (coe
         du_resp'8322'_188
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_'60''45'resp'45''8776'_388
            (coe v0)))
-- Relation.Binary.Construct.Flip.EqAndOrd.isStrictTotalOrder
d_isStrictTotalOrder_556 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsStrictTotalOrder_624 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsStrictTotalOrder_624
d_isStrictTotalOrder_556 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_isStrictTotalOrder_556 v6
du_isStrictTotalOrder_556 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsStrictTotalOrder_624 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsStrictTotalOrder_624
du_isStrictTotalOrder_556 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_constructor_680
      (coe
         du_isStrictPartialOrder_518
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isStrictPartialOrder_632
            (coe v0)))
      (coe
         du_compare_126
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_compare_634 (coe v0)))
-- Relation.Binary.Construct.Flip.EqAndOrd.setoid
d_setoid_612 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_setoid_612 ~v0 ~v1 v2 = du_setoid_612 v2
du_setoid_612 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
du_setoid_612 v0
  = coe
      MAlonzo.Code.Relation.Binary.Bundles.C_constructor_84
      (coe
         du_isEquivalence_210
         (coe
            MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_62 (coe v0)))
-- Relation.Binary.Construct.Flip.EqAndOrd.decSetoid
d_decSetoid_644 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_DecSetoid_90 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_DecSetoid_90
d_decSetoid_644 ~v0 ~v1 v2 = du_decSetoid_644 v2
du_decSetoid_644 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_DecSetoid_90 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_DecSetoid_90
du_decSetoid_644 v0
  = coe
      MAlonzo.Code.Relation.Binary.Bundles.C_constructor_134
      (coe
         du_isDecEquivalence_232
         (coe
            MAlonzo.Code.Relation.Binary.Bundles.d_isDecEquivalence_106
            (coe v0)))
-- Relation.Binary.Construct.Flip.EqAndOrd.preorder
d_preorder_682 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Preorder_142 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Preorder_142
d_preorder_682 ~v0 ~v1 ~v2 v3 = du_preorder_682 v3
du_preorder_682 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Preorder_142 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Preorder_142
du_preorder_682 v0
  = coe
      MAlonzo.Code.Relation.Binary.Bundles.C_constructor_232
      (coe
         du_isPreorder_258
         (coe
            MAlonzo.Code.Relation.Binary.Bundles.d_isPreorder_164 (coe v0)))
-- Relation.Binary.Construct.Flip.EqAndOrd.totalPreorder
d_totalPreorder_760 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240
d_totalPreorder_760 ~v0 ~v1 ~v2 v3 = du_totalPreorder_760 v3
du_totalPreorder_760 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_240
du_totalPreorder_760 v0
  = coe
      MAlonzo.Code.Relation.Binary.Bundles.C_constructor_334
      (coe
         du_isTotalPreorder_304
         (coe
            MAlonzo.Code.Relation.Binary.Bundles.d_isTotalPreorder_262
            (coe v0)))
-- Relation.Binary.Construct.Flip.EqAndOrd.poset
d_poset_844 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Poset_492 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Poset_492
d_poset_844 ~v0 ~v1 ~v2 v3 = du_poset_844 v3
du_poset_844 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Poset_492 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Poset_492
du_poset_844 v0
  = coe
      MAlonzo.Code.Relation.Binary.Bundles.C_constructor_588
      (coe
         du_isPartialOrder_350
         (coe
            MAlonzo.Code.Relation.Binary.Bundles.d_isPartialOrder_514
            (coe v0)))
-- Relation.Binary.Construct.Flip.EqAndOrd.totalOrder
d_totalOrder_928 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_986 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_986
d_totalOrder_928 ~v0 ~v1 ~v2 v3 = du_totalOrder_928 v3
du_totalOrder_928 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_986 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_986
du_totalOrder_928 v0
  = coe
      MAlonzo.Code.Relation.Binary.Bundles.C_constructor_1090
      (coe
         du_isTotalOrder_398
         (coe
            MAlonzo.Code.Relation.Binary.Bundles.d_isTotalOrder_1008 (coe v0)))
-- Relation.Binary.Construct.Flip.EqAndOrd.decTotalOrder
d_decTotalOrder_1022 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_DecTotalOrder_1098 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_DecTotalOrder_1098
d_decTotalOrder_1022 ~v0 ~v1 ~v2 v3 = du_decTotalOrder_1022 v3
du_decTotalOrder_1022 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_DecTotalOrder_1098 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_DecTotalOrder_1098
du_decTotalOrder_1022 v0
  = coe
      MAlonzo.Code.Relation.Binary.Bundles.C_constructor_1272
      (coe
         du_isDecTotalOrder_450
         (coe
            MAlonzo.Code.Relation.Binary.Bundles.d_isDecTotalOrder_1120
            (coe v0)))
-- Relation.Binary.Construct.Flip.EqAndOrd.strictPartialOrder
d_strictPartialOrder_1134 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictPartialOrder_760 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictPartialOrder_760
d_strictPartialOrder_1134 ~v0 ~v1 ~v2 v3
  = du_strictPartialOrder_1134 v3
du_strictPartialOrder_1134 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictPartialOrder_760 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictPartialOrder_760
du_strictPartialOrder_1134 v0
  = coe
      MAlonzo.Code.Relation.Binary.Bundles.C_constructor_842
      (coe
         du_isStrictPartialOrder_518
         (coe
            MAlonzo.Code.Relation.Binary.Bundles.d_isStrictPartialOrder_782
            (coe v0)))
-- Relation.Binary.Construct.Flip.EqAndOrd.strictTotalOrder
d_strictTotalOrder_1204 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1280 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1280
d_strictTotalOrder_1204 ~v0 ~v1 ~v2 v3
  = du_strictTotalOrder_1204 v3
du_strictTotalOrder_1204 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1280 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1280
du_strictTotalOrder_1204 v0
  = coe
      MAlonzo.Code.Relation.Binary.Bundles.C_constructor_1386
      (coe
         du_isStrictTotalOrder_556
         (coe
            MAlonzo.Code.Relation.Binary.Bundles.d_isStrictTotalOrder_1302
            (coe v0)))
