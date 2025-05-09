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

module MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd where

import Data.Text qualified
import MAlonzo.Code.Agda.Builtin.Sigma qualified
import MAlonzo.Code.Agda.Primitive qualified
import MAlonzo.Code.Data.Irrelevant qualified
import MAlonzo.Code.Data.Sum.Base qualified
import MAlonzo.Code.Relation.Binary.Bundles qualified
import MAlonzo.Code.Relation.Binary.Definitions qualified
import MAlonzo.Code.Relation.Binary.Structures qualified
import MAlonzo.Code.Relation.Nullary.Decidable.Core qualified
import MAlonzo.RTE (AgdaAny, add64, addInt, coe, eq64, eqInt, erased, geqInt, lt64, ltInt, mul64,
                    mulInt, quot64, quotInt, rem64, remInt, sub64, subInt, word64FromNat,
                    word64ToNat)
import MAlonzo.RTE qualified

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
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_210 ~v0 ~v1 ~v2 ~v3 v4 = du_isEquivalence_210 v4
du_isEquivalence_210 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
du_isEquivalence_210 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_IsEquivalence'46'constructor_745
      (coe
         du_refl_44
         (coe MAlonzo.Code.Relation.Binary.Structures.d_refl_34 (coe v0)))
      (coe
         du_sym_48
         (coe MAlonzo.Code.Relation.Binary.Structures.d_sym_36 (coe v0)))
      (coe
         du_trans_52
         (coe MAlonzo.Code.Relation.Binary.Structures.d_trans_38 (coe v0)))
-- Relation.Binary.Construct.Flip.EqAndOrd.isDecEquivalence
d_isDecEquivalence_232 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecEquivalence_44 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecEquivalence_44
d_isDecEquivalence_232 ~v0 ~v1 ~v2 ~v3 v4
  = du_isDecEquivalence_232 v4
du_isDecEquivalence_232 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecEquivalence_44 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecEquivalence_44
du_isDecEquivalence_232 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_IsDecEquivalence'46'constructor_3083
      (coe
         du_isEquivalence_210
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_50
            (coe v0)))
      (coe
         du_dec_206
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d__'8799'__52 (coe v0)))
-- Relation.Binary.Construct.Flip.EqAndOrd.isPreorder
d_isPreorder_258 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPreorder_70 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPreorder_70
d_isPreorder_258 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 = du_isPreorder_258 v6
du_isPreorder_258 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsPreorder_70 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPreorder_70
du_isPreorder_258 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_IsPreorder'46'constructor_4003
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_80
         (coe v0))
      (coe
         du_reflexive_106
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_sym_36
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_80
               (coe v0)))
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_reflexive_82 (coe v0)))
      (coe
         du_trans_52
         (coe MAlonzo.Code.Relation.Binary.Structures.d_trans_84 (coe v0)))
-- Relation.Binary.Construct.Flip.EqAndOrd.isTotalPreorder
d_isTotalPreorder_304 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsTotalPreorder_124 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsTotalPreorder_124
d_isTotalPreorder_304 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_isTotalPreorder_304 v6
du_isTotalPreorder_304 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsTotalPreorder_124 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsTotalPreorder_124
du_isTotalPreorder_304 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_IsTotalPreorder'46'constructor_8325
      (coe
         du_isPreorder_258
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_132 (coe v0)))
      (coe
         du_total_60
         (coe MAlonzo.Code.Relation.Binary.Structures.d_total_134 (coe v0)))
-- Relation.Binary.Construct.Flip.EqAndOrd.isPartialOrder
d_isPartialOrder_350 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialOrder_174 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialOrder_174
d_isPartialOrder_350 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_isPartialOrder_350 v6
du_isPartialOrder_350 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialOrder_174 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialOrder_174
du_isPartialOrder_350 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_IsPartialOrder'46'constructor_9853
      (coe
         du_isPreorder_258
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_182 (coe v0)))
      (coe
         du_antisym_122
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_antisym_184 (coe v0)))
-- Relation.Binary.Construct.Flip.EqAndOrd.isTotalOrder
d_isTotalOrder_398 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsTotalOrder_404 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsTotalOrder_404
d_isTotalOrder_398 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_isTotalOrder_398 v6
du_isTotalOrder_398 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsTotalOrder_404 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsTotalOrder_404
du_isTotalOrder_398 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_IsTotalOrder'46'constructor_20555
      (coe
         du_isPartialOrder_350
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPartialOrder_412
            (coe v0)))
      (coe
         du_total_60
         (coe MAlonzo.Code.Relation.Binary.Structures.d_total_414 (coe v0)))
-- Relation.Binary.Construct.Flip.EqAndOrd.isDecTotalOrder
d_isDecTotalOrder_450 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecTotalOrder_460 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecTotalOrder_460
d_isDecTotalOrder_450 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_isDecTotalOrder_450 v6
du_isDecTotalOrder_450 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecTotalOrder_460 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecTotalOrder_460
du_isDecTotalOrder_450 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_IsDecTotalOrder'46'constructor_22695
      (coe
         du_isTotalOrder_398
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isTotalOrder_470
            (coe v0)))
      (coe
         MAlonzo.Code.Relation.Binary.Structures.d__'8799'__472 (coe v0))
      (coe
         du_dec_206
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d__'8804''63'__474
            (coe v0)))
-- Relation.Binary.Construct.Flip.EqAndOrd.isStrictPartialOrder
d_isStrictPartialOrder_516 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsStrictPartialOrder_290 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsStrictPartialOrder_290
d_isStrictPartialOrder_516 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_isStrictPartialOrder_516 v6
du_isStrictPartialOrder_516 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsStrictPartialOrder_290 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsStrictPartialOrder_290
du_isStrictPartialOrder_516 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_IsStrictPartialOrder'46'constructor_14045
      (MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_302
         (coe v0))
      (coe
         du_trans_52
         (coe MAlonzo.Code.Relation.Binary.Structures.d_trans_306 (coe v0)))
      (coe
         du_resp'8322'_188
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_'60''45'resp'45''8776'_308
            (coe v0)))
-- Relation.Binary.Construct.Flip.EqAndOrd.isStrictTotalOrder
d_isStrictTotalOrder_554 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsStrictTotalOrder_534 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsStrictTotalOrder_534
d_isStrictTotalOrder_554 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_isStrictTotalOrder_554 v6
du_isStrictTotalOrder_554 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsStrictTotalOrder_534 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsStrictTotalOrder_534
du_isStrictTotalOrder_554 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_IsStrictTotalOrder'46'constructor_24953
      (coe
         du_isStrictPartialOrder_516
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isStrictPartialOrder_542
            (coe v0)))
      (coe
         du_compare_126
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_compare_544 (coe v0)))
-- Relation.Binary.Construct.Flip.EqAndOrd.setoid
d_setoid_610 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
d_setoid_610 ~v0 ~v1 v2 = du_setoid_610 v2
du_setoid_610 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
du_setoid_610 v0
  = coe
      MAlonzo.Code.Relation.Binary.Bundles.C_Setoid'46'constructor_733
      (coe
         du_isEquivalence_210
         (coe
            MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v0)))
-- Relation.Binary.Construct.Flip.EqAndOrd.decSetoid
d_decSetoid_640 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_DecSetoid_84 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_DecSetoid_84
d_decSetoid_640 ~v0 ~v1 v2 = du_decSetoid_640 v2
du_decSetoid_640 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_DecSetoid_84 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_DecSetoid_84
du_decSetoid_640 v0
  = coe
      MAlonzo.Code.Relation.Binary.Bundles.C_DecSetoid'46'constructor_1389
      (coe
         du_isDecEquivalence_232
         (coe
            MAlonzo.Code.Relation.Binary.Bundles.d_isDecEquivalence_100
            (coe v0)))
-- Relation.Binary.Construct.Flip.EqAndOrd.preorder
d_preorder_676 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Preorder_132 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Preorder_132
d_preorder_676 ~v0 ~v1 ~v2 v3 = du_preorder_676 v3
du_preorder_676 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Preorder_132 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Preorder_132
du_preorder_676 v0
  = coe
      MAlonzo.Code.Relation.Binary.Bundles.C_Preorder'46'constructor_2267
      (coe
         du_isPreorder_258
         (coe
            MAlonzo.Code.Relation.Binary.Bundles.d_isPreorder_154 (coe v0)))
-- Relation.Binary.Construct.Flip.EqAndOrd.totalPreorder
d_totalPreorder_746 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222
d_totalPreorder_746 ~v0 ~v1 ~v2 v3 = du_totalPreorder_746 v3
du_totalPreorder_746 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_222
du_totalPreorder_746 v0
  = coe
      MAlonzo.Code.Relation.Binary.Bundles.C_TotalPreorder'46'constructor_4573
      (coe
         du_isTotalPreorder_304
         (coe
            MAlonzo.Code.Relation.Binary.Bundles.d_isTotalPreorder_244
            (coe v0)))
-- Relation.Binary.Construct.Flip.EqAndOrd.poset
d_poset_822 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Poset_314 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Poset_314
d_poset_822 ~v0 ~v1 ~v2 v3 = du_poset_822 v3
du_poset_822 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Poset_314 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Poset_314
du_poset_822 v0
  = coe
      MAlonzo.Code.Relation.Binary.Bundles.C_Poset'46'constructor_6389
      (coe
         du_isPartialOrder_350
         (coe
            MAlonzo.Code.Relation.Binary.Bundles.d_isPartialOrder_336
            (coe v0)))
-- Relation.Binary.Construct.Flip.EqAndOrd.totalOrder
d_totalOrder_898 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764
d_totalOrder_898 ~v0 ~v1 ~v2 v3 = du_totalOrder_898 v3
du_totalOrder_898 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_764
du_totalOrder_898 v0
  = coe
      MAlonzo.Code.Relation.Binary.Bundles.C_TotalOrder'46'constructor_15747
      (coe
         du_isTotalOrder_398
         (coe
            MAlonzo.Code.Relation.Binary.Bundles.d_isTotalOrder_786 (coe v0)))
-- Relation.Binary.Construct.Flip.EqAndOrd.decTotalOrder
d_decTotalOrder_984 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_DecTotalOrder_866 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_DecTotalOrder_866
d_decTotalOrder_984 ~v0 ~v1 ~v2 v3 = du_decTotalOrder_984 v3
du_decTotalOrder_984 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_DecTotalOrder_866 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_DecTotalOrder_866
du_decTotalOrder_984 v0
  = coe
      MAlonzo.Code.Relation.Binary.Bundles.C_DecTotalOrder'46'constructor_17849
      (coe
         du_isDecTotalOrder_450
         (coe
            MAlonzo.Code.Relation.Binary.Bundles.d_isDecTotalOrder_888
            (coe v0)))
-- Relation.Binary.Construct.Flip.EqAndOrd.strictPartialOrder
d_strictPartialOrder_1088 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictPartialOrder_556 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictPartialOrder_556
d_strictPartialOrder_1088 ~v0 ~v1 ~v2 v3
  = du_strictPartialOrder_1088 v3
du_strictPartialOrder_1088 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictPartialOrder_556 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictPartialOrder_556
du_strictPartialOrder_1088 v0
  = coe
      MAlonzo.Code.Relation.Binary.Bundles.C_StrictPartialOrder'46'constructor_11097
      (coe
         du_isStrictPartialOrder_516
         (coe
            MAlonzo.Code.Relation.Binary.Bundles.d_isStrictPartialOrder_578
            (coe v0)))
-- Relation.Binary.Construct.Flip.EqAndOrd.strictTotalOrder
d_strictTotalOrder_1150 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036
d_strictTotalOrder_1150 ~v0 ~v1 ~v2 v3
  = du_strictTotalOrder_1150 v3
du_strictTotalOrder_1150 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036
du_strictTotalOrder_1150 v0
  = coe
      MAlonzo.Code.Relation.Binary.Bundles.C_StrictTotalOrder'46'constructor_21059
      (coe
         du_isStrictTotalOrder_554
         (coe
            MAlonzo.Code.Relation.Binary.Bundles.d_isStrictTotalOrder_1058
            (coe v0)))
