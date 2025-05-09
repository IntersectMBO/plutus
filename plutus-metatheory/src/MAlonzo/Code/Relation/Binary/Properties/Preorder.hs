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

module MAlonzo.Code.Relation.Binary.Properties.Preorder where

import Data.Text qualified
import MAlonzo.Code.Agda.Builtin.Sigma qualified
import MAlonzo.Code.Agda.Primitive qualified
import MAlonzo.Code.Data.Product.Base qualified
import MAlonzo.Code.Relation.Binary.Bundles qualified
import MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd qualified
import MAlonzo.Code.Relation.Binary.Structures qualified
import MAlonzo.RTE (AgdaAny, add64, addInt, coe, eq64, eqInt, erased, geqInt, lt64, ltInt, mul64,
                    mulInt, quot64, quotInt, rem64, remInt, sub64, subInt, word64FromNat,
                    word64ToNat)
import MAlonzo.RTE qualified

-- Relation.Binary.Properties.Preorder._._≳_
d__'8819'__24 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Preorder_132 ->
  AgdaAny -> AgdaAny -> ()
d__'8819'__24 = erased
-- Relation.Binary.Properties.Preorder.converse-isPreorder
d_converse'45'isPreorder_78 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Preorder_132 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPreorder_70
d_converse'45'isPreorder_78 ~v0 ~v1 ~v2 v3
  = du_converse'45'isPreorder_78 v3
du_converse'45'isPreorder_78 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Preorder_132 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPreorder_70
du_converse'45'isPreorder_78 v0
  = coe
      MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_isPreorder_258
      (coe
         MAlonzo.Code.Relation.Binary.Bundles.d_isPreorder_154 (coe v0))
-- Relation.Binary.Properties.Preorder.converse-preorder
d_converse'45'preorder_80 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Preorder_132 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Preorder_132
d_converse'45'preorder_80 ~v0 ~v1 ~v2 v3
  = du_converse'45'preorder_80 v3
du_converse'45'preorder_80 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Preorder_132 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Preorder_132
du_converse'45'preorder_80 v0
  = coe
      MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_preorder_676
      (coe v0)
-- Relation.Binary.Properties.Preorder.InducedEquivalence
d_InducedEquivalence_82 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Preorder_132 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
d_InducedEquivalence_82 ~v0 ~v1 ~v2 v3
  = du_InducedEquivalence_82 v3
du_InducedEquivalence_82 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Preorder_132 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
du_InducedEquivalence_82 v0
  = coe
      MAlonzo.Code.Relation.Binary.Bundles.C_Setoid'46'constructor_733
      (coe
         MAlonzo.Code.Relation.Binary.Structures.C_IsEquivalence'46'constructor_745
         (coe
            (\ v1 ->
               coe
                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                 (coe
                    MAlonzo.Code.Relation.Binary.Structures.du_refl_98
                    (coe
                       MAlonzo.Code.Relation.Binary.Bundles.d_isPreorder_154 (coe v0))
                    (coe v1))
                 (coe
                    MAlonzo.Code.Relation.Binary.Structures.du_refl_98
                    (coe
                       MAlonzo.Code.Relation.Binary.Bundles.d_isPreorder_154 (coe v0))
                    (coe v1))))
         (coe (\ v1 v2 -> coe MAlonzo.Code.Data.Product.Base.du_swap_370))
         (coe
            (\ v1 v2 v3 ->
               coe
                 MAlonzo.Code.Data.Product.Base.du_zip_198
                 (coe
                    MAlonzo.Code.Relation.Binary.Structures.d_trans_84
                    (MAlonzo.Code.Relation.Binary.Bundles.d_isPreorder_154 (coe v0)) v1
                    v2 v3)
                 (coe
                    (\ v4 v5 v6 v7 ->
                       coe
                         MAlonzo.Code.Relation.Binary.Structures.d_trans_84
                         (MAlonzo.Code.Relation.Binary.Bundles.d_isPreorder_154 (coe v0)) v3
                         v2 v1 v7 v6)))))
-- Relation.Binary.Properties.Preorder.invIsPreorder
d_invIsPreorder_88 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Preorder_132 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPreorder_70
d_invIsPreorder_88 ~v0 ~v1 ~v2 v3 = du_invIsPreorder_88 v3
du_invIsPreorder_88 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Preorder_132 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPreorder_70
du_invIsPreorder_88 v0 = coe du_converse'45'isPreorder_78 (coe v0)
-- Relation.Binary.Properties.Preorder.invPreorder
d_invPreorder_90 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Preorder_132 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Preorder_132
d_invPreorder_90 ~v0 ~v1 ~v2 v3 = du_invPreorder_90 v3
du_invPreorder_90 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Preorder_132 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Preorder_132
du_invPreorder_90 v0 = coe du_converse'45'preorder_80 (coe v0)
