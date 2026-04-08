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

module MAlonzo.Code.Relation.Binary.Properties.Preorder where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Data.Product.Base
import qualified MAlonzo.Code.Relation.Binary.Bundles
import qualified MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd
import qualified MAlonzo.Code.Relation.Binary.Structures

-- Relation.Binary.Properties.Preorder._._∼ᵒ_
d__'8764''7506'__26 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Preorder_142 ->
  AgdaAny -> AgdaAny -> ()
d__'8764''7506'__26 = erased
-- Relation.Binary.Properties.Preorder.converse-isPreorder
d_converse'45'isPreorder_86 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Preorder_142 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPreorder_76
d_converse'45'isPreorder_86 ~v0 ~v1 ~v2 v3
  = du_converse'45'isPreorder_86 v3
du_converse'45'isPreorder_86 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Preorder_142 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPreorder_76
du_converse'45'isPreorder_86 v0
  = coe
      MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_isPreorder_258
      (coe
         MAlonzo.Code.Relation.Binary.Bundles.d_isPreorder_164 (coe v0))
-- Relation.Binary.Properties.Preorder.converse-preorder
d_converse'45'preorder_88 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Preorder_142 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Preorder_142
d_converse'45'preorder_88 ~v0 ~v1 ~v2 v3
  = du_converse'45'preorder_88 v3
du_converse'45'preorder_88 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Preorder_142 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Preorder_142
du_converse'45'preorder_88 v0
  = coe
      MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_preorder_682
      (coe v0)
-- Relation.Binary.Properties.Preorder.InducedEquivalence
d_InducedEquivalence_90 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Preorder_142 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
d_InducedEquivalence_90 ~v0 ~v1 ~v2 v3
  = du_InducedEquivalence_90 v3
du_InducedEquivalence_90 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Preorder_142 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_46
du_InducedEquivalence_90 v0
  = coe
      MAlonzo.Code.Relation.Binary.Bundles.C_constructor_84
      (coe
         MAlonzo.Code.Relation.Binary.Structures.C_constructor_46
         (coe
            (\ v1 ->
               coe
                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                 (coe
                    MAlonzo.Code.Relation.Binary.Structures.du_refl_104
                    (coe
                       MAlonzo.Code.Relation.Binary.Bundles.d_isPreorder_164 (coe v0))
                    (coe v1))
                 (coe
                    MAlonzo.Code.Relation.Binary.Structures.du_refl_104
                    (coe
                       MAlonzo.Code.Relation.Binary.Bundles.d_isPreorder_164 (coe v0))
                    (coe v1))))
         (coe (\ v1 v2 -> coe MAlonzo.Code.Data.Product.Base.du_swap_370))
         (coe
            (\ v1 v2 v3 ->
               coe
                 MAlonzo.Code.Data.Product.Base.du_zip_198
                 (coe
                    MAlonzo.Code.Relation.Binary.Structures.d_trans_90
                    (MAlonzo.Code.Relation.Binary.Bundles.d_isPreorder_164 (coe v0)) v1
                    v2 v3)
                 (coe
                    (\ v4 v5 v6 v7 ->
                       coe
                         MAlonzo.Code.Relation.Binary.Structures.d_trans_90
                         (MAlonzo.Code.Relation.Binary.Bundles.d_isPreorder_164 (coe v0)) v3
                         v2 v1 v7 v6)))))
-- Relation.Binary.Properties.Preorder.invIsPreorder
d_invIsPreorder_96 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Preorder_142 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPreorder_76
d_invIsPreorder_96 ~v0 ~v1 ~v2 v3 = du_invIsPreorder_96 v3
du_invIsPreorder_96 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Preorder_142 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPreorder_76
du_invIsPreorder_96 v0 = coe du_converse'45'isPreorder_86 (coe v0)
-- Relation.Binary.Properties.Preorder.invPreorder
d_invPreorder_98 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Preorder_142 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Preorder_142
d_invPreorder_98 ~v0 ~v1 ~v2 v3 = du_invPreorder_98 v3
du_invPreorder_98 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Preorder_142 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_Preorder_142
du_invPreorder_98 v0 = coe du_converse'45'preorder_88 (coe v0)
