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

module MAlonzo.Code.Data.Tree.AVL.Key where

import Data.Text qualified
import MAlonzo.Code.Agda.Builtin.Sigma qualified
import MAlonzo.Code.Agda.Primitive qualified
import MAlonzo.Code.Data.Irrelevant qualified
import MAlonzo.Code.Relation.Binary.Bundles qualified
import MAlonzo.Code.Relation.Binary.Construct.Add.Extrema.Equality qualified
import MAlonzo.Code.Relation.Binary.Construct.Add.Extrema.Strict qualified
import MAlonzo.Code.Relation.Binary.Construct.Add.Infimum.Strict qualified
import MAlonzo.Code.Relation.Binary.Construct.Add.Point.Equality qualified
import MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict qualified
import MAlonzo.Code.Relation.Binary.Structures qualified
import MAlonzo.RTE (AgdaAny, add64, addInt, coe, eq64, eqInt, erased, geqInt, lt64, ltInt, mul64,
                    mulInt, quot64, quotInt, rem64, remInt, sub64, subInt, word64FromNat,
                    word64ToNat)
import MAlonzo.RTE qualified

-- Data.Tree.AVL.Key.Key⁺
d_Key'8314'_58 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 -> ()
d_Key'8314'_58 = erased
-- Data.Tree.AVL.Key._._≈∙_
d__'8776''8729'__62 a0 a1 a2 a3 a4 a5 = ()
-- Data.Tree.AVL.Key._._<⁺_
d__'60''8314'__72 a0 a1 a2 a3 a4 a5 = ()
-- Data.Tree.AVL.Key._<_<_
d__'60'_'60'__80 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  Maybe (Maybe AgdaAny) -> AgdaAny -> Maybe (Maybe AgdaAny) -> ()
d__'60'_'60'__80 = erased
-- Data.Tree.AVL.Key.⊥⁺<[_]<⊤⁺
d_'8869''8314''60''91'_'93''60''8868''8314'_90 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8869''8314''60''91'_'93''60''8868''8314'_90 ~v0 ~v1
  = du_'8869''8314''60''91'_'93''60''8868''8314'_90
du_'8869''8314''60''91'_'93''60''8868''8314'_90 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8869''8314''60''91'_'93''60''8868''8314'_90
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.C_'91'_'93'_26
         (coe
            MAlonzo.Code.Relation.Binary.Construct.Add.Infimum.Strict.C_'8869''8331''60''91'_'93'_24))
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.C_'91'_'93''60''8868''8314'_30)
-- Data.Tree.AVL.Key.refl⁺
d_refl'8314'_94 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  Maybe (Maybe AgdaAny) ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Point.Equality.T__'8776''8729'__20
d_refl'8314'_94 ~v0 ~v1 ~v2 v3 v4 = du_refl'8314'_94 v3 v4
du_refl'8314'_94 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  Maybe (Maybe AgdaAny) ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Point.Equality.T__'8776''8729'__20
du_refl'8314'_94 v0 v1
  = coe
      MAlonzo.Code.Relation.Binary.Construct.Add.Extrema.Equality.du_'8776''177''45'refl_98
      (let v2
             = coe
                 MAlonzo.Code.Relation.Binary.Bundles.du_decStrictPartialOrder_1098
                 (coe v0) in
       coe
         (let v3
                = coe
                    MAlonzo.Code.Relation.Binary.Bundles.du_decSetoid_728 (coe v2) in
          coe
            (MAlonzo.Code.Relation.Binary.Structures.d_refl_34
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_50
                  (coe
                     MAlonzo.Code.Relation.Binary.Bundles.d_isDecEquivalence_100
                     (coe v3))))))
      v1
-- Data.Tree.AVL.Key.sym⁺
d_sym'8314'_100 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  Maybe (Maybe AgdaAny) ->
  Maybe (Maybe AgdaAny) ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Point.Equality.T__'8776''8729'__20 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Point.Equality.T__'8776''8729'__20
d_sym'8314'_100 ~v0 ~v1 ~v2 v3 v4 v5 = du_sym'8314'_100 v3 v4 v5
du_sym'8314'_100 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  Maybe (Maybe AgdaAny) ->
  Maybe (Maybe AgdaAny) ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Point.Equality.T__'8776''8729'__20 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Point.Equality.T__'8776''8729'__20
du_sym'8314'_100 v0 v1 v2
  = coe
      MAlonzo.Code.Relation.Binary.Construct.Add.Extrema.Equality.du_'8776''177''45'sym_100
      (let v3
             = coe
                 MAlonzo.Code.Relation.Binary.Bundles.du_decStrictPartialOrder_1098
                 (coe v0) in
       coe
         (let v4
                = coe
                    MAlonzo.Code.Relation.Binary.Bundles.du_decSetoid_728 (coe v3) in
          coe
            (let v5
                   = coe
                       MAlonzo.Code.Relation.Binary.Bundles.du_setoid_108 (coe v4) in
             coe
               (MAlonzo.Code.Relation.Binary.Structures.d_sym_36
                  (coe
                     MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                     (coe v5))))))
      v1 v2
-- Data.Tree.AVL.Key.trans⁺
d_trans'8314'_108 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  Maybe (Maybe AgdaAny) ->
  Maybe (Maybe AgdaAny) ->
  Maybe (Maybe AgdaAny) ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.T__'60''8314'__20 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.T__'60''8314'__20 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.T__'60''8314'__20
d_trans'8314'_108 ~v0 ~v1 ~v2 v3 v4 v5 v6
  = du_trans'8314'_108 v3 v4 v5 v6
du_trans'8314'_108 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  Maybe (Maybe AgdaAny) ->
  Maybe (Maybe AgdaAny) ->
  Maybe (Maybe AgdaAny) ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.T__'60''8314'__20 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.T__'60''8314'__20 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.T__'60''8314'__20
du_trans'8314'_108 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Relation.Binary.Construct.Add.Extrema.Strict.du_'60''177''45'trans_162
      (MAlonzo.Code.Relation.Binary.Structures.d_trans_306
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isStrictPartialOrder_542
            (coe
               MAlonzo.Code.Relation.Binary.Bundles.d_isStrictTotalOrder_1058
               (coe v0))))
      v1 v2 v3
-- Data.Tree.AVL.Key.irrefl⁺
d_irrefl'8314'_114 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  Maybe (Maybe AgdaAny) ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.T__'60''8314'__20 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_irrefl'8314'_114 = erased
-- Data.Tree.AVL.Key.strictPartialOrder
d_strictPartialOrder_118 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictPartialOrder_556
d_strictPartialOrder_118 ~v0 ~v1 ~v2 v3
  = du_strictPartialOrder_118 v3
du_strictPartialOrder_118 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictPartialOrder_556
du_strictPartialOrder_118 v0
  = coe
      MAlonzo.Code.Relation.Binary.Bundles.C_StrictPartialOrder'46'constructor_11097
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Add.Extrema.Strict.du_'60''177''45'isStrictPartialOrder_334
         (MAlonzo.Code.Relation.Binary.Structures.d_isStrictPartialOrder_542
            (coe
               MAlonzo.Code.Relation.Binary.Bundles.d_isStrictTotalOrder_1058
               (coe v0))))
-- Data.Tree.AVL.Key.strictTotalOrder
d_strictTotalOrder_202 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036
d_strictTotalOrder_202 ~v0 ~v1 ~v2 v3 = du_strictTotalOrder_202 v3
du_strictTotalOrder_202 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1036
du_strictTotalOrder_202 v0
  = coe
      MAlonzo.Code.Relation.Binary.Bundles.C_StrictTotalOrder'46'constructor_21059
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Add.Extrema.Strict.du_'60''177''45'isStrictTotalOrder_338
         (MAlonzo.Code.Relation.Binary.Bundles.d_isStrictTotalOrder_1058
            (coe v0)))
