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

module MAlonzo.Code.Data.Tree.AVL.Key where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Relation.Binary.Bundles
import qualified MAlonzo.Code.Relation.Binary.Construct.Add.Extrema.Equality
import qualified MAlonzo.Code.Relation.Binary.Construct.Add.Extrema.Strict
import qualified MAlonzo.Code.Relation.Binary.Construct.Add.Infimum.Strict
import qualified MAlonzo.Code.Relation.Binary.Construct.Add.Point.Equality
import qualified MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict
import qualified MAlonzo.Code.Relation.Binary.Structures

-- Data.Tree.AVL.Key.Key⁺
d_Key'8314'_60 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1280 -> ()
d_Key'8314'_60 = erased
-- Data.Tree.AVL.Key._._≈∙_
d__'8776''8729'__64 a0 a1 a2 a3 a4 a5 = ()
-- Data.Tree.AVL.Key._._<⁺_
d__'60''8314'__74 a0 a1 a2 a3 a4 a5 = ()
-- Data.Tree.AVL.Key._<_<_
d__'60'_'60'__82 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1280 ->
  Maybe (Maybe AgdaAny) -> AgdaAny -> Maybe (Maybe AgdaAny) -> ()
d__'60'_'60'__82 = erased
-- Data.Tree.AVL.Key.⊥⁺<[_]<⊤⁺
d_'8869''8314''60''91'_'93''60''8868''8314'_92 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1280 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8869''8314''60''91'_'93''60''8868''8314'_92 ~v0 ~v1
  = du_'8869''8314''60''91'_'93''60''8868''8314'_92
du_'8869''8314''60''91'_'93''60''8868''8314'_92 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8869''8314''60''91'_'93''60''8868''8314'_92
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.C_'91'_'93'_26
         (coe
            MAlonzo.Code.Relation.Binary.Construct.Add.Infimum.Strict.C_'8869''8331''60''91'_'93'_24))
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.C_'91'_'93''60''8868''8314'_30)
-- Data.Tree.AVL.Key.refl⁺
d_refl'8314'_96 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1280 ->
  Maybe (Maybe AgdaAny) ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Point.Equality.T__'8776''8729'__20
d_refl'8314'_96 ~v0 ~v1 ~v2 v3 v4 = du_refl'8314'_96 v3 v4
du_refl'8314'_96 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1280 ->
  Maybe (Maybe AgdaAny) ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Point.Equality.T__'8776''8729'__20
du_refl'8314'_96 v0 v1
  = coe
      MAlonzo.Code.Relation.Binary.Construct.Add.Extrema.Equality.du_'8776''177''45'refl_98
      (MAlonzo.Code.Relation.Binary.Structures.d_refl_36
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_382
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_isStrictPartialOrder_632
               (coe
                  MAlonzo.Code.Relation.Binary.Bundles.d_isStrictTotalOrder_1302
                  (coe v0)))))
      v1
-- Data.Tree.AVL.Key.sym⁺
d_sym'8314'_102 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1280 ->
  Maybe (Maybe AgdaAny) ->
  Maybe (Maybe AgdaAny) ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Point.Equality.T__'8776''8729'__20 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Point.Equality.T__'8776''8729'__20
d_sym'8314'_102 ~v0 ~v1 ~v2 v3 v4 v5 = du_sym'8314'_102 v3 v4 v5
du_sym'8314'_102 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1280 ->
  Maybe (Maybe AgdaAny) ->
  Maybe (Maybe AgdaAny) ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Point.Equality.T__'8776''8729'__20 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Point.Equality.T__'8776''8729'__20
du_sym'8314'_102 v0 v1 v2
  = coe
      MAlonzo.Code.Relation.Binary.Construct.Add.Extrema.Equality.du_'8776''177''45'sym_100
      (MAlonzo.Code.Relation.Binary.Structures.d_sym_38
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_382
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_isStrictPartialOrder_632
               (coe
                  MAlonzo.Code.Relation.Binary.Bundles.d_isStrictTotalOrder_1302
                  (coe v0)))))
      v1 v2
-- Data.Tree.AVL.Key.trans⁺
d_trans'8314'_110 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1280 ->
  Maybe (Maybe AgdaAny) ->
  Maybe (Maybe AgdaAny) ->
  Maybe (Maybe AgdaAny) ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.T__'60''8314'__20 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.T__'60''8314'__20 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.T__'60''8314'__20
d_trans'8314'_110 ~v0 ~v1 ~v2 v3 v4 v5 v6
  = du_trans'8314'_110 v3 v4 v5 v6
du_trans'8314'_110 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1280 ->
  Maybe (Maybe AgdaAny) ->
  Maybe (Maybe AgdaAny) ->
  Maybe (Maybe AgdaAny) ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.T__'60''8314'__20 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.T__'60''8314'__20 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.T__'60''8314'__20
du_trans'8314'_110 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Relation.Binary.Construct.Add.Extrema.Strict.du_'60''177''45'trans_168
      (MAlonzo.Code.Relation.Binary.Structures.d_trans_386
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isStrictPartialOrder_632
            (coe
               MAlonzo.Code.Relation.Binary.Bundles.d_isStrictTotalOrder_1302
               (coe v0))))
      v1 v2 v3
-- Data.Tree.AVL.Key.irrefl⁺
d_irrefl'8314'_116 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1280 ->
  Maybe (Maybe AgdaAny) ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.T__'60''8314'__20 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_irrefl'8314'_116 = erased
-- Data.Tree.AVL.Key.strictPartialOrder
d_strictPartialOrder_120 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1280 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictPartialOrder_760
d_strictPartialOrder_120 ~v0 ~v1 ~v2 v3
  = du_strictPartialOrder_120 v3
du_strictPartialOrder_120 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1280 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictPartialOrder_760
du_strictPartialOrder_120 v0
  = coe
      MAlonzo.Code.Relation.Binary.Bundles.C_constructor_842
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Add.Extrema.Strict.du_'60''177''45'isStrictPartialOrder_340
         (MAlonzo.Code.Relation.Binary.Structures.d_isStrictPartialOrder_632
            (coe
               MAlonzo.Code.Relation.Binary.Bundles.d_isStrictTotalOrder_1302
               (coe v0))))
-- Data.Tree.AVL.Key.strictTotalOrder
d_strictTotalOrder_212 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1280 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1280
d_strictTotalOrder_212 ~v0 ~v1 ~v2 v3 = du_strictTotalOrder_212 v3
du_strictTotalOrder_212 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1280 ->
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1280
du_strictTotalOrder_212 v0
  = coe
      MAlonzo.Code.Relation.Binary.Bundles.C_constructor_1386
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Add.Extrema.Strict.du_'60''177''45'isStrictTotalOrder_344
         (MAlonzo.Code.Relation.Binary.Bundles.d_isStrictTotalOrder_1302
            (coe v0)))
