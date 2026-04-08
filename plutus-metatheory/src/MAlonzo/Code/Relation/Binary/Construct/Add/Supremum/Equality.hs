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

module MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Equality where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Relation.Binary.Construct.Add.Point.Equality
import qualified MAlonzo.Code.Relation.Binary.Structures
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core

-- Relation.Binary.Construct.Add.Supremum.Equality._._≈∙_
d__'8776''8729'__22 a0 a1 a2 a3 a4 a5 = ()
-- Relation.Binary.Construct.Add.Supremum.Equality._.[≈]-injective
d_'91''8776''93''45'injective_26 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Point.Equality.T__'8776''8729'__20 ->
  AgdaAny
d_'91''8776''93''45'injective_26 ~v0 ~v1 ~v2 ~v3
  = du_'91''8776''93''45'injective_26
du_'91''8776''93''45'injective_26 ::
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Point.Equality.T__'8776''8729'__20 ->
  AgdaAny
du_'91''8776''93''45'injective_26 v0 v1 v2
  = coe
      MAlonzo.Code.Relation.Binary.Construct.Add.Point.Equality.du_'91''8776''93''45'injective_34
      v2
-- Relation.Binary.Construct.Add.Supremum.Equality._.≈∙-dec
d_'8776''8729''45'dec_28 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  Maybe AgdaAny ->
  Maybe AgdaAny ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_'8776''8729''45'dec_28 ~v0 ~v1 ~v2 ~v3
  = du_'8776''8729''45'dec_28
du_'8776''8729''45'dec_28 ::
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  Maybe AgdaAny ->
  Maybe AgdaAny ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du_'8776''8729''45'dec_28
  = coe
      MAlonzo.Code.Relation.Binary.Construct.Add.Point.Equality.du_'8776''8729''45'dec_66
-- Relation.Binary.Construct.Add.Supremum.Equality._.≈∙-irrelevant
d_'8776''8729''45'irrelevant_30 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  Maybe AgdaAny ->
  Maybe AgdaAny ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Point.Equality.T__'8776''8729'__20 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Point.Equality.T__'8776''8729'__20 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8776''8729''45'irrelevant_30 = erased
-- Relation.Binary.Construct.Add.Supremum.Equality._.≈∙-isDecEquivalence
d_'8776''8729''45'isDecEquivalence_32 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecEquivalence_48 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecEquivalence_48
d_'8776''8729''45'isDecEquivalence_32 ~v0 ~v1 ~v2 ~v3
  = du_'8776''8729''45'isDecEquivalence_32
du_'8776''8729''45'isDecEquivalence_32 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecEquivalence_48 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecEquivalence_48
du_'8776''8729''45'isDecEquivalence_32
  = coe
      MAlonzo.Code.Relation.Binary.Construct.Add.Point.Equality.du_'8776''8729''45'isDecEquivalence_128
-- Relation.Binary.Construct.Add.Supremum.Equality._.≈∙-isEquivalence
d_'8776''8729''45'isEquivalence_34 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
d_'8776''8729''45'isEquivalence_34 ~v0 ~v1 ~v2 ~v3
  = du_'8776''8729''45'isEquivalence_34
du_'8776''8729''45'isEquivalence_34 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_28
du_'8776''8729''45'isEquivalence_34
  = coe
      MAlonzo.Code.Relation.Binary.Construct.Add.Point.Equality.du_'8776''8729''45'isEquivalence_108
-- Relation.Binary.Construct.Add.Supremum.Equality._.≈∙-refl
d_'8776''8729''45'refl_36 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  Maybe AgdaAny ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Point.Equality.T__'8776''8729'__20
d_'8776''8729''45'refl_36 ~v0 ~v1 ~v2 ~v3
  = du_'8776''8729''45'refl_36
du_'8776''8729''45'refl_36 ::
  (AgdaAny -> AgdaAny) ->
  Maybe AgdaAny ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Point.Equality.T__'8776''8729'__20
du_'8776''8729''45'refl_36
  = coe
      MAlonzo.Code.Relation.Binary.Construct.Add.Point.Equality.du_'8776''8729''45'refl_38
-- Relation.Binary.Construct.Add.Supremum.Equality._.≈∙-substitutive
d_'8776''8729''45'substitutive_38 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  ((AgdaAny -> ()) ->
   AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (Maybe AgdaAny -> ()) ->
  Maybe AgdaAny ->
  Maybe AgdaAny ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Point.Equality.T__'8776''8729'__20 ->
  AgdaAny -> AgdaAny
d_'8776''8729''45'substitutive_38 ~v0 ~v1 ~v2 ~v3
  = du_'8776''8729''45'substitutive_38
du_'8776''8729''45'substitutive_38 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  ((AgdaAny -> ()) ->
   AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (Maybe AgdaAny -> ()) ->
  Maybe AgdaAny ->
  Maybe AgdaAny ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Point.Equality.T__'8776''8729'__20 ->
  AgdaAny -> AgdaAny
du_'8776''8729''45'substitutive_38 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Relation.Binary.Construct.Add.Point.Equality.du_'8776''8729''45'substitutive_96
      v1 v2 v3 v4 v5
-- Relation.Binary.Construct.Add.Supremum.Equality._.≈∙-sym
d_'8776''8729''45'sym_40 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  Maybe AgdaAny ->
  Maybe AgdaAny ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Point.Equality.T__'8776''8729'__20 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Point.Equality.T__'8776''8729'__20
d_'8776''8729''45'sym_40 ~v0 ~v1 ~v2 ~v3
  = du_'8776''8729''45'sym_40
du_'8776''8729''45'sym_40 ::
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  Maybe AgdaAny ->
  Maybe AgdaAny ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Point.Equality.T__'8776''8729'__20 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Point.Equality.T__'8776''8729'__20
du_'8776''8729''45'sym_40
  = coe
      MAlonzo.Code.Relation.Binary.Construct.Add.Point.Equality.du_'8776''8729''45'sym_46
-- Relation.Binary.Construct.Add.Supremum.Equality._.≈∙-trans
d_'8776''8729''45'trans_42 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  Maybe AgdaAny ->
  Maybe AgdaAny ->
  Maybe AgdaAny ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Point.Equality.T__'8776''8729'__20 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Point.Equality.T__'8776''8729'__20 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Point.Equality.T__'8776''8729'__20
d_'8776''8729''45'trans_42 ~v0 ~v1 ~v2 ~v3
  = du_'8776''8729''45'trans_42
du_'8776''8729''45'trans_42 ::
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  Maybe AgdaAny ->
  Maybe AgdaAny ->
  Maybe AgdaAny ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Point.Equality.T__'8776''8729'__20 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Point.Equality.T__'8776''8729'__20 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Point.Equality.T__'8776''8729'__20
du_'8776''8729''45'trans_42
  = coe
      MAlonzo.Code.Relation.Binary.Construct.Add.Point.Equality.du_'8776''8729''45'trans_54
