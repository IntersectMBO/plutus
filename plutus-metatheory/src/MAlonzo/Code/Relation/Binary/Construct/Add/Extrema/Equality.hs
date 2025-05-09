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

module MAlonzo.Code.Relation.Binary.Construct.Add.Extrema.Equality where

import Data.Text qualified
import MAlonzo.Code.Agda.Builtin.Equality qualified
import MAlonzo.Code.Agda.Primitive qualified
import MAlonzo.Code.Function.Base qualified
import MAlonzo.Code.Relation.Binary.Construct.Add.Point.Equality qualified
import MAlonzo.Code.Relation.Binary.Structures qualified
import MAlonzo.Code.Relation.Nullary.Decidable.Core qualified
import MAlonzo.RTE (AgdaAny, add64, addInt, coe, eq64, eqInt, erased, geqInt, lt64, ltInt, mul64,
                    mulInt, quot64, quotInt, rem64, remInt, sub64, subInt, word64FromNat,
                    word64ToNat)
import MAlonzo.RTE qualified

-- Relation.Binary.Construct.Add.Extrema.Equality.Inf._≈∙_
d__'8776''8729'__22 a0 a1 a2 a3 a4 a5 = ()
-- Relation.Binary.Construct.Add.Extrema.Equality.Sup._≈∙_
d__'8776''8729'__54 a0 a1 a2 a3 a4 a5 = ()
-- Relation.Binary.Construct.Add.Extrema.Equality.[≈]-injective
d_'91''8776''93''45'injective_96 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Point.Equality.T__'8776''8729'__20 ->
  AgdaAny
d_'91''8776''93''45'injective_96 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_'91''8776''93''45'injective_96
du_'91''8776''93''45'injective_96 ::
  MAlonzo.Code.Relation.Binary.Construct.Add.Point.Equality.T__'8776''8729'__20 ->
  AgdaAny
du_'91''8776''93''45'injective_96
  = coe
      MAlonzo.Code.Function.Base.du__'8728''8242'__216
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Add.Point.Equality.du_'91''8776''93''45'injective_34)
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Add.Point.Equality.du_'91''8776''93''45'injective_34)
-- Relation.Binary.Construct.Add.Extrema.Equality.≈±-refl
d_'8776''177''45'refl_98 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  Maybe (Maybe AgdaAny) ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Point.Equality.T__'8776''8729'__20
d_'8776''177''45'refl_98 ~v0 ~v1 ~v2 ~v3
  = du_'8776''177''45'refl_98
du_'8776''177''45'refl_98 ::
  (AgdaAny -> AgdaAny) ->
  Maybe (Maybe AgdaAny) ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Point.Equality.T__'8776''8729'__20
du_'8776''177''45'refl_98
  = coe
      MAlonzo.Code.Function.Base.du__'8728''8242'__216
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Add.Point.Equality.du_'8776''8729''45'refl_38)
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Add.Point.Equality.du_'8776''8729''45'refl_38)
-- Relation.Binary.Construct.Add.Extrema.Equality.≈±-sym
d_'8776''177''45'sym_100 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  Maybe (Maybe AgdaAny) ->
  Maybe (Maybe AgdaAny) ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Point.Equality.T__'8776''8729'__20 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Point.Equality.T__'8776''8729'__20
d_'8776''177''45'sym_100 ~v0 ~v1 ~v2 ~v3
  = du_'8776''177''45'sym_100
du_'8776''177''45'sym_100 ::
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  Maybe (Maybe AgdaAny) ->
  Maybe (Maybe AgdaAny) ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Point.Equality.T__'8776''8729'__20 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Point.Equality.T__'8776''8729'__20
du_'8776''177''45'sym_100
  = coe
      MAlonzo.Code.Function.Base.du__'8728''8242'__216
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Add.Point.Equality.du_'8776''8729''45'sym_46)
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Add.Point.Equality.du_'8776''8729''45'sym_46)
-- Relation.Binary.Construct.Add.Extrema.Equality.≈±-trans
d_'8776''177''45'trans_102 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  Maybe (Maybe AgdaAny) ->
  Maybe (Maybe AgdaAny) ->
  Maybe (Maybe AgdaAny) ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Point.Equality.T__'8776''8729'__20 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Point.Equality.T__'8776''8729'__20 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Point.Equality.T__'8776''8729'__20
d_'8776''177''45'trans_102 ~v0 ~v1 ~v2 ~v3
  = du_'8776''177''45'trans_102
du_'8776''177''45'trans_102 ::
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  Maybe (Maybe AgdaAny) ->
  Maybe (Maybe AgdaAny) ->
  Maybe (Maybe AgdaAny) ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Point.Equality.T__'8776''8729'__20 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Point.Equality.T__'8776''8729'__20 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Point.Equality.T__'8776''8729'__20
du_'8776''177''45'trans_102
  = coe
      MAlonzo.Code.Function.Base.du__'8728''8242'__216
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Add.Point.Equality.du_'8776''8729''45'trans_54)
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Add.Point.Equality.du_'8776''8729''45'trans_54)
-- Relation.Binary.Construct.Add.Extrema.Equality.≈±-dec
d_'8776''177''45'dec_104 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  Maybe (Maybe AgdaAny) ->
  Maybe (Maybe AgdaAny) ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_'8776''177''45'dec_104 ~v0 ~v1 ~v2 ~v3
  = du_'8776''177''45'dec_104
du_'8776''177''45'dec_104 ::
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  Maybe (Maybe AgdaAny) ->
  Maybe (Maybe AgdaAny) ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du_'8776''177''45'dec_104
  = coe
      MAlonzo.Code.Function.Base.du__'8728''8242'__216
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Add.Point.Equality.du_'8776''8729''45'dec_66)
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Add.Point.Equality.du_'8776''8729''45'dec_66)
-- Relation.Binary.Construct.Add.Extrema.Equality.≈±-irrelevant
d_'8776''177''45'irrelevant_106 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  Maybe (Maybe AgdaAny) ->
  Maybe (Maybe AgdaAny) ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Point.Equality.T__'8776''8729'__20 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Point.Equality.T__'8776''8729'__20 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8776''177''45'irrelevant_106 = erased
-- Relation.Binary.Construct.Add.Extrema.Equality.≈±-substitutive
d_'8776''177''45'substitutive_110 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  ((AgdaAny -> ()) ->
   AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (Maybe (Maybe AgdaAny) -> ()) ->
  Maybe (Maybe AgdaAny) ->
  Maybe (Maybe AgdaAny) ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Point.Equality.T__'8776''8729'__20 ->
  AgdaAny -> AgdaAny
d_'8776''177''45'substitutive_110 ~v0 ~v1 ~v2 ~v3 ~v4
  = du_'8776''177''45'substitutive_110
du_'8776''177''45'substitutive_110 ::
  ((AgdaAny -> ()) ->
   AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (Maybe (Maybe AgdaAny) -> ()) ->
  Maybe (Maybe AgdaAny) ->
  Maybe (Maybe AgdaAny) ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Point.Equality.T__'8776''8729'__20 ->
  AgdaAny -> AgdaAny
du_'8776''177''45'substitutive_110
  = coe
      MAlonzo.Code.Function.Base.du__'8728''8242'__216
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Add.Point.Equality.du_'8776''8729''45'substitutive_96)
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Add.Point.Equality.du_'8776''8729''45'substitutive_96)
-- Relation.Binary.Construct.Add.Extrema.Equality.≈±-isEquivalence
d_'8776''177''45'isEquivalence_112 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_'8776''177''45'isEquivalence_112 ~v0 ~v1 ~v2 ~v3
  = du_'8776''177''45'isEquivalence_112
du_'8776''177''45'isEquivalence_112 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
du_'8776''177''45'isEquivalence_112
  = coe
      MAlonzo.Code.Function.Base.du__'8728''8242'__216
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Add.Point.Equality.du_'8776''8729''45'isEquivalence_108)
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Add.Point.Equality.du_'8776''8729''45'isEquivalence_108)
-- Relation.Binary.Construct.Add.Extrema.Equality.≈±-isDecEquivalence
d_'8776''177''45'isDecEquivalence_114 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecEquivalence_44 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecEquivalence_44
d_'8776''177''45'isDecEquivalence_114 ~v0 ~v1 ~v2 ~v3
  = du_'8776''177''45'isDecEquivalence_114
du_'8776''177''45'isDecEquivalence_114 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecEquivalence_44 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecEquivalence_44
du_'8776''177''45'isDecEquivalence_114
  = coe
      MAlonzo.Code.Function.Base.du__'8728''8242'__216
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Add.Point.Equality.du_'8776''8729''45'isDecEquivalence_128)
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Add.Point.Equality.du_'8776''8729''45'isDecEquivalence_128)
