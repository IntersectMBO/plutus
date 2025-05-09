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

module MAlonzo.Code.Relation.Binary.Construct.Add.Extrema.NonStrict where

import Data.Text qualified
import MAlonzo.Code.Agda.Builtin.Equality qualified
import MAlonzo.Code.Agda.Builtin.Maybe qualified
import MAlonzo.Code.Agda.Primitive qualified
import MAlonzo.Code.Data.Sum.Base qualified
import MAlonzo.Code.Function.Base qualified
import MAlonzo.Code.Relation.Binary.Construct.Add.Infimum.NonStrict qualified
import MAlonzo.Code.Relation.Binary.Construct.Add.Point.Equality qualified
import MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.NonStrict qualified
import MAlonzo.Code.Relation.Binary.Structures qualified
import MAlonzo.Code.Relation.Nullary.Decidable.Core qualified
import MAlonzo.RTE (AgdaAny, add64, addInt, coe, eq64, eqInt, erased, geqInt, lt64, ltInt, mul64,
                    mulInt, quot64, quotInt, rem64, remInt, sub64, subInt, word64FromNat,
                    word64ToNat)
import MAlonzo.RTE qualified

-- Relation.Binary.Construct.Add.Extrema.NonStrict.Inf._≤₋_
d__'8804''8331'__22 a0 a1 a2 a3 a4 a5 = ()
-- Relation.Binary.Construct.Add.Extrema.NonStrict.Sup._≤⁺_
d__'8804''8314'__76 a0 a1 a2 a3 a4 a5 = ()
-- Relation.Binary.Construct.Add.Extrema.NonStrict.⊥±≤_
d_'8869''177''8804'__148 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  Maybe (Maybe AgdaAny) ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.NonStrict.T__'8804''8314'__20
d_'8869''177''8804'__148 ~v0 ~v1 ~v2 ~v3 v4
  = du_'8869''177''8804'__148 v4
du_'8869''177''8804'__148 ::
  Maybe (Maybe AgdaAny) ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.NonStrict.T__'8804''8314'__20
du_'8869''177''8804'__148 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v1
        -> coe
             seq (coe v1)
             (coe
                MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.NonStrict.C_'91'_'93'_26
                (coe
                   MAlonzo.Code.Relation.Binary.Construct.Add.Infimum.NonStrict.C_'8869''8331''8804'__24))
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.NonStrict.C__'8804''8868''8314'_30
      _ -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Construct.Add.Extrema.NonStrict._≤⊤±
d__'8804''8868''177'_154 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  Maybe (Maybe AgdaAny) ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.NonStrict.T__'8804''8314'__20
d__'8804''8868''177'_154 ~v0 ~v1 ~v2 ~v3 v4
  = du__'8804''8868''177'_154 v4
du__'8804''8868''177'_154 ::
  Maybe (Maybe AgdaAny) ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.NonStrict.T__'8804''8314'__20
du__'8804''8868''177'_154 v0
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v1
        -> coe
             seq (coe v1)
             (coe
                MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.NonStrict.C__'8804''8868''8314'_30)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.NonStrict.C__'8804''8868''8314'_30
      _ -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Construct.Add.Extrema.NonStrict.[≤]-injective
d_'91''8804''93''45'injective_162 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.NonStrict.T__'8804''8314'__20 ->
  AgdaAny
d_'91''8804''93''45'injective_162 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_'91''8804''93''45'injective_162
du_'91''8804''93''45'injective_162 ::
  MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.NonStrict.T__'8804''8314'__20 ->
  AgdaAny
du_'91''8804''93''45'injective_162
  = coe
      MAlonzo.Code.Function.Base.du__'8728''8242'__216
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Add.Infimum.NonStrict.du_'91''8804''93''45'injective_36)
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.NonStrict.du_'91''8804''93''45'injective_36)
-- Relation.Binary.Construct.Add.Extrema.NonStrict.≤±-trans
d_'8804''177''45'trans_164 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  Maybe (Maybe AgdaAny) ->
  Maybe (Maybe AgdaAny) ->
  Maybe (Maybe AgdaAny) ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.NonStrict.T__'8804''8314'__20 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.NonStrict.T__'8804''8314'__20 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.NonStrict.T__'8804''8314'__20
d_'8804''177''45'trans_164 ~v0 ~v1 ~v2 ~v3
  = du_'8804''177''45'trans_164
du_'8804''177''45'trans_164 ::
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  Maybe (Maybe AgdaAny) ->
  Maybe (Maybe AgdaAny) ->
  Maybe (Maybe AgdaAny) ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.NonStrict.T__'8804''8314'__20 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.NonStrict.T__'8804''8314'__20 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.NonStrict.T__'8804''8314'__20
du_'8804''177''45'trans_164
  = coe
      MAlonzo.Code.Function.Base.du__'8728''8242'__216
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.NonStrict.du_'8804''8314''45'trans_40)
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Add.Infimum.NonStrict.du_'8804''8331''45'trans_40)
-- Relation.Binary.Construct.Add.Extrema.NonStrict.≤±-minimum
d_'8804''177''45'minimum_166 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  Maybe (Maybe AgdaAny) ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.NonStrict.T__'8804''8314'__20
d_'8804''177''45'minimum_166 ~v0 ~v1 ~v2 ~v3
  = du_'8804''177''45'minimum_166
du_'8804''177''45'minimum_166 ::
  Maybe (Maybe AgdaAny) ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.NonStrict.T__'8804''8314'__20
du_'8804''177''45'minimum_166 = coe du_'8869''177''8804'__148
-- Relation.Binary.Construct.Add.Extrema.NonStrict.≤±-maximum
d_'8804''177''45'maximum_168 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  Maybe (Maybe AgdaAny) ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.NonStrict.T__'8804''8314'__20
d_'8804''177''45'maximum_168 ~v0 ~v1 ~v2 ~v3
  = du_'8804''177''45'maximum_168
du_'8804''177''45'maximum_168 ::
  Maybe (Maybe AgdaAny) ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.NonStrict.T__'8804''8314'__20
du_'8804''177''45'maximum_168 = coe du__'8804''8868''177'_154
-- Relation.Binary.Construct.Add.Extrema.NonStrict.≤±-dec
d_'8804''177''45'dec_170 ::
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
d_'8804''177''45'dec_170 ~v0 ~v1 ~v2 ~v3
  = du_'8804''177''45'dec_170
du_'8804''177''45'dec_170 ::
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  Maybe (Maybe AgdaAny) ->
  Maybe (Maybe AgdaAny) ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du_'8804''177''45'dec_170
  = coe
      MAlonzo.Code.Function.Base.du__'8728''8242'__216
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.NonStrict.du_'8804''8314''45'dec_56)
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Add.Infimum.NonStrict.du_'8804''8331''45'dec_56)
-- Relation.Binary.Construct.Add.Extrema.NonStrict.≤±-total
d_'8804''177''45'total_172 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30) ->
  Maybe (Maybe AgdaAny) ->
  Maybe (Maybe AgdaAny) -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_'8804''177''45'total_172 ~v0 ~v1 ~v2 ~v3
  = du_'8804''177''45'total_172
du_'8804''177''45'total_172 ::
  (AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30) ->
  Maybe (Maybe AgdaAny) ->
  Maybe (Maybe AgdaAny) -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_'8804''177''45'total_172
  = coe
      MAlonzo.Code.Function.Base.du__'8728''8242'__216
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.NonStrict.du_'8804''8314''45'total_72)
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Add.Infimum.NonStrict.du_'8804''8331''45'total_72)
-- Relation.Binary.Construct.Add.Extrema.NonStrict.≤±-irrelevant
d_'8804''177''45'irrelevant_174 ::
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
  MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.NonStrict.T__'8804''8314'__20 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.NonStrict.T__'8804''8314'__20 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8804''177''45'irrelevant_174 = erased
-- Relation.Binary.Construct.Add.Extrema.NonStrict.≤±-reflexive-≡
d_'8804''177''45'reflexive'45''8801'_176 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny) ->
  Maybe (Maybe AgdaAny) ->
  Maybe (Maybe AgdaAny) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.NonStrict.T__'8804''8314'__20
d_'8804''177''45'reflexive'45''8801'_176 ~v0 ~v1 ~v2 ~v3
  = du_'8804''177''45'reflexive'45''8801'_176
du_'8804''177''45'reflexive'45''8801'_176 ::
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny) ->
  Maybe (Maybe AgdaAny) ->
  Maybe (Maybe AgdaAny) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.NonStrict.T__'8804''8314'__20
du_'8804''177''45'reflexive'45''8801'_176
  = coe
      MAlonzo.Code.Function.Base.du__'8728''8242'__216
      (\ v0 v1 v2 v3 ->
         coe
           MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.NonStrict.du_'8804''8314''45'reflexive'45''8801'_100
           v0 v1)
      (\ v0 v1 v2 v3 ->
         coe
           MAlonzo.Code.Relation.Binary.Construct.Add.Infimum.NonStrict.du_'8804''8331''45'reflexive'45''8801'_100
           v0 v1)
-- Relation.Binary.Construct.Add.Extrema.NonStrict.≤±-antisym-≡
d_'8804''177''45'antisym'45''8801'_178 ::
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
  MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.NonStrict.T__'8804''8314'__20 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.NonStrict.T__'8804''8314'__20 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8804''177''45'antisym'45''8801'_178 = erased
-- Relation.Binary.Construct.Add.Extrema.NonStrict._._._≈∙_
d__'8776''8729'__190 a0 a1 a2 a3 a4 a5 a6 a7 = ()
-- Relation.Binary.Construct.Add.Extrema.NonStrict._.≤±-reflexive
d_'8804''177''45'reflexive_216 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  Maybe (Maybe AgdaAny) ->
  Maybe (Maybe AgdaAny) ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Point.Equality.T__'8776''8729'__20 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.NonStrict.T__'8804''8314'__20
d_'8804''177''45'reflexive_216 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_'8804''177''45'reflexive_216
du_'8804''177''45'reflexive_216 ::
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  Maybe (Maybe AgdaAny) ->
  Maybe (Maybe AgdaAny) ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Point.Equality.T__'8776''8729'__20 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.NonStrict.T__'8804''8314'__20
du_'8804''177''45'reflexive_216
  = coe
      MAlonzo.Code.Function.Base.du__'8728''8242'__216
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.NonStrict.du_'8804''8314''45'reflexive_158)
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Add.Infimum.NonStrict.du_'8804''8331''45'reflexive_158)
-- Relation.Binary.Construct.Add.Extrema.NonStrict._.≤±-antisym
d_'8804''177''45'antisym_218 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  Maybe (Maybe AgdaAny) ->
  Maybe (Maybe AgdaAny) ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.NonStrict.T__'8804''8314'__20 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.NonStrict.T__'8804''8314'__20 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Point.Equality.T__'8776''8729'__20
d_'8804''177''45'antisym_218 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_'8804''177''45'antisym_218
du_'8804''177''45'antisym_218 ::
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  Maybe (Maybe AgdaAny) ->
  Maybe (Maybe AgdaAny) ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.NonStrict.T__'8804''8314'__20 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.NonStrict.T__'8804''8314'__20 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Point.Equality.T__'8776''8729'__20
du_'8804''177''45'antisym_218
  = coe
      MAlonzo.Code.Function.Base.du__'8728''8242'__216
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.NonStrict.du_'8804''8314''45'antisym_166)
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Add.Infimum.NonStrict.du_'8804''8331''45'antisym_166)
-- Relation.Binary.Construct.Add.Extrema.NonStrict.≤±-isPreorder-≡
d_'8804''177''45'isPreorder'45''8801'_220 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPreorder_70 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPreorder_70
d_'8804''177''45'isPreorder'45''8801'_220 ~v0 ~v1 ~v2 ~v3
  = du_'8804''177''45'isPreorder'45''8801'_220
du_'8804''177''45'isPreorder'45''8801'_220 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsPreorder_70 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPreorder_70
du_'8804''177''45'isPreorder'45''8801'_220
  = coe
      MAlonzo.Code.Function.Base.du__'8728''8242'__216
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.NonStrict.du_'8804''8314''45'isPreorder'45''8801'_176)
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Add.Infimum.NonStrict.du_'8804''8331''45'isPreorder'45''8801'_176)
-- Relation.Binary.Construct.Add.Extrema.NonStrict.≤±-isPartialOrder-≡
d_'8804''177''45'isPartialOrder'45''8801'_222 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialOrder_174 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialOrder_174
d_'8804''177''45'isPartialOrder'45''8801'_222 ~v0 ~v1 ~v2 ~v3
  = du_'8804''177''45'isPartialOrder'45''8801'_222
du_'8804''177''45'isPartialOrder'45''8801'_222 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialOrder_174 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialOrder_174
du_'8804''177''45'isPartialOrder'45''8801'_222
  = coe
      MAlonzo.Code.Function.Base.du__'8728''8242'__216
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.NonStrict.du_'8804''8314''45'isPartialOrder'45''8801'_218)
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Add.Infimum.NonStrict.du_'8804''8331''45'isPartialOrder'45''8801'_218)
-- Relation.Binary.Construct.Add.Extrema.NonStrict.≤±-isDecPartialOrder-≡
d_'8804''177''45'isDecPartialOrder'45''8801'_224 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecPartialOrder_224 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecPartialOrder_224
d_'8804''177''45'isDecPartialOrder'45''8801'_224 ~v0 ~v1 ~v2 ~v3
  = du_'8804''177''45'isDecPartialOrder'45''8801'_224
du_'8804''177''45'isDecPartialOrder'45''8801'_224 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecPartialOrder_224 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecPartialOrder_224
du_'8804''177''45'isDecPartialOrder'45''8801'_224
  = coe
      MAlonzo.Code.Function.Base.du__'8728''8242'__216
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.NonStrict.du_'8804''8314''45'isDecPartialOrder'45''8801'_264)
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Add.Infimum.NonStrict.du_'8804''8331''45'isDecPartialOrder'45''8801'_264)
-- Relation.Binary.Construct.Add.Extrema.NonStrict.≤±-isTotalOrder-≡
d_'8804''177''45'isTotalOrder'45''8801'_226 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsTotalOrder_404 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsTotalOrder_404
d_'8804''177''45'isTotalOrder'45''8801'_226 ~v0 ~v1 ~v2 ~v3
  = du_'8804''177''45'isTotalOrder'45''8801'_226
du_'8804''177''45'isTotalOrder'45''8801'_226 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsTotalOrder_404 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsTotalOrder_404
du_'8804''177''45'isTotalOrder'45''8801'_226
  = coe
      MAlonzo.Code.Function.Base.du__'8728''8242'__216
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.NonStrict.du_'8804''8314''45'isTotalOrder'45''8801'_322)
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Add.Infimum.NonStrict.du_'8804''8331''45'isTotalOrder'45''8801'_322)
-- Relation.Binary.Construct.Add.Extrema.NonStrict.≤±-isDecTotalOrder-≡
d_'8804''177''45'isDecTotalOrder'45''8801'_228 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecTotalOrder_460 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecTotalOrder_460
d_'8804''177''45'isDecTotalOrder'45''8801'_228 ~v0 ~v1 ~v2 ~v3
  = du_'8804''177''45'isDecTotalOrder'45''8801'_228
du_'8804''177''45'isDecTotalOrder'45''8801'_228 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecTotalOrder_460 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecTotalOrder_460
du_'8804''177''45'isDecTotalOrder'45''8801'_228
  = coe
      MAlonzo.Code.Function.Base.du__'8728''8242'__216
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.NonStrict.du_'8804''8314''45'isDecTotalOrder'45''8801'_374)
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Add.Infimum.NonStrict.du_'8804''8331''45'isDecTotalOrder'45''8801'_374)
-- Relation.Binary.Construct.Add.Extrema.NonStrict._._._≈∙_
d__'8776''8729'__240 a0 a1 a2 a3 a4 a5 a6 a7 = ()
-- Relation.Binary.Construct.Add.Extrema.NonStrict._.≤±-isPreorder
d_'8804''177''45'isPreorder_266 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPreorder_70 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPreorder_70
d_'8804''177''45'isPreorder_266 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_'8804''177''45'isPreorder_266
du_'8804''177''45'isPreorder_266 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsPreorder_70 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPreorder_70
du_'8804''177''45'isPreorder_266
  = coe
      MAlonzo.Code.Function.Base.du__'8728''8242'__216
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.NonStrict.du_'8804''8314''45'isPreorder_480)
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Add.Infimum.NonStrict.du_'8804''8331''45'isPreorder_480)
-- Relation.Binary.Construct.Add.Extrema.NonStrict._.≤±-isPartialOrder
d_'8804''177''45'isPartialOrder_268 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialOrder_174 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialOrder_174
d_'8804''177''45'isPartialOrder_268 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_'8804''177''45'isPartialOrder_268
du_'8804''177''45'isPartialOrder_268 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialOrder_174 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialOrder_174
du_'8804''177''45'isPartialOrder_268
  = coe
      MAlonzo.Code.Function.Base.du__'8728''8242'__216
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.NonStrict.du_'8804''8314''45'isPartialOrder_522)
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Add.Infimum.NonStrict.du_'8804''8331''45'isPartialOrder_522)
-- Relation.Binary.Construct.Add.Extrema.NonStrict._.≤±-isDecPartialOrder
d_'8804''177''45'isDecPartialOrder_270 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecPartialOrder_224 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecPartialOrder_224
d_'8804''177''45'isDecPartialOrder_270 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_'8804''177''45'isDecPartialOrder_270
du_'8804''177''45'isDecPartialOrder_270 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecPartialOrder_224 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecPartialOrder_224
du_'8804''177''45'isDecPartialOrder_270
  = coe
      MAlonzo.Code.Function.Base.du__'8728''8242'__216
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.NonStrict.du_'8804''8314''45'isDecPartialOrder_568)
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Add.Infimum.NonStrict.du_'8804''8331''45'isDecPartialOrder_568)
-- Relation.Binary.Construct.Add.Extrema.NonStrict._.≤±-isTotalOrder
d_'8804''177''45'isTotalOrder_272 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsTotalOrder_404 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsTotalOrder_404
d_'8804''177''45'isTotalOrder_272 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_'8804''177''45'isTotalOrder_272
du_'8804''177''45'isTotalOrder_272 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsTotalOrder_404 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsTotalOrder_404
du_'8804''177''45'isTotalOrder_272
  = coe
      MAlonzo.Code.Function.Base.du__'8728''8242'__216
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.NonStrict.du_'8804''8314''45'isTotalOrder_626)
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Add.Infimum.NonStrict.du_'8804''8331''45'isTotalOrder_626)
-- Relation.Binary.Construct.Add.Extrema.NonStrict._.≤±-isDecTotalOrder
d_'8804''177''45'isDecTotalOrder_274 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecTotalOrder_460 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecTotalOrder_460
d_'8804''177''45'isDecTotalOrder_274 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_'8804''177''45'isDecTotalOrder_274
du_'8804''177''45'isDecTotalOrder_274 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecTotalOrder_460 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecTotalOrder_460
du_'8804''177''45'isDecTotalOrder_274
  = coe
      MAlonzo.Code.Function.Base.du__'8728''8242'__216
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.NonStrict.du_'8804''8314''45'isDecTotalOrder_678)
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Add.Infimum.NonStrict.du_'8804''8331''45'isDecTotalOrder_678)
