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

module MAlonzo.Code.Relation.Binary.Construct.Add.Point.Equality where

import Data.Text qualified
import MAlonzo.Code.Agda.Builtin.Bool qualified
import MAlonzo.Code.Agda.Builtin.Equality qualified
import MAlonzo.Code.Agda.Builtin.Maybe qualified
import MAlonzo.Code.Agda.Primitive qualified
import MAlonzo.Code.Function.Base qualified
import MAlonzo.Code.Relation.Binary.Structures qualified
import MAlonzo.Code.Relation.Nullary.Decidable.Core qualified
import MAlonzo.Code.Relation.Nullary.Reflects qualified
import MAlonzo.RTE (AgdaAny, add64, addInt, coe, eq64, eqInt, erased, geqInt, lt64, ltInt, mul64,
                    mulInt, quot64, quotInt, rem64, remInt, sub64, subInt, word64FromNat,
                    word64ToNat)
import MAlonzo.RTE qualified

-- Relation.Binary.Construct.Add.Point.Equality._≈∙_
d__'8776''8729'__20 a0 a1 a2 a3 a4 a5 = ()
data T__'8776''8729'__20
  = C_'8729''8776''8729'_22 | C_'91'_'93'_28 AgdaAny
-- Relation.Binary.Construct.Add.Point.Equality.[≈]-injective
d_'91''8776''93''45'injective_34 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  AgdaAny -> AgdaAny -> T__'8776''8729'__20 -> AgdaAny
d_'91''8776''93''45'injective_34 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_'91''8776''93''45'injective_34 v6
du_'91''8776''93''45'injective_34 :: T__'8776''8729'__20 -> AgdaAny
du_'91''8776''93''45'injective_34 v0
  = case coe v0 of
      C_'91'_'93'_28 v3 -> coe v3
      _                 -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Construct.Add.Point.Equality.≈∙-refl
d_'8776''8729''45'refl_38 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) -> Maybe AgdaAny -> T__'8776''8729'__20
d_'8776''8729''45'refl_38 ~v0 ~v1 ~v2 ~v3 v4 v5
  = du_'8776''8729''45'refl_38 v4 v5
du_'8776''8729''45'refl_38 ::
  (AgdaAny -> AgdaAny) -> Maybe AgdaAny -> T__'8776''8729'__20
du_'8776''8729''45'refl_38 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
        -> coe C_'91'_'93'_28 (coe v0 v2)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe C_'8729''8776''8729'_22
      _ -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Construct.Add.Point.Equality.≈∙-sym
d_'8776''8729''45'sym_46 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  Maybe AgdaAny ->
  Maybe AgdaAny -> T__'8776''8729'__20 -> T__'8776''8729'__20
d_'8776''8729''45'sym_46 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7
  = du_'8776''8729''45'sym_46 v4 v5 v6 v7
du_'8776''8729''45'sym_46 ::
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  Maybe AgdaAny ->
  Maybe AgdaAny -> T__'8776''8729'__20 -> T__'8776''8729'__20
du_'8776''8729''45'sym_46 v0 v1 v2 v3
  = case coe v3 of
      C_'8729''8776''8729'_22 -> coe v3
      C_'91'_'93'_28 v6
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v7
               -> case coe v2 of
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v8
                      -> coe C_'91'_'93'_28 (coe v0 v7 v8 v6)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Construct.Add.Point.Equality.≈∙-trans
d_'8776''8729''45'trans_54 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  Maybe AgdaAny ->
  Maybe AgdaAny ->
  Maybe AgdaAny ->
  T__'8776''8729'__20 -> T__'8776''8729'__20 -> T__'8776''8729'__20
d_'8776''8729''45'trans_54 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 v8 v9
  = du_'8776''8729''45'trans_54 v4 v5 v6 v7 v8 v9
du_'8776''8729''45'trans_54 ::
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  Maybe AgdaAny ->
  Maybe AgdaAny ->
  Maybe AgdaAny ->
  T__'8776''8729'__20 -> T__'8776''8729'__20 -> T__'8776''8729'__20
du_'8776''8729''45'trans_54 v0 v1 v2 v3 v4 v5
  = case coe v4 of
      C_'8729''8776''8729'_22 -> coe v5
      C_'91'_'93'_28 v8
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v9
               -> case coe v2 of
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v10
                      -> case coe v5 of
                           C_'91'_'93'_28 v13
                             -> case coe v3 of
                                  MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v14
                                    -> coe C_'91'_'93'_28 (coe v0 v9 v10 v14 v8 v13)
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Construct.Add.Point.Equality.≈∙-dec
d_'8776''8729''45'dec_66 ::
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
d_'8776''8729''45'dec_66 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_'8776''8729''45'dec_66 v4 v5 v6
du_'8776''8729''45'dec_66 ::
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  Maybe AgdaAny ->
  Maybe AgdaAny ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du_'8776''8729''45'dec_66 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_168
                    (coe C_'91'_'93'_28) (coe du_'91''8776''93''45'injective_34)
                    (coe v0 v3 v4)
             MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                    (coe
                       MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                       (coe C_'8729''8776''8729'_22))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Construct.Add.Point.Equality.≈∙-irrelevant
d_'8776''8729''45'irrelevant_84 ::
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
  T__'8776''8729'__20 ->
  T__'8776''8729'__20 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8776''8729''45'irrelevant_84 = erased
-- Relation.Binary.Construct.Add.Point.Equality.≈∙-substitutive
d_'8776''8729''45'substitutive_96 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  ((AgdaAny -> ()) ->
   AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (Maybe AgdaAny -> ()) ->
  Maybe AgdaAny ->
  Maybe AgdaAny -> T__'8776''8729'__20 -> AgdaAny -> AgdaAny
d_'8776''8729''45'substitutive_96 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6 v7 v8
                                  v9
  = du_'8776''8729''45'substitutive_96 v5 v6 v7 v8 v9
du_'8776''8729''45'substitutive_96 ::
  ((AgdaAny -> ()) ->
   AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (Maybe AgdaAny -> ()) ->
  Maybe AgdaAny ->
  Maybe AgdaAny -> T__'8776''8729'__20 -> AgdaAny -> AgdaAny
du_'8776''8729''45'substitutive_96 v0 v1 v2 v3 v4
  = case coe v4 of
      C_'8729''8776''8729'_22 -> coe (\ v5 -> v5)
      C_'91'_'93'_28 v7
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v8
               -> case coe v3 of
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v9
                      -> coe
                           v0
                           (coe
                              MAlonzo.Code.Function.Base.du__'8728''8242'__216 (coe v1)
                              (coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16))
                           v8 v9 v7
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Construct.Add.Point.Equality.≈∙-isEquivalence
d_'8776''8729''45'isEquivalence_108 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_'8776''8729''45'isEquivalence_108 ~v0 ~v1 ~v2 ~v3 v4
  = du_'8776''8729''45'isEquivalence_108 v4
du_'8776''8729''45'isEquivalence_108 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
du_'8776''8729''45'isEquivalence_108 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_IsEquivalence'46'constructor_745
      (coe
         du_'8776''8729''45'refl_38
         (coe MAlonzo.Code.Relation.Binary.Structures.d_refl_34 (coe v0)))
      (coe
         du_'8776''8729''45'sym_46
         (coe MAlonzo.Code.Relation.Binary.Structures.d_sym_36 (coe v0)))
      (coe
         du_'8776''8729''45'trans_54
         (coe MAlonzo.Code.Relation.Binary.Structures.d_trans_38 (coe v0)))
-- Relation.Binary.Construct.Add.Point.Equality.≈∙-isDecEquivalence
d_'8776''8729''45'isDecEquivalence_128 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecEquivalence_44 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecEquivalence_44
d_'8776''8729''45'isDecEquivalence_128 ~v0 ~v1 ~v2 ~v3 v4
  = du_'8776''8729''45'isDecEquivalence_128 v4
du_'8776''8729''45'isDecEquivalence_128 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecEquivalence_44 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecEquivalence_44
du_'8776''8729''45'isDecEquivalence_128 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_IsDecEquivalence'46'constructor_3083
      (coe
         du_'8776''8729''45'isEquivalence_108
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_50
            (coe v0)))
      (coe
         du_'8776''8729''45'dec_66
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d__'8799'__52 (coe v0)))
