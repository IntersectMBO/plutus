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

module MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.NonStrict where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Bool
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Data.Maybe.Properties
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Relation.Binary.Construct.Add.Point.Equality
import qualified MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties
import qualified MAlonzo.Code.Relation.Binary.Structures
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core
import qualified MAlonzo.Code.Relation.Nullary.Reflects

-- Relation.Binary.Construct.Add.Supremum.NonStrict._≤⁺_
d__'8804''8314'__20 a0 a1 a2 a3 a4 a5 = ()
data T__'8804''8314'__20
  = C_'91'_'93'_26 AgdaAny | C__'8804''8868''8314'_30
-- Relation.Binary.Construct.Add.Supremum.NonStrict.[≤]-injective
d_'91''8804''93''45'injective_36 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  AgdaAny -> AgdaAny -> T__'8804''8314'__20 -> AgdaAny
d_'91''8804''93''45'injective_36 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_'91''8804''93''45'injective_36 v6
du_'91''8804''93''45'injective_36 :: T__'8804''8314'__20 -> AgdaAny
du_'91''8804''93''45'injective_36 v0
  = case coe v0 of
      C_'91'_'93'_26 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Construct.Add.Supremum.NonStrict.≤⁺-trans
d_'8804''8314''45'trans_40 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  Maybe AgdaAny ->
  Maybe AgdaAny ->
  Maybe AgdaAny ->
  T__'8804''8314'__20 -> T__'8804''8314'__20 -> T__'8804''8314'__20
d_'8804''8314''45'trans_40 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 v8 v9
  = du_'8804''8314''45'trans_40 v4 v5 v6 v7 v8 v9
du_'8804''8314''45'trans_40 ::
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  Maybe AgdaAny ->
  Maybe AgdaAny ->
  Maybe AgdaAny ->
  T__'8804''8314'__20 -> T__'8804''8314'__20 -> T__'8804''8314'__20
du_'8804''8314''45'trans_40 v0 v1 v2 v3 v4 v5
  = case coe v4 of
      C_'91'_'93'_26 v8
        -> let v9 = seq (coe v5) (coe C__'8804''8868''8314'_30) in
           coe
             (case coe v1 of
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v10
                  -> let v11 = seq (coe v5) (coe C__'8804''8868''8314'_30) in
                     coe
                       (case coe v2 of
                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v12
                            -> case coe v5 of
                                 C_'91'_'93'_26 v15
                                   -> case coe v3 of
                                        MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v16
                                          -> coe C_'91'_'93'_26 (coe v0 v10 v12 v16 v8 v15)
                                        _ -> coe v11
                                 C__'8804''8868''8314'_30 -> coe C__'8804''8868''8314'_30
                                 _ -> MAlonzo.RTE.mazUnreachableError
                          _ -> coe v11)
                _ -> coe v9)
      C__'8804''8868''8314'_30
        -> coe seq (coe v5) (coe C__'8804''8868''8314'_30)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Construct.Add.Supremum.NonStrict.≤⁺-maximum
d_'8804''8314''45'maximum_54 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) -> Maybe AgdaAny -> T__'8804''8314'__20
d_'8804''8314''45'maximum_54 ~v0 ~v1 ~v2 ~v3
  = du_'8804''8314''45'maximum_54
du_'8804''8314''45'maximum_54 ::
  Maybe AgdaAny -> T__'8804''8314'__20
du_'8804''8314''45'maximum_54 v0 = coe C__'8804''8868''8314'_30
-- Relation.Binary.Construct.Add.Supremum.NonStrict.≤⁺-dec
d_'8804''8314''45'dec_56 ::
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
d_'8804''8314''45'dec_56 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_'8804''8314''45'dec_56 v4 v5 v6
du_'8804''8314''45'dec_56 ::
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  Maybe AgdaAny ->
  Maybe AgdaAny ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du_'8804''8314''45'dec_56 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                    (coe C_'91'_'93'_26) (coe du_'91''8804''93''45'injective_36)
                    (coe v0 v4 v3)
             MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
             (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
             (coe
                MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                (coe C__'8804''8868''8314'_30))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Construct.Add.Supremum.NonStrict.≤⁺-total
d_'8804''8314''45'total_72 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30) ->
  Maybe AgdaAny ->
  Maybe AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_'8804''8314''45'total_72 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_'8804''8314''45'total_72 v4 v5 v6
du_'8804''8314''45'total_72 ::
  (AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30) ->
  Maybe AgdaAny ->
  Maybe AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_'8804''8314''45'total_72 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
               -> coe
                    MAlonzo.Code.Data.Sum.Base.du_map_84 (coe C_'91'_'93'_26)
                    (coe C_'91'_'93'_26) (coe v0 v4 v3)
             MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                    (coe C__'8804''8868''8314'_30)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
             (coe C__'8804''8868''8314'_30)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Construct.Add.Supremum.NonStrict.≤⁺-irrelevant
d_'8804''8314''45'irrelevant_88 ::
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
  T__'8804''8314'__20 ->
  T__'8804''8314'__20 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8804''8314''45'irrelevant_88 = erased
-- Relation.Binary.Construct.Add.Supremum.NonStrict.≤⁺-reflexive-≡
d_'8804''8314''45'reflexive'45''8801'_100 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny) ->
  Maybe AgdaAny ->
  Maybe AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T__'8804''8314'__20
d_'8804''8314''45'reflexive'45''8801'_100 ~v0 ~v1 ~v2 ~v3 v4 v5 ~v6
                                          ~v7
  = du_'8804''8314''45'reflexive'45''8801'_100 v4 v5
du_'8804''8314''45'reflexive'45''8801'_100 ::
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny) ->
  Maybe AgdaAny -> T__'8804''8314'__20
du_'8804''8314''45'reflexive'45''8801'_100 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
        -> coe C_'91'_'93'_26 (coe v0 v2 v2 erased)
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe C__'8804''8868''8314'_30
      _ -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Construct.Add.Supremum.NonStrict.≤⁺-antisym-≡
d_'8804''8314''45'antisym'45''8801'_108 ::
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
  T__'8804''8314'__20 ->
  T__'8804''8314'__20 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8804''8314''45'antisym'45''8801'_108 = erased
-- Relation.Binary.Construct.Add.Supremum.NonStrict._._._≈∙_
d__'8776''8729'__128 a0 a1 a2 a3 a4 a5 a6 a7 = ()
-- Relation.Binary.Construct.Add.Supremum.NonStrict._.≤⁺-reflexive
d_'8804''8314''45'reflexive_158 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  Maybe AgdaAny ->
  Maybe AgdaAny ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Point.Equality.T__'8776''8729'__20 ->
  T__'8804''8314'__20
d_'8804''8314''45'reflexive_158 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 v8 v9
  = du_'8804''8314''45'reflexive_158 v6 v7 v8 v9
du_'8804''8314''45'reflexive_158 ::
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  Maybe AgdaAny ->
  Maybe AgdaAny ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Point.Equality.T__'8776''8729'__20 ->
  T__'8804''8314'__20
du_'8804''8314''45'reflexive_158 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Relation.Binary.Construct.Add.Point.Equality.C_'8729''8776''8729'_22
        -> coe C__'8804''8868''8314'_30
      MAlonzo.Code.Relation.Binary.Construct.Add.Point.Equality.C_'91'_'93'_28 v6
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v7
               -> case coe v2 of
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v8
                      -> coe C_'91'_'93'_26 (coe v0 v7 v8 v6)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Construct.Add.Supremum.NonStrict._.≤⁺-antisym
d_'8804''8314''45'antisym_166 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  Maybe AgdaAny ->
  Maybe AgdaAny ->
  T__'8804''8314'__20 ->
  T__'8804''8314'__20 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Point.Equality.T__'8776''8729'__20
d_'8804''8314''45'antisym_166 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 v8 v9
                              v10
  = du_'8804''8314''45'antisym_166 v6 v7 v8 v9 v10
du_'8804''8314''45'antisym_166 ::
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  Maybe AgdaAny ->
  Maybe AgdaAny ->
  T__'8804''8314'__20 ->
  T__'8804''8314'__20 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Point.Equality.T__'8776''8729'__20
du_'8804''8314''45'antisym_166 v0 v1 v2 v3 v4
  = case coe v3 of
      C_'91'_'93'_26 v7
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v8
               -> case coe v2 of
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v9
                      -> case coe v4 of
                           C_'91'_'93'_26 v12
                             -> coe
                                  MAlonzo.Code.Relation.Binary.Construct.Add.Point.Equality.C_'91'_'93'_28
                                  (coe v0 v8 v9 v7 v12)
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C__'8804''8868''8314'_30
        -> coe
             seq (coe v4)
             (coe
                MAlonzo.Code.Relation.Binary.Construct.Add.Point.Equality.C_'8729''8776''8729'_22)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Construct.Add.Supremum.NonStrict.≤⁺-isPreorder-≡
d_'8804''8314''45'isPreorder'45''8801'_176 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPreorder_76 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPreorder_76
d_'8804''8314''45'isPreorder'45''8801'_176 ~v0 ~v1 ~v2 ~v3 v4
  = du_'8804''8314''45'isPreorder'45''8801'_176 v4
du_'8804''8314''45'isPreorder'45''8801'_176 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsPreorder_76 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPreorder_76
du_'8804''8314''45'isPreorder'45''8801'_176 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_constructor_126
      (coe
         MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties.du_isEquivalence_396)
      (\ v1 v2 v3 ->
         coe
           du_'8804''8314''45'reflexive'45''8801'_100
           (coe
              MAlonzo.Code.Relation.Binary.Structures.d_reflexive_88 (coe v0))
           v1)
      (coe
         du_'8804''8314''45'trans_40
         (coe MAlonzo.Code.Relation.Binary.Structures.d_trans_90 (coe v0)))
-- Relation.Binary.Construct.Add.Supremum.NonStrict.≤⁺-isPartialOrder-≡
d_'8804''8314''45'isPartialOrder'45''8801'_218 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialOrder_248 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialOrder_248
d_'8804''8314''45'isPartialOrder'45''8801'_218 ~v0 ~v1 ~v2 ~v3 v4
  = du_'8804''8314''45'isPartialOrder'45''8801'_218 v4
du_'8804''8314''45'isPartialOrder'45''8801'_218 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialOrder_248 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialOrder_248
du_'8804''8314''45'isPartialOrder'45''8801'_218 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_constructor_294
      (coe
         du_'8804''8314''45'isPreorder'45''8801'_176
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256 (coe v0)))
      erased
-- Relation.Binary.Construct.Add.Supremum.NonStrict.≤⁺-isDecPartialOrder-≡
d_'8804''8314''45'isDecPartialOrder'45''8801'_264 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecPartialOrder_300 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecPartialOrder_300
d_'8804''8314''45'isDecPartialOrder'45''8801'_264 ~v0 ~v1 ~v2 ~v3
                                                  v4
  = du_'8804''8314''45'isDecPartialOrder'45''8801'_264 v4
du_'8804''8314''45'isDecPartialOrder'45''8801'_264 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecPartialOrder_300 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecPartialOrder_300
du_'8804''8314''45'isDecPartialOrder'45''8801'_264 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_constructor_364
      (coe
         du_'8804''8314''45'isPartialOrder'45''8801'_218
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPartialOrder_310
            (coe v0)))
      (coe
         MAlonzo.Code.Data.Maybe.Properties.du_'8801''45'dec_24
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d__'8799'__312 (coe v0)))
      (coe
         du_'8804''8314''45'dec_56
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d__'8804''63'__314
            (coe v0)))
-- Relation.Binary.Construct.Add.Supremum.NonStrict.≤⁺-isTotalOrder-≡
d_'8804''8314''45'isTotalOrder'45''8801'_324 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsTotalOrder_488 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsTotalOrder_488
d_'8804''8314''45'isTotalOrder'45''8801'_324 ~v0 ~v1 ~v2 ~v3 v4
  = du_'8804''8314''45'isTotalOrder'45''8801'_324 v4
du_'8804''8314''45'isTotalOrder'45''8801'_324 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsTotalOrder_488 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsTotalOrder_488
du_'8804''8314''45'isTotalOrder'45''8801'_324 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_constructor_540
      (coe
         du_'8804''8314''45'isPartialOrder'45''8801'_218
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPartialOrder_496
            (coe v0)))
      (coe
         du_'8804''8314''45'total_72
         (coe MAlonzo.Code.Relation.Binary.Structures.d_total_498 (coe v0)))
-- Relation.Binary.Construct.Add.Supremum.NonStrict.≤⁺-isDecTotalOrder-≡
d_'8804''8314''45'isDecTotalOrder'45''8801'_376 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecTotalOrder_546 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecTotalOrder_546
d_'8804''8314''45'isDecTotalOrder'45''8801'_376 ~v0 ~v1 ~v2 ~v3 v4
  = du_'8804''8314''45'isDecTotalOrder'45''8801'_376 v4
du_'8804''8314''45'isDecTotalOrder'45''8801'_376 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecTotalOrder_546 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecTotalOrder_546
du_'8804''8314''45'isDecTotalOrder'45''8801'_376 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_constructor_618
      (coe
         du_'8804''8314''45'isTotalOrder'45''8801'_324
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isTotalOrder_556
            (coe v0)))
      (coe
         MAlonzo.Code.Data.Maybe.Properties.du_'8801''45'dec_24
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d__'8799'__558 (coe v0)))
      (coe
         du_'8804''8314''45'dec_56
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d__'8804''63'__560
            (coe v0)))
-- Relation.Binary.Construct.Add.Supremum.NonStrict._._._≈∙_
d__'8776''8729'__454 a0 a1 a2 a3 a4 a5 a6 a7 = ()
-- Relation.Binary.Construct.Add.Supremum.NonStrict._.≤⁺-isPreorder
d_'8804''8314''45'isPreorder_484 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPreorder_76 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPreorder_76
d_'8804''8314''45'isPreorder_484 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_'8804''8314''45'isPreorder_484 v6
du_'8804''8314''45'isPreorder_484 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsPreorder_76 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPreorder_76
du_'8804''8314''45'isPreorder_484 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_constructor_126
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Add.Point.Equality.du_'8776''8729''45'isEquivalence_108
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_86
            (coe v0)))
      (coe
         du_'8804''8314''45'reflexive_158
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_reflexive_88 (coe v0)))
      (coe
         du_'8804''8314''45'trans_40
         (coe MAlonzo.Code.Relation.Binary.Structures.d_trans_90 (coe v0)))
-- Relation.Binary.Construct.Add.Supremum.NonStrict._.≤⁺-isPartialOrder
d_'8804''8314''45'isPartialOrder_526 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialOrder_248 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialOrder_248
d_'8804''8314''45'isPartialOrder_526 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_'8804''8314''45'isPartialOrder_526 v6
du_'8804''8314''45'isPartialOrder_526 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialOrder_248 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialOrder_248
du_'8804''8314''45'isPartialOrder_526 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_constructor_294
      (coe
         du_'8804''8314''45'isPreorder_484
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPreorder_256 (coe v0)))
      (coe
         du_'8804''8314''45'antisym_166
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_antisym_258 (coe v0)))
-- Relation.Binary.Construct.Add.Supremum.NonStrict._.≤⁺-isDecPartialOrder
d_'8804''8314''45'isDecPartialOrder_572 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecPartialOrder_300 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecPartialOrder_300
d_'8804''8314''45'isDecPartialOrder_572 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_'8804''8314''45'isDecPartialOrder_572 v6
du_'8804''8314''45'isDecPartialOrder_572 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecPartialOrder_300 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecPartialOrder_300
du_'8804''8314''45'isDecPartialOrder_572 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_constructor_364
      (coe
         du_'8804''8314''45'isPartialOrder_526
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPartialOrder_310
            (coe v0)))
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Add.Point.Equality.du_'8776''8729''45'dec_66
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d__'8799'__312 (coe v0)))
      (coe
         du_'8804''8314''45'dec_56
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d__'8804''63'__314
            (coe v0)))
-- Relation.Binary.Construct.Add.Supremum.NonStrict._.≤⁺-isTotalOrder
d_'8804''8314''45'isTotalOrder_632 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsTotalOrder_488 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsTotalOrder_488
d_'8804''8314''45'isTotalOrder_632 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_'8804''8314''45'isTotalOrder_632 v6
du_'8804''8314''45'isTotalOrder_632 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsTotalOrder_488 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsTotalOrder_488
du_'8804''8314''45'isTotalOrder_632 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_constructor_540
      (coe
         du_'8804''8314''45'isPartialOrder_526
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isPartialOrder_496
            (coe v0)))
      (coe
         du_'8804''8314''45'total_72
         (coe MAlonzo.Code.Relation.Binary.Structures.d_total_498 (coe v0)))
-- Relation.Binary.Construct.Add.Supremum.NonStrict._.≤⁺-isDecTotalOrder
d_'8804''8314''45'isDecTotalOrder_684 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecTotalOrder_546 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecTotalOrder_546
d_'8804''8314''45'isDecTotalOrder_684 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_'8804''8314''45'isDecTotalOrder_684 v6
du_'8804''8314''45'isDecTotalOrder_684 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecTotalOrder_546 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecTotalOrder_546
du_'8804''8314''45'isDecTotalOrder_684 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_constructor_618
      (coe
         du_'8804''8314''45'isTotalOrder_632
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isTotalOrder_556
            (coe v0)))
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Add.Point.Equality.du_'8776''8729''45'dec_66
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d__'8799'__558 (coe v0)))
      (coe
         du_'8804''8314''45'dec_56
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d__'8804''63'__560
            (coe v0)))
