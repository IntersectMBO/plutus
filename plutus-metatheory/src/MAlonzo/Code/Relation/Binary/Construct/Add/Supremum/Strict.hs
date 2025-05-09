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

module MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict where

import Data.Text qualified
import MAlonzo.Code.Agda.Builtin.Bool qualified
import MAlonzo.Code.Agda.Builtin.Equality qualified
import MAlonzo.Code.Agda.Builtin.Maybe qualified
import MAlonzo.Code.Agda.Builtin.Sigma qualified
import MAlonzo.Code.Agda.Primitive qualified
import MAlonzo.Code.Data.Irrelevant qualified
import MAlonzo.Code.Data.Maybe.Properties qualified
import MAlonzo.Code.Data.Product.Base qualified
import MAlonzo.Code.Relation.Binary.Construct.Add.Point.Equality qualified
import MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.NonStrict qualified
import MAlonzo.Code.Relation.Binary.Definitions qualified
import MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties qualified
import MAlonzo.Code.Relation.Binary.Structures qualified
import MAlonzo.Code.Relation.Nullary.Decidable.Core qualified
import MAlonzo.Code.Relation.Nullary.Reflects qualified
import MAlonzo.RTE (AgdaAny, add64, addInt, coe, eq64, eqInt, erased, geqInt, lt64, ltInt, mul64,
                    mulInt, quot64, quotInt, rem64, remInt, sub64, subInt, word64FromNat,
                    word64ToNat)
import MAlonzo.RTE qualified

-- Relation.Binary.Construct.Add.Supremum.Strict._<⁺_
d__'60''8314'__20 a0 a1 a2 a3 a4 a5 = ()
data T__'60''8314'__20
  = C_'91'_'93'_26 AgdaAny | C_'91'_'93''60''8868''8314'_30
-- Relation.Binary.Construct.Add.Supremum.Strict.[<]-injective
d_'91''60''93''45'injective_36 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  AgdaAny -> AgdaAny -> T__'60''8314'__20 -> AgdaAny
d_'91''60''93''45'injective_36 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_'91''60''93''45'injective_36 v6
du_'91''60''93''45'injective_36 :: T__'60''8314'__20 -> AgdaAny
du_'91''60''93''45'injective_36 v0
  = case coe v0 of
      C_'91'_'93'_26 v3 -> coe v3
      _                 -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Construct.Add.Supremum.Strict.<⁺-asym
d_'60''8314''45'asym_40 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  Maybe AgdaAny ->
  Maybe AgdaAny ->
  T__'60''8314'__20 ->
  T__'60''8314'__20 -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'60''8314''45'asym_40 = erased
-- Relation.Binary.Construct.Add.Supremum.Strict.<⁺-trans
d_'60''8314''45'trans_48 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  Maybe AgdaAny ->
  Maybe AgdaAny ->
  Maybe AgdaAny ->
  T__'60''8314'__20 -> T__'60''8314'__20 -> T__'60''8314'__20
d_'60''8314''45'trans_48 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 v8 v9
  = du_'60''8314''45'trans_48 v4 v5 v6 v7 v8 v9
du_'60''8314''45'trans_48 ::
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  Maybe AgdaAny ->
  Maybe AgdaAny ->
  Maybe AgdaAny ->
  T__'60''8314'__20 -> T__'60''8314'__20 -> T__'60''8314'__20
du_'60''8314''45'trans_48 v0 v1 v2 v3 v4 v5
  = case coe v4 of
      C_'91'_'93'_26 v8
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v9
               -> case coe v2 of
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v10
                      -> case coe v5 of
                           C_'91'_'93'_26 v13
                             -> case coe v3 of
                                  MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v14
                                    -> coe C_'91'_'93'_26 (coe v0 v9 v10 v14 v8 v13)
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           C_'91'_'93''60''8868''8314'_30
                             -> coe C_'91'_'93''60''8868''8314'_30
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Construct.Add.Supremum.Strict.<⁺-dec
d_'60''8314''45'dec_62 ::
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
d_'60''8314''45'dec_62 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_'60''8314''45'dec_62 v4 v5 v6
du_'60''8314''45'dec_62 ::
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  Maybe AgdaAny ->
  Maybe AgdaAny ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du_'60''8314''45'dec_62 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_168
                    (coe C_'91'_'93'_26) (coe du_'91''60''93''45'injective_36)
                    (coe v0 v3 v4)
             MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                    (coe
                       MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                       (coe C_'91'_'93''60''8868''8314'_30))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> coe
             seq (coe v2)
             (coe
                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Construct.Add.Supremum.Strict.<⁺-irrelevant
d_'60''8314''45'irrelevant_80 ::
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
  T__'60''8314'__20 ->
  T__'60''8314'__20 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'60''8314''45'irrelevant_80 = erased
-- Relation.Binary.Construct.Add.Supremum.Strict._._._≤⁺_
d__'8804''8314'__102 a0 a1 a2 a3 a4 a5 a6 a7 = ()
-- Relation.Binary.Construct.Add.Supremum.Strict._.<⁺-transʳ
d_'60''8314''45'trans'691'_154 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  Maybe AgdaAny ->
  Maybe AgdaAny ->
  Maybe AgdaAny ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.NonStrict.T__'8804''8314'__20 ->
  T__'60''8314'__20 -> T__'60''8314'__20
d_'60''8314''45'trans'691'_154 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 v8 v9
                               v10 v11
  = du_'60''8314''45'trans'691'_154 v6 v7 v8 v9 v10 v11
du_'60''8314''45'trans'691'_154 ::
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  Maybe AgdaAny ->
  Maybe AgdaAny ->
  Maybe AgdaAny ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.NonStrict.T__'8804''8314'__20 ->
  T__'60''8314'__20 -> T__'60''8314'__20
du_'60''8314''45'trans'691'_154 v0 v1 v2 v3 v4 v5
  = case coe v4 of
      MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.NonStrict.C_'91'_'93'_26 v8
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v9
               -> case coe v2 of
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v10
                      -> case coe v5 of
                           C_'91'_'93'_26 v13
                             -> case coe v3 of
                                  MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v14
                                    -> coe C_'91'_'93'_26 (coe v0 v9 v10 v14 v8 v13)
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           C_'91'_'93''60''8868''8314'_30
                             -> coe C_'91'_'93''60''8868''8314'_30
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Construct.Add.Supremum.Strict._.<⁺-transˡ
d_'60''8314''45'trans'737'_168 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  Maybe AgdaAny ->
  Maybe AgdaAny ->
  Maybe AgdaAny ->
  T__'60''8314'__20 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.NonStrict.T__'8804''8314'__20 ->
  T__'60''8314'__20
d_'60''8314''45'trans'737'_168 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 v8 v9
                               v10 v11
  = du_'60''8314''45'trans'737'_168 v6 v7 v8 v9 v10 v11
du_'60''8314''45'trans'737'_168 ::
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  Maybe AgdaAny ->
  Maybe AgdaAny ->
  Maybe AgdaAny ->
  T__'60''8314'__20 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.NonStrict.T__'8804''8314'__20 ->
  T__'60''8314'__20
du_'60''8314''45'trans'737'_168 v0 v1 v2 v3 v4 v5
  = case coe v4 of
      C_'91'_'93'_26 v8
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v9
               -> case coe v2 of
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v10
                      -> case coe v5 of
                           MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.NonStrict.C_'91'_'93'_26 v13
                             -> case coe v3 of
                                  MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v14
                                    -> coe C_'91'_'93'_26 (coe v0 v9 v10 v14 v8 v13)
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.NonStrict.C__'8804''8868''8314'_30
                             -> coe C_'91'_'93''60''8868''8314'_30
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      C_'91'_'93''60''8868''8314'_30
        -> coe seq (coe v5) (coe C_'91'_'93''60''8868''8314'_30)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Construct.Add.Supremum.Strict.<⁺-cmp-≡
d_'60''8314''45'cmp'45''8801'_184 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny ->
   AgdaAny -> MAlonzo.Code.Relation.Binary.Definitions.T_Tri_158) ->
  Maybe AgdaAny ->
  Maybe AgdaAny -> MAlonzo.Code.Relation.Binary.Definitions.T_Tri_158
d_'60''8314''45'cmp'45''8801'_184 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_'60''8314''45'cmp'45''8801'_184 v4 v5 v6
du_'60''8314''45'cmp'45''8801'_184 ::
  (AgdaAny ->
   AgdaAny -> MAlonzo.Code.Relation.Binary.Definitions.T_Tri_158) ->
  Maybe AgdaAny ->
  Maybe AgdaAny -> MAlonzo.Code.Relation.Binary.Definitions.T_Tri_158
du_'60''8314''45'cmp'45''8801'_184 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
               -> let v5 = coe v0 v3 v4 in
                  coe
                    (case coe v5 of
                       MAlonzo.Code.Relation.Binary.Definitions.C_tri'60'_172 v6
                         -> coe
                              MAlonzo.Code.Relation.Binary.Definitions.C_tri'60'_172
                              (coe C_'91'_'93'_26 v6)
                       MAlonzo.Code.Relation.Binary.Definitions.C_tri'8776'_180 v7
                         -> coe
                              MAlonzo.Code.Relation.Binary.Definitions.C_tri'8776'_180 erased
                       MAlonzo.Code.Relation.Binary.Definitions.C_tri'62'_188 v8
                         -> coe
                              MAlonzo.Code.Relation.Binary.Definitions.C_tri'62'_188
                              (coe C_'91'_'93'_26 v8)
                       _ -> MAlonzo.RTE.mazUnreachableError)
             MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
               -> coe
                    MAlonzo.Code.Relation.Binary.Definitions.C_tri'60'_172
                    (coe C_'91'_'93''60''8868''8314'_30)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
               -> coe
                    MAlonzo.Code.Relation.Binary.Definitions.C_tri'62'_188
                    (coe C_'91'_'93''60''8868''8314'_30)
             MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
               -> coe
                    MAlonzo.Code.Relation.Binary.Definitions.C_tri'8776'_180 erased
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Construct.Add.Supremum.Strict.<⁺-irrefl-≡
d_'60''8314''45'irrefl'45''8801'_240 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  Maybe AgdaAny ->
  Maybe AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T__'60''8314'__20 -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'60''8314''45'irrefl'45''8801'_240 = erased
-- Relation.Binary.Construct.Add.Supremum.Strict.<⁺-respˡ-≡
d_'60''8314''45'resp'737''45''8801'_246 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  Maybe AgdaAny ->
  Maybe AgdaAny ->
  Maybe AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T__'60''8314'__20 -> T__'60''8314'__20
d_'60''8314''45'resp'737''45''8801'_246 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6
                                        ~v7 v8
  = du_'60''8314''45'resp'737''45''8801'_246 v8
du_'60''8314''45'resp'737''45''8801'_246 ::
  T__'60''8314'__20 -> T__'60''8314'__20
du_'60''8314''45'resp'737''45''8801'_246 v0 = coe v0
-- Relation.Binary.Construct.Add.Supremum.Strict.<⁺-respʳ-≡
d_'60''8314''45'resp'691''45''8801'_250 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  Maybe AgdaAny ->
  Maybe AgdaAny ->
  Maybe AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T__'60''8314'__20 -> T__'60''8314'__20
d_'60''8314''45'resp'691''45''8801'_250 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6
                                        ~v7 v8
  = du_'60''8314''45'resp'691''45''8801'_250 v8
du_'60''8314''45'resp'691''45''8801'_250 ::
  T__'60''8314'__20 -> T__'60''8314'__20
du_'60''8314''45'resp'691''45''8801'_250 v0 = coe v0
-- Relation.Binary.Construct.Add.Supremum.Strict.<⁺-resp-≡
d_'60''8314''45'resp'45''8801'_254 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'60''8314''45'resp'45''8801'_254 ~v0 ~v1 ~v2 ~v3
  = du_'60''8314''45'resp'45''8801'_254
du_'60''8314''45'resp'45''8801'_254 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'60''8314''45'resp'45''8801'_254
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe (\ v0 v1 v2 v3 v4 -> v4)) (coe (\ v0 v1 v2 v3 v4 -> v4))
-- Relation.Binary.Construct.Add.Supremum.Strict._._._≈∙_
d__'8776''8729'__266 a0 a1 a2 a3 a4 a5 a6 a7 = ()
-- Relation.Binary.Construct.Add.Supremum.Strict._.<⁺-cmp
d_'60''8314''45'cmp_296 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny ->
   AgdaAny -> MAlonzo.Code.Relation.Binary.Definitions.T_Tri_158) ->
  Maybe AgdaAny ->
  Maybe AgdaAny -> MAlonzo.Code.Relation.Binary.Definitions.T_Tri_158
d_'60''8314''45'cmp_296 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 v8
  = du_'60''8314''45'cmp_296 v6 v7 v8
du_'60''8314''45'cmp_296 ::
  (AgdaAny ->
   AgdaAny -> MAlonzo.Code.Relation.Binary.Definitions.T_Tri_158) ->
  Maybe AgdaAny ->
  Maybe AgdaAny -> MAlonzo.Code.Relation.Binary.Definitions.T_Tri_158
du_'60''8314''45'cmp_296 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
               -> let v5 = coe v0 v3 v4 in
                  coe
                    (case coe v5 of
                       MAlonzo.Code.Relation.Binary.Definitions.C_tri'60'_172 v6
                         -> coe
                              MAlonzo.Code.Relation.Binary.Definitions.C_tri'60'_172
                              (coe C_'91'_'93'_26 v6)
                       MAlonzo.Code.Relation.Binary.Definitions.C_tri'8776'_180 v7
                         -> coe
                              MAlonzo.Code.Relation.Binary.Definitions.C_tri'8776'_180
                              (coe
                                 MAlonzo.Code.Relation.Binary.Construct.Add.Point.Equality.C_'91'_'93'_28
                                 v7)
                       MAlonzo.Code.Relation.Binary.Definitions.C_tri'62'_188 v8
                         -> coe
                              MAlonzo.Code.Relation.Binary.Definitions.C_tri'62'_188
                              (coe C_'91'_'93'_26 v8)
                       _ -> MAlonzo.RTE.mazUnreachableError)
             MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
               -> coe
                    MAlonzo.Code.Relation.Binary.Definitions.C_tri'60'_172
                    (coe C_'91'_'93''60''8868''8314'_30)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
               -> coe
                    MAlonzo.Code.Relation.Binary.Definitions.C_tri'62'_188
                    (coe C_'91'_'93''60''8868''8314'_30)
             MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
               -> coe
                    MAlonzo.Code.Relation.Binary.Definitions.C_tri'8776'_180
                    (coe
                       MAlonzo.Code.Relation.Binary.Construct.Add.Point.Equality.C_'8729''8776''8729'_22)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Construct.Add.Supremum.Strict._.<⁺-irrefl
d_'60''8314''45'irrefl_354 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  Maybe AgdaAny ->
  Maybe AgdaAny ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Point.Equality.T__'8776''8729'__20 ->
  T__'60''8314'__20 -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'60''8314''45'irrefl_354 = erased
-- Relation.Binary.Construct.Add.Supremum.Strict._.<⁺-respˡ-≈⁺
d_'60''8314''45'resp'737''45''8776''8314'_362 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  Maybe AgdaAny ->
  Maybe AgdaAny ->
  Maybe AgdaAny ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Point.Equality.T__'8776''8729'__20 ->
  T__'60''8314'__20 -> T__'60''8314'__20
d_'60''8314''45'resp'737''45''8776''8314'_362 ~v0 ~v1 ~v2 ~v3 ~v4
                                              ~v5 v6 v7 v8 v9 v10 v11
  = du_'60''8314''45'resp'737''45''8776''8314'_362
      v6 v7 v8 v9 v10 v11
du_'60''8314''45'resp'737''45''8776''8314'_362 ::
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  Maybe AgdaAny ->
  Maybe AgdaAny ->
  Maybe AgdaAny ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Point.Equality.T__'8776''8729'__20 ->
  T__'60''8314'__20 -> T__'60''8314'__20
du_'60''8314''45'resp'737''45''8776''8314'_362 v0 v1 v2 v3 v4 v5
  = case coe v4 of
      MAlonzo.Code.Relation.Binary.Construct.Add.Point.Equality.C_'8729''8776''8729'_22
        -> coe v5
      MAlonzo.Code.Relation.Binary.Construct.Add.Point.Equality.C_'91'_'93'_28 v8
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v9
               -> case coe v3 of
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v10
                      -> case coe v5 of
                           C_'91'_'93'_26 v13
                             -> case coe v1 of
                                  MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v14
                                    -> coe C_'91'_'93'_26 (coe v0 v14 v9 v10 v8 v13)
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           C_'91'_'93''60''8868''8314'_30
                             -> coe C_'91'_'93''60''8868''8314'_30
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Construct.Add.Supremum.Strict._.<⁺-respʳ-≈⁺
d_'60''8314''45'resp'691''45''8776''8314'_380 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  Maybe AgdaAny ->
  Maybe AgdaAny ->
  Maybe AgdaAny ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Point.Equality.T__'8776''8729'__20 ->
  T__'60''8314'__20 -> T__'60''8314'__20
d_'60''8314''45'resp'691''45''8776''8314'_380 ~v0 ~v1 ~v2 ~v3 ~v4
                                              ~v5 v6 v7 v8 v9 v10 v11
  = du_'60''8314''45'resp'691''45''8776''8314'_380
      v6 v7 v8 v9 v10 v11
du_'60''8314''45'resp'691''45''8776''8314'_380 ::
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  Maybe AgdaAny ->
  Maybe AgdaAny ->
  Maybe AgdaAny ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Point.Equality.T__'8776''8729'__20 ->
  T__'60''8314'__20 -> T__'60''8314'__20
du_'60''8314''45'resp'691''45''8776''8314'_380 v0 v1 v2 v3 v4 v5
  = case coe v4 of
      MAlonzo.Code.Relation.Binary.Construct.Add.Point.Equality.C_'8729''8776''8729'_22
        -> coe v5
      MAlonzo.Code.Relation.Binary.Construct.Add.Point.Equality.C_'91'_'93'_28 v8
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v9
               -> case coe v3 of
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v10
                      -> case coe v5 of
                           C_'91'_'93'_26 v13
                             -> case coe v1 of
                                  MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v14
                                    -> coe C_'91'_'93'_26 (coe v0 v14 v9 v10 v8 v13)
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Construct.Add.Supremum.Strict._.<⁺-resp-≈⁺
d_'60''8314''45'resp'45''8776''8314'_392 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'60''8314''45'resp'45''8776''8314'_392 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_'60''8314''45'resp'45''8776''8314'_392
du_'60''8314''45'resp'45''8776''8314'_392 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'60''8314''45'resp'45''8776''8314'_392
  = coe
      MAlonzo.Code.Data.Product.Base.du_map_128
      (coe du_'60''8314''45'resp'691''45''8776''8314'_380)
      (coe (\ v0 -> coe du_'60''8314''45'resp'737''45''8776''8314'_362))
-- Relation.Binary.Construct.Add.Supremum.Strict.<⁺-isStrictPartialOrder-≡
d_'60''8314''45'isStrictPartialOrder'45''8801'_394 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsStrictPartialOrder_290 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsStrictPartialOrder_290
d_'60''8314''45'isStrictPartialOrder'45''8801'_394 ~v0 ~v1 ~v2 ~v3
                                                   v4
  = du_'60''8314''45'isStrictPartialOrder'45''8801'_394 v4
du_'60''8314''45'isStrictPartialOrder'45''8801'_394 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsStrictPartialOrder_290 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsStrictPartialOrder_290
du_'60''8314''45'isStrictPartialOrder'45''8801'_394 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_IsStrictPartialOrder'46'constructor_14045
      (coe
         MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties.du_isEquivalence_396)
      (coe
         du_'60''8314''45'trans_48
         (coe MAlonzo.Code.Relation.Binary.Structures.d_trans_306 (coe v0)))
      (coe du_'60''8314''45'resp'45''8801'_254)
-- Relation.Binary.Construct.Add.Supremum.Strict.<⁺-isDecStrictPartialOrder-≡
d_'60''8314''45'isDecStrictPartialOrder'45''8801'_430 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecStrictPartialOrder_336 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecStrictPartialOrder_336
d_'60''8314''45'isDecStrictPartialOrder'45''8801'_430 ~v0 ~v1 ~v2
                                                      ~v3 v4
  = du_'60''8314''45'isDecStrictPartialOrder'45''8801'_430 v4
du_'60''8314''45'isDecStrictPartialOrder'45''8801'_430 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecStrictPartialOrder_336 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecStrictPartialOrder_336
du_'60''8314''45'isDecStrictPartialOrder'45''8801'_430 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_IsDecStrictPartialOrder'46'constructor_18663
      (coe
         du_'60''8314''45'isStrictPartialOrder'45''8801'_394
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isStrictPartialOrder_346
            (coe v0)))
      (coe
         MAlonzo.Code.Data.Maybe.Properties.du_'8801''45'dec_24
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d__'8799'__348 (coe v0)))
      (coe
         du_'60''8314''45'dec_62
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d__'60''63'__350 (coe v0)))
-- Relation.Binary.Construct.Add.Supremum.Strict.<⁺-isStrictTotalOrder-≡
d_'60''8314''45'isStrictTotalOrder'45''8801'_478 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsStrictTotalOrder_534 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsStrictTotalOrder_534
d_'60''8314''45'isStrictTotalOrder'45''8801'_478 ~v0 ~v1 ~v2 ~v3 v4
  = du_'60''8314''45'isStrictTotalOrder'45''8801'_478 v4
du_'60''8314''45'isStrictTotalOrder'45''8801'_478 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsStrictTotalOrder_534 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsStrictTotalOrder_534
du_'60''8314''45'isStrictTotalOrder'45''8801'_478 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_IsStrictTotalOrder'46'constructor_24953
      (coe
         du_'60''8314''45'isStrictPartialOrder'45''8801'_394
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isStrictPartialOrder_542
            (coe v0)))
      (coe
         du_'60''8314''45'cmp'45''8801'_184
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_compare_544 (coe v0)))
-- Relation.Binary.Construct.Add.Supremum.Strict._._._≈∙_
d__'8776''8729'__542 a0 a1 a2 a3 a4 a5 a6 a7 = ()
-- Relation.Binary.Construct.Add.Supremum.Strict._.<⁺-isStrictPartialOrder
d_'60''8314''45'isStrictPartialOrder_572 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsStrictPartialOrder_290 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsStrictPartialOrder_290
d_'60''8314''45'isStrictPartialOrder_572 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_'60''8314''45'isStrictPartialOrder_572 v6
du_'60''8314''45'isStrictPartialOrder_572 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsStrictPartialOrder_290 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsStrictPartialOrder_290
du_'60''8314''45'isStrictPartialOrder_572 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_IsStrictPartialOrder'46'constructor_14045
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Add.Point.Equality.du_'8776''8729''45'isEquivalence_108
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_302
            (coe v0)))
      (coe
         du_'60''8314''45'trans_48
         (coe MAlonzo.Code.Relation.Binary.Structures.d_trans_306 (coe v0)))
      (coe
         du_'60''8314''45'resp'45''8776''8314'_392
         (MAlonzo.Code.Relation.Binary.Structures.d_'60''45'resp'45''8776'_308
            (coe v0)))
-- Relation.Binary.Construct.Add.Supremum.Strict._.<⁺-isDecStrictPartialOrder
d_'60''8314''45'isDecStrictPartialOrder_608 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecStrictPartialOrder_336 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecStrictPartialOrder_336
d_'60''8314''45'isDecStrictPartialOrder_608 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
                                            v6
  = du_'60''8314''45'isDecStrictPartialOrder_608 v6
du_'60''8314''45'isDecStrictPartialOrder_608 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecStrictPartialOrder_336 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecStrictPartialOrder_336
du_'60''8314''45'isDecStrictPartialOrder_608 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_IsDecStrictPartialOrder'46'constructor_18663
      (coe
         du_'60''8314''45'isStrictPartialOrder_572
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isStrictPartialOrder_346
            (coe v0)))
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Add.Point.Equality.du_'8776''8729''45'dec_66
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d__'8799'__348 (coe v0)))
      (coe
         du_'60''8314''45'dec_62
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d__'60''63'__350 (coe v0)))
-- Relation.Binary.Construct.Add.Supremum.Strict._.<⁺-isStrictTotalOrder
d_'60''8314''45'isStrictTotalOrder_656 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsStrictTotalOrder_534 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsStrictTotalOrder_534
d_'60''8314''45'isStrictTotalOrder_656 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_'60''8314''45'isStrictTotalOrder_656 v6
du_'60''8314''45'isStrictTotalOrder_656 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsStrictTotalOrder_534 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsStrictTotalOrder_534
du_'60''8314''45'isStrictTotalOrder_656 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_IsStrictTotalOrder'46'constructor_24953
      (coe
         du_'60''8314''45'isStrictPartialOrder_572
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isStrictPartialOrder_542
            (coe v0)))
      (coe
         du_'60''8314''45'cmp_296
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_compare_544 (coe v0)))
