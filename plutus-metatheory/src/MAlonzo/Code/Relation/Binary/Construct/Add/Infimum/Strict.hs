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

module MAlonzo.Code.Relation.Binary.Construct.Add.Infimum.Strict where

import Data.Text qualified
import MAlonzo.Code.Agda.Builtin.Bool qualified
import MAlonzo.Code.Agda.Builtin.Equality qualified
import MAlonzo.Code.Agda.Builtin.Maybe qualified
import MAlonzo.Code.Agda.Builtin.Sigma qualified
import MAlonzo.Code.Agda.Primitive qualified
import MAlonzo.Code.Data.Irrelevant qualified
import MAlonzo.Code.Data.Maybe.Properties qualified
import MAlonzo.Code.Data.Product.Base qualified
import MAlonzo.Code.Relation.Binary.Construct.Add.Infimum.NonStrict qualified
import MAlonzo.Code.Relation.Binary.Construct.Add.Point.Equality qualified
import MAlonzo.Code.Relation.Binary.Definitions qualified
import MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties qualified
import MAlonzo.Code.Relation.Binary.Structures qualified
import MAlonzo.Code.Relation.Nullary.Decidable.Core qualified
import MAlonzo.Code.Relation.Nullary.Reflects qualified
import MAlonzo.RTE (AgdaAny, add64, addInt, coe, eq64, eqInt, erased, geqInt, lt64, ltInt, mul64,
                    mulInt, quot64, quotInt, rem64, remInt, sub64, subInt, word64FromNat,
                    word64ToNat)
import MAlonzo.RTE qualified

-- Relation.Binary.Construct.Add.Infimum.Strict._<₋_
d__'60''8331'__20 a0 a1 a2 a3 a4 a5 = ()
data T__'60''8331'__20
  = C_'8869''8331''60''91'_'93'_24 | C_'91'_'93'_30 AgdaAny
-- Relation.Binary.Construct.Add.Infimum.Strict.[<]-injective
d_'91''60''93''45'injective_36 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  AgdaAny -> AgdaAny -> T__'60''8331'__20 -> AgdaAny
d_'91''60''93''45'injective_36 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_'91''60''93''45'injective_36 v6
du_'91''60''93''45'injective_36 :: T__'60''8331'__20 -> AgdaAny
du_'91''60''93''45'injective_36 v0
  = case coe v0 of
      C_'91'_'93'_30 v3 -> coe v3
      _                 -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Construct.Add.Infimum.Strict.<₋-asym
d_'60''8331''45'asym_40 ::
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
  T__'60''8331'__20 ->
  T__'60''8331'__20 -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'60''8331''45'asym_40 = erased
-- Relation.Binary.Construct.Add.Infimum.Strict.<₋-trans
d_'60''8331''45'trans_48 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  Maybe AgdaAny ->
  Maybe AgdaAny ->
  Maybe AgdaAny ->
  T__'60''8331'__20 -> T__'60''8331'__20 -> T__'60''8331'__20
d_'60''8331''45'trans_48 ~v0 ~v1 ~v2 ~v3 v4 v5 v6 v7 v8 v9
  = du_'60''8331''45'trans_48 v4 v5 v6 v7 v8 v9
du_'60''8331''45'trans_48 ::
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  Maybe AgdaAny ->
  Maybe AgdaAny ->
  Maybe AgdaAny ->
  T__'60''8331'__20 -> T__'60''8331'__20 -> T__'60''8331'__20
du_'60''8331''45'trans_48 v0 v1 v2 v3 v4 v5
  = case coe v4 of
      C_'8869''8331''60''91'_'93'_24
        -> coe seq (coe v5) (coe C_'8869''8331''60''91'_'93'_24)
      C_'91'_'93'_30 v8
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v9
               -> case coe v2 of
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v10
                      -> case coe v5 of
                           C_'91'_'93'_30 v13
                             -> case coe v3 of
                                  MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v14
                                    -> coe C_'91'_'93'_30 (coe v0 v9 v10 v14 v8 v13)
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Construct.Add.Infimum.Strict.<₋-dec
d_'60''8331''45'dec_62 ::
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
d_'60''8331''45'dec_62 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_'60''8331''45'dec_62 v4 v5 v6
du_'60''8331''45'dec_62 ::
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  Maybe AgdaAny ->
  Maybe AgdaAny ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du_'60''8331''45'dec_62 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_168
                    (coe C_'91'_'93'_30) (coe du_'91''60''93''45'injective_36)
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
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                    (coe
                       MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                       (coe C_'8869''8331''60''91'_'93'_24))
             MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Construct.Add.Infimum.Strict.<₋-irrelevant
d_'60''8331''45'irrelevant_80 ::
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
  T__'60''8331'__20 ->
  T__'60''8331'__20 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'60''8331''45'irrelevant_80 = erased
-- Relation.Binary.Construct.Add.Infimum.Strict._._._≤₋_
d__'8804''8331'__102 a0 a1 a2 a3 a4 a5 a6 a7 = ()
-- Relation.Binary.Construct.Add.Infimum.Strict._.<₋-transʳ
d_'60''8331''45'trans'691'_154 ::
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
  MAlonzo.Code.Relation.Binary.Construct.Add.Infimum.NonStrict.T__'8804''8331'__20 ->
  T__'60''8331'__20 -> T__'60''8331'__20
d_'60''8331''45'trans'691'_154 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 v8 v9
                               v10 v11
  = du_'60''8331''45'trans'691'_154 v6 v7 v8 v9 v10 v11
du_'60''8331''45'trans'691'_154 ::
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  Maybe AgdaAny ->
  Maybe AgdaAny ->
  Maybe AgdaAny ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Infimum.NonStrict.T__'8804''8331'__20 ->
  T__'60''8331'__20 -> T__'60''8331'__20
du_'60''8331''45'trans'691'_154 v0 v1 v2 v3 v4 v5
  = case coe v4 of
      MAlonzo.Code.Relation.Binary.Construct.Add.Infimum.NonStrict.C_'8869''8331''8804'__24
        -> coe seq (coe v5) (coe C_'8869''8331''60''91'_'93'_24)
      MAlonzo.Code.Relation.Binary.Construct.Add.Infimum.NonStrict.C_'91'_'93'_30 v8
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v9
               -> case coe v2 of
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v10
                      -> case coe v5 of
                           C_'91'_'93'_30 v13
                             -> case coe v3 of
                                  MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v14
                                    -> coe C_'91'_'93'_30 (coe v0 v9 v10 v14 v8 v13)
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Construct.Add.Infimum.Strict._.<₋-transˡ
d_'60''8331''45'trans'737'_172 ::
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
  T__'60''8331'__20 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Infimum.NonStrict.T__'8804''8331'__20 ->
  T__'60''8331'__20
d_'60''8331''45'trans'737'_172 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 v8 v9
                               v10 v11
  = du_'60''8331''45'trans'737'_172 v6 v7 v8 v9 v10 v11
du_'60''8331''45'trans'737'_172 ::
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  Maybe AgdaAny ->
  Maybe AgdaAny ->
  Maybe AgdaAny ->
  T__'60''8331'__20 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Infimum.NonStrict.T__'8804''8331'__20 ->
  T__'60''8331'__20
du_'60''8331''45'trans'737'_172 v0 v1 v2 v3 v4 v5
  = case coe v4 of
      C_'8869''8331''60''91'_'93'_24
        -> coe seq (coe v5) (coe C_'8869''8331''60''91'_'93'_24)
      C_'91'_'93'_30 v8
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v9
               -> case coe v2 of
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v10
                      -> case coe v5 of
                           MAlonzo.Code.Relation.Binary.Construct.Add.Infimum.NonStrict.C_'91'_'93'_30 v13
                             -> case coe v3 of
                                  MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v14
                                    -> coe C_'91'_'93'_30 (coe v0 v9 v10 v14 v8 v13)
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Construct.Add.Infimum.Strict.<₋-cmp-≡
d_'60''8331''45'cmp'45''8801'_186 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny ->
   AgdaAny -> MAlonzo.Code.Relation.Binary.Definitions.T_Tri_158) ->
  Maybe AgdaAny ->
  Maybe AgdaAny -> MAlonzo.Code.Relation.Binary.Definitions.T_Tri_158
d_'60''8331''45'cmp'45''8801'_186 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_'60''8331''45'cmp'45''8801'_186 v4 v5 v6
du_'60''8331''45'cmp'45''8801'_186 ::
  (AgdaAny ->
   AgdaAny -> MAlonzo.Code.Relation.Binary.Definitions.T_Tri_158) ->
  Maybe AgdaAny ->
  Maybe AgdaAny -> MAlonzo.Code.Relation.Binary.Definitions.T_Tri_158
du_'60''8331''45'cmp'45''8801'_186 v0 v1 v2
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
                              (coe C_'91'_'93'_30 v6)
                       MAlonzo.Code.Relation.Binary.Definitions.C_tri'8776'_180 v7
                         -> coe
                              MAlonzo.Code.Relation.Binary.Definitions.C_tri'8776'_180 erased
                       MAlonzo.Code.Relation.Binary.Definitions.C_tri'62'_188 v8
                         -> coe
                              MAlonzo.Code.Relation.Binary.Definitions.C_tri'62'_188
                              (coe C_'91'_'93'_30 v8)
                       _ -> MAlonzo.RTE.mazUnreachableError)
             MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
               -> coe
                    MAlonzo.Code.Relation.Binary.Definitions.C_tri'62'_188
                    (coe C_'8869''8331''60''91'_'93'_24)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
               -> coe
                    MAlonzo.Code.Relation.Binary.Definitions.C_tri'60'_172
                    (coe C_'8869''8331''60''91'_'93'_24)
             MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
               -> coe
                    MAlonzo.Code.Relation.Binary.Definitions.C_tri'8776'_180 erased
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Construct.Add.Infimum.Strict.<₋-irrefl-≡
d_'60''8331''45'irrefl'45''8801'_242 ::
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
  T__'60''8331'__20 -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'60''8331''45'irrefl'45''8801'_242 = erased
-- Relation.Binary.Construct.Add.Infimum.Strict.<₋-respˡ-≡
d_'60''8331''45'resp'737''45''8801'_248 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  Maybe AgdaAny ->
  Maybe AgdaAny ->
  Maybe AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T__'60''8331'__20 -> T__'60''8331'__20
d_'60''8331''45'resp'737''45''8801'_248 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6
                                        ~v7 v8
  = du_'60''8331''45'resp'737''45''8801'_248 v8
du_'60''8331''45'resp'737''45''8801'_248 ::
  T__'60''8331'__20 -> T__'60''8331'__20
du_'60''8331''45'resp'737''45''8801'_248 v0 = coe v0
-- Relation.Binary.Construct.Add.Infimum.Strict.<₋-respʳ-≡
d_'60''8331''45'resp'691''45''8801'_252 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  Maybe AgdaAny ->
  Maybe AgdaAny ->
  Maybe AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T__'60''8331'__20 -> T__'60''8331'__20
d_'60''8331''45'resp'691''45''8801'_252 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6
                                        ~v7 v8
  = du_'60''8331''45'resp'691''45''8801'_252 v8
du_'60''8331''45'resp'691''45''8801'_252 ::
  T__'60''8331'__20 -> T__'60''8331'__20
du_'60''8331''45'resp'691''45''8801'_252 v0 = coe v0
-- Relation.Binary.Construct.Add.Infimum.Strict.<₋-resp-≡
d_'60''8331''45'resp'45''8801'_256 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'60''8331''45'resp'45''8801'_256 ~v0 ~v1 ~v2 ~v3
  = du_'60''8331''45'resp'45''8801'_256
du_'60''8331''45'resp'45''8801'_256 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'60''8331''45'resp'45''8801'_256
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe (\ v0 v1 v2 v3 v4 -> v4)) (coe (\ v0 v1 v2 v3 v4 -> v4))
-- Relation.Binary.Construct.Add.Infimum.Strict._._._≈∙_
d__'8776''8729'__268 a0 a1 a2 a3 a4 a5 a6 a7 = ()
-- Relation.Binary.Construct.Add.Infimum.Strict._.<₋-cmp
d_'60''8331''45'cmp_298 ::
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
d_'60''8331''45'cmp_298 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 v8
  = du_'60''8331''45'cmp_298 v6 v7 v8
du_'60''8331''45'cmp_298 ::
  (AgdaAny ->
   AgdaAny -> MAlonzo.Code.Relation.Binary.Definitions.T_Tri_158) ->
  Maybe AgdaAny ->
  Maybe AgdaAny -> MAlonzo.Code.Relation.Binary.Definitions.T_Tri_158
du_'60''8331''45'cmp_298 v0 v1 v2
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
                              (coe C_'91'_'93'_30 v6)
                       MAlonzo.Code.Relation.Binary.Definitions.C_tri'8776'_180 v7
                         -> coe
                              MAlonzo.Code.Relation.Binary.Definitions.C_tri'8776'_180
                              (coe
                                 MAlonzo.Code.Relation.Binary.Construct.Add.Point.Equality.C_'91'_'93'_28
                                 v7)
                       MAlonzo.Code.Relation.Binary.Definitions.C_tri'62'_188 v8
                         -> coe
                              MAlonzo.Code.Relation.Binary.Definitions.C_tri'62'_188
                              (coe C_'91'_'93'_30 v8)
                       _ -> MAlonzo.RTE.mazUnreachableError)
             MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
               -> coe
                    MAlonzo.Code.Relation.Binary.Definitions.C_tri'62'_188
                    (coe C_'8869''8331''60''91'_'93'_24)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
               -> coe
                    MAlonzo.Code.Relation.Binary.Definitions.C_tri'60'_172
                    (coe C_'8869''8331''60''91'_'93'_24)
             MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
               -> coe
                    MAlonzo.Code.Relation.Binary.Definitions.C_tri'8776'_180
                    (coe
                       MAlonzo.Code.Relation.Binary.Construct.Add.Point.Equality.C_'8729''8776''8729'_22)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Construct.Add.Infimum.Strict._.<₋-irrefl
d_'60''8331''45'irrefl_356 ::
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
  T__'60''8331'__20 -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'60''8331''45'irrefl_356 = erased
-- Relation.Binary.Construct.Add.Infimum.Strict._.<₋-respˡ-≈₋
d_'60''8331''45'resp'737''45''8776''8331'_364 ::
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
  T__'60''8331'__20 -> T__'60''8331'__20
d_'60''8331''45'resp'737''45''8776''8331'_364 ~v0 ~v1 ~v2 ~v3 ~v4
                                              ~v5 v6 v7 v8 v9 v10 v11
  = du_'60''8331''45'resp'737''45''8776''8331'_364
      v6 v7 v8 v9 v10 v11
du_'60''8331''45'resp'737''45''8776''8331'_364 ::
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  Maybe AgdaAny ->
  Maybe AgdaAny ->
  Maybe AgdaAny ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Point.Equality.T__'8776''8729'__20 ->
  T__'60''8331'__20 -> T__'60''8331'__20
du_'60''8331''45'resp'737''45''8776''8331'_364 v0 v1 v2 v3 v4 v5
  = case coe v4 of
      MAlonzo.Code.Relation.Binary.Construct.Add.Point.Equality.C_'8729''8776''8729'_22
        -> coe v5
      MAlonzo.Code.Relation.Binary.Construct.Add.Point.Equality.C_'91'_'93'_28 v8
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v9
               -> case coe v3 of
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v10
                      -> case coe v5 of
                           C_'91'_'93'_30 v13
                             -> case coe v1 of
                                  MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v14
                                    -> coe C_'91'_'93'_30 (coe v0 v14 v9 v10 v8 v13)
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Construct.Add.Infimum.Strict._.<₋-respʳ-≈₋
d_'60''8331''45'resp'691''45''8776''8331'_376 ::
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
  T__'60''8331'__20 -> T__'60''8331'__20
d_'60''8331''45'resp'691''45''8776''8331'_376 ~v0 ~v1 ~v2 ~v3 ~v4
                                              ~v5 v6 v7 v8 v9 v10 v11
  = du_'60''8331''45'resp'691''45''8776''8331'_376
      v6 v7 v8 v9 v10 v11
du_'60''8331''45'resp'691''45''8776''8331'_376 ::
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  Maybe AgdaAny ->
  Maybe AgdaAny ->
  Maybe AgdaAny ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Point.Equality.T__'8776''8729'__20 ->
  T__'60''8331'__20 -> T__'60''8331'__20
du_'60''8331''45'resp'691''45''8776''8331'_376 v0 v1 v2 v3 v4 v5
  = case coe v4 of
      MAlonzo.Code.Relation.Binary.Construct.Add.Point.Equality.C_'8729''8776''8729'_22
        -> coe v5
      MAlonzo.Code.Relation.Binary.Construct.Add.Point.Equality.C_'91'_'93'_28 v8
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v9
               -> case coe v3 of
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v10
                      -> case coe v5 of
                           C_'8869''8331''60''91'_'93'_24
                             -> coe C_'8869''8331''60''91'_'93'_24
                           C_'91'_'93'_30 v13
                             -> case coe v1 of
                                  MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v14
                                    -> coe C_'91'_'93'_30 (coe v0 v14 v9 v10 v8 v13)
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Relation.Binary.Construct.Add.Infimum.Strict._.<₋-resp-≈₋
d_'60''8331''45'resp'45''8776''8331'_394 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'60''8331''45'resp'45''8776''8331'_394 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_'60''8331''45'resp'45''8776''8331'_394
du_'60''8331''45'resp'45''8776''8331'_394 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'60''8331''45'resp'45''8776''8331'_394
  = coe
      MAlonzo.Code.Data.Product.Base.du_map_128
      (coe du_'60''8331''45'resp'691''45''8776''8331'_376)
      (coe (\ v0 -> coe du_'60''8331''45'resp'737''45''8776''8331'_364))
-- Relation.Binary.Construct.Add.Infimum.Strict.<₋-isStrictPartialOrder-≡
d_'60''8331''45'isStrictPartialOrder'45''8801'_396 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsStrictPartialOrder_290 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsStrictPartialOrder_290
d_'60''8331''45'isStrictPartialOrder'45''8801'_396 ~v0 ~v1 ~v2 ~v3
                                                   v4
  = du_'60''8331''45'isStrictPartialOrder'45''8801'_396 v4
du_'60''8331''45'isStrictPartialOrder'45''8801'_396 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsStrictPartialOrder_290 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsStrictPartialOrder_290
du_'60''8331''45'isStrictPartialOrder'45''8801'_396 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_IsStrictPartialOrder'46'constructor_14045
      (coe
         MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties.du_isEquivalence_396)
      (coe
         du_'60''8331''45'trans_48
         (coe MAlonzo.Code.Relation.Binary.Structures.d_trans_306 (coe v0)))
      (coe du_'60''8331''45'resp'45''8801'_256)
-- Relation.Binary.Construct.Add.Infimum.Strict.<₋-isDecStrictPartialOrder-≡
d_'60''8331''45'isDecStrictPartialOrder'45''8801'_432 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecStrictPartialOrder_336 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecStrictPartialOrder_336
d_'60''8331''45'isDecStrictPartialOrder'45''8801'_432 ~v0 ~v1 ~v2
                                                      ~v3 v4
  = du_'60''8331''45'isDecStrictPartialOrder'45''8801'_432 v4
du_'60''8331''45'isDecStrictPartialOrder'45''8801'_432 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecStrictPartialOrder_336 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecStrictPartialOrder_336
du_'60''8331''45'isDecStrictPartialOrder'45''8801'_432 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_IsDecStrictPartialOrder'46'constructor_18663
      (coe
         du_'60''8331''45'isStrictPartialOrder'45''8801'_396
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isStrictPartialOrder_346
            (coe v0)))
      (coe
         MAlonzo.Code.Data.Maybe.Properties.du_'8801''45'dec_24
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d__'8799'__348 (coe v0)))
      (coe
         du_'60''8331''45'dec_62
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d__'60''63'__350 (coe v0)))
-- Relation.Binary.Construct.Add.Infimum.Strict.<₋-isStrictTotalOrder-≡
d_'60''8331''45'isStrictTotalOrder'45''8801'_480 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsStrictTotalOrder_534 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsStrictTotalOrder_534
d_'60''8331''45'isStrictTotalOrder'45''8801'_480 ~v0 ~v1 ~v2 ~v3 v4
  = du_'60''8331''45'isStrictTotalOrder'45''8801'_480 v4
du_'60''8331''45'isStrictTotalOrder'45''8801'_480 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsStrictTotalOrder_534 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsStrictTotalOrder_534
du_'60''8331''45'isStrictTotalOrder'45''8801'_480 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_IsStrictTotalOrder'46'constructor_24953
      (coe
         du_'60''8331''45'isStrictPartialOrder'45''8801'_396
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isStrictPartialOrder_542
            (coe v0)))
      (coe
         du_'60''8331''45'cmp'45''8801'_186
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_compare_544 (coe v0)))
-- Relation.Binary.Construct.Add.Infimum.Strict._._._≈∙_
d__'8776''8729'__544 a0 a1 a2 a3 a4 a5 a6 a7 = ()
-- Relation.Binary.Construct.Add.Infimum.Strict._.<₋-isStrictPartialOrder
d_'60''8331''45'isStrictPartialOrder_574 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsStrictPartialOrder_290 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsStrictPartialOrder_290
d_'60''8331''45'isStrictPartialOrder_574 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_'60''8331''45'isStrictPartialOrder_574 v6
du_'60''8331''45'isStrictPartialOrder_574 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsStrictPartialOrder_290 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsStrictPartialOrder_290
du_'60''8331''45'isStrictPartialOrder_574 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_IsStrictPartialOrder'46'constructor_14045
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Add.Point.Equality.du_'8776''8729''45'isEquivalence_108
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_302
            (coe v0)))
      (coe
         du_'60''8331''45'trans_48
         (coe MAlonzo.Code.Relation.Binary.Structures.d_trans_306 (coe v0)))
      (coe
         du_'60''8331''45'resp'45''8776''8331'_394
         (MAlonzo.Code.Relation.Binary.Structures.d_'60''45'resp'45''8776'_308
            (coe v0)))
-- Relation.Binary.Construct.Add.Infimum.Strict._.<₋-isDecStrictPartialOrder
d_'60''8331''45'isDecStrictPartialOrder_610 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecStrictPartialOrder_336 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecStrictPartialOrder_336
d_'60''8331''45'isDecStrictPartialOrder_610 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
                                            v6
  = du_'60''8331''45'isDecStrictPartialOrder_610 v6
du_'60''8331''45'isDecStrictPartialOrder_610 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecStrictPartialOrder_336 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecStrictPartialOrder_336
du_'60''8331''45'isDecStrictPartialOrder_610 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_IsDecStrictPartialOrder'46'constructor_18663
      (coe
         du_'60''8331''45'isStrictPartialOrder_574
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isStrictPartialOrder_346
            (coe v0)))
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Add.Point.Equality.du_'8776''8729''45'dec_66
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d__'8799'__348 (coe v0)))
      (coe
         du_'60''8331''45'dec_62
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d__'60''63'__350 (coe v0)))
-- Relation.Binary.Construct.Add.Infimum.Strict._.<₋-isStrictTotalOrder
d_'60''8331''45'isStrictTotalOrder_658 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsStrictTotalOrder_534 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsStrictTotalOrder_534
d_'60''8331''45'isStrictTotalOrder_658 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_'60''8331''45'isStrictTotalOrder_658 v6
du_'60''8331''45'isStrictTotalOrder_658 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsStrictTotalOrder_534 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsStrictTotalOrder_534
du_'60''8331''45'isStrictTotalOrder_658 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_IsStrictTotalOrder'46'constructor_24953
      (coe
         du_'60''8331''45'isStrictPartialOrder_574
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isStrictPartialOrder_542
            (coe v0)))
      (coe
         du_'60''8331''45'cmp_298
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_compare_544 (coe v0)))
