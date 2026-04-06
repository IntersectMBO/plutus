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

module MAlonzo.Code.Relation.Binary.Construct.Add.Infimum.Strict where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Bool
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Data.Maybe.Properties
import qualified MAlonzo.Code.Data.Product.Base
import qualified MAlonzo.Code.Induction.WellFounded
import qualified MAlonzo.Code.Relation.Binary.Construct.Add.Infimum.NonStrict
import qualified MAlonzo.Code.Relation.Binary.Construct.Add.Point.Equality
import qualified MAlonzo.Code.Relation.Binary.Definitions
import qualified MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties
import qualified MAlonzo.Code.Relation.Binary.Structures
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core
import qualified MAlonzo.Code.Relation.Nullary.Reflects

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
      _ -> MAlonzo.RTE.mazUnreachableError
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
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
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
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v7
               -> coe seq (coe v5) (coe C_'8869''8331''60''91'_'93'_24)
             MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v5
             _ -> MAlonzo.RTE.mazUnreachableError
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
d_'60''8331''45'trans'737'_170 ::
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
d_'60''8331''45'trans'737'_170 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 v8 v9
                               v10 v11
  = du_'60''8331''45'trans'737'_170 v6 v7 v8 v9 v10 v11
du_'60''8331''45'trans'737'_170 ::
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  Maybe AgdaAny ->
  Maybe AgdaAny ->
  Maybe AgdaAny ->
  T__'60''8331'__20 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Infimum.NonStrict.T__'8804''8331'__20 ->
  T__'60''8331'__20
du_'60''8331''45'trans'737'_170 v0 v1 v2 v3 v4 v5
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
-- Relation.Binary.Construct.Add.Infimum.Strict.<₋-accessible-⊥₋
d_'60''8331''45'accessible'45''8869''8331'_182 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42
d_'60''8331''45'accessible'45''8869''8331'_182 = erased
-- Relation.Binary.Construct.Add.Infimum.Strict.<₋-accessible[_]
d_'60''8331''45'accessible'91'_'93'_186 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  AgdaAny ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42
d_'60''8331''45'accessible'91'_'93'_186 = erased
-- Relation.Binary.Construct.Add.Infimum.Strict._.wf-acc
d_wf'45'acc_194 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  Maybe AgdaAny ->
  T__'60''8331'__20 -> MAlonzo.Code.Induction.WellFounded.T_Acc_42
d_wf'45'acc_194 = erased
-- Relation.Binary.Construct.Add.Infimum.Strict.<₋-wellFounded
d_'60''8331''45'wellFounded_200 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> MAlonzo.Code.Induction.WellFounded.T_Acc_42) ->
  Maybe AgdaAny -> MAlonzo.Code.Induction.WellFounded.T_Acc_42
d_'60''8331''45'wellFounded_200 = erased
-- Relation.Binary.Construct.Add.Infimum.Strict.<₋-cmp-≡
d_'60''8331''45'cmp'45''8801'_208 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny ->
   AgdaAny -> MAlonzo.Code.Relation.Binary.Definitions.T_Tri_158) ->
  Maybe AgdaAny ->
  Maybe AgdaAny -> MAlonzo.Code.Relation.Binary.Definitions.T_Tri_158
d_'60''8331''45'cmp'45''8801'_208 ~v0 ~v1 ~v2 ~v3 v4 v5 v6
  = du_'60''8331''45'cmp'45''8801'_208 v4 v5 v6
du_'60''8331''45'cmp'45''8801'_208 ::
  (AgdaAny ->
   AgdaAny -> MAlonzo.Code.Relation.Binary.Definitions.T_Tri_158) ->
  Maybe AgdaAny ->
  Maybe AgdaAny -> MAlonzo.Code.Relation.Binary.Definitions.T_Tri_158
du_'60''8331''45'cmp'45''8801'_208 v0 v1 v2
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
d_'60''8331''45'irrefl'45''8801'_264 ::
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
d_'60''8331''45'irrefl'45''8801'_264 = erased
-- Relation.Binary.Construct.Add.Infimum.Strict.<₋-respˡ-≡
d_'60''8331''45'resp'737''45''8801'_270 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  Maybe AgdaAny ->
  Maybe AgdaAny ->
  Maybe AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T__'60''8331'__20 -> T__'60''8331'__20
d_'60''8331''45'resp'737''45''8801'_270 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6
                                        ~v7 v8
  = du_'60''8331''45'resp'737''45''8801'_270 v8
du_'60''8331''45'resp'737''45''8801'_270 ::
  T__'60''8331'__20 -> T__'60''8331'__20
du_'60''8331''45'resp'737''45''8801'_270 v0 = coe v0
-- Relation.Binary.Construct.Add.Infimum.Strict.<₋-respʳ-≡
d_'60''8331''45'resp'691''45''8801'_274 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  Maybe AgdaAny ->
  Maybe AgdaAny ->
  Maybe AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T__'60''8331'__20 -> T__'60''8331'__20
d_'60''8331''45'resp'691''45''8801'_274 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6
                                        ~v7 v8
  = du_'60''8331''45'resp'691''45''8801'_274 v8
du_'60''8331''45'resp'691''45''8801'_274 ::
  T__'60''8331'__20 -> T__'60''8331'__20
du_'60''8331''45'resp'691''45''8801'_274 v0 = coe v0
-- Relation.Binary.Construct.Add.Infimum.Strict.<₋-resp-≡
d_'60''8331''45'resp'45''8801'_278 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'60''8331''45'resp'45''8801'_278 ~v0 ~v1 ~v2 ~v3
  = du_'60''8331''45'resp'45''8801'_278
du_'60''8331''45'resp'45''8801'_278 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'60''8331''45'resp'45''8801'_278
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe (\ v0 v1 v2 v3 v4 -> v4)) (coe (\ v0 v1 v2 v3 v4 -> v4))
-- Relation.Binary.Construct.Add.Infimum.Strict._._._≈∙_
d__'8776''8729'__290 a0 a1 a2 a3 a4 a5 a6 a7 = ()
-- Relation.Binary.Construct.Add.Infimum.Strict._.<₋-cmp
d_'60''8331''45'cmp_312 ::
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
d_'60''8331''45'cmp_312 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 v8
  = du_'60''8331''45'cmp_312 v6 v7 v8
du_'60''8331''45'cmp_312 ::
  (AgdaAny ->
   AgdaAny -> MAlonzo.Code.Relation.Binary.Definitions.T_Tri_158) ->
  Maybe AgdaAny ->
  Maybe AgdaAny -> MAlonzo.Code.Relation.Binary.Definitions.T_Tri_158
du_'60''8331''45'cmp_312 v0 v1 v2
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
d_'60''8331''45'irrefl_370 ::
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
d_'60''8331''45'irrefl_370 = erased
-- Relation.Binary.Construct.Add.Infimum.Strict._.<₋-respˡ-≈₋
d_'60''8331''45'resp'737''45''8776''8331'_378 ::
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
d_'60''8331''45'resp'737''45''8776''8331'_378 ~v0 ~v1 ~v2 ~v3 ~v4
                                              ~v5 v6 v7 v8 v9 v10 v11
  = du_'60''8331''45'resp'737''45''8776''8331'_378
      v6 v7 v8 v9 v10 v11
du_'60''8331''45'resp'737''45''8776''8331'_378 ::
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  Maybe AgdaAny ->
  Maybe AgdaAny ->
  Maybe AgdaAny ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Point.Equality.T__'8776''8729'__20 ->
  T__'60''8331'__20 -> T__'60''8331'__20
du_'60''8331''45'resp'737''45''8776''8331'_378 v0 v1 v2 v3 v4 v5
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
d_'60''8331''45'resp'691''45''8776''8331'_390 ::
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
d_'60''8331''45'resp'691''45''8776''8331'_390 ~v0 ~v1 ~v2 ~v3 ~v4
                                              ~v5 v6 v7 v8 v9 v10 v11
  = du_'60''8331''45'resp'691''45''8776''8331'_390
      v6 v7 v8 v9 v10 v11
du_'60''8331''45'resp'691''45''8776''8331'_390 ::
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  Maybe AgdaAny ->
  Maybe AgdaAny ->
  Maybe AgdaAny ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Point.Equality.T__'8776''8729'__20 ->
  T__'60''8331'__20 -> T__'60''8331'__20
du_'60''8331''45'resp'691''45''8776''8331'_390 v0 v1 v2 v3 v4 v5
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
d_'60''8331''45'resp'45''8776''8331'_408 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'60''8331''45'resp'45''8776''8331'_408 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_'60''8331''45'resp'45''8776''8331'_408
du_'60''8331''45'resp'45''8776''8331'_408 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'60''8331''45'resp'45''8776''8331'_408
  = coe
      MAlonzo.Code.Data.Product.Base.du_map_128
      (coe du_'60''8331''45'resp'691''45''8776''8331'_390)
      (coe (\ v0 -> coe du_'60''8331''45'resp'737''45''8776''8331'_378))
-- Relation.Binary.Construct.Add.Infimum.Strict.<₋-isStrictPartialOrder-≡
d_'60''8331''45'isStrictPartialOrder'45''8801'_410 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsStrictPartialOrder_370 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsStrictPartialOrder_370
d_'60''8331''45'isStrictPartialOrder'45''8801'_410 ~v0 ~v1 ~v2 ~v3
                                                   v4
  = du_'60''8331''45'isStrictPartialOrder'45''8801'_410 v4
du_'60''8331''45'isStrictPartialOrder'45''8801'_410 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsStrictPartialOrder_370 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsStrictPartialOrder_370
du_'60''8331''45'isStrictPartialOrder'45''8801'_410 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_constructor_412
      (coe
         MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties.du_isEquivalence_396)
      (coe
         du_'60''8331''45'trans_48
         (coe MAlonzo.Code.Relation.Binary.Structures.d_trans_386 (coe v0)))
      (coe du_'60''8331''45'resp'45''8801'_278)
-- Relation.Binary.Construct.Add.Infimum.Strict.<₋-isDecStrictPartialOrder-≡
d_'60''8331''45'isDecStrictPartialOrder'45''8801'_446 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecStrictPartialOrder_418 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecStrictPartialOrder_418
d_'60''8331''45'isDecStrictPartialOrder'45''8801'_446 ~v0 ~v1 ~v2
                                                      ~v3 v4
  = du_'60''8331''45'isDecStrictPartialOrder'45''8801'_446 v4
du_'60''8331''45'isDecStrictPartialOrder'45''8801'_446 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecStrictPartialOrder_418 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecStrictPartialOrder_418
du_'60''8331''45'isDecStrictPartialOrder'45''8801'_446 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_constructor_482
      (coe
         du_'60''8331''45'isStrictPartialOrder'45''8801'_410
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isStrictPartialOrder_428
            (coe v0)))
      (coe
         MAlonzo.Code.Data.Maybe.Properties.du_'8801''45'dec_24
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d__'8799'__430 (coe v0)))
      (coe
         du_'60''8331''45'dec_62
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d__'60''63'__432 (coe v0)))
-- Relation.Binary.Construct.Add.Infimum.Strict.<₋-isStrictTotalOrder-≡
d_'60''8331''45'isStrictTotalOrder'45''8801'_494 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsStrictTotalOrder_624 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsStrictTotalOrder_624
d_'60''8331''45'isStrictTotalOrder'45''8801'_494 ~v0 ~v1 ~v2 ~v3 v4
  = du_'60''8331''45'isStrictTotalOrder'45''8801'_494 v4
du_'60''8331''45'isStrictTotalOrder'45''8801'_494 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsStrictTotalOrder_624 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsStrictTotalOrder_624
du_'60''8331''45'isStrictTotalOrder'45''8801'_494 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_constructor_680
      (coe
         du_'60''8331''45'isStrictPartialOrder'45''8801'_410
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isStrictPartialOrder_632
            (coe v0)))
      (coe
         du_'60''8331''45'cmp'45''8801'_208
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_compare_634 (coe v0)))
-- Relation.Binary.Construct.Add.Infimum.Strict._._._≈∙_
d__'8776''8729'__558 a0 a1 a2 a3 a4 a5 a6 a7 = ()
-- Relation.Binary.Construct.Add.Infimum.Strict._.<₋-isStrictPartialOrder
d_'60''8331''45'isStrictPartialOrder_580 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsStrictPartialOrder_370 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsStrictPartialOrder_370
d_'60''8331''45'isStrictPartialOrder_580 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_'60''8331''45'isStrictPartialOrder_580 v6
du_'60''8331''45'isStrictPartialOrder_580 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsStrictPartialOrder_370 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsStrictPartialOrder_370
du_'60''8331''45'isStrictPartialOrder_580 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_constructor_412
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Add.Point.Equality.du_'8776''8729''45'isEquivalence_108
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isEquivalence_382
            (coe v0)))
      (coe
         du_'60''8331''45'trans_48
         (coe MAlonzo.Code.Relation.Binary.Structures.d_trans_386 (coe v0)))
      (coe
         du_'60''8331''45'resp'45''8776''8331'_408
         (MAlonzo.Code.Relation.Binary.Structures.d_'60''45'resp'45''8776'_388
            (coe v0)))
-- Relation.Binary.Construct.Add.Infimum.Strict._.<₋-isDecStrictPartialOrder
d_'60''8331''45'isDecStrictPartialOrder_616 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecStrictPartialOrder_418 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecStrictPartialOrder_418
d_'60''8331''45'isDecStrictPartialOrder_616 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
                                            v6
  = du_'60''8331''45'isDecStrictPartialOrder_616 v6
du_'60''8331''45'isDecStrictPartialOrder_616 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecStrictPartialOrder_418 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecStrictPartialOrder_418
du_'60''8331''45'isDecStrictPartialOrder_616 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_constructor_482
      (coe
         du_'60''8331''45'isStrictPartialOrder_580
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isStrictPartialOrder_428
            (coe v0)))
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Add.Point.Equality.du_'8776''8729''45'dec_66
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d__'8799'__430 (coe v0)))
      (coe
         du_'60''8331''45'dec_62
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d__'60''63'__432 (coe v0)))
-- Relation.Binary.Construct.Add.Infimum.Strict._.<₋-isStrictTotalOrder
d_'60''8331''45'isStrictTotalOrder_664 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsStrictTotalOrder_624 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsStrictTotalOrder_624
d_'60''8331''45'isStrictTotalOrder_664 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6
  = du_'60''8331''45'isStrictTotalOrder_664 v6
du_'60''8331''45'isStrictTotalOrder_664 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsStrictTotalOrder_624 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsStrictTotalOrder_624
du_'60''8331''45'isStrictTotalOrder_664 v0
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_constructor_680
      (coe
         du_'60''8331''45'isStrictPartialOrder_580
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_isStrictPartialOrder_632
            (coe v0)))
      (coe
         du_'60''8331''45'cmp_312
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_compare_634 (coe v0)))
