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

module MAlonzo.Code.Data.Nat.Induction where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.Unit
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Induction
import qualified MAlonzo.Code.Induction.WellFounded
import qualified MAlonzo.Code.Level

-- Data.Nat.Induction.Rec
d_Rec_10 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (Integer -> ()) -> Integer -> ()
d_Rec_10 = erased
-- Data.Nat.Induction.recBuilder
d_recBuilder_22 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (Integer -> ()) ->
  (Integer -> AgdaAny -> AgdaAny) -> Integer -> AgdaAny
d_recBuilder_22 ~v0 ~v1 v2 v3 = du_recBuilder_22 v2 v3
du_recBuilder_22 ::
  (Integer -> AgdaAny -> AgdaAny) -> Integer -> AgdaAny
du_recBuilder_22 v0 v1
  = case coe v1 of
      0 -> coe
             MAlonzo.Code.Level.C_lift_20
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      _ -> let v2 = subInt (coe v1) (coe (1 :: Integer)) in
           coe (coe v0 v2 (coe du_recBuilder_22 (coe v0) (coe v2)))
-- Data.Nat.Induction.rec
d_rec_34 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (Integer -> ()) ->
  (Integer -> AgdaAny -> AgdaAny) -> Integer -> AgdaAny
d_rec_34 ~v0 = du_rec_34
du_rec_34 ::
  (Integer -> ()) ->
  (Integer -> AgdaAny -> AgdaAny) -> Integer -> AgdaAny
du_rec_34
  = coe
      MAlonzo.Code.Induction.du_build_36
      (\ v0 v1 v2 -> coe du_recBuilder_22 v1 v2)
-- Data.Nat.Induction.CRec
d_CRec_38 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (Integer -> ()) -> Integer -> ()
d_CRec_38 = erased
-- Data.Nat.Induction.cRecBuilder
d_cRecBuilder_50 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (Integer -> ()) ->
  (Integer -> AgdaAny -> AgdaAny) -> Integer -> AgdaAny
d_cRecBuilder_50 v0 ~v1 v2 v3 = du_cRecBuilder_50 v0 v2 v3
du_cRecBuilder_50 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (Integer -> AgdaAny -> AgdaAny) -> Integer -> AgdaAny
du_cRecBuilder_50 v0 v1 v2
  = case coe v2 of
      0 -> coe
             MAlonzo.Code.Level.C_lift_20
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      _ -> let v3 = subInt (coe v2) (coe (1 :: Integer)) in
           coe
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                (coe v1 v3 (coe du_ih_66 (coe v0) (coe v1) (coe v3)))
                (coe du_ih_66 (coe v0) (coe v1) (coe v3)))
-- Data.Nat.Induction._.ih
d_ih_66 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (Integer -> ()) ->
  (Integer -> AgdaAny -> AgdaAny) -> Integer -> AgdaAny
d_ih_66 v0 ~v1 v2 v3 = du_ih_66 v0 v2 v3
du_ih_66 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (Integer -> AgdaAny -> AgdaAny) -> Integer -> AgdaAny
du_ih_66 v0 v1 v2
  = coe du_cRecBuilder_50 (coe v0) (coe v1) (coe v2)
-- Data.Nat.Induction.cRec
d_cRec_68 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (Integer -> ()) ->
  (Integer -> AgdaAny -> AgdaAny) -> Integer -> AgdaAny
d_cRec_68 v0
  = coe
      MAlonzo.Code.Induction.du_build_36
      (\ v1 v2 v3 -> coe du_cRecBuilder_50 (coe v0) v2 v3)
-- Data.Nat.Induction.<′-Rec
d_'60''8242''45'Rec_70 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (Integer -> ()) -> Integer -> ()
d_'60''8242''45'Rec_70 = erased
-- Data.Nat.Induction.<′-wellFounded
d_'60''8242''45'wellFounded_72 ::
  Integer -> MAlonzo.Code.Induction.WellFounded.T_Acc_42
d_'60''8242''45'wellFounded_72 = erased
-- Data.Nat.Induction.<′-wellFounded′
d_'60''8242''45'wellFounded'8242'_76 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804''8242'__342 ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42
d_'60''8242''45'wellFounded'8242'_76 = erased
-- Data.Nat.Induction._._.wfRec
d_wfRec_94 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (Integer -> ()) ->
  (Integer ->
   (Integer ->
    MAlonzo.Code.Data.Nat.Base.T__'8804''8242'__342 -> AgdaAny) ->
   AgdaAny) ->
  Integer -> AgdaAny
d_wfRec_94 ~v0 = du_wfRec_94
du_wfRec_94 ::
  (Integer -> ()) ->
  (Integer ->
   (Integer ->
    MAlonzo.Code.Data.Nat.Base.T__'8804''8242'__342 -> AgdaAny) ->
   AgdaAny) ->
  Integer -> AgdaAny
du_wfRec_94 = coe MAlonzo.Code.Induction.WellFounded.du_wfRec_168
-- Data.Nat.Induction._._.wfRecBuilder
d_wfRecBuilder_96 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (Integer -> ()) ->
  (Integer ->
   (Integer ->
    MAlonzo.Code.Data.Nat.Base.T__'8804''8242'__342 -> AgdaAny) ->
   AgdaAny) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804''8242'__342 -> AgdaAny
d_wfRecBuilder_96 ~v0 = du_wfRecBuilder_96
du_wfRecBuilder_96 ::
  (Integer -> ()) ->
  (Integer ->
   (Integer ->
    MAlonzo.Code.Data.Nat.Base.T__'8804''8242'__342 -> AgdaAny) ->
   AgdaAny) ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804''8242'__342 -> AgdaAny
du_wfRecBuilder_96 v0 v1 v2 v3
  = coe MAlonzo.Code.Induction.WellFounded.du_wfRecBuilder_160 v1 v3
-- Data.Nat.Induction.<-Rec
d_'60''45'Rec_98 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (Integer -> ()) -> Integer -> ()
d_'60''45'Rec_98 = erased
-- Data.Nat.Induction.<-wellFounded
d_'60''45'wellFounded_100 ::
  Integer -> MAlonzo.Code.Induction.WellFounded.T_Acc_42
d_'60''45'wellFounded_100 = erased
-- Data.Nat.Induction.<-wellFounded-fast
d_'60''45'wellFounded'45'fast_102 ::
  Integer -> MAlonzo.Code.Induction.WellFounded.T_Acc_42
d_'60''45'wellFounded'45'fast_102 = erased
-- Data.Nat.Induction._.<-wellFounded-skip
d_'60''45'wellFounded'45'skip_110 ::
  Integer -> Integer -> MAlonzo.Code.Induction.WellFounded.T_Acc_42
d_'60''45'wellFounded'45'skip_110 = erased
-- Data.Nat.Induction._._.wfRec
d_wfRec_132 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (Integer -> ()) ->
  (Integer ->
   (Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> AgdaAny) ->
   AgdaAny) ->
  Integer -> AgdaAny
d_wfRec_132 ~v0 = du_wfRec_132
du_wfRec_132 ::
  (Integer -> ()) ->
  (Integer ->
   (Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> AgdaAny) ->
   AgdaAny) ->
  Integer -> AgdaAny
du_wfRec_132 = coe MAlonzo.Code.Induction.WellFounded.du_wfRec_168
-- Data.Nat.Induction._._.wfRecBuilder
d_wfRecBuilder_134 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (Integer -> ()) ->
  (Integer ->
   (Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> AgdaAny) ->
   AgdaAny) ->
  Integer ->
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> AgdaAny
d_wfRecBuilder_134 ~v0 = du_wfRecBuilder_134
du_wfRecBuilder_134 ::
  (Integer -> ()) ->
  (Integer ->
   (Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> AgdaAny) ->
   AgdaAny) ->
  Integer ->
  Integer -> MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> AgdaAny
du_wfRecBuilder_134 v0 v1 v2 v3
  = coe MAlonzo.Code.Induction.WellFounded.du_wfRecBuilder_160 v1 v3
