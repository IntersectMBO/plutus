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

module MAlonzo.Code.Utils.List where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Data.Empty
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Data.List.Properties

-- Utils.List.Bwd
d_Bwd_6 a0 = ()
data T_Bwd_6 = C_'91''93'_10 | C__'58''60'__12 T_Bwd_6 AgdaAny
-- Utils.List.bwd-length
d_bwd'45'length_16 :: () -> T_Bwd_6 -> Integer
d_bwd'45'length_16 ~v0 v1 = du_bwd'45'length_16 v1
du_bwd'45'length_16 :: T_Bwd_6 -> Integer
du_bwd'45'length_16 v0
  = case coe v0 of
      C_'91''93'_10 -> coe (0 :: Integer)
      C__'58''60'__12 v1 v2
        -> coe
             addInt (coe (1 :: Integer)) (coe du_bwd'45'length_16 (coe v1))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Utils.List.bwd-foldr
d_bwd'45'foldr_26 ::
  () ->
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny -> T_Bwd_6 -> AgdaAny
d_bwd'45'foldr_26 ~v0 ~v1 v2 v3 v4 = du_bwd'45'foldr_26 v2 v3 v4
du_bwd'45'foldr_26 ::
  (AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny -> T_Bwd_6 -> AgdaAny
du_bwd'45'foldr_26 v0 v1 v2
  = case coe v2 of
      C_'91''93'_10 -> coe v1
      C__'58''60'__12 v3 v4
        -> coe du_bwd'45'foldr_26 (coe v0) (coe v0 v4 v1) (coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Utils.List._<>>_
d__'60''62''62'__42 :: () -> T_Bwd_6 -> [AgdaAny] -> [AgdaAny]
d__'60''62''62'__42 ~v0 v1 v2 = du__'60''62''62'__42 v1 v2
du__'60''62''62'__42 :: T_Bwd_6 -> [AgdaAny] -> [AgdaAny]
du__'60''62''62'__42 v0 v1
  = case coe v0 of
      C_'91''93'_10 -> coe v1
      C__'58''60'__12 v2 v3
        -> coe
             du__'60''62''62'__42 (coe v2)
             (coe
                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v3) (coe v1))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Utils.List._<><_
d__'60''62''60'__54 :: () -> T_Bwd_6 -> [AgdaAny] -> T_Bwd_6
d__'60''62''60'__54 ~v0 v1 v2 = du__'60''62''60'__54 v1 v2
du__'60''62''60'__54 :: T_Bwd_6 -> [AgdaAny] -> T_Bwd_6
du__'60''62''60'__54 v0 v1
  = case coe v1 of
      [] -> coe v0
      (:) v2 v3
        -> coe
             du__'60''62''60'__54 (coe C__'58''60'__12 (coe v0) (coe v2))
             (coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Utils.List._:<L_
d__'58''60'L__66 :: () -> [AgdaAny] -> AgdaAny -> [AgdaAny]
d__'58''60'L__66 ~v0 v1 v2 = du__'58''60'L__66 v1 v2
du__'58''60'L__66 :: [AgdaAny] -> AgdaAny -> [AgdaAny]
du__'58''60'L__66 v0 v1
  = coe
      MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v0)
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v1)
         (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
-- Utils.List._∷B_
d__'8759'B__74 :: () -> AgdaAny -> T_Bwd_6 -> T_Bwd_6
d__'8759'B__74 ~v0 v1 v2 = du__'8759'B__74 v1 v2
du__'8759'B__74 :: AgdaAny -> T_Bwd_6 -> T_Bwd_6
du__'8759'B__74 v0 v1
  = case coe v1 of
      C_'91''93'_10 -> coe C__'58''60'__12 (coe v1) (coe v0)
      C__'58''60'__12 v2 v3
        -> coe
             C__'58''60'__12 (coe du__'8759'B__74 (coe v0) (coe v2)) (coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Utils.List.lemma<>1
d_lemma'60''62'1_90 ::
  () ->
  T_Bwd_6 ->
  [AgdaAny] -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_lemma'60''62'1_90 = erased
-- Utils.List.lemma<>1'
d_lemma'60''62'1''_106 ::
  () ->
  T_Bwd_6 ->
  [AgdaAny] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_lemma'60''62'1''_106 = erased
-- Utils.List.lemma<>2
d_lemma'60''62'2_118 ::
  () ->
  T_Bwd_6 ->
  [AgdaAny] -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_lemma'60''62'2_118 = erased
-- Utils.List.lemma<>2'
d_lemma'60''62'2''_134 ::
  () ->
  T_Bwd_6 ->
  [AgdaAny] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_lemma'60''62'2''_134 = erased
-- Utils.List.lemma-<>>-++
d_lemma'45''60''62''62''45''43''43'_148 ::
  () ->
  T_Bwd_6 ->
  [AgdaAny] ->
  [AgdaAny] -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_lemma'45''60''62''62''45''43''43'_148 = erased
-- Utils.List.lemma-bwd-foldr
d_lemma'45'bwd'45'foldr_172 ::
  () ->
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  T_Bwd_6 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_lemma'45'bwd'45'foldr_172 = erased
-- Utils.List.<><-cancelʳ
d_'60''62''60''45'cancel'691'_194 ::
  () ->
  T_Bwd_6 ->
  T_Bwd_6 ->
  [AgdaAny] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'60''62''60''45'cancel'691'_194 = erased
-- Utils.List.<>>[]-cancelʳ
d_'60''62''62''91''93''45'cancel'691'_232 ::
  () ->
  T_Bwd_6 ->
  T_Bwd_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'60''62''62''91''93''45'cancel'691'_232 = erased
-- Utils.List.<>>-cancelʳ
d_'60''62''62''45'cancel'691'_248 ::
  () ->
  T_Bwd_6 ->
  T_Bwd_6 ->
  [AgdaAny] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'60''62''62''45'cancel'691'_248 = erased
-- Utils.List.<>>-cancelˡ
d_'60''62''62''45'cancel'737'_266 ::
  () ->
  T_Bwd_6 ->
  [AgdaAny] ->
  [AgdaAny] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'60''62''62''45'cancel'737'_266 = erased
-- Utils.List.IList
d_IList_302 a0 a1 a2 = ()
data T_IList_302
  = C_'91''93'_308 | C__'8759'__314 AgdaAny T_IList_302
-- Utils.List._++I_
d__'43''43'I__324 ::
  () ->
  (AgdaAny -> ()) ->
  [AgdaAny] -> [AgdaAny] -> T_IList_302 -> T_IList_302 -> T_IList_302
d__'43''43'I__324 ~v0 ~v1 v2 ~v3 v4 v5
  = du__'43''43'I__324 v2 v4 v5
du__'43''43'I__324 ::
  [AgdaAny] -> T_IList_302 -> T_IList_302 -> T_IList_302
du__'43''43'I__324 v0 v1 v2
  = case coe v1 of
      C_'91''93'_308 -> coe v2
      C__'8759'__314 v5 v6
        -> case coe v0 of
             (:) v7 v8
               -> coe
                    C__'8759'__314 v5
                    (coe du__'43''43'I__324 (coe v8) (coe v6) (coe v2))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Utils.List.lengthT
d_lengthT_340 ::
  () -> [AgdaAny] -> (AgdaAny -> ()) -> T_IList_302 -> Integer
d_lengthT_340 ~v0 v1 ~v2 ~v3 = du_lengthT_340 v1
du_lengthT_340 :: [AgdaAny] -> Integer
du_lengthT_340 v0
  = coe MAlonzo.Code.Data.List.Base.du_length_284 v0
-- Utils.List.iGetIdx
d_iGetIdx_350 ::
  () -> [AgdaAny] -> (AgdaAny -> ()) -> T_IList_302 -> [AgdaAny]
d_iGetIdx_350 ~v0 v1 ~v2 ~v3 = du_iGetIdx_350 v1
du_iGetIdx_350 :: [AgdaAny] -> [AgdaAny]
du_iGetIdx_350 v0 = coe v0
-- Utils.List._:<I_
d__'58''60'I__364 ::
  () ->
  (AgdaAny -> ()) ->
  AgdaAny -> [AgdaAny] -> T_IList_302 -> AgdaAny -> T_IList_302
d__'58''60'I__364 ~v0 ~v1 ~v2 v3 v4 v5
  = du__'58''60'I__364 v3 v4 v5
du__'58''60'I__364 ::
  [AgdaAny] -> T_IList_302 -> AgdaAny -> T_IList_302
du__'58''60'I__364 v0 v1 v2
  = coe
      du__'43''43'I__324 (coe v0) (coe v1)
      (coe C__'8759'__314 v2 (coe C_'91''93'_308))
-- Utils.List.∷-injectiveI
d_'8759''45'injectiveI_390 ::
  () ->
  (AgdaAny -> ()) ->
  AgdaAny ->
  [AgdaAny] ->
  [AgdaAny] ->
  AgdaAny ->
  AgdaAny ->
  T_IList_302 ->
  T_IList_302 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8759''45'injectiveI_390 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
                           ~v10
  = du_'8759''45'injectiveI_390
du_'8759''45'injectiveI_390 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8759''45'injectiveI_390
  = coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased
-- Utils.List.IBwd
d_IBwd_396 a0 a1 a2 = ()
data T_IBwd_396
  = C_'91''93'_402 | C__'58''60'__408 T_IBwd_396 AgdaAny
-- Utils.List._<>>I_
d__'60''62''62'I__418 ::
  () ->
  (AgdaAny -> ()) ->
  T_Bwd_6 -> [AgdaAny] -> T_IBwd_396 -> T_IList_302 -> T_IList_302
d__'60''62''62'I__418 ~v0 ~v1 v2 ~v3 v4 v5
  = du__'60''62''62'I__418 v2 v4 v5
du__'60''62''62'I__418 ::
  T_Bwd_6 -> T_IBwd_396 -> T_IList_302 -> T_IList_302
du__'60''62''62'I__418 v0 v1 v2
  = case coe v1 of
      C_'91''93'_402 -> coe v2
      C__'58''60'__408 v5 v6
        -> case coe v0 of
             C__'58''60'__12 v7 v8
               -> coe
                    du__'60''62''62'I__418 (coe v7) (coe v5) (coe C__'8759'__314 v6 v2)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Utils.List._<><I_
d__'60''62''60'I__436 ::
  () ->
  (AgdaAny -> ()) ->
  T_Bwd_6 -> [AgdaAny] -> T_IBwd_396 -> T_IList_302 -> T_IBwd_396
d__'60''62''60'I__436 ~v0 ~v1 ~v2 v3 v4 v5
  = du__'60''62''60'I__436 v3 v4 v5
du__'60''62''60'I__436 ::
  [AgdaAny] -> T_IBwd_396 -> T_IList_302 -> T_IBwd_396
du__'60''62''60'I__436 v0 v1 v2
  = case coe v2 of
      C_'91''93'_308 -> coe v1
      C__'8759'__314 v5 v6
        -> case coe v0 of
             (:) v7 v8
               -> coe
                    du__'60''62''60'I__436 (coe v8) (coe C__'58''60'__408 v1 v5)
                    (coe v6)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Utils.List.lemma<>I1
d_lemma'60''62'I1_458 ::
  () ->
  (AgdaAny -> ()) ->
  T_Bwd_6 ->
  [AgdaAny] ->
  T_IBwd_396 ->
  T_IList_302 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_lemma'60''62'I1_458 = erased
-- Utils.List.lemma<>I2
d_lemma'60''62'I2_480 ::
  () ->
  (AgdaAny -> ()) ->
  T_Bwd_6 ->
  [AgdaAny] ->
  T_IBwd_396 ->
  T_IList_302 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_lemma'60''62'I2_480 = erased
-- Utils.List.lemma<>I2'
d_lemma'60''62'I2''_502 ::
  () ->
  (AgdaAny -> ()) ->
  T_Bwd_6 ->
  [AgdaAny] ->
  T_IBwd_396 ->
  T_IList_302 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_lemma'60''62'I2''_502 = erased
-- Utils.List.IBwd2IList'
d_IBwd2IList''_520 ::
  () ->
  (AgdaAny -> ()) ->
  T_Bwd_6 ->
  [AgdaAny] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_IBwd_396 -> T_IList_302
d_IBwd2IList''_520 ~v0 ~v1 v2 ~v3 ~v4 v5
  = du_IBwd2IList''_520 v2 v5
du_IBwd2IList''_520 :: T_Bwd_6 -> T_IBwd_396 -> T_IList_302
du_IBwd2IList''_520 v0 v1
  = coe du__'60''62''62'I__418 (coe v0) (coe v1) (coe C_'91''93'_308)
-- Utils.List.IBwd2IList
d_IBwd2IList_538 ::
  () ->
  (AgdaAny -> ()) ->
  T_Bwd_6 ->
  [AgdaAny] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_IBwd_396 -> T_IList_302
d_IBwd2IList_538 ~v0 ~v1 v2 ~v3 ~v4 v5 = du_IBwd2IList_538 v2 v5
du_IBwd2IList_538 :: T_Bwd_6 -> T_IBwd_396 -> T_IList_302
du_IBwd2IList_538 v0 v1
  = coe du__'60''62''62'I__418 (coe v0) (coe v1) (coe C_'91''93'_308)
-- Utils.List.IList2IBwd
d_IList2IBwd_552 ::
  () ->
  (AgdaAny -> ()) ->
  [AgdaAny] ->
  T_Bwd_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_IList_302 -> T_IBwd_396
d_IList2IBwd_552 ~v0 ~v1 v2 ~v3 ~v4 v5 = du_IList2IBwd_552 v2 v5
du_IList2IBwd_552 :: [AgdaAny] -> T_IList_302 -> T_IBwd_396
du_IList2IBwd_552 v0 v1
  = coe du__'60''62''60'I__436 (coe v0) (coe C_'91''93'_402) (coe v1)
-- Utils.List.IBwd<>IList
d_IBwd'60''62'IList_574 ::
  () ->
  (AgdaAny -> ()) ->
  T_Bwd_6 ->
  [AgdaAny] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_IBwd_396 ->
  T_IList_302 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_IBwd'60''62'IList_574 = erased
-- Utils.List.split
d_split_590 ::
  () ->
  T_Bwd_6 ->
  [AgdaAny] ->
  (AgdaAny -> ()) ->
  T_IList_302 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_split_590 ~v0 v1 ~v2 ~v3 v4 = du_split_590 v1 v4
du_split_590 ::
  T_Bwd_6 -> T_IList_302 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_split_590 v0 v1
  = case coe v0 of
      C_'91''93'_10
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe C_'91''93'_402)
             (coe v1)
      C__'58''60'__12 v2 v3
        -> let v4 = coe du_split_590 (coe v2) (coe v1) in
           coe
             (case coe v4 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                  -> case coe v6 of
                       C__'8759'__314 v9 v10
                         -> coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                              (coe C__'58''60'__408 v5 v9) (coe v10)
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Utils.List.bsplit
d_bsplit_630 ::
  () ->
  T_Bwd_6 ->
  [AgdaAny] ->
  (AgdaAny -> ()) ->
  T_IBwd_396 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_bsplit_630 ~v0 ~v1 v2 ~v3 v4 = du_bsplit_630 v2 v4
du_bsplit_630 ::
  [AgdaAny] -> T_IBwd_396 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_bsplit_630 v0 v1
  = case coe v0 of
      []
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
             (coe C_'91''93'_308)
      (:) v2 v3
        -> let v4 = coe du_bsplit_630 (coe v3) (coe v1) in
           coe
             (case coe v4 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                  -> case coe v5 of
                       C__'58''60'__408 v9 v10
                         -> coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v9)
                              (coe C__'8759'__314 v10 v6)
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Utils.List.inj-IBwd2IList
d_inj'45'IBwd2IList_676 ::
  () ->
  (AgdaAny -> ()) ->
  T_Bwd_6 ->
  [AgdaAny] ->
  T_IBwd_396 ->
  T_IBwd_396 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_inj'45'IBwd2IList_676 = erased
-- Utils.List._≣_<>>_
d__'8803'_'60''62''62'__684 a0 a1 a2 a3 = ()
data T__'8803'_'60''62''62'__684
  = C_start_690 | C_bubble_700 T__'8803'_'60''62''62'__684
-- Utils.List.lem-≣-<>>
d_lem'45''8803''45''60''62''62'_710 ::
  () ->
  [AgdaAny] ->
  T_Bwd_6 ->
  [AgdaAny] ->
  T__'8803'_'60''62''62'__684 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_lem'45''8803''45''60''62''62'_710 = erased
-- Utils.List.lem-≣-<>>'
d_lem'45''8803''45''60''62''62'''_722 ::
  () ->
  [AgdaAny] ->
  T_Bwd_6 ->
  [AgdaAny] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T__'8803'_'60''62''62'__684
d_lem'45''8803''45''60''62''62'''_722 ~v0 ~v1 v2 ~v3 ~v4
  = du_lem'45''8803''45''60''62''62'''_722 v2
du_lem'45''8803''45''60''62''62'''_722 ::
  T_Bwd_6 -> T__'8803'_'60''62''62'__684
du_lem'45''8803''45''60''62''62'''_722 v0
  = case coe v0 of
      C_'91''93'_10 -> coe C_start_690
      C__'58''60'__12 v1 v2
        -> coe
             C_bubble_700 (coe du_lem'45''8803''45''60''62''62'''_722 (coe v1))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Utils.List.done-≣-<>>
d_done'45''8803''45''60''62''62'_734 ::
  () -> [AgdaAny] -> T__'8803'_'60''62''62'__684
d_done'45''8803''45''60''62''62'_734 ~v0 v1
  = du_done'45''8803''45''60''62''62'_734 v1
du_done'45''8803''45''60''62''62'_734 ::
  [AgdaAny] -> T__'8803'_'60''62''62'__684
du_done'45''8803''45''60''62''62'_734 v0
  = coe
      du_lem'45''8803''45''60''62''62'''_722
      (coe du__'60''62''60'__54 (coe C_'91''93'_10) (coe v0))
-- Utils.List.no-empty-≣-<>>
d_no'45'empty'45''8803''45''60''62''62'_744 ::
  () ->
  T_Bwd_6 ->
  AgdaAny ->
  [AgdaAny] ->
  T__'8803'_'60''62''62'__684 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_no'45'empty'45''8803''45''60''62''62'_744 = erased
-- Utils.List.unique-≣-<>>
d_unique'45''8803''45''60''62''62'_760 ::
  () ->
  [AgdaAny] ->
  T_Bwd_6 ->
  [AgdaAny] ->
  T__'8803'_'60''62''62'__684 ->
  T__'8803'_'60''62''62'__684 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_unique'45''8803''45''60''62''62'_760 = erased
-- Utils.List.lemma-≣-<>>-refl
d_lemma'45''8803''45''60''62''62''45'refl_780 ::
  () -> T_Bwd_6 -> [AgdaAny] -> T__'8803'_'60''62''62'__684
d_lemma'45''8803''45''60''62''62''45'refl_780 ~v0 v1 ~v2
  = du_lemma'45''8803''45''60''62''62''45'refl_780 v1
du_lemma'45''8803''45''60''62''62''45'refl_780 ::
  T_Bwd_6 -> T__'8803'_'60''62''62'__684
du_lemma'45''8803''45''60''62''62''45'refl_780 v0
  = case coe v0 of
      C_'91''93'_10 -> coe C_start_690
      C__'58''60'__12 v1 v2
        -> coe
             C_bubble_700
             (coe du_lemma'45''8803''45''60''62''62''45'refl_780 (coe v1))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Utils.List.IIList
d_IIList_802 a0 a1 a2 a3 a4 = ()
data T_IIList_802
  = C_'91''93'_810 | C__'8759'__820 AgdaAny T_IIList_802
-- Utils.List.IIBwd
d_IIBwd_832 a0 a1 a2 a3 a4 = ()
data T_IIBwd_832
  = C_'91''93'_840 | C__'58''60'__850 T_IIBwd_832 AgdaAny
-- Utils.List._<>>II_
d__'60''62''62'II__870 ::
  () ->
  (AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_Bwd_6 ->
  [AgdaAny] ->
  T_IBwd_396 ->
  T_IList_302 -> T_IIBwd_832 -> T_IIList_802 -> T_IIList_802
d__'60''62''62'II__870 ~v0 ~v1 ~v2 v3 ~v4 v5 ~v6 v7 v8
  = du__'60''62''62'II__870 v3 v5 v7 v8
du__'60''62''62'II__870 ::
  T_Bwd_6 ->
  T_IBwd_396 -> T_IIBwd_832 -> T_IIList_802 -> T_IIList_802
du__'60''62''62'II__870 v0 v1 v2 v3
  = case coe v2 of
      C_'91''93'_840 -> coe v3
      C__'58''60'__850 v8 v9
        -> case coe v0 of
             C__'58''60'__12 v10 v11
               -> case coe v1 of
                    C__'58''60'__408 v14 v15
                      -> coe
                           du__'60''62''62'II__870 (coe v10) (coe v14) (coe v8)
                           (coe C__'8759'__820 v9 v3)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Utils.List.IIBwd2IIList
d_IIBwd2IIList_902 ::
  () ->
  (AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_Bwd_6 ->
  [AgdaAny] ->
  T_IBwd_396 ->
  T_IList_302 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_IIBwd_832 -> T_IIList_802
d_IIBwd2IIList_902 ~v0 ~v1 ~v2 v3 ~v4 v5 ~v6 ~v7 ~v8 v9
  = du_IIBwd2IIList_902 v3 v5 v9
du_IIBwd2IIList_902 ::
  T_Bwd_6 -> T_IBwd_396 -> T_IIBwd_832 -> T_IIList_802
du_IIBwd2IIList_902 v0 v1 v2
  = coe
      du__'60''62''62'II__870 (coe v0) (coe v1) (coe v2)
      (coe C_'91''93'_810)
-- Utils.List.splitI
d_splitI_924 ::
  () ->
  T_Bwd_6 ->
  [AgdaAny] ->
  (AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IBwd_396 ->
  T_IList_302 ->
  T_IIList_802 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_splitI_924 ~v0 v1 ~v2 ~v3 ~v4 v5 ~v6 v7 = du_splitI_924 v1 v5 v7
du_splitI_924 ::
  T_Bwd_6 ->
  T_IBwd_396 ->
  T_IIList_802 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_splitI_924 v0 v1 v2
  = case coe v1 of
      C_'91''93'_402
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe C_'91''93'_840)
             (coe v2)
      C__'58''60'__408 v5 v6
        -> case coe v0 of
             C__'58''60'__12 v7 v8
               -> let v9 = coe du_splitI_924 (coe v7) (coe v5) (coe v2) in
                  coe
                    (case coe v9 of
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
                         -> case coe v11 of
                              C__'8759'__820 v16 v17
                                -> coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                     (coe C__'58''60'__850 v10 v16) (coe v17)
                              _ -> MAlonzo.RTE.mazUnreachableError
                       _ -> MAlonzo.RTE.mazUnreachableError)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Utils.List.bsplitI
d_bsplitI_974 ::
  () ->
  T_Bwd_6 ->
  [AgdaAny] ->
  (AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  T_IBwd_396 ->
  T_IList_302 ->
  T_IIBwd_832 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_bsplitI_974 ~v0 ~v1 v2 ~v3 ~v4 ~v5 v6 v7
  = du_bsplitI_974 v2 v6 v7
du_bsplitI_974 ::
  [AgdaAny] ->
  T_IList_302 ->
  T_IIBwd_832 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_bsplitI_974 v0 v1 v2
  = case coe v1 of
      C_'91''93'_308
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2)
             (coe C_'91''93'_810)
      C__'8759'__314 v5 v6
        -> case coe v0 of
             (:) v7 v8
               -> let v9 = coe du_bsplitI_974 (coe v8) (coe v6) (coe v2) in
                  coe
                    (case coe v9 of
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
                         -> case coe v10 of
                              C__'58''60'__850 v16 v17
                                -> coe
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v16)
                                     (coe C__'8759'__820 v17 v11)
                              _ -> MAlonzo.RTE.mazUnreachableError
                       _ -> MAlonzo.RTE.mazUnreachableError)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Utils.List.proj-IIList
d_proj'45'IIList_1028 ::
  () ->
  (AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  AgdaAny ->
  AgdaAny ->
  T_Bwd_6 ->
  [AgdaAny] -> T_IBwd_396 -> T_IList_302 -> T_IIList_802 -> AgdaAny
d_proj'45'IIList_1028 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 v7 ~v8 v9
  = du_proj'45'IIList_1028 v5 v7 v9
du_proj'45'IIList_1028 ::
  T_Bwd_6 -> T_IBwd_396 -> T_IIList_802 -> AgdaAny
du_proj'45'IIList_1028 v0 v1 v2
  = let v3 = coe du_splitI_924 (coe v0) (coe v1) (coe v2) in
    coe
      (case coe v3 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
           -> case coe v5 of
                C__'8759'__820 v10 v11 -> coe v10
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Utils.List.proj-IIBwd
d_proj'45'IIBwd_1074 ::
  () ->
  (AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  AgdaAny ->
  AgdaAny ->
  T_Bwd_6 ->
  [AgdaAny] -> T_IBwd_396 -> T_IList_302 -> T_IIBwd_832 -> AgdaAny
d_proj'45'IIBwd_1074 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 ~v7 v8 v9
  = du_proj'45'IIBwd_1074 v6 v8 v9
du_proj'45'IIBwd_1074 ::
  [AgdaAny] -> T_IList_302 -> T_IIBwd_832 -> AgdaAny
du_proj'45'IIBwd_1074 v0 v1 v2
  = let v3 = coe du_bsplitI_974 (coe v0) (coe v1) (coe v2) in
    coe
      (case coe v3 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
           -> case coe v4 of
                C__'58''60'__850 v10 v11 -> coe v11
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Utils.List._≣I_<>>_
d__'8803'I_'60''62''62'__1110 a0 a1 a2 a3 a4 a5 a6 a7 a8 = ()
data T__'8803'I_'60''62''62'__1110
  = C_start_1120 | C_bubble_1136 T__'8803'I_'60''62''62'__1110
-- Utils.List.lem-≣I-<>>1
d_lem'45''8803'I'45''60''62''62'1_1156 ::
  () ->
  (AgdaAny -> ()) ->
  [AgdaAny] ->
  T_IList_302 ->
  T_Bwd_6 ->
  T_IBwd_396 ->
  [AgdaAny] ->
  T_IList_302 ->
  T__'8803'_'60''62''62'__684 ->
  T__'8803'I_'60''62''62'__1110 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_lem'45''8803'I'45''60''62''62'1_1156 = erased
-- Utils.List.lem-≣I-<>>1'
d_lem'45''8803'I'45''60''62''62'1''_1178 ::
  () ->
  (AgdaAny -> ()) ->
  [AgdaAny] ->
  T_IList_302 ->
  T_Bwd_6 ->
  T_IBwd_396 ->
  [AgdaAny] ->
  T_IList_302 ->
  T__'8803'_'60''62''62'__684 ->
  T__'8803'I_'60''62''62'__1110 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_lem'45''8803'I'45''60''62''62'1''_1178 = erased
-- Utils.List.lem-≣I-<>>2
d_lem'45''8803'I'45''60''62''62'2_1200 ::
  () ->
  (AgdaAny -> ()) ->
  [AgdaAny] ->
  T_IList_302 ->
  T_Bwd_6 ->
  T_IBwd_396 ->
  [AgdaAny] ->
  T_IList_302 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T__'8803'I_'60''62''62'__1110
d_lem'45''8803'I'45''60''62''62'2_1200 ~v0 ~v1 ~v2 ~v3 v4 v5 ~v6
                                       ~v7 ~v8 ~v9
  = du_lem'45''8803'I'45''60''62''62'2_1200 v4 v5
du_lem'45''8803'I'45''60''62''62'2_1200 ::
  T_Bwd_6 -> T_IBwd_396 -> T__'8803'I_'60''62''62'__1110
du_lem'45''8803'I'45''60''62''62'2_1200 v0 v1
  = case coe v1 of
      C_'91''93'_402 -> coe C_start_1120
      C__'58''60'__408 v4 v5
        -> case coe v0 of
             C__'58''60'__12 v6 v7
               -> coe
                    C_bubble_1136
                    (coe du_lem'45''8803'I'45''60''62''62'2_1200 (coe v6) (coe v4))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Utils.List.lem-≣I-<>>2'
d_lem'45''8803'I'45''60''62''62'2''_1224 ::
  () ->
  (AgdaAny -> ()) ->
  [AgdaAny] ->
  T_IList_302 ->
  T_Bwd_6 ->
  T_IBwd_396 ->
  [AgdaAny] ->
  T_IList_302 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T__'8803'I_'60''62''62'__1110
d_lem'45''8803'I'45''60''62''62'2''_1224 ~v0 ~v1 ~v2 ~v3 v4 v5 ~v6
                                         ~v7 ~v8 ~v9
  = du_lem'45''8803'I'45''60''62''62'2''_1224 v4 v5
du_lem'45''8803'I'45''60''62''62'2''_1224 ::
  T_Bwd_6 -> T_IBwd_396 -> T__'8803'I_'60''62''62'__1110
du_lem'45''8803'I'45''60''62''62'2''_1224 v0 v1
  = case coe v1 of
      C_'91''93'_402 -> coe C_start_1120
      C__'58''60'__408 v4 v5
        -> case coe v0 of
             C__'58''60'__12 v6 v7
               -> coe
                    C_bubble_1136
                    (coe du_lem'45''8803'I'45''60''62''62'2''_1224 (coe v6) (coe v4))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Utils.List.done-≣I-<>>
d_done'45''8803'I'45''60''62''62'_1238 ::
  () ->
  (AgdaAny -> ()) ->
  [AgdaAny] -> T_IList_302 -> T__'8803'I_'60''62''62'__1110
d_done'45''8803'I'45''60''62''62'_1238 ~v0 ~v1 v2 v3
  = du_done'45''8803'I'45''60''62''62'_1238 v2 v3
du_done'45''8803'I'45''60''62''62'_1238 ::
  [AgdaAny] -> T_IList_302 -> T__'8803'I_'60''62''62'__1110
du_done'45''8803'I'45''60''62''62'_1238 v0 v1
  = coe
      du_lem'45''8803'I'45''60''62''62'2_1200
      (coe du__'60''62''60'__54 (coe C_'91''93'_10) (coe v0))
      (coe du__'60''62''60'I__436 (coe v0) (coe C_'91''93'_402) (coe v1))
-- Utils.List.lemma<>I3
d_lemma'60''62'I3_1252 ::
  () ->
  (AgdaAny -> ()) ->
  T_Bwd_6 ->
  T_IBwd_396 ->
  T_IList_302 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_lemma'60''62'I3_1252 = erased
-- Utils.List.lem-<><I-subst
d_lem'45''60''62''60'I'45'subst_1272 ::
  () ->
  (AgdaAny -> ()) ->
  [AgdaAny] ->
  [AgdaAny] ->
  T_IList_302 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_lem'45''60''62''60'I'45'subst_1272 = erased
-- Utils.List.lemma-<>>I-++I
d_lemma'45''60''62''62'I'45''43''43'I_1290 ::
  () ->
  (AgdaAny -> ()) ->
  T_Bwd_6 ->
  [AgdaAny] ->
  [AgdaAny] ->
  T_IBwd_396 ->
  T_IList_302 ->
  T_IList_302 -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_lemma'45''60''62''62'I'45''43''43'I_1290 = erased
-- Utils.List.<>>I[]-cancelʳ
d_'60''62''62'I'91''93''45'cancel'691'_1314 ::
  () ->
  (AgdaAny -> ()) ->
  T_Bwd_6 ->
  T_IBwd_396 ->
  T_IBwd_396 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'60''62''62'I'91''93''45'cancel'691'_1314 = erased
-- Utils.List.<>>I-cancelˡ
d_'60''62''62'I'45'cancel'737'_1336 ::
  () ->
  (AgdaAny -> ()) ->
  T_Bwd_6 ->
  [AgdaAny] ->
  T_IBwd_396 ->
  T_IList_302 ->
  T_IList_302 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'60''62''62'I'45'cancel'737'_1336 = erased
-- Utils.List.equalbyPredicate++
d_equalbyPredicate'43''43'_1394 ::
  () ->
  (AgdaAny -> ()) ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_IList_302 ->
  T_IList_302 ->
  (AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  (AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_equalbyPredicate'43''43'_1394 = erased
-- Utils.List.equalbyPredicate
d_equalbyPredicate_1500 ::
  () ->
  (AgdaAny -> ()) ->
  T_Bwd_6 ->
  T_Bwd_6 ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_IBwd_396 ->
  T_IBwd_396 ->
  (AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  (AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_equalbyPredicate_1500 = erased
-- Utils.List.equalbyPredicate++I
d_equalbyPredicate'43''43'I_1588 ::
  () ->
  (AgdaAny -> ()) ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  T_IList_302 ->
  T_IList_302 ->
  T_IList_302 ->
  T_IList_302 ->
  T_IList_302 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_IIList_802 ->
  T_IIList_802 ->
  (AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  (AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_equalbyPredicate'43''43'I_1588 ~v0 ~v1 v2 v3 ~v4 ~v5 ~v6 ~v7 v8
                                 v9 ~v10 ~v11 ~v12 ~v13 ~v14 ~v15 ~v16 ~v17 ~v18 ~v19 ~v20 v21 v22
                                 ~v23 ~v24
  = du_equalbyPredicate'43''43'I_1588 v2 v3 v8 v9 v21 v22
du_equalbyPredicate'43''43'I_1588 ::
  [AgdaAny] ->
  [AgdaAny] ->
  T_IList_302 ->
  T_IList_302 ->
  T_IIList_802 ->
  T_IIList_802 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_equalbyPredicate'43''43'I_1588 v0 v1 v2 v3 v4 v5
  = case coe v4 of
      C_'91''93'_810
        -> case coe v5 of
             C_'91''93'_810
               -> let v6
                        = coe
                            MAlonzo.Code.Data.List.Properties.du_'8759''45'injective_46 in
                  coe
                    (coe
                       seq (coe v6)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                             (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased))))
             C__'8759'__820 v10 v11
               -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_14
             _ -> MAlonzo.RTE.mazUnreachableError
      C__'8759'__820 v10 v11
        -> case coe v0 of
             (:) v12 v13
               -> case coe v2 of
                    C__'8759'__314 v16 v17
                      -> case coe v5 of
                           C_'91''93'_810 -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_14
                           C__'8759'__820 v22 v23
                             -> case coe v1 of
                                  (:) v24 v25
                                    -> case coe v3 of
                                         C__'8759'__314 v28 v29
                                           -> let v30
                                                    = coe
                                                        MAlonzo.Code.Data.List.Properties.du_'8759''45'injective_46 in
                                              coe
                                                (coe
                                                   seq (coe v30)
                                                   (let v31 = coe du_'8759''45'injectiveI_390 in
                                                    coe
                                                      (coe
                                                         seq (coe v31)
                                                         (let v32
                                                                = coe
                                                                    du_equalbyPredicate'43''43'I_1588
                                                                    (coe v13) (coe v25) (coe v17)
                                                                    (coe v29) (coe v11) (coe v23) in
                                                          coe
                                                            (case coe v32 of
                                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v33 v34
                                                                 -> case coe v34 of
                                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v35 v36
                                                                        -> coe
                                                                             seq (coe v36)
                                                                             (coe
                                                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                erased
                                                                                (coe
                                                                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                   erased
                                                                                   (coe
                                                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                      erased
                                                                                      erased)))
                                                                      _ -> MAlonzo.RTE.mazUnreachableError
                                                               _ -> MAlonzo.RTE.mazUnreachableError)))))
                                         _ -> MAlonzo.RTE.mazUnreachableError
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Utils.List.equalbyPredicateI
d_equalbyPredicateI_1810 ::
  () ->
  (AgdaAny -> ()) ->
  T_Bwd_6 ->
  T_Bwd_6 ->
  [AgdaAny] ->
  [AgdaAny] ->
  [AgdaAny] ->
  T_IList_302 ->
  T_IBwd_396 ->
  T_IBwd_396 ->
  T_IList_302 ->
  T_IList_302 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_IIBwd_832 ->
  T_IIBwd_832 ->
  (AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  (AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_equalbyPredicateI_1810 ~v0 ~v1 v2 v3 ~v4 ~v5 ~v6 ~v7 v8 v9 ~v10
                         ~v11 ~v12 ~v13 ~v14 ~v15 ~v16 ~v17 ~v18 ~v19 ~v20 v21 v22 ~v23 ~v24
  = du_equalbyPredicateI_1810 v2 v3 v8 v9 v21 v22
du_equalbyPredicateI_1810 ::
  T_Bwd_6 ->
  T_Bwd_6 ->
  T_IBwd_396 ->
  T_IBwd_396 ->
  T_IIBwd_832 ->
  T_IIBwd_832 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_equalbyPredicateI_1810 v0 v1 v2 v3 v4 v5
  = let v6
          = coe
              du_equalbyPredicate'43''43'I_1588
              (coe
                 du__'60''62''62'__42 (coe v0)
                 (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
              (coe
                 du__'60''62''62'__42 (coe v1)
                 (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
              (coe du__'60''62''62'I__418 (coe v0) (coe v2) (coe C_'91''93'_308))
              (coe du__'60''62''62'I__418 (coe v1) (coe v3) (coe C_'91''93'_308))
              (coe
                 du__'60''62''62'II__870 (coe v0) (coe v2) (coe v4)
                 (coe C_'91''93'_810))
              (coe du_IIBwd2IIList_902 (coe v1) (coe v3) (coe v5)) in
    coe
      (case coe v6 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
           -> case coe v8 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                  -> coe
                       seq (coe v10)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                             (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased)))
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> MAlonzo.RTE.mazUnreachableError)
