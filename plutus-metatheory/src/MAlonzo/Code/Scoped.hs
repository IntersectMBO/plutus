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

module MAlonzo.Code.Scoped where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.Nat
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Builtin
import qualified MAlonzo.Code.Builtin.Constant.AtomicType
import qualified MAlonzo.Code.Builtin.Constant.Type
import qualified MAlonzo.Code.Builtin.Signature
import qualified MAlonzo.Code.Data.Fin.Base
import qualified MAlonzo.Code.Data.Integer.Show
import qualified MAlonzo.Code.Data.Maybe.Base
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Data.String.Base
import qualified MAlonzo.Code.Raw
import qualified MAlonzo.Code.RawU
import qualified MAlonzo.Code.Utils

import PlutusCore.DeBruijn
import Raw
import qualified Data.Text as T
-- Scoped.ScopedTy
d_ScopedTy_14 a0 = ()
data T_ScopedTy_14
  = C_'96'_18 MAlonzo.Code.Data.Fin.Base.T_Fin_10 |
    C__'8658'__20 T_ScopedTy_14 T_ScopedTy_14 |
    C_Π_22 MAlonzo.Code.Utils.T_Kind_702 T_ScopedTy_14 |
    C_ƛ_24 MAlonzo.Code.Utils.T_Kind_702 T_ScopedTy_14 |
    C__'183'__26 T_ScopedTy_14 T_ScopedTy_14 |
    C_con_30 MAlonzo.Code.Utils.T_Kind_702
             MAlonzo.Code.Builtin.Constant.Type.T_TyCon_6 |
    C_μ_32 T_ScopedTy_14 T_ScopedTy_14 |
    C_SOP_34 (MAlonzo.Code.Utils.T_List_384
                (MAlonzo.Code.Utils.T_List_384 T_ScopedTy_14))
-- Scoped.Tel⋆
d_Tel'8902'_36 :: Integer -> Integer -> ()
d_Tel'8902'_36 = erased
-- Scoped.Weirdℕ
d_Weirdℕ_42 a0 = ()
data T_Weirdℕ_42 = C_Z_44 | C_S_48 T_Weirdℕ_42 | C_T_52 T_Weirdℕ_42
-- Scoped.WeirdFin
d_WeirdFin_56 a0 a1 = ()
data T_WeirdFin_56
  = C_Z_62 | C_S_68 T_WeirdFin_56 | C_T_74 T_WeirdFin_56
-- Scoped.wtoℕ
d_wtoℕ_78 :: Integer -> T_Weirdℕ_42 -> Integer
d_wtoℕ_78 ~v0 v1 = du_wtoℕ_78 v1
du_wtoℕ_78 :: T_Weirdℕ_42 -> Integer
du_wtoℕ_78 v0
  = case coe v0 of
      C_Z_44 -> coe (0 :: Integer)
      C_S_48 v2
        -> coe addInt (coe (1 :: Integer)) (coe du_wtoℕ_78 (coe v2))
      C_T_52 v2
        -> coe addInt (coe (1 :: Integer)) (coe du_wtoℕ_78 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Scoped.WeirdFintoℕ
d_WeirdFintoℕ_88 ::
  Integer -> T_Weirdℕ_42 -> T_WeirdFin_56 -> Integer
d_WeirdFintoℕ_88 ~v0 v1 v2 = du_WeirdFintoℕ_88 v1 v2
du_WeirdFintoℕ_88 :: T_Weirdℕ_42 -> T_WeirdFin_56 -> Integer
du_WeirdFintoℕ_88 v0 v1
  = case coe v1 of
      C_Z_62 -> coe (0 :: Integer)
      C_S_68 v4
        -> case coe v0 of
             C_S_48 v6
               -> coe
                    addInt (coe (1 :: Integer))
                    (coe du_WeirdFintoℕ_88 (coe v6) (coe v4))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_T_74 v4
        -> case coe v0 of
             C_T_52 v6 -> coe du_WeirdFintoℕ_88 (coe v6) (coe v4)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Scoped.wtoℕTm
d_wtoℕTm_96 :: Integer -> T_Weirdℕ_42 -> Integer
d_wtoℕTm_96 ~v0 v1 = du_wtoℕTm_96 v1
du_wtoℕTm_96 :: T_Weirdℕ_42 -> Integer
du_wtoℕTm_96 v0
  = case coe v0 of
      C_Z_44 -> coe (0 :: Integer)
      C_S_48 v2
        -> coe addInt (coe (1 :: Integer)) (coe du_wtoℕTm_96 (coe v2))
      C_T_52 v2 -> coe du_wtoℕTm_96 (coe v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Scoped.wtoℕTy
d_wtoℕTy_104 :: Integer -> T_Weirdℕ_42 -> Integer
d_wtoℕTy_104 ~v0 v1 = du_wtoℕTy_104 v1
du_wtoℕTy_104 :: T_Weirdℕ_42 -> Integer
du_wtoℕTy_104 v0
  = case coe v0 of
      C_Z_44 -> coe (0 :: Integer)
      C_S_48 v2 -> coe du_wtoℕTm_96 (coe v2)
      C_T_52 v2
        -> coe addInt (coe (1 :: Integer)) (coe du_wtoℕTm_96 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Scoped.lookupWTm
d_lookupWTm_116 ::
  Integer -> Integer -> T_Weirdℕ_42 -> Maybe Integer
d_lookupWTm_116 v0 ~v1 v2 = du_lookupWTm_116 v0 v2
du_lookupWTm_116 :: Integer -> T_Weirdℕ_42 -> Maybe Integer
du_lookupWTm_116 v0 v1
  = case coe v0 of
      0 -> case coe v1 of
             C_Z_44 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             C_S_48 v3
               -> coe
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe (0 :: Integer))
             C_T_52 v3 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> let v2 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (case coe v1 of
                C_Z_44 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                C_S_48 v4
                  -> coe
                       MAlonzo.Code.Utils.du_fmap_224
                       (coe MAlonzo.Code.Utils.d_MaybeMonad_240)
                       (coe (\ v5 -> addInt (coe (1 :: Integer)) (coe v5)))
                       (coe du_lookupWTm_116 (coe v2) (coe v4))
                C_T_52 v4 -> coe du_lookupWTm_116 (coe v2) (coe v4)
                _ -> MAlonzo.RTE.mazUnreachableError)
-- Scoped.lookupWTy
d_lookupWTy_138 ::
  Integer -> Integer -> T_Weirdℕ_42 -> Maybe Integer
d_lookupWTy_138 v0 ~v1 v2 = du_lookupWTy_138 v0 v2
du_lookupWTy_138 :: Integer -> T_Weirdℕ_42 -> Maybe Integer
du_lookupWTy_138 v0 v1
  = case coe v0 of
      0 -> case coe v1 of
             C_Z_44 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             C_S_48 v3 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             C_T_52 v3
               -> coe
                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe (0 :: Integer))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> let v2 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (case coe v1 of
                C_Z_44 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                C_S_48 v4 -> coe du_lookupWTy_138 (coe v2) (coe v4)
                C_T_52 v4
                  -> coe
                       MAlonzo.Code.Utils.du_fmap_224
                       (coe MAlonzo.Code.Utils.d_MaybeMonad_240)
                       (coe (\ v5 -> addInt (coe (1 :: Integer)) (coe v5)))
                       (coe du_lookupWTy_138 (coe v2) (coe v4))
                _ -> MAlonzo.RTE.mazUnreachableError)
-- Scoped.lookupWTm'
d_lookupWTm''_158 :: Integer -> Integer -> T_Weirdℕ_42 -> Integer
d_lookupWTm''_158 v0 ~v1 v2 = du_lookupWTm''_158 v0 v2
du_lookupWTm''_158 :: Integer -> T_Weirdℕ_42 -> Integer
du_lookupWTm''_158 v0 v1
  = case coe v1 of
      C_Z_44 -> coe v0
      C_S_48 v3
        -> case coe v0 of
             0 -> coe (1 :: Integer)
             _ -> let v4 = subInt (coe v0) (coe (1 :: Integer)) in
                  coe
                    (coe
                       addInt (coe (1 :: Integer))
                       (coe du_lookupWTm''_158 (coe v4) (coe v3)))
      C_T_52 v3
        -> coe
             addInt (coe (1 :: Integer))
             (coe du_lookupWTm''_158 (coe v0) (coe v3))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Scoped.lookupWTy'
d_lookupWTy''_176 :: Integer -> Integer -> T_Weirdℕ_42 -> Integer
d_lookupWTy''_176 v0 ~v1 v2 = du_lookupWTy''_176 v0 v2
du_lookupWTy''_176 :: Integer -> T_Weirdℕ_42 -> Integer
du_lookupWTy''_176 v0 v1
  = case coe v1 of
      C_Z_44 -> coe v0
      C_S_48 v3
        -> coe
             addInt (coe (1 :: Integer))
             (coe du_lookupWTy''_176 (coe v0) (coe v3))
      C_T_52 v3
        -> case coe v0 of
             0 -> coe (1 :: Integer)
             _ -> let v4 = subInt (coe v0) (coe (1 :: Integer)) in
                  coe
                    (coe
                       addInt (coe (1 :: Integer))
                       (coe du_lookupWTy''_176 (coe v4) (coe v3)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Scoped.shifterTy
d_shifterTy_194 ::
  Integer ->
  T_Weirdℕ_42 ->
  MAlonzo.Code.Raw.T_RawTy_2 -> MAlonzo.Code.Raw.T_RawTy_2
d_shifterTy_194 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Raw.C_'96'_6 v3
        -> coe
             MAlonzo.Code.Raw.C_'96'_6
             (coe
                MAlonzo.Code.Data.Maybe.Base.du_maybe_32 (coe (\ v4 -> v4))
                (coe (100 :: Integer))
                (coe
                   du_lookupWTy_138
                   (coe
                      MAlonzo.Code.Data.Nat.Base.d_'8739'_'45'_'8739'_280 (coe v3)
                      (coe (1 :: Integer)))
                   (coe v1)))
      MAlonzo.Code.Raw.C__'8658'__8 v3 v4
        -> coe
             MAlonzo.Code.Raw.C__'8658'__8
             (coe d_shifterTy_194 (coe v0) (coe v1) (coe v3))
             (coe d_shifterTy_194 (coe v0) (coe v1) (coe v4))
      MAlonzo.Code.Raw.C_Π_10 v3 v4
        -> coe
             MAlonzo.Code.Raw.C_Π_10 (coe v3)
             (coe
                d_shifterTy_194 (coe addInt (coe (1 :: Integer)) (coe v0))
                (coe C_T_52 v1) (coe v4))
      MAlonzo.Code.Raw.C_ƛ_12 v3 v4
        -> coe
             MAlonzo.Code.Raw.C_ƛ_12 (coe v3)
             (coe
                d_shifterTy_194 (coe addInt (coe (1 :: Integer)) (coe v0))
                (coe C_T_52 v1) (coe v4))
      MAlonzo.Code.Raw.C__'183'__14 v3 v4
        -> coe
             MAlonzo.Code.Raw.C__'183'__14
             (coe d_shifterTy_194 (coe v0) (coe v1) (coe v3))
             (coe d_shifterTy_194 (coe v0) (coe v1) (coe v4))
      MAlonzo.Code.Raw.C_con_16 v3 -> coe v2
      MAlonzo.Code.Raw.C_μ_18 v3 v4
        -> coe
             MAlonzo.Code.Raw.C_μ_18
             (coe d_shifterTy_194 (coe v0) (coe v1) (coe v3))
             (coe d_shifterTy_194 (coe v0) (coe v1) (coe v4))
      MAlonzo.Code.Raw.C_SOP_22 v3
        -> coe
             MAlonzo.Code.Raw.C_SOP_22
             (coe d_shifterTyListList_206 (coe v0) (coe v1) (coe v3))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Scoped.shifterTyList
d_shifterTyList_200 ::
  Integer ->
  T_Weirdℕ_42 ->
  MAlonzo.Code.Utils.T_List_384 MAlonzo.Code.Raw.T_RawTy_2 ->
  MAlonzo.Code.Utils.T_List_384 MAlonzo.Code.Raw.T_RawTy_2
d_shifterTyList_200 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Utils.C_'91''93'_388 -> coe v2
      MAlonzo.Code.Utils.C__'8759'__390 v3 v4
        -> coe
             MAlonzo.Code.Utils.C__'8759'__390
             (coe d_shifterTy_194 (coe v0) (coe v1) (coe v3))
             (coe d_shifterTyList_200 (coe v0) (coe v1) (coe v4))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Scoped.shifterTyListList
d_shifterTyListList_206 ::
  Integer ->
  T_Weirdℕ_42 ->
  MAlonzo.Code.Utils.T_List_384
    (MAlonzo.Code.Utils.T_List_384 MAlonzo.Code.Raw.T_RawTy_2) ->
  MAlonzo.Code.Utils.T_List_384
    (MAlonzo.Code.Utils.T_List_384 MAlonzo.Code.Raw.T_RawTy_2)
d_shifterTyListList_206 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Utils.C_'91''93'_388 -> coe v2
      MAlonzo.Code.Utils.C__'8759'__390 v3 v4
        -> coe
             MAlonzo.Code.Utils.C__'8759'__390
             (coe d_shifterTyList_200 (coe v0) (coe v1) (coe v3))
             (coe d_shifterTyListList_206 (coe v0) (coe v1) (coe v4))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Scoped.shifter
d_shifter_272 ::
  Integer ->
  T_Weirdℕ_42 ->
  MAlonzo.Code.Raw.T_RawTm_32 -> MAlonzo.Code.Raw.T_RawTm_32
d_shifter_272 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Raw.C_'96'_34 v3
        -> coe
             MAlonzo.Code.Raw.C_'96'_34
             (coe
                MAlonzo.Code.Data.Maybe.Base.du_maybe_32 (coe (\ v4 -> v4))
                (coe (100 :: Integer))
                (coe
                   du_lookupWTm_116
                   (coe
                      MAlonzo.Code.Data.Nat.Base.d_'8739'_'45'_'8739'_280 (coe v3)
                      (coe (1 :: Integer)))
                   (coe v1)))
      MAlonzo.Code.Raw.C_Λ_36 v3 v4
        -> coe
             MAlonzo.Code.Raw.C_Λ_36 (coe v3)
             (coe
                d_shifter_272 (coe addInt (coe (1 :: Integer)) (coe v0))
                (coe C_T_52 v1) (coe v4))
      MAlonzo.Code.Raw.C__'183''8902'__38 v3 v4
        -> coe
             MAlonzo.Code.Raw.C__'183''8902'__38
             (coe d_shifter_272 (coe v0) (coe v1) (coe v3))
             (coe d_shifterTy_194 (coe v0) (coe v1) (coe v4))
      MAlonzo.Code.Raw.C_ƛ_40 v3 v4
        -> coe
             MAlonzo.Code.Raw.C_ƛ_40
             (coe d_shifterTy_194 (coe v0) (coe C_S_48 v1) (coe v3))
             (coe d_shifter_272 (coe v0) (coe C_S_48 v1) (coe v4))
      MAlonzo.Code.Raw.C__'183'__42 v3 v4
        -> coe
             MAlonzo.Code.Raw.C__'183'__42
             (coe d_shifter_272 (coe v0) (coe v1) (coe v3))
             (coe d_shifter_272 (coe v0) (coe v1) (coe v4))
      MAlonzo.Code.Raw.C_con_44 v3 -> coe v2
      MAlonzo.Code.Raw.C_error_46 v3
        -> coe
             MAlonzo.Code.Raw.C_error_46
             (coe d_shifterTy_194 (coe v0) (coe v1) (coe v3))
      MAlonzo.Code.Raw.C_builtin_48 v3 -> coe v2
      MAlonzo.Code.Raw.C_wrap_50 v3 v4 v5
        -> coe
             MAlonzo.Code.Raw.C_wrap_50
             (coe d_shifterTy_194 (coe v0) (coe v1) (coe v3))
             (coe d_shifterTy_194 (coe v0) (coe v1) (coe v4))
             (coe d_shifter_272 (coe v0) (coe v1) (coe v5))
      MAlonzo.Code.Raw.C_unwrap_52 v3
        -> coe
             MAlonzo.Code.Raw.C_unwrap_52
             (coe d_shifter_272 (coe v0) (coe v1) (coe v3))
      MAlonzo.Code.Raw.C_constr_60 v3 v4 v5
        -> coe
             MAlonzo.Code.Raw.C_constr_60
             (coe d_shifterTy_194 (coe v0) (coe v1) (coe v3)) (coe v4)
             (coe d_shifterList_278 (coe v0) (coe v1) (coe v5))
      MAlonzo.Code.Raw.C_case_68 v3 v4 v5
        -> coe
             MAlonzo.Code.Raw.C_case_68
             (coe d_shifterTy_194 (coe v0) (coe v1) (coe v3))
             (coe d_shifter_272 (coe v0) (coe v1) (coe v4))
             (coe d_shifterList_278 (coe v0) (coe v1) (coe v5))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Scoped.shifterList
d_shifterList_278 ::
  Integer ->
  T_Weirdℕ_42 ->
  MAlonzo.Code.Utils.T_List_384 MAlonzo.Code.Raw.T_RawTm_32 ->
  MAlonzo.Code.Utils.T_List_384 MAlonzo.Code.Raw.T_RawTm_32
d_shifterList_278 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Utils.C_'91''93'_388 -> coe v2
      MAlonzo.Code.Utils.C__'8759'__390 v3 v4
        -> coe
             MAlonzo.Code.Utils.C__'8759'__390
             (coe d_shifter_272 (coe v0) (coe v1) (coe v3))
             (coe d_shifterList_278 (coe v0) (coe v1) (coe v4))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Scoped.unshifterTy
d_unshifterTy_360 ::
  Integer ->
  T_Weirdℕ_42 ->
  MAlonzo.Code.Raw.T_RawTy_2 -> MAlonzo.Code.Raw.T_RawTy_2
d_unshifterTy_360 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Raw.C_'96'_6 v3
        -> coe
             MAlonzo.Code.Raw.C_'96'_6
             (coe du_lookupWTy''_176 (coe v3) (coe v1))
      MAlonzo.Code.Raw.C__'8658'__8 v3 v4
        -> coe
             MAlonzo.Code.Raw.C__'8658'__8
             (coe d_unshifterTy_360 (coe v0) (coe v1) (coe v3))
             (coe d_unshifterTy_360 (coe v0) (coe v1) (coe v4))
      MAlonzo.Code.Raw.C_Π_10 v3 v4
        -> coe
             MAlonzo.Code.Raw.C_Π_10 (coe v3)
             (coe
                d_unshifterTy_360 (coe addInt (coe (1 :: Integer)) (coe v0))
                (coe C_T_52 v1) (coe v4))
      MAlonzo.Code.Raw.C_ƛ_12 v3 v4
        -> coe
             MAlonzo.Code.Raw.C_ƛ_12 (coe v3)
             (coe
                d_unshifterTy_360 (coe addInt (coe (1 :: Integer)) (coe v0))
                (coe C_T_52 v1) (coe v4))
      MAlonzo.Code.Raw.C__'183'__14 v3 v4
        -> coe
             MAlonzo.Code.Raw.C__'183'__14
             (coe d_unshifterTy_360 (coe v0) (coe v1) (coe v3))
             (coe d_unshifterTy_360 (coe v0) (coe v1) (coe v4))
      MAlonzo.Code.Raw.C_con_16 v3 -> coe v2
      MAlonzo.Code.Raw.C_μ_18 v3 v4
        -> coe
             MAlonzo.Code.Raw.C_μ_18
             (coe d_unshifterTy_360 (coe v0) (coe v1) (coe v3))
             (coe d_unshifterTy_360 (coe v0) (coe v1) (coe v4))
      MAlonzo.Code.Raw.C_SOP_22 v3
        -> coe
             MAlonzo.Code.Raw.C_SOP_22
             (coe d_unshifterTyListList_372 (coe v0) (coe v1) (coe v3))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Scoped.unshifterTyList
d_unshifterTyList_366 ::
  Integer ->
  T_Weirdℕ_42 ->
  MAlonzo.Code.Utils.T_List_384 MAlonzo.Code.Raw.T_RawTy_2 ->
  MAlonzo.Code.Utils.T_List_384 MAlonzo.Code.Raw.T_RawTy_2
d_unshifterTyList_366 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Utils.C_'91''93'_388 -> coe v2
      MAlonzo.Code.Utils.C__'8759'__390 v3 v4
        -> coe
             MAlonzo.Code.Utils.C__'8759'__390
             (coe d_unshifterTy_360 (coe v0) (coe v1) (coe v3))
             (coe d_unshifterTyList_366 (coe v0) (coe v1) (coe v4))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Scoped.unshifterTyListList
d_unshifterTyListList_372 ::
  Integer ->
  T_Weirdℕ_42 ->
  MAlonzo.Code.Utils.T_List_384
    (MAlonzo.Code.Utils.T_List_384 MAlonzo.Code.Raw.T_RawTy_2) ->
  MAlonzo.Code.Utils.T_List_384
    (MAlonzo.Code.Utils.T_List_384 MAlonzo.Code.Raw.T_RawTy_2)
d_unshifterTyListList_372 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Utils.C_'91''93'_388 -> coe v2
      MAlonzo.Code.Utils.C__'8759'__390 v3 v4
        -> coe
             MAlonzo.Code.Utils.C__'8759'__390
             (coe d_unshifterTyList_366 (coe v0) (coe v1) (coe v3))
             (coe d_unshifterTyListList_372 (coe v0) (coe v1) (coe v4))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Scoped.unshifter
d_unshifter_434 ::
  Integer ->
  T_Weirdℕ_42 ->
  MAlonzo.Code.Raw.T_RawTm_32 -> MAlonzo.Code.Raw.T_RawTm_32
d_unshifter_434 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Raw.C_'96'_34 v3
        -> coe
             MAlonzo.Code.Raw.C_'96'_34
             (coe du_lookupWTm''_158 (coe v3) (coe v1))
      MAlonzo.Code.Raw.C_Λ_36 v3 v4
        -> coe
             MAlonzo.Code.Raw.C_Λ_36 (coe v3)
             (coe
                d_unshifter_434 (coe addInt (coe (1 :: Integer)) (coe v0))
                (coe C_T_52 v1) (coe v4))
      MAlonzo.Code.Raw.C__'183''8902'__38 v3 v4
        -> coe
             MAlonzo.Code.Raw.C__'183''8902'__38
             (coe d_unshifter_434 (coe v0) (coe v1) (coe v3))
             (coe d_unshifterTy_360 (coe v0) (coe v1) (coe v4))
      MAlonzo.Code.Raw.C_ƛ_40 v3 v4
        -> coe
             MAlonzo.Code.Raw.C_ƛ_40
             (coe d_unshifterTy_360 (coe v0) (coe C_S_48 v1) (coe v3))
             (coe d_unshifter_434 (coe v0) (coe C_S_48 v1) (coe v4))
      MAlonzo.Code.Raw.C__'183'__42 v3 v4
        -> coe
             MAlonzo.Code.Raw.C__'183'__42
             (coe d_unshifter_434 (coe v0) (coe v1) (coe v3))
             (coe d_unshifter_434 (coe v0) (coe v1) (coe v4))
      MAlonzo.Code.Raw.C_con_44 v3 -> coe v2
      MAlonzo.Code.Raw.C_error_46 v3
        -> coe
             MAlonzo.Code.Raw.C_error_46
             (coe d_unshifterTy_360 (coe v0) (coe v1) (coe v3))
      MAlonzo.Code.Raw.C_builtin_48 v3 -> coe v2
      MAlonzo.Code.Raw.C_wrap_50 v3 v4 v5
        -> coe
             MAlonzo.Code.Raw.C_wrap_50
             (coe d_unshifterTy_360 (coe v0) (coe v1) (coe v3))
             (coe d_unshifterTy_360 (coe v0) (coe v1) (coe v4))
             (coe d_unshifter_434 (coe v0) (coe v1) (coe v5))
      MAlonzo.Code.Raw.C_unwrap_52 v3
        -> coe
             MAlonzo.Code.Raw.C_unwrap_52
             (coe d_unshifter_434 (coe v0) (coe v1) (coe v3))
      MAlonzo.Code.Raw.C_constr_60 v3 v4 v5
        -> coe
             MAlonzo.Code.Raw.C_constr_60
             (coe d_unshifterTy_360 (coe v0) (coe v1) (coe v3)) (coe v4)
             (coe d_unshifterList_440 (coe v0) (coe v1) (coe v5))
      MAlonzo.Code.Raw.C_case_68 v3 v4 v5
        -> coe
             MAlonzo.Code.Raw.C_case_68
             (coe d_unshifterTy_360 (coe v0) (coe v1) (coe v3))
             (coe d_unshifter_434 (coe v0) (coe v1) (coe v4))
             (coe d_unshifterList_440 (coe v0) (coe v1) (coe v5))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Scoped.unshifterList
d_unshifterList_440 ::
  Integer ->
  T_Weirdℕ_42 ->
  MAlonzo.Code.Utils.T_List_384 MAlonzo.Code.Raw.T_RawTm_32 ->
  MAlonzo.Code.Utils.T_List_384 MAlonzo.Code.Raw.T_RawTm_32
d_unshifterList_440 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Utils.C_'91''93'_388 -> coe v2
      MAlonzo.Code.Utils.C__'8759'__390 v3 v4
        -> coe
             MAlonzo.Code.Utils.C__'8759'__390
             (coe d_unshifter_434 (coe v0) (coe v1) (coe v3))
             (coe d_unshifterList_440 (coe v0) (coe v1) (coe v4))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Scoped.ScopedTm
d_ScopedTm_522 a0 a1 = ()
data T_ScopedTm_522
  = C_'96'_528 T_WeirdFin_56 |
    C_Λ_530 MAlonzo.Code.Utils.T_Kind_702 T_ScopedTm_522 |
    C__'183''8902'__532 T_ScopedTm_522 T_ScopedTy_14 |
    C_ƛ_534 T_ScopedTy_14 T_ScopedTm_522 |
    C__'183'__536 T_ScopedTm_522 T_ScopedTm_522 |
    C_con_538 MAlonzo.Code.RawU.T_TmCon_202 |
    C_error_540 T_ScopedTy_14 |
    C_builtin_544 MAlonzo.Code.Builtin.T_Builtin_2 |
    C_wrap_546 T_ScopedTy_14 T_ScopedTy_14 T_ScopedTm_522 |
    C_unwrap_548 T_ScopedTm_522 |
    C_constr_556 T_ScopedTy_14 Integer
                 (MAlonzo.Code.Utils.T_List_384 T_ScopedTm_522) |
    C_case_564 T_ScopedTy_14 T_ScopedTm_522
               (MAlonzo.Code.Utils.T_List_384 T_ScopedTm_522)
-- Scoped.Tel
d_Tel_568 :: Integer -> T_Weirdℕ_42 -> Integer -> ()
d_Tel_568 = erased
-- Scoped.FreeVariableError
type T_FreeVariableError_574 = FreeVariableError
d_FreeVariableError_574
  = error
      "MAlonzo Runtime Error: postulate evaluated: Scoped.FreeVariableError"
-- Scoped.ScopeError
d_ScopeError_576 = ()
type T_ScopeError_576 = ScopeError
pattern C_deBError_578 = DeBError
pattern C_freeVariableError_580 a0 = FreeVariableError a0
check_deBError_578 :: T_ScopeError_576
check_deBError_578 = DeBError
check_freeVariableError_580 ::
  T_FreeVariableError_574 -> T_ScopeError_576
check_freeVariableError_580 = FreeVariableError
cover_ScopeError_576 :: ScopeError -> ()
cover_ScopeError_576 x
  = case x of
      DeBError -> ()
      FreeVariableError _ -> ()
-- Scoped.ℕtoFin
d_ℕtoFin_584 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Utils.T_Either_6
    T_ScopeError_576 MAlonzo.Code.Data.Fin.Base.T_Fin_10
d_ℕtoFin_584 v0 v1
  = case coe v0 of
      0 -> coe MAlonzo.Code.Utils.C_inj'8321'_12 (coe C_deBError_578)
      _ -> let v2 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (case coe v1 of
                0 -> coe
                       MAlonzo.Code.Utils.C_inj'8322'_14
                       (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)
                _ -> let v3 = subInt (coe v1) (coe (1 :: Integer)) in
                     coe
                       (coe
                          MAlonzo.Code.Utils.du_fmap_224
                          (coe MAlonzo.Code.Utils.du_EitherP_274)
                          (coe MAlonzo.Code.Data.Fin.Base.C_suc_16)
                          (coe d_ℕtoFin_584 (coe v2) (coe v3))))
-- Scoped.ℕtoWeirdFin
d_ℕtoWeirdFin_596 ::
  Integer ->
  T_Weirdℕ_42 ->
  Integer ->
  MAlonzo.Code.Utils.T_Either_6 T_ScopeError_576 T_WeirdFin_56
d_ℕtoWeirdFin_596 ~v0 v1 v2 = du_ℕtoWeirdFin_596 v1 v2
du_ℕtoWeirdFin_596 ::
  T_Weirdℕ_42 ->
  Integer ->
  MAlonzo.Code.Utils.T_Either_6 T_ScopeError_576 T_WeirdFin_56
du_ℕtoWeirdFin_596 v0 v1
  = case coe v0 of
      C_Z_44
        -> coe MAlonzo.Code.Utils.C_inj'8321'_12 (coe C_deBError_578)
      C_S_48 v3
        -> case coe v1 of
             0 -> coe MAlonzo.Code.Utils.C_inj'8322'_14 (coe C_Z_62)
             _ -> let v4 = subInt (coe v1) (coe (1 :: Integer)) in
                  coe
                    (coe
                       MAlonzo.Code.Utils.du_eitherBind_42
                       (coe du_ℕtoWeirdFin_596 (coe v3) (coe v4))
                       (coe
                          (\ v5 -> coe MAlonzo.Code.Utils.C_inj'8322'_14 (coe C_S_68 v5))))
      C_T_52 v3
        -> coe
             MAlonzo.Code.Utils.du_eitherBind_42
             (coe du_ℕtoWeirdFin_596 (coe v3) (coe v1))
             (coe
                (\ v4 -> coe MAlonzo.Code.Utils.C_inj'8322'_14 (coe C_T_74 v4)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Scoped.scopeCheckTy
d_scopeCheckTy_616 ::
  Integer ->
  MAlonzo.Code.Raw.T_RawTy_2 ->
  MAlonzo.Code.Utils.T_Either_6 T_ScopeError_576 T_ScopedTy_14
d_scopeCheckTy_616 v0 v1
  = case coe v1 of
      MAlonzo.Code.Raw.C_'96'_6 v2
        -> coe
             MAlonzo.Code.Utils.du_fmap_224
             (coe MAlonzo.Code.Utils.du_EitherP_274) (coe C_'96'_18)
             (coe d_ℕtoFin_584 (coe v0) (coe v2))
      MAlonzo.Code.Raw.C__'8658'__8 v2 v3
        -> coe
             MAlonzo.Code.Utils.du_eitherBind_42
             (coe d_scopeCheckTy_616 (coe v0) (coe v2))
             (coe
                (\ v4 ->
                   coe
                     MAlonzo.Code.Utils.du_eitherBind_42
                     (coe d_scopeCheckTy_616 (coe v0) (coe v3))
                     (coe
                        (\ v5 ->
                           coe
                             MAlonzo.Code.Utils.C_inj'8322'_14
                             (coe C__'8658'__20 (coe v4) (coe v5))))))
      MAlonzo.Code.Raw.C_Π_10 v2 v3
        -> coe
             MAlonzo.Code.Utils.du_fmap_224
             (coe MAlonzo.Code.Utils.du_EitherP_274) (coe C_Π_22 (coe v2))
             (coe
                d_scopeCheckTy_616 (coe addInt (coe (1 :: Integer)) (coe v0))
                (coe v3))
      MAlonzo.Code.Raw.C_ƛ_12 v2 v3
        -> coe
             MAlonzo.Code.Utils.du_fmap_224
             (coe MAlonzo.Code.Utils.du_EitherP_274) (coe C_ƛ_24 (coe v2))
             (coe
                d_scopeCheckTy_616 (coe addInt (coe (1 :: Integer)) (coe v0))
                (coe v3))
      MAlonzo.Code.Raw.C__'183'__14 v2 v3
        -> coe
             MAlonzo.Code.Utils.du_eitherBind_42
             (coe d_scopeCheckTy_616 (coe v0) (coe v2))
             (coe
                (\ v4 ->
                   coe
                     MAlonzo.Code.Utils.du_eitherBind_42
                     (coe d_scopeCheckTy_616 (coe v0) (coe v3))
                     (coe
                        (\ v5 ->
                           coe
                             MAlonzo.Code.Utils.C_inj'8322'_14
                             (coe C__'183'__26 (coe v4) (coe v5))))))
      MAlonzo.Code.Raw.C_con_16 v2
        -> case coe v2 of
             MAlonzo.Code.Raw.C_atomic_24 v3
               -> coe
                    MAlonzo.Code.Utils.C_inj'8322'_14
                    (coe
                       C_con_30 (coe MAlonzo.Code.Utils.C_'9839'_706)
                       (coe MAlonzo.Code.Builtin.Constant.Type.C_atomic_8 (coe v3)))
             MAlonzo.Code.Raw.C_list_26
               -> coe
                    MAlonzo.Code.Utils.C_inj'8322'_14
                    (coe
                       C_con_30
                       (coe
                          MAlonzo.Code.Utils.C__'8658'__708
                          (coe MAlonzo.Code.Utils.C_'9839'_706)
                          (coe MAlonzo.Code.Utils.C_'9839'_706))
                       (coe MAlonzo.Code.Builtin.Constant.Type.C_list_10))
             MAlonzo.Code.Raw.C_array_28
               -> coe
                    MAlonzo.Code.Utils.C_inj'8322'_14
                    (coe
                       C_con_30
                       (coe
                          MAlonzo.Code.Utils.C__'8658'__708
                          (coe MAlonzo.Code.Utils.C_'9839'_706)
                          (coe MAlonzo.Code.Utils.C_'9839'_706))
                       (coe MAlonzo.Code.Builtin.Constant.Type.C_array_12))
             MAlonzo.Code.Raw.C_pair_30
               -> coe
                    MAlonzo.Code.Utils.C_inj'8322'_14
                    (coe
                       C_con_30
                       (coe
                          MAlonzo.Code.Utils.C__'8658'__708
                          (coe MAlonzo.Code.Utils.C_'9839'_706)
                          (coe
                             MAlonzo.Code.Utils.C__'8658'__708
                             (coe MAlonzo.Code.Utils.C_'9839'_706)
                             (coe MAlonzo.Code.Utils.C_'9839'_706)))
                       (coe MAlonzo.Code.Builtin.Constant.Type.C_pair_14))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Raw.C_μ_18 v2 v3
        -> coe
             MAlonzo.Code.Utils.du_eitherBind_42
             (coe d_scopeCheckTy_616 (coe v0) (coe v2))
             (coe
                (\ v4 ->
                   coe
                     MAlonzo.Code.Utils.du_eitherBind_42
                     (coe d_scopeCheckTy_616 (coe v0) (coe v3))
                     (coe
                        (\ v5 ->
                           coe
                             MAlonzo.Code.Utils.C_inj'8322'_14
                             (coe C_μ_32 (coe v4) (coe v5))))))
      MAlonzo.Code.Raw.C_SOP_22 v2
        -> coe
             MAlonzo.Code.Utils.du_eitherBind_42
             (coe d_scopeCheckTyListList_624 (coe v0) (coe v2))
             (coe
                (\ v3 ->
                   coe MAlonzo.Code.Utils.C_inj'8322'_14 (coe C_SOP_34 (coe v3))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Scoped.scopeCheckTyList
d_scopeCheckTyList_620 ::
  Integer ->
  MAlonzo.Code.Utils.T_List_384 MAlonzo.Code.Raw.T_RawTy_2 ->
  MAlonzo.Code.Utils.T_Either_6
    T_ScopeError_576 (MAlonzo.Code.Utils.T_List_384 T_ScopedTy_14)
d_scopeCheckTyList_620 v0 v1
  = case coe v1 of
      MAlonzo.Code.Utils.C_'91''93'_388
        -> coe MAlonzo.Code.Utils.C_inj'8322'_14 (coe v1)
      MAlonzo.Code.Utils.C__'8759'__390 v2 v3
        -> coe
             MAlonzo.Code.Utils.du_eitherBind_42
             (coe d_scopeCheckTy_616 (coe v0) (coe v2))
             (coe
                (\ v4 ->
                   coe
                     MAlonzo.Code.Utils.du_eitherBind_42
                     (coe d_scopeCheckTyList_620 (coe v0) (coe v3))
                     (coe
                        (\ v5 ->
                           coe
                             MAlonzo.Code.Utils.C_inj'8322'_14
                             (coe MAlonzo.Code.Utils.C__'8759'__390 (coe v4) (coe v5))))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Scoped.scopeCheckTyListList
d_scopeCheckTyListList_624 ::
  Integer ->
  MAlonzo.Code.Utils.T_List_384
    (MAlonzo.Code.Utils.T_List_384 MAlonzo.Code.Raw.T_RawTy_2) ->
  MAlonzo.Code.Utils.T_Either_6
    T_ScopeError_576
    (MAlonzo.Code.Utils.T_List_384
       (MAlonzo.Code.Utils.T_List_384 T_ScopedTy_14))
d_scopeCheckTyListList_624 v0 v1
  = case coe v1 of
      MAlonzo.Code.Utils.C_'91''93'_388
        -> coe MAlonzo.Code.Utils.C_inj'8322'_14 (coe v1)
      MAlonzo.Code.Utils.C__'8759'__390 v2 v3
        -> coe
             MAlonzo.Code.Utils.du_eitherBind_42
             (coe d_scopeCheckTyList_620 (coe v0) (coe v2))
             (coe
                (\ v4 ->
                   coe
                     MAlonzo.Code.Utils.du_eitherBind_42
                     (coe d_scopeCheckTyListList_624 (coe v0) (coe v3))
                     (coe
                        (\ v5 ->
                           coe
                             MAlonzo.Code.Utils.C_inj'8322'_14
                             (coe MAlonzo.Code.Utils.C__'8759'__390 (coe v4) (coe v5))))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Scoped.scopeCheckTm
d_scopeCheckTm_686 ::
  Integer ->
  T_Weirdℕ_42 ->
  MAlonzo.Code.Raw.T_RawTm_32 ->
  MAlonzo.Code.Utils.T_Either_6 T_ScopeError_576 T_ScopedTm_522
d_scopeCheckTm_686 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Raw.C_'96'_34 v3
        -> coe
             MAlonzo.Code.Utils.du_fmap_224
             (coe MAlonzo.Code.Utils.du_EitherP_274) (coe C_'96'_528)
             (coe du_ℕtoWeirdFin_596 (coe v1) (coe v3))
      MAlonzo.Code.Raw.C_Λ_36 v3 v4
        -> coe
             MAlonzo.Code.Utils.du_fmap_224
             (coe MAlonzo.Code.Utils.du_EitherP_274) (coe C_Λ_530 (coe v3))
             (coe
                d_scopeCheckTm_686 (coe addInt (coe (1 :: Integer)) (coe v0))
                (coe C_T_52 v1) (coe v4))
      MAlonzo.Code.Raw.C__'183''8902'__38 v3 v4
        -> coe
             MAlonzo.Code.Utils.du_eitherBind_42
             (coe d_scopeCheckTy_616 (coe v0) (coe v4))
             (coe
                (\ v5 ->
                   coe
                     MAlonzo.Code.Utils.du_eitherBind_42
                     (coe d_scopeCheckTm_686 (coe v0) (coe v1) (coe v3))
                     (coe
                        (\ v6 ->
                           coe
                             MAlonzo.Code.Utils.C_inj'8322'_14
                             (coe C__'183''8902'__532 (coe v6) (coe v5))))))
      MAlonzo.Code.Raw.C_ƛ_40 v3 v4
        -> coe
             MAlonzo.Code.Utils.du_eitherBind_42
             (coe d_scopeCheckTy_616 (coe v0) (coe v3))
             (coe
                (\ v5 ->
                   coe
                     MAlonzo.Code.Utils.du_eitherBind_42
                     (coe d_scopeCheckTm_686 (coe v0) (coe C_S_48 v1) (coe v4))
                     (coe
                        (\ v6 ->
                           coe
                             MAlonzo.Code.Utils.C_inj'8322'_14
                             (coe C_ƛ_534 (coe v5) (coe v6))))))
      MAlonzo.Code.Raw.C__'183'__42 v3 v4
        -> coe
             MAlonzo.Code.Utils.du_eitherBind_42
             (coe d_scopeCheckTm_686 (coe v0) (coe v1) (coe v3))
             (coe
                (\ v5 ->
                   coe
                     MAlonzo.Code.Utils.du_eitherBind_42
                     (coe d_scopeCheckTm_686 (coe v0) (coe v1) (coe v4))
                     (coe
                        (\ v6 ->
                           coe
                             MAlonzo.Code.Utils.C_inj'8322'_14
                             (coe C__'183'__536 (coe v5) (coe v6))))))
      MAlonzo.Code.Raw.C_con_44 v3
        -> coe
             MAlonzo.Code.Utils.C_inj'8322'_14
             (coe C_con_538 (coe MAlonzo.Code.RawU.d_tagCon2TmCon_256 (coe v3)))
      MAlonzo.Code.Raw.C_error_46 v3
        -> coe
             MAlonzo.Code.Utils.du_fmap_224
             (coe MAlonzo.Code.Utils.du_EitherP_274) (coe C_error_540)
             (coe d_scopeCheckTy_616 (coe v0) (coe v3))
      MAlonzo.Code.Raw.C_builtin_48 v3
        -> coe
             MAlonzo.Code.Utils.C_inj'8322'_14 (coe C_builtin_544 (coe v3))
      MAlonzo.Code.Raw.C_wrap_50 v3 v4 v5
        -> coe
             MAlonzo.Code.Utils.du_eitherBind_42
             (coe d_scopeCheckTy_616 (coe v0) (coe v3))
             (coe
                (\ v6 ->
                   coe
                     MAlonzo.Code.Utils.du_eitherBind_42
                     (coe d_scopeCheckTy_616 (coe v0) (coe v4))
                     (coe
                        (\ v7 ->
                           coe
                             MAlonzo.Code.Utils.du_eitherBind_42
                             (coe d_scopeCheckTm_686 (coe v0) (coe v1) (coe v5))
                             (coe
                                (\ v8 ->
                                   coe
                                     MAlonzo.Code.Utils.C_inj'8322'_14
                                     (coe C_wrap_546 (coe v6) (coe v7) (coe v8))))))))
      MAlonzo.Code.Raw.C_unwrap_52 v3
        -> coe
             MAlonzo.Code.Utils.du_fmap_224
             (coe MAlonzo.Code.Utils.du_EitherP_274) (coe C_unwrap_548)
             (coe d_scopeCheckTm_686 (coe v0) (coe v1) (coe v3))
      MAlonzo.Code.Raw.C_constr_60 v3 v4 v5
        -> coe
             MAlonzo.Code.Utils.du_eitherBind_42
             (coe d_scopeCheckTy_616 (coe v0) (coe v3))
             (coe
                (\ v6 ->
                   coe
                     MAlonzo.Code.Utils.du_eitherBind_42
                     (coe d_scopeCheckTmList_692 (coe v0) (coe v1) (coe v5))
                     (coe
                        (\ v7 ->
                           coe
                             MAlonzo.Code.Utils.C_inj'8322'_14
                             (coe C_constr_556 (coe v6) (coe v4) (coe v7))))))
      MAlonzo.Code.Raw.C_case_68 v3 v4 v5
        -> coe
             MAlonzo.Code.Utils.du_eitherBind_42
             (coe d_scopeCheckTy_616 (coe v0) (coe v3))
             (coe
                (\ v6 ->
                   coe
                     MAlonzo.Code.Utils.du_eitherBind_42
                     (coe d_scopeCheckTm_686 (coe v0) (coe v1) (coe v4))
                     (coe
                        (\ v7 ->
                           coe
                             MAlonzo.Code.Utils.du_eitherBind_42
                             (coe d_scopeCheckTmList_692 (coe v0) (coe v1) (coe v5))
                             (coe
                                (\ v8 ->
                                   coe
                                     MAlonzo.Code.Utils.C_inj'8322'_14
                                     (coe C_case_564 (coe v6) (coe v7) (coe v8))))))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Scoped.scopeCheckTmList
d_scopeCheckTmList_692 ::
  Integer ->
  T_Weirdℕ_42 ->
  MAlonzo.Code.Utils.T_List_384 MAlonzo.Code.Raw.T_RawTm_32 ->
  MAlonzo.Code.Utils.T_Either_6
    T_ScopeError_576 (MAlonzo.Code.Utils.T_List_384 T_ScopedTm_522)
d_scopeCheckTmList_692 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Utils.C_'91''93'_388
        -> coe MAlonzo.Code.Utils.C_inj'8322'_14 (coe v2)
      MAlonzo.Code.Utils.C__'8759'__390 v3 v4
        -> coe
             MAlonzo.Code.Utils.du_eitherBind_42
             (coe d_scopeCheckTm_686 (coe v0) (coe v1) (coe v3))
             (coe
                (\ v5 ->
                   coe
                     MAlonzo.Code.Utils.du_eitherBind_42
                     (coe d_scopeCheckTmList_692 (coe v0) (coe v1) (coe v4))
                     (coe
                        (\ v6 ->
                           coe
                             MAlonzo.Code.Utils.C_inj'8322'_14
                             (coe MAlonzo.Code.Utils.C__'8759'__390 (coe v5) (coe v6))))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Scoped.extricateScopeTy
d_extricateScopeTy_780 ::
  Integer -> T_ScopedTy_14 -> MAlonzo.Code.Raw.T_RawTy_2
d_extricateScopeTy_780 v0 v1
  = case coe v1 of
      C_'96'_18 v2
        -> coe
             MAlonzo.Code.Raw.C_'96'_6
             (coe MAlonzo.Code.Data.Fin.Base.du_toℕ_18 (coe v2))
      C__'8658'__20 v2 v3
        -> coe
             MAlonzo.Code.Raw.C__'8658'__8
             (coe d_extricateScopeTy_780 (coe v0) (coe v2))
             (coe d_extricateScopeTy_780 (coe v0) (coe v3))
      C_Π_22 v2 v3
        -> coe
             MAlonzo.Code.Raw.C_Π_10 (coe v2)
             (coe
                d_extricateScopeTy_780 (coe addInt (coe (1 :: Integer)) (coe v0))
                (coe v3))
      C_ƛ_24 v2 v3
        -> coe
             MAlonzo.Code.Raw.C_ƛ_12 (coe v2)
             (coe
                d_extricateScopeTy_780 (coe addInt (coe (1 :: Integer)) (coe v0))
                (coe v3))
      C__'183'__26 v2 v3
        -> coe
             MAlonzo.Code.Raw.C__'183'__14
             (coe d_extricateScopeTy_780 (coe v0) (coe v2))
             (coe d_extricateScopeTy_780 (coe v0) (coe v3))
      C_con_30 v2 v3
        -> case coe v3 of
             MAlonzo.Code.Builtin.Constant.Type.C_atomic_8 v4
               -> coe
                    MAlonzo.Code.Raw.C_con_16
                    (coe MAlonzo.Code.Raw.C_atomic_24 (coe v4))
             MAlonzo.Code.Builtin.Constant.Type.C_list_10
               -> coe MAlonzo.Code.Raw.C_con_16 (coe MAlonzo.Code.Raw.C_list_26)
             MAlonzo.Code.Builtin.Constant.Type.C_array_12
               -> coe MAlonzo.Code.Raw.C_con_16 (coe MAlonzo.Code.Raw.C_array_28)
             MAlonzo.Code.Builtin.Constant.Type.C_pair_14
               -> coe MAlonzo.Code.Raw.C_con_16 (coe MAlonzo.Code.Raw.C_pair_30)
             _ -> MAlonzo.RTE.mazUnreachableError
      C_μ_32 v2 v3
        -> coe
             MAlonzo.Code.Raw.C_μ_18
             (coe d_extricateScopeTy_780 (coe v0) (coe v2))
             (coe d_extricateScopeTy_780 (coe v0) (coe v3))
      C_SOP_34 v2
        -> coe
             MAlonzo.Code.Raw.C_SOP_22
             (coe d_extricateScopeTyListList_788 (coe v0) (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Scoped.extricateScopeTyList
d_extricateScopeTyList_784 ::
  Integer ->
  MAlonzo.Code.Utils.T_List_384 T_ScopedTy_14 ->
  MAlonzo.Code.Utils.T_List_384 MAlonzo.Code.Raw.T_RawTy_2
d_extricateScopeTyList_784 v0 v1
  = case coe v1 of
      MAlonzo.Code.Utils.C_'91''93'_388 -> coe v1
      MAlonzo.Code.Utils.C__'8759'__390 v2 v3
        -> coe
             MAlonzo.Code.Utils.C__'8759'__390
             (coe d_extricateScopeTy_780 (coe v0) (coe v2))
             (coe d_extricateScopeTyList_784 (coe v0) (coe v3))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Scoped.extricateScopeTyListList
d_extricateScopeTyListList_788 ::
  Integer ->
  MAlonzo.Code.Utils.T_List_384
    (MAlonzo.Code.Utils.T_List_384 T_ScopedTy_14) ->
  MAlonzo.Code.Utils.T_List_384
    (MAlonzo.Code.Utils.T_List_384 MAlonzo.Code.Raw.T_RawTy_2)
d_extricateScopeTyListList_788 v0 v1
  = case coe v1 of
      MAlonzo.Code.Utils.C_'91''93'_388 -> coe v1
      MAlonzo.Code.Utils.C__'8759'__390 v2 v3
        -> coe
             MAlonzo.Code.Utils.C__'8759'__390
             (coe d_extricateScopeTyList_784 (coe v0) (coe v2))
             (coe d_extricateScopeTyListList_788 (coe v0) (coe v3))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Scoped.extricateScope
d_extricateScope_828 ::
  Integer ->
  T_Weirdℕ_42 -> T_ScopedTm_522 -> MAlonzo.Code.Raw.T_RawTm_32
d_extricateScope_828 v0 v1 v2
  = case coe v2 of
      C_'96'_528 v3
        -> coe
             MAlonzo.Code.Raw.C_'96'_34
             (coe du_WeirdFintoℕ_88 (coe v1) (coe v3))
      C_Λ_530 v3 v4
        -> coe
             MAlonzo.Code.Raw.C_Λ_36 (coe v3)
             (coe
                d_extricateScope_828 (coe addInt (coe (1 :: Integer)) (coe v0))
                (coe C_T_52 v1) (coe v4))
      C__'183''8902'__532 v3 v4
        -> coe
             MAlonzo.Code.Raw.C__'183''8902'__38
             (coe d_extricateScope_828 (coe v0) (coe v1) (coe v3))
             (coe d_extricateScopeTy_780 (coe v0) (coe v4))
      C_ƛ_534 v3 v4
        -> coe
             MAlonzo.Code.Raw.C_ƛ_40
             (coe d_extricateScopeTy_780 (coe v0) (coe v3))
             (coe d_extricateScope_828 (coe v0) (coe C_S_48 v1) (coe v4))
      C__'183'__536 v3 v4
        -> coe
             MAlonzo.Code.Raw.C__'183'__42
             (coe d_extricateScope_828 (coe v0) (coe v1) (coe v3))
             (coe d_extricateScope_828 (coe v0) (coe v1) (coe v4))
      C_con_538 v3
        -> coe
             MAlonzo.Code.Raw.C_con_44
             (coe MAlonzo.Code.RawU.d_tmCon2TagCon_368 (coe v3))
      C_error_540 v3
        -> coe
             MAlonzo.Code.Raw.C_error_46
             (coe d_extricateScopeTy_780 (coe v0) (coe v3))
      C_builtin_544 v3 -> coe MAlonzo.Code.Raw.C_builtin_48 (coe v3)
      C_wrap_546 v3 v4 v5
        -> coe
             MAlonzo.Code.Raw.C_wrap_50
             (coe d_extricateScopeTy_780 (coe v0) (coe v3))
             (coe d_extricateScopeTy_780 (coe v0) (coe v4))
             (coe d_extricateScope_828 (coe v0) (coe v1) (coe v5))
      C_unwrap_548 v3
        -> coe
             MAlonzo.Code.Raw.C_unwrap_52
             (coe d_extricateScope_828 (coe v0) (coe v1) (coe v3))
      C_constr_556 v3 v4 v5
        -> coe
             MAlonzo.Code.Raw.C_constr_60
             (coe d_extricateScopeTy_780 (coe v0) (coe v3)) (coe v4)
             (coe d_extricateScopeList_834 (coe v0) (coe v1) (coe v5))
      C_case_564 v3 v4 v5
        -> coe
             MAlonzo.Code.Raw.C_case_68
             (coe d_extricateScopeTy_780 (coe v0) (coe v3))
             (coe d_extricateScope_828 (coe v0) (coe v1) (coe v4))
             (coe d_extricateScopeList_834 (coe v0) (coe v1) (coe v5))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Scoped.extricateScopeList
d_extricateScopeList_834 ::
  Integer ->
  T_Weirdℕ_42 ->
  MAlonzo.Code.Utils.T_List_384 T_ScopedTm_522 ->
  MAlonzo.Code.Utils.T_List_384 MAlonzo.Code.Raw.T_RawTm_32
d_extricateScopeList_834 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Utils.C_'91''93'_388 -> coe v2
      MAlonzo.Code.Utils.C__'8759'__390 v3 v4
        -> coe
             MAlonzo.Code.Utils.C__'8759'__390
             (coe d_extricateScope_828 (coe v0) (coe v1) (coe v3))
             (coe d_extricateScopeList_834 (coe v0) (coe v1) (coe v4))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Scoped.uglyWeirdFin
d_uglyWeirdFin_888 ::
  Integer ->
  T_Weirdℕ_42 ->
  T_WeirdFin_56 -> MAlonzo.Code.Agda.Builtin.String.T_String_6
d_uglyWeirdFin_888 ~v0 v1 v2 = du_uglyWeirdFin_888 v1 v2
du_uglyWeirdFin_888 ::
  T_Weirdℕ_42 ->
  T_WeirdFin_56 -> MAlonzo.Code.Agda.Builtin.String.T_String_6
du_uglyWeirdFin_888 v0 v1
  = case coe v1 of
      C_Z_62 -> coe ("0" :: Data.Text.Text)
      C_S_68 v4
        -> case coe v0 of
             C_S_48 v6
               -> coe
                    MAlonzo.Code.Data.String.Base.d__'43''43'__20
                    ("(S " :: Data.Text.Text)
                    (coe
                       MAlonzo.Code.Data.String.Base.d__'43''43'__20
                       (coe du_uglyWeirdFin_888 (coe v6) (coe v4))
                       (")" :: Data.Text.Text))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_T_74 v4
        -> case coe v0 of
             C_T_52 v6
               -> coe
                    MAlonzo.Code.Data.String.Base.d__'43''43'__20
                    ("(T " :: Data.Text.Text)
                    (coe
                       MAlonzo.Code.Data.String.Base.d__'43''43'__20
                       (coe du_uglyWeirdFin_888 (coe v6) (coe v4))
                       (")" :: Data.Text.Text))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Scoped.uglyTmCon
d_uglyTmCon_894 ::
  MAlonzo.Code.RawU.T_TmCon_202 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_uglyTmCon_894 v0
  = case coe v0 of
      MAlonzo.Code.RawU.C_tmCon_206 v1 v2
        -> let v3 = "size" :: Data.Text.Text in
           coe
             (case coe v1 of
                MAlonzo.Code.Builtin.Signature.C_atomic_12 v5
                  -> case coe v5 of
                       MAlonzo.Code.Builtin.Constant.AtomicType.C_aInteger_8
                         -> coe
                              MAlonzo.Code.Data.String.Base.d__'43''43'__20
                              ("(integer " :: Data.Text.Text)
                              (coe
                                 MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                 (MAlonzo.Code.Data.Integer.Show.d_show_6 (coe v2))
                                 (")" :: Data.Text.Text))
                       MAlonzo.Code.Builtin.Constant.AtomicType.C_aBytestring_10
                         -> coe ("bytestring" :: Data.Text.Text)
                       _ -> coe v3
                _ -> coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Scoped.showNat
d_showNat_902 ::
  Integer -> MAlonzo.Code.Agda.Builtin.String.T_String_6
d_showNat_902 = T.pack . show
-- Scoped.uglyBuiltin
d_uglyBuiltin_904 ::
  MAlonzo.Code.Builtin.T_Builtin_2 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_uglyBuiltin_904 v0
  = let v1 = "other" :: Data.Text.Text in
    coe
      (case coe v0 of
         MAlonzo.Code.Builtin.C_addInteger_4
           -> coe ("addInteger" :: Data.Text.Text)
         _ -> coe v1)
-- Scoped.ugly
d_ugly_910 ::
  Integer ->
  T_Weirdℕ_42 ->
  T_ScopedTm_522 -> MAlonzo.Code.Agda.Builtin.String.T_String_6
d_ugly_910 ~v0 v1 v2 = du_ugly_910 v1 v2
du_ugly_910 ::
  T_Weirdℕ_42 ->
  T_ScopedTm_522 -> MAlonzo.Code.Agda.Builtin.String.T_String_6
du_ugly_910 v0 v1
  = case coe v1 of
      C_'96'_528 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("(` " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (coe du_uglyWeirdFin_888 (coe v0) (coe v2))
                (")" :: Data.Text.Text))
      C_Λ_530 v2 v3
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("(\923 " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (coe du_ugly_910 (coe C_T_52 v0) (coe v3)) (")" :: Data.Text.Text))
      C__'183''8902'__532 v2 v3
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("( " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (coe du_ugly_910 (coe v0) (coe v2))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (" \183\8902 " :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      ("TYPE" :: Data.Text.Text) (")" :: Data.Text.Text))))
      C_ƛ_534 v2 v3
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("(\411 " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (coe du_ugly_910 (coe C_S_48 v0) (coe v3)) (")" :: Data.Text.Text))
      C__'183'__536 v2 v3
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("( " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (coe du_ugly_910 (coe v0) (coe v2))
                (coe
                   MAlonzo.Code.Data.String.Base.d__'43''43'__20
                   (" \183 " :: Data.Text.Text)
                   (coe
                      MAlonzo.Code.Data.String.Base.d__'43''43'__20
                      (coe du_ugly_910 (coe v0) (coe v3)) (")" :: Data.Text.Text))))
      C_con_538 v2 -> coe ("(con " :: Data.Text.Text)
      C_error_540 v2 -> coe ("error _" :: Data.Text.Text)
      C_builtin_544 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("builtin " :: Data.Text.Text) (d_uglyBuiltin_904 (coe v2))
      C_wrap_546 v2 v3 v4
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("(wrap " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (coe du_ugly_910 (coe v0) (coe v4)) (")" :: Data.Text.Text))
      C_unwrap_548 v2
        -> coe
             MAlonzo.Code.Data.String.Base.d__'43''43'__20
             ("(unwrap " :: Data.Text.Text)
             (coe
                MAlonzo.Code.Data.String.Base.d__'43''43'__20
                (coe du_ugly_910 (coe v0) (coe v2)) (")" :: Data.Text.Text))
      C_constr_556 v2 v3 v4 -> coe ("constr" :: Data.Text.Text)
      C_case_564 v2 v3 v4 -> coe ("case" :: Data.Text.Text)
      _ -> MAlonzo.RTE.mazUnreachableError
