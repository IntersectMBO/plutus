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

module MAlonzo.Code.Data.Nat.Binary.Base where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Algebra.Bundles.Raw
import qualified MAlonzo.Code.Data.Bool.Base
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Data.Sum.Base

-- Data.Nat.Binary.Base.ℕᵇ
d_ℕ'7495'_8 = ()
data T_ℕ'7495'_8
  = C_zero_10 | C_2'91'1'43'_'93'_12 T_ℕ'7495'_8 |
    C_1'43''91'2_'93'_14 T_ℕ'7495'_8
-- Data.Nat.Binary.Base._<_
d__'60'__16 a0 a1 = ()
data T__'60'__16
  = C_0'60'even_20 | C_0'60'odd_24 | C_even'60'even_30 T__'60'__16 |
    C_even'60'odd_36 T__'60'__16 |
    C_odd'60'even_42 MAlonzo.Code.Data.Sum.Base.T__'8846'__30 |
    C_odd'60'odd_48 T__'60'__16
-- Data.Nat.Binary.Base._>_
d__'62'__50 :: T_ℕ'7495'_8 -> T_ℕ'7495'_8 -> ()
d__'62'__50 = erased
-- Data.Nat.Binary.Base._≤_
d__'8804'__56 :: T_ℕ'7495'_8 -> T_ℕ'7495'_8 -> ()
d__'8804'__56 = erased
-- Data.Nat.Binary.Base._≥_
d__'8805'__62 :: T_ℕ'7495'_8 -> T_ℕ'7495'_8 -> ()
d__'8805'__62 = erased
-- Data.Nat.Binary.Base._≮_
d__'8814'__68 :: T_ℕ'7495'_8 -> T_ℕ'7495'_8 -> ()
d__'8814'__68 = erased
-- Data.Nat.Binary.Base._≯_
d__'8815'__74 :: T_ℕ'7495'_8 -> T_ℕ'7495'_8 -> ()
d__'8815'__74 = erased
-- Data.Nat.Binary.Base._≰_
d__'8816'__80 :: T_ℕ'7495'_8 -> T_ℕ'7495'_8 -> ()
d__'8816'__80 = erased
-- Data.Nat.Binary.Base._≱_
d__'8817'__86 :: T_ℕ'7495'_8 -> T_ℕ'7495'_8 -> ()
d__'8817'__86 = erased
-- Data.Nat.Binary.Base.double
d_double_92 :: T_ℕ'7495'_8 -> T_ℕ'7495'_8
d_double_92 v0
  = case coe v0 of
      C_zero_10 -> coe v0
      C_2'91'1'43'_'93'_12 v1
        -> coe C_2'91'1'43'_'93'_12 (coe C_1'43''91'2_'93'_14 (coe v1))
      C_1'43''91'2_'93'_14 v1
        -> coe C_2'91'1'43'_'93'_12 (coe d_double_92 (coe v1))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Nat.Binary.Base.suc
d_suc_98 :: T_ℕ'7495'_8 -> T_ℕ'7495'_8
d_suc_98 v0
  = case coe v0 of
      C_zero_10 -> coe C_1'43''91'2_'93'_14 (coe v0)
      C_2'91'1'43'_'93'_12 v1
        -> coe C_1'43''91'2_'93'_14 (coe d_suc_98 (coe v1))
      C_1'43''91'2_'93'_14 v1 -> coe C_2'91'1'43'_'93'_12 (coe v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Nat.Binary.Base.pred
d_pred_104 :: T_ℕ'7495'_8 -> T_ℕ'7495'_8
d_pred_104 v0
  = case coe v0 of
      C_zero_10 -> coe v0
      C_2'91'1'43'_'93'_12 v1 -> coe C_1'43''91'2_'93'_14 (coe v1)
      C_1'43''91'2_'93'_14 v1 -> coe d_double_92 (coe v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Nat.Binary.Base._+_
d__'43'__110 :: T_ℕ'7495'_8 -> T_ℕ'7495'_8 -> T_ℕ'7495'_8
d__'43'__110 v0 v1
  = case coe v0 of
      C_zero_10 -> coe v1
      C_2'91'1'43'_'93'_12 v2
        -> case coe v1 of
             C_zero_10 -> coe v0
             C_2'91'1'43'_'93'_12 v3
               -> coe
                    C_2'91'1'43'_'93'_12
                    (coe d_suc_98 (coe d__'43'__110 (coe v2) (coe v3)))
             C_1'43''91'2_'93'_14 v3
               -> coe
                    d_suc_98
                    (coe C_2'91'1'43'_'93'_12 (coe d__'43'__110 (coe v2) (coe v3)))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_1'43''91'2_'93'_14 v2
        -> case coe v1 of
             C_zero_10 -> coe v0
             C_2'91'1'43'_'93'_12 v3
               -> coe
                    d_suc_98
                    (coe C_2'91'1'43'_'93'_12 (coe d__'43'__110 (coe v2) (coe v3)))
             C_1'43''91'2_'93'_14 v3
               -> coe
                    d_suc_98
                    (coe C_1'43''91'2_'93'_14 (coe d__'43'__110 (coe v2) (coe v3)))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Nat.Binary.Base._*_
d__'42'__132 :: T_ℕ'7495'_8 -> T_ℕ'7495'_8 -> T_ℕ'7495'_8
d__'42'__132 v0 v1
  = case coe v0 of
      C_zero_10 -> coe v0
      C_2'91'1'43'_'93'_12 v2
        -> case coe v1 of
             C_zero_10 -> coe v1
             C_2'91'1'43'_'93'_12 v3
               -> coe
                    d_double_92
                    (coe
                       C_2'91'1'43'_'93'_12
                       (coe
                          d__'43'__110 (coe v2)
                          (coe d__'43'__110 (coe v3) (coe d__'42'__132 (coe v2) (coe v3)))))
             C_1'43''91'2_'93'_14 v3
               -> coe
                    C_2'91'1'43'_'93'_12
                    (coe d__'43'__110 (coe v2) (coe d__'42'__132 (coe v3) (coe v0)))
             _ -> MAlonzo.RTE.mazUnreachableError
      C_1'43''91'2_'93'_14 v2
        -> case coe v1 of
             C_zero_10 -> coe v1
             C_2'91'1'43'_'93'_12 v3
               -> coe
                    C_2'91'1'43'_'93'_12
                    (coe d__'43'__110 (coe v3) (coe d__'42'__132 (coe v2) (coe v1)))
             C_1'43''91'2_'93'_14 v3
               -> coe
                    C_1'43''91'2_'93'_14
                    (coe d__'43'__110 (coe v2) (coe d__'42'__132 (coe v3) (coe v0)))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Nat.Binary.Base.toℕ
d_toℕ_150 :: T_ℕ'7495'_8 -> Integer
d_toℕ_150 v0
  = case coe v0 of
      C_zero_10 -> coe (0 :: Integer)
      C_2'91'1'43'_'93'_12 v1
        -> coe
             mulInt (coe (2 :: Integer))
             (coe addInt (coe (1 :: Integer)) (coe d_toℕ_150 (coe v1)))
      C_1'43''91'2_'93'_14 v1
        -> coe
             addInt (coe (1 :: Integer))
             (coe mulInt (coe (2 :: Integer)) (coe d_toℕ_150 (coe v1)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Nat.Binary.Base.fromℕ
d_fromℕ_156 :: Integer -> T_ℕ'7495'_8
d_fromℕ_156 v0 = coe du_helper_162 (coe v0) (coe v0)
-- Data.Nat.Binary.Base.fromℕ.helper
d_helper_162 :: Integer -> Integer -> Integer -> T_ℕ'7495'_8
d_helper_162 ~v0 v1 v2 = du_helper_162 v1 v2
du_helper_162 :: Integer -> Integer -> T_ℕ'7495'_8
du_helper_162 v0 v1
  = let v2 = coe C_zero_10 in
    coe
      (case coe v0 of
         0 -> coe C_zero_10
         _ -> let v3 = subInt (coe v0) (coe (1 :: Integer)) in
              coe
                (case coe v1 of
                   _ | coe geqInt (coe v1) (coe (1 :: Integer)) ->
                       let v4 = subInt (coe v1) (coe (1 :: Integer)) in
                       coe
                         (coe
                            MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
                            (coe
                               eqInt
                               (coe
                                  MAlonzo.Code.Data.Nat.Base.du__'37'__326 (coe v3)
                                  (coe (2 :: Integer)))
                               (coe (0 :: Integer)))
                            (coe
                               C_1'43''91'2_'93'_14
                               (coe
                                  du_helper_162
                                  (coe
                                     MAlonzo.Code.Data.Nat.Base.du__'47'__314 (coe v3)
                                     (coe (2 :: Integer)))
                                  (coe v4)))
                            (coe
                               C_2'91'1'43'_'93'_12
                               (coe
                                  du_helper_162
                                  (coe
                                     MAlonzo.Code.Data.Nat.Base.du__'47'__314 (coe v3)
                                     (coe (2 :: Integer)))
                                  (coe v4))))
                   _ -> coe v2))
-- Data.Nat.Binary.Base.fromℕ'
d_fromℕ''_168 :: Integer -> T_ℕ'7495'_8
d_fromℕ''_168 v0
  = case coe v0 of
      0 -> coe C_zero_10
      _ -> let v1 = subInt (coe v0) (coe (1 :: Integer)) in
           coe (coe d_suc_98 (coe d_fromℕ''_168 (coe v1)))
-- Data.Nat.Binary.Base._<ℕ_
d__'60'ℕ__172 :: T_ℕ'7495'_8 -> T_ℕ'7495'_8 -> ()
d__'60'ℕ__172 = erased
-- Data.Nat.Binary.Base.size
d_size_174 :: T_ℕ'7495'_8 -> Integer
d_size_174 v0
  = case coe v0 of
      C_zero_10 -> coe (0 :: Integer)
      C_2'91'1'43'_'93'_12 v1
        -> coe addInt (coe (1 :: Integer)) (coe d_size_174 (coe v1))
      C_1'43''91'2_'93'_14 v1
        -> coe addInt (coe (1 :: Integer)) (coe d_size_174 (coe v1))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Nat.Binary.Base.0ᵇ
d_0'7495'_180 :: T_ℕ'7495'_8
d_0'7495'_180 = coe C_zero_10
-- Data.Nat.Binary.Base.1ᵇ
d_1'7495'_182 :: T_ℕ'7495'_8
d_1'7495'_182 = coe d_suc_98 (coe d_0'7495'_180)
-- Data.Nat.Binary.Base.2ᵇ
d_2'7495'_184 :: T_ℕ'7495'_8
d_2'7495'_184 = coe d_suc_98 (coe d_1'7495'_182)
-- Data.Nat.Binary.Base.3ᵇ
d_3'7495'_186 :: T_ℕ'7495'_8
d_3'7495'_186 = coe d_suc_98 (coe d_2'7495'_184)
-- Data.Nat.Binary.Base.4ᵇ
d_4'7495'_188 :: T_ℕ'7495'_8
d_4'7495'_188 = coe d_suc_98 (coe d_3'7495'_186)
-- Data.Nat.Binary.Base.5ᵇ
d_5'7495'_190 :: T_ℕ'7495'_8
d_5'7495'_190 = coe d_suc_98 (coe d_4'7495'_188)
-- Data.Nat.Binary.Base.6ᵇ
d_6'7495'_192 :: T_ℕ'7495'_8
d_6'7495'_192 = coe d_suc_98 (coe d_5'7495'_190)
-- Data.Nat.Binary.Base.7ᵇ
d_7'7495'_194 :: T_ℕ'7495'_8
d_7'7495'_194 = coe d_suc_98 (coe d_6'7495'_192)
-- Data.Nat.Binary.Base.8ᵇ
d_8'7495'_196 :: T_ℕ'7495'_8
d_8'7495'_196 = coe d_suc_98 (coe d_7'7495'_194)
-- Data.Nat.Binary.Base.9ᵇ
d_9'7495'_198 :: T_ℕ'7495'_8
d_9'7495'_198 = coe d_suc_98 (coe d_8'7495'_196)
-- Data.Nat.Binary.Base.+-rawMagma
d_'43''45'rawMagma_200 ::
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMagma_42
d_'43''45'rawMagma_200
  = coe
      MAlonzo.Code.Algebra.Bundles.Raw.C_RawMagma'46'constructor_487
      d__'43'__110
-- Data.Nat.Binary.Base.+-0-rawMonoid
d_'43''45'0'45'rawMonoid_202 ::
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMonoid_70
d_'43''45'0'45'rawMonoid_202
  = coe
      MAlonzo.Code.Algebra.Bundles.Raw.C_RawMonoid'46'constructor_857
      d__'43'__110 d_0'7495'_180
-- Data.Nat.Binary.Base.*-rawMagma
d_'42''45'rawMagma_204 ::
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMagma_42
d_'42''45'rawMagma_204
  = coe
      MAlonzo.Code.Algebra.Bundles.Raw.C_RawMagma'46'constructor_487
      d__'42'__132
-- Data.Nat.Binary.Base.*-1-rawMonoid
d_'42''45'1'45'rawMonoid_206 ::
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMonoid_70
d_'42''45'1'45'rawMonoid_206
  = coe
      MAlonzo.Code.Algebra.Bundles.Raw.C_RawMonoid'46'constructor_857
      d__'42'__132 d_1'7495'_182
