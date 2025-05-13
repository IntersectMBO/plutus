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

module MAlonzo.Code.Data.Parity.Base where

import Data.Text qualified
import MAlonzo.Code.Algebra.Bundles.Raw qualified
import MAlonzo.Code.Data.Sign.Base qualified
import MAlonzo.RTE (AgdaAny, add64, addInt, coe, eq64, eqInt, erased, geqInt, lt64, ltInt, mul64,
                    mulInt, quot64, quotInt, rem64, remInt, sub64, subInt, word64FromNat,
                    word64ToNat)
import MAlonzo.RTE qualified

-- Data.Parity.Base.Parity
d_Parity_6 = ()
data T_Parity_6 = C_0ℙ_8 | C_1ℙ_10
-- Data.Parity.Base._⁻¹
d__'8315''185'_12 :: T_Parity_6 -> T_Parity_6
d__'8315''185'_12 v0
  = case coe v0 of
      C_0ℙ_8  -> coe C_1ℙ_10
      C_1ℙ_10 -> coe C_0ℙ_8
      _       -> MAlonzo.RTE.mazUnreachableError
-- Data.Parity.Base._+_
d__'43'__14 :: T_Parity_6 -> T_Parity_6 -> T_Parity_6
d__'43'__14 v0 v1
  = case coe v0 of
      C_0ℙ_8  -> coe v1
      C_1ℙ_10 -> coe d__'8315''185'_12 (coe v1)
      _       -> MAlonzo.RTE.mazUnreachableError
-- Data.Parity.Base._*_
d__'42'__20 :: T_Parity_6 -> T_Parity_6 -> T_Parity_6
d__'42'__20 v0 v1
  = case coe v0 of
      C_0ℙ_8  -> coe v0
      C_1ℙ_10 -> coe v1
      _       -> MAlonzo.RTE.mazUnreachableError
-- Data.Parity.Base.+-rawMagma
d_'43''45'rawMagma_26 ::
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMagma_36
d_'43''45'rawMagma_26
  = coe
      MAlonzo.Code.Algebra.Bundles.Raw.C_RawMagma'46'constructor_341
      d__'43'__14
-- Data.Parity.Base.+-0-rawMonoid
d_'43''45'0'45'rawMonoid_28 ::
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMonoid_64
d_'43''45'0'45'rawMonoid_28
  = coe
      MAlonzo.Code.Algebra.Bundles.Raw.C_RawMonoid'46'constructor_745
      d__'43'__14 (coe C_0ℙ_8)
-- Data.Parity.Base.+-0-rawGroup
d_'43''45'0'45'rawGroup_30 ::
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawGroup_96
d_'43''45'0'45'rawGroup_30
  = coe
      MAlonzo.Code.Algebra.Bundles.Raw.C_RawGroup'46'constructor_1207
      d__'43'__14 (coe C_0ℙ_8) d__'8315''185'_12
-- Data.Parity.Base.*-rawMagma
d_'42''45'rawMagma_32 ::
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMagma_36
d_'42''45'rawMagma_32
  = coe
      MAlonzo.Code.Algebra.Bundles.Raw.C_RawMagma'46'constructor_341
      d__'42'__20
-- Data.Parity.Base.*-1-rawMonoid
d_'42''45'1'45'rawMonoid_34 ::
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMonoid_64
d_'42''45'1'45'rawMonoid_34
  = coe
      MAlonzo.Code.Algebra.Bundles.Raw.C_RawMonoid'46'constructor_745
      d__'42'__20 (coe C_1ℙ_10)
-- Data.Parity.Base.+-*-rawNearSemiring
d_'43''45''42''45'rawNearSemiring_36 ::
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawNearSemiring_134
d_'43''45''42''45'rawNearSemiring_36
  = coe
      MAlonzo.Code.Algebra.Bundles.Raw.C_RawNearSemiring'46'constructor_1729
      d__'43'__14 d__'42'__20 (coe C_0ℙ_8)
-- Data.Parity.Base.+-*-rawSemiring
d_'43''45''42''45'rawSemiring_38 ::
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawSemiring_174
d_'43''45''42''45'rawSemiring_38
  = coe
      MAlonzo.Code.Algebra.Bundles.Raw.C_RawSemiring'46'constructor_2353
      d__'43'__14 d__'42'__20 (coe C_0ℙ_8) (coe C_1ℙ_10)
-- Data.Parity.Base.toSign
d_toSign_40 :: T_Parity_6 -> MAlonzo.Code.Data.Sign.Base.T_Sign_6
d_toSign_40 v0
  = case coe v0 of
      C_0ℙ_8  -> coe MAlonzo.Code.Data.Sign.Base.C_'43'_10
      C_1ℙ_10 -> coe MAlonzo.Code.Data.Sign.Base.C_'45'_8
      _       -> MAlonzo.RTE.mazUnreachableError
-- Data.Parity.Base.fromSign
d_fromSign_42 :: MAlonzo.Code.Data.Sign.Base.T_Sign_6 -> T_Parity_6
d_fromSign_42 v0
  = case coe v0 of
      MAlonzo.Code.Data.Sign.Base.C_'45'_8  -> coe C_1ℙ_10
      MAlonzo.Code.Data.Sign.Base.C_'43'_10 -> coe C_0ℙ_8
      _                                     -> MAlonzo.RTE.mazUnreachableError
