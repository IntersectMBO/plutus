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

module MAlonzo.Code.Data.Sign.Base where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Algebra.Bundles.Raw

-- Data.Sign.Base.Sign
d_Sign_6 = ()
data T_Sign_6 = C_'45'_8 | C_'43'_10
-- Data.Sign.Base.opposite
d_opposite_12 :: T_Sign_6 -> T_Sign_6
d_opposite_12 v0
  = case coe v0 of
      C_'45'_8 -> coe C_'43'_10
      C_'43'_10 -> coe C_'45'_8
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Sign.Base._*_
d__'42'__14 :: T_Sign_6 -> T_Sign_6 -> T_Sign_6
d__'42'__14 v0 v1
  = case coe v0 of
      C_'45'_8 -> coe d_opposite_12 (coe v1)
      C_'43'_10 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Sign.Base.*-rawMagma
d_'42''45'rawMagma_20 ::
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMagma_44
d_'42''45'rawMagma_20
  = coe MAlonzo.Code.Algebra.Bundles.Raw.C_constructor_68 d__'42'__14
-- Data.Sign.Base.*-1-rawMonoid
d_'42''45'1'45'rawMonoid_22 ::
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMonoid_74
d_'42''45'1'45'rawMonoid_22
  = coe
      MAlonzo.Code.Algebra.Bundles.Raw.C_constructor_102 d__'42'__14
      (coe C_'43'_10)
-- Data.Sign.Base.*-1-rawGroup
d_'42''45'1'45'rawGroup_24 ::
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawGroup_108
d_'42''45'1'45'rawGroup_24
  = coe
      MAlonzo.Code.Algebra.Bundles.Raw.C_constructor_142 d__'42'__14
      (coe C_'43'_10) d_opposite_12
