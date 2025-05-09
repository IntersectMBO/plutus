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

module MAlonzo.Code.Data.Sign.Base where

import Data.Text qualified
import MAlonzo.Code.Algebra.Bundles.Raw qualified
import MAlonzo.RTE (AgdaAny, add64, addInt, coe, eq64, eqInt, erased, geqInt, lt64, ltInt, mul64,
                    mulInt, quot64, quotInt, rem64, remInt, sub64, subInt, word64FromNat,
                    word64ToNat)
import MAlonzo.RTE qualified

-- Data.Sign.Base.Sign
d_Sign_6 = ()
data T_Sign_6 = C_'45'_8 | C_'43'_10
-- Data.Sign.Base.opposite
d_opposite_12 :: T_Sign_6 -> T_Sign_6
d_opposite_12 v0
  = case coe v0 of
      C_'45'_8  -> coe C_'43'_10
      C_'43'_10 -> coe C_'45'_8
      _         -> MAlonzo.RTE.mazUnreachableError
-- Data.Sign.Base._*_
d__'42'__14 :: T_Sign_6 -> T_Sign_6 -> T_Sign_6
d__'42'__14 v0 v1
  = case coe v0 of
      C_'45'_8  -> coe d_opposite_12 (coe v1)
      C_'43'_10 -> coe v1
      _         -> MAlonzo.RTE.mazUnreachableError
-- Data.Sign.Base.*-rawMagma
d_'42''45'rawMagma_20 ::
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMagma_36
d_'42''45'rawMagma_20
  = coe
      MAlonzo.Code.Algebra.Bundles.Raw.C_RawMagma'46'constructor_341
      d__'42'__14
-- Data.Sign.Base.*-1-rawMonoid
d_'42''45'1'45'rawMonoid_22 ::
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMonoid_64
d_'42''45'1'45'rawMonoid_22
  = coe
      MAlonzo.Code.Algebra.Bundles.Raw.C_RawMonoid'46'constructor_745
      d__'42'__14 (coe C_'43'_10)
-- Data.Sign.Base.*-1-rawGroup
d_'42''45'1'45'rawGroup_24 ::
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawGroup_96
d_'42''45'1'45'rawGroup_24
  = coe
      MAlonzo.Code.Algebra.Bundles.Raw.C_RawGroup'46'constructor_1207
      d__'42'__14 (coe C_'43'_10) d_opposite_12
