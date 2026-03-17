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

module MAlonzo.Code.Tactic.Defaults where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Algebra.Lattice.Bundles
import qualified MAlonzo.Code.Class.MonadTC
import qualified MAlonzo.Code.Reflection.Debug

-- Tactic.Defaults.defaultTCOptionsI
d_defaultTCOptionsI_4 :: MAlonzo.Code.Class.MonadTC.T_TCOptions_12
d_defaultTCOptionsI_4
  = coe
      MAlonzo.Code.Class.MonadTC.C_TCOptions'46'constructor_49
      (coe
         MAlonzo.Code.Reflection.Debug.C_DebugOptions'46'constructor_1897
         (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
         (coe MAlonzo.Code.Reflection.Debug.C_All_60)
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.d_'8869'_716
            (coe MAlonzo.Code.Reflection.Debug.d_Filter'45'Alg_68))
         (coe (100 :: Integer)) (coe '\9475'))
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
            (coe ("reduceDec/constrs" :: Data.Text.Text)) (coe (5 :: Integer)))
         (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
