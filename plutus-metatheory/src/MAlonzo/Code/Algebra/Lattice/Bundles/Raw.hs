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

module MAlonzo.Code.Algebra.Lattice.Bundles.Raw where

import Data.Text qualified
import MAlonzo.Code.Agda.Primitive qualified
import MAlonzo.Code.Algebra.Bundles.Raw qualified
import MAlonzo.RTE (AgdaAny, add64, addInt, coe, eq64, eqInt, erased, geqInt, lt64, ltInt, mul64,
                    mulInt, quot64, quotInt, rem64, remInt, sub64, subInt, word64FromNat,
                    word64ToNat)
import MAlonzo.RTE qualified

-- Algebra.Lattice.Bundles.Raw.RawLattice
d_RawLattice_12 a0 a1 = ()
data T_RawLattice_12
  = C_RawLattice'46'constructor_121 (AgdaAny -> AgdaAny -> AgdaAny)
                                    (AgdaAny -> AgdaAny -> AgdaAny)
-- Algebra.Lattice.Bundles.Raw.RawLattice.Carrier
d_Carrier_26 :: T_RawLattice_12 -> ()
d_Carrier_26 = erased
-- Algebra.Lattice.Bundles.Raw.RawLattice._≈_
d__'8776'__28 :: T_RawLattice_12 -> AgdaAny -> AgdaAny -> ()
d__'8776'__28 = erased
-- Algebra.Lattice.Bundles.Raw.RawLattice._∧_
d__'8743'__30 :: T_RawLattice_12 -> AgdaAny -> AgdaAny -> AgdaAny
d__'8743'__30 v0
  = case coe v0 of
      C_RawLattice'46'constructor_121 v3 v4 -> coe v3
      _                                     -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Lattice.Bundles.Raw.RawLattice._∨_
d__'8744'__32 :: T_RawLattice_12 -> AgdaAny -> AgdaAny -> AgdaAny
d__'8744'__32 v0
  = case coe v0 of
      C_RawLattice'46'constructor_121 v3 v4 -> coe v4
      _                                     -> MAlonzo.RTE.mazUnreachableError
-- Algebra.Lattice.Bundles.Raw.RawLattice.∨-rawMagma
d_'8744''45'rawMagma_34 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_RawLattice_12 -> MAlonzo.Code.Algebra.Bundles.Raw.T_RawMagma_36
d_'8744''45'rawMagma_34 ~v0 ~v1 v2 = du_'8744''45'rawMagma_34 v2
du_'8744''45'rawMagma_34 ::
  T_RawLattice_12 -> MAlonzo.Code.Algebra.Bundles.Raw.T_RawMagma_36
du_'8744''45'rawMagma_34 v0
  = coe
      MAlonzo.Code.Algebra.Bundles.Raw.C_RawMagma'46'constructor_341
      (d__'8744'__32 (coe v0))
-- Algebra.Lattice.Bundles.Raw.RawLattice.∧-rawMagma
d_'8743''45'rawMagma_36 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_RawLattice_12 -> MAlonzo.Code.Algebra.Bundles.Raw.T_RawMagma_36
d_'8743''45'rawMagma_36 ~v0 ~v1 v2 = du_'8743''45'rawMagma_36 v2
du_'8743''45'rawMagma_36 ::
  T_RawLattice_12 -> MAlonzo.Code.Algebra.Bundles.Raw.T_RawMagma_36
du_'8743''45'rawMagma_36 v0
  = coe
      MAlonzo.Code.Algebra.Bundles.Raw.C_RawMagma'46'constructor_341
      (d__'8743'__30 (coe v0))
-- Algebra.Lattice.Bundles.Raw.RawLattice._._≉_
d__'8777'__40 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  T_RawLattice_12 -> AgdaAny -> AgdaAny -> ()
d__'8777'__40 = erased
