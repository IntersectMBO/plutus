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

module MAlonzo.Code.Reflection.Debug where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Bool
import qualified MAlonzo.Code.Agda.Builtin.Char
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.Reflection
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Algebra.Bundles.Raw
import qualified MAlonzo.Code.Algebra.Function
import qualified MAlonzo.Code.Algebra.Lattice.Bundles
import qualified MAlonzo.Code.Algebra.Lattice.Bundles.Raw
import qualified MAlonzo.Code.Algebra.Lattice.Structures
import qualified MAlonzo.Code.Data.Bool.Base
import qualified MAlonzo.Code.Data.Bool.Properties
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Data.String.Base
import qualified MAlonzo.Code.Data.String.Properties
import qualified MAlonzo.Code.Relation.Binary.Bundles
import qualified MAlonzo.Code.Relation.Binary.Structures
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core

-- Reflection.Debug.IsErrorPart
d_IsErrorPart_6 a0 = ()
newtype T_IsErrorPart_6
  = C_IsErrorPart'46'constructor_5 (AgdaAny ->
                                    MAlonzo.Code.Agda.Builtin.Reflection.T_ErrorPart_308)
-- Reflection.Debug.IsErrorPart.toErrorPart
d_toErrorPart_12 ::
  T_IsErrorPart_6 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Reflection.T_ErrorPart_308
d_toErrorPart_12 v0
  = case coe v0 of
      C_IsErrorPart'46'constructor_5 v1 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Reflection.Debug._.toErrorPart
d_toErrorPart_16 ::
  T_IsErrorPart_6 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Reflection.T_ErrorPart_308
d_toErrorPart_16 v0 = coe d_toErrorPart_12 (coe v0)
-- Reflection.Debug.IsErrorPart-String
d_IsErrorPart'45'String_18 :: T_IsErrorPart_6
d_IsErrorPart'45'String_18
  = coe
      C_IsErrorPart'46'constructor_5
      (coe MAlonzo.Code.Agda.Builtin.Reflection.C_strErr_310)
-- Reflection.Debug.IsErrorPart-Term
d_IsErrorPart'45'Term_20 :: T_IsErrorPart_6
d_IsErrorPart'45'Term_20
  = coe
      C_IsErrorPart'46'constructor_5
      (coe MAlonzo.Code.Agda.Builtin.Reflection.C_termErr_312)
-- Reflection.Debug.IsErrorPart-Name
d_IsErrorPart'45'Name_22 :: T_IsErrorPart_6
d_IsErrorPart'45'Name_22
  = coe
      C_IsErrorPart'46'constructor_5
      (coe MAlonzo.Code.Agda.Builtin.Reflection.C_nameErr_316)
-- Reflection.Debug.IsErrorPart-Pattern
d_IsErrorPart'45'Pattern_24 :: T_IsErrorPart_6
d_IsErrorPart'45'Pattern_24
  = coe
      C_IsErrorPart'46'constructor_5
      (coe MAlonzo.Code.Agda.Builtin.Reflection.C_pattErr_314)
-- Reflection.Debug.IsErrorPart-Clause
d_IsErrorPart'45'Clause_26 :: T_IsErrorPart_6
d_IsErrorPart'45'Clause_26
  = coe
      C_IsErrorPart'46'constructor_5
      (coe
         (\ v0 ->
            coe
              MAlonzo.Code.Agda.Builtin.Reflection.C_termErr_312
              (coe
                 MAlonzo.Code.Agda.Builtin.Reflection.C_pat'45'lam_196
                 (coe MAlonzo.Code.Data.List.Base.du_'91'_'93'_270 (coe v0))
                 (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))
-- Reflection.Debug.IsErrorPart-ListClause
d_IsErrorPart'45'ListClause_30 :: T_IsErrorPart_6
d_IsErrorPart'45'ListClause_30
  = coe
      C_IsErrorPart'46'constructor_5
      (coe
         (\ v0 ->
            coe
              MAlonzo.Code.Agda.Builtin.Reflection.C_termErr_312
              (coe
                 MAlonzo.Code.Agda.Builtin.Reflection.C_pat'45'lam_196 (coe v0)
                 (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))))
-- Reflection.Debug._∷ᵈ_
d__'8759''7496'__36 ::
  () ->
  AgdaAny ->
  T_IsErrorPart_6 ->
  [MAlonzo.Code.Agda.Builtin.Reflection.T_ErrorPart_308] ->
  [MAlonzo.Code.Agda.Builtin.Reflection.T_ErrorPart_308]
d__'8759''7496'__36 ~v0 v1 v2 v3 = du__'8759''7496'__36 v1 v2 v3
du__'8759''7496'__36 ::
  AgdaAny ->
  T_IsErrorPart_6 ->
  [MAlonzo.Code.Agda.Builtin.Reflection.T_ErrorPart_308] ->
  [MAlonzo.Code.Agda.Builtin.Reflection.T_ErrorPart_308]
du__'8759''7496'__36 v0 v1 v2
  = coe
      MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
      (coe d_toErrorPart_12 v1 v0) (coe v2)
-- Reflection.Debug._++ᵈ_
d__'43''43''7496'__44 ::
  () ->
  [AgdaAny] ->
  T_IsErrorPart_6 ->
  [MAlonzo.Code.Agda.Builtin.Reflection.T_ErrorPart_308] ->
  [MAlonzo.Code.Agda.Builtin.Reflection.T_ErrorPart_308]
d__'43''43''7496'__44 ~v0 v1 v2 v3
  = du__'43''43''7496'__44 v1 v2 v3
du__'43''43''7496'__44 ::
  [AgdaAny] ->
  T_IsErrorPart_6 ->
  [MAlonzo.Code.Agda.Builtin.Reflection.T_ErrorPart_308] ->
  [MAlonzo.Code.Agda.Builtin.Reflection.T_ErrorPart_308]
du__'43''43''7496'__44 v0 v1 v2
  = coe
      MAlonzo.Code.Data.List.Base.du__'43''43'__32
      (coe
         MAlonzo.Code.Data.List.Base.du_map_22
         (coe d_toErrorPart_12 (coe v1)) (coe v0))
      (coe v2)
-- Reflection.Debug._ᵈ
d__'7496'_52 ::
  () ->
  T_IsErrorPart_6 ->
  [AgdaAny] -> [MAlonzo.Code.Agda.Builtin.Reflection.T_ErrorPart_308]
d__'7496'_52 ~v0 v1 = du__'7496'_52 v1
du__'7496'_52 ::
  T_IsErrorPart_6 ->
  [AgdaAny] -> [MAlonzo.Code.Agda.Builtin.Reflection.T_ErrorPart_308]
du__'7496'_52 v0
  = coe
      MAlonzo.Code.Data.List.Base.du_map_22
      (coe d_toErrorPart_12 (coe v0))
-- Reflection.Debug.DebugSelection
d_DebugSelection_54 = ()
data T_DebugSelection_54
  = C_FullPath_56 | C_Last_58 | C_All_60 |
    C_Custom_62 ([MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
                 MAlonzo.Code.Agda.Builtin.String.T_String_6)
-- Reflection.Debug.Filter
d_Filter_64 :: ()
d_Filter_64 = erased
-- Reflection.Debug.Filter.Filter-Alg
d_Filter'45'Alg_68 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_BooleanAlgebra_682
d_Filter'45'Alg_68
  = coe
      MAlonzo.Code.Algebra.Function.du_hom_264
      (coe
         MAlonzo.Code.Data.Bool.Properties.d_'8744''45''8743''45'booleanAlgebra_3414)
-- Reflection.Debug.Filter._._∧_
d__'8743'__72 ::
  ([MAlonzo.Code.Agda.Builtin.String.T_String_6] -> Bool) ->
  ([MAlonzo.Code.Agda.Builtin.String.T_String_6] -> Bool) ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] -> Bool
d__'8743'__72
  = coe
      MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710
      (coe d_Filter'45'Alg_68)
-- Reflection.Debug.Filter._._∨_
d__'8744'__74 ::
  ([MAlonzo.Code.Agda.Builtin.String.T_String_6] -> Bool) ->
  ([MAlonzo.Code.Agda.Builtin.String.T_String_6] -> Bool) ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] -> Bool
d__'8744'__74
  = coe
      MAlonzo.Code.Algebra.Lattice.Bundles.d__'8744'__708
      (coe d_Filter'45'Alg_68)
-- Reflection.Debug.Filter._._≈_
d__'8776'__76 ::
  ([MAlonzo.Code.Agda.Builtin.String.T_String_6] -> Bool) ->
  ([MAlonzo.Code.Agda.Builtin.String.T_String_6] -> Bool) -> ()
d__'8776'__76 = erased
-- Reflection.Debug.Filter._._≉_
d__'8777'__78 ::
  ([MAlonzo.Code.Agda.Builtin.String.T_String_6] -> Bool) ->
  ([MAlonzo.Code.Agda.Builtin.String.T_String_6] -> Bool) -> ()
d__'8777'__78 = erased
-- Reflection.Debug.Filter._.Carrier
d_Carrier_80 :: ()
d_Carrier_80 = erased
-- Reflection.Debug.Filter._.absorptive
d_absorptive_82 :: MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_absorptive_82
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.d_absorptive_3020
      (coe
         MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3070
         (coe
            MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3154
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
               (coe d_Filter'45'Alg_68))))
-- Reflection.Debug.Filter._.distributiveLattice
d_distributiveLattice_84 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_DistributiveLattice_584
d_distributiveLattice_84
  = coe
      MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_790
      (coe d_Filter'45'Alg_68)
-- Reflection.Debug.Filter._.isBooleanAlgebra
d_isBooleanAlgebra_86 ::
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsBooleanAlgebra_3134
d_isBooleanAlgebra_86
  = coe
      MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
      (coe d_Filter'45'Alg_68)
-- Reflection.Debug.Filter._.isDistributiveLattice
d_isDistributiveLattice_88 ::
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsDistributiveLattice_3058
d_isDistributiveLattice_88
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3154
      (coe
         MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
         (coe d_Filter'45'Alg_68))
-- Reflection.Debug.Filter._.isEquivalence
d_isEquivalence_90 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_isEquivalence_90
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3006
      (coe
         MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3070
         (coe
            MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3154
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
               (coe d_Filter'45'Alg_68))))
-- Reflection.Debug.Filter._.isLattice
d_isLattice_92 ::
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsLattice_2984
d_isLattice_92
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3070
      (coe
         MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3154
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
            (coe d_Filter'45'Alg_68)))
-- Reflection.Debug.Filter._.isPartialEquivalence
d_isPartialEquivalence_94 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialEquivalence_16
d_isPartialEquivalence_94
  = let v0 = d_Filter'45'Alg_68 in
    coe
      (let v1
             = MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
                 (coe v0) in
       coe
         (let v2
                = MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3154
                    (coe v1) in
          coe
            (let v3
                   = MAlonzo.Code.Algebra.Lattice.Structures.d_isLattice_3070
                       (coe v2) in
             coe
               (coe
                  MAlonzo.Code.Relation.Binary.Structures.du_isPartialEquivalence_42
                  (coe
                     MAlonzo.Code.Algebra.Lattice.Structures.d_isEquivalence_3006
                     (coe v3))))))
-- Reflection.Debug.Filter._.lattice
d_lattice_96 :: MAlonzo.Code.Algebra.Lattice.Bundles.T_Lattice_500
d_lattice_96
  = let v0 = d_Filter'45'Alg_68 in
    coe
      (coe
         MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_790
            (coe v0)))
-- Reflection.Debug.Filter._.rawLattice
d_rawLattice_98 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.Raw.T_RawLattice_12
d_rawLattice_98
  = let v0 = d_Filter'45'Alg_68 in
    coe
      (let v1
             = coe
                 MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_790
                 (coe v0) in
       coe
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.du_rawLattice_566
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664 (coe v1))))
-- Reflection.Debug.Filter._.refl
d_refl_100 ::
  ([MAlonzo.Code.Agda.Builtin.String.T_String_6] -> Bool) ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_refl_100 = erased
-- Reflection.Debug.Filter._.reflexive
d_reflexive_102 ::
  ([MAlonzo.Code.Agda.Builtin.String.T_String_6] -> Bool) ->
  ([MAlonzo.Code.Agda.Builtin.String.T_String_6] -> Bool) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reflexive_102 = erased
-- Reflection.Debug.Filter._.setoid
d_setoid_104 :: MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
d_setoid_104
  = let v0 = d_Filter'45'Alg_68 in
    coe
      (let v1
             = coe
                 MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_790
                 (coe v0) in
       coe
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.du_setoid_574
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664 (coe v1))))
-- Reflection.Debug.Filter._.sym
d_sym_106 ::
  ([MAlonzo.Code.Agda.Builtin.String.T_String_6] -> Bool) ->
  ([MAlonzo.Code.Agda.Builtin.String.T_String_6] -> Bool) ->
  ([MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_sym_106 = erased
-- Reflection.Debug.Filter._.trans
d_trans_108 ::
  ([MAlonzo.Code.Agda.Builtin.String.T_String_6] -> Bool) ->
  ([MAlonzo.Code.Agda.Builtin.String.T_String_6] -> Bool) ->
  ([MAlonzo.Code.Agda.Builtin.String.T_String_6] -> Bool) ->
  ([MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  ([MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_trans_108 = erased
-- Reflection.Debug.Filter._.¬_
d_'172'__110 ::
  ([MAlonzo.Code.Agda.Builtin.String.T_String_6] -> Bool) ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] -> Bool
d_'172'__110
  = coe
      MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712
      (coe d_Filter'45'Alg_68)
-- Reflection.Debug.Filter._.¬-cong
d_'172''45'cong_112 ::
  ([MAlonzo.Code.Agda.Builtin.String.T_String_6] -> Bool) ->
  ([MAlonzo.Code.Agda.Builtin.String.T_String_6] -> Bool) ->
  ([MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'172''45'cong_112 = erased
-- Reflection.Debug.Filter._.∧-absorbs-∨
d_'8743''45'absorbs'45''8744'_114 ::
  ([MAlonzo.Code.Agda.Builtin.String.T_String_6] -> Bool) ->
  ([MAlonzo.Code.Agda.Builtin.String.T_String_6] -> Bool) ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8743''45'absorbs'45''8744'_114 = erased
-- Reflection.Debug.Filter._.∧-assoc
d_'8743''45'assoc_116 ::
  ([MAlonzo.Code.Agda.Builtin.String.T_String_6] -> Bool) ->
  ([MAlonzo.Code.Agda.Builtin.String.T_String_6] -> Bool) ->
  ([MAlonzo.Code.Agda.Builtin.String.T_String_6] -> Bool) ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8743''45'assoc_116 = erased
-- Reflection.Debug.Filter._.∧-comm
d_'8743''45'comm_118 ::
  ([MAlonzo.Code.Agda.Builtin.String.T_String_6] -> Bool) ->
  ([MAlonzo.Code.Agda.Builtin.String.T_String_6] -> Bool) ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8743''45'comm_118 = erased
-- Reflection.Debug.Filter._.∧-complement
d_'8743''45'complement_120 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8743''45'complement_120
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.d_'8743''45'complement_3158
      (coe
         MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
         (coe d_Filter'45'Alg_68))
-- Reflection.Debug.Filter._.∧-complementʳ
d_'8743''45'complement'691'_122 ::
  ([MAlonzo.Code.Agda.Builtin.String.T_String_6] -> Bool) ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8743''45'complement'691'_122 = erased
-- Reflection.Debug.Filter._.∧-complementˡ
d_'8743''45'complement'737'_124 ::
  ([MAlonzo.Code.Agda.Builtin.String.T_String_6] -> Bool) ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8743''45'complement'737'_124 = erased
-- Reflection.Debug.Filter._.∧-cong
d_'8743''45'cong_126 ::
  ([MAlonzo.Code.Agda.Builtin.String.T_String_6] -> Bool) ->
  ([MAlonzo.Code.Agda.Builtin.String.T_String_6] -> Bool) ->
  ([MAlonzo.Code.Agda.Builtin.String.T_String_6] -> Bool) ->
  ([MAlonzo.Code.Agda.Builtin.String.T_String_6] -> Bool) ->
  ([MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  ([MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8743''45'cong_126 = erased
-- Reflection.Debug.Filter._.∧-congʳ
d_'8743''45'cong'691'_128 ::
  ([MAlonzo.Code.Agda.Builtin.String.T_String_6] -> Bool) ->
  ([MAlonzo.Code.Agda.Builtin.String.T_String_6] -> Bool) ->
  ([MAlonzo.Code.Agda.Builtin.String.T_String_6] -> Bool) ->
  ([MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8743''45'cong'691'_128 = erased
-- Reflection.Debug.Filter._.∧-congˡ
d_'8743''45'cong'737'_130 ::
  ([MAlonzo.Code.Agda.Builtin.String.T_String_6] -> Bool) ->
  ([MAlonzo.Code.Agda.Builtin.String.T_String_6] -> Bool) ->
  ([MAlonzo.Code.Agda.Builtin.String.T_String_6] -> Bool) ->
  ([MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8743''45'cong'737'_130 = erased
-- Reflection.Debug.Filter._.∧-distrib-∨
d_'8743''45'distrib'45''8744'_132 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8743''45'distrib'45''8744'_132
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.d_'8743''45'distrib'45''8744'_3074
      (coe
         MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3154
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
            (coe d_Filter'45'Alg_68)))
-- Reflection.Debug.Filter._.∧-distribʳ-∨
d_'8743''45'distrib'691''45''8744'_134 ::
  ([MAlonzo.Code.Agda.Builtin.String.T_String_6] -> Bool) ->
  ([MAlonzo.Code.Agda.Builtin.String.T_String_6] -> Bool) ->
  ([MAlonzo.Code.Agda.Builtin.String.T_String_6] -> Bool) ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8743''45'distrib'691''45''8744'_134 = erased
-- Reflection.Debug.Filter._.∧-distribˡ-∨
d_'8743''45'distrib'737''45''8744'_136 ::
  ([MAlonzo.Code.Agda.Builtin.String.T_String_6] -> Bool) ->
  ([MAlonzo.Code.Agda.Builtin.String.T_String_6] -> Bool) ->
  ([MAlonzo.Code.Agda.Builtin.String.T_String_6] -> Bool) ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8743''45'distrib'737''45''8744'_136 = erased
-- Reflection.Debug.Filter._.∧-rawMagma
d_'8743''45'rawMagma_138 ::
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMagma_42
d_'8743''45'rawMagma_138
  = let v0 = d_Filter'45'Alg_68 in
    coe
      (let v1
             = coe
                 MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_790
                 (coe v0) in
       coe
         (let v2
                = coe
                    MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664 (coe v1) in
          coe
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.Raw.du_'8743''45'rawMagma_36
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.du_rawLattice_566 (coe v2)))))
-- Reflection.Debug.Filter._.∨-absorbs-∧
d_'8744''45'absorbs'45''8743'_140 ::
  ([MAlonzo.Code.Agda.Builtin.String.T_String_6] -> Bool) ->
  ([MAlonzo.Code.Agda.Builtin.String.T_String_6] -> Bool) ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8744''45'absorbs'45''8743'_140 = erased
-- Reflection.Debug.Filter._.∨-assoc
d_'8744''45'assoc_142 ::
  ([MAlonzo.Code.Agda.Builtin.String.T_String_6] -> Bool) ->
  ([MAlonzo.Code.Agda.Builtin.String.T_String_6] -> Bool) ->
  ([MAlonzo.Code.Agda.Builtin.String.T_String_6] -> Bool) ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8744''45'assoc_142 = erased
-- Reflection.Debug.Filter._.∨-comm
d_'8744''45'comm_144 ::
  ([MAlonzo.Code.Agda.Builtin.String.T_String_6] -> Bool) ->
  ([MAlonzo.Code.Agda.Builtin.String.T_String_6] -> Bool) ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8744''45'comm_144 = erased
-- Reflection.Debug.Filter._.∨-complement
d_'8744''45'complement_146 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8744''45'complement_146
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.d_'8744''45'complement_3156
      (coe
         MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
         (coe d_Filter'45'Alg_68))
-- Reflection.Debug.Filter._.∨-complementʳ
d_'8744''45'complement'691'_148 ::
  ([MAlonzo.Code.Agda.Builtin.String.T_String_6] -> Bool) ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8744''45'complement'691'_148 = erased
-- Reflection.Debug.Filter._.∨-complementˡ
d_'8744''45'complement'737'_150 ::
  ([MAlonzo.Code.Agda.Builtin.String.T_String_6] -> Bool) ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8744''45'complement'737'_150 = erased
-- Reflection.Debug.Filter._.∨-cong
d_'8744''45'cong_152 ::
  ([MAlonzo.Code.Agda.Builtin.String.T_String_6] -> Bool) ->
  ([MAlonzo.Code.Agda.Builtin.String.T_String_6] -> Bool) ->
  ([MAlonzo.Code.Agda.Builtin.String.T_String_6] -> Bool) ->
  ([MAlonzo.Code.Agda.Builtin.String.T_String_6] -> Bool) ->
  ([MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  ([MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8744''45'cong_152 = erased
-- Reflection.Debug.Filter._.∨-congʳ
d_'8744''45'cong'691'_154 ::
  ([MAlonzo.Code.Agda.Builtin.String.T_String_6] -> Bool) ->
  ([MAlonzo.Code.Agda.Builtin.String.T_String_6] -> Bool) ->
  ([MAlonzo.Code.Agda.Builtin.String.T_String_6] -> Bool) ->
  ([MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8744''45'cong'691'_154 = erased
-- Reflection.Debug.Filter._.∨-congˡ
d_'8744''45'cong'737'_156 ::
  ([MAlonzo.Code.Agda.Builtin.String.T_String_6] -> Bool) ->
  ([MAlonzo.Code.Agda.Builtin.String.T_String_6] -> Bool) ->
  ([MAlonzo.Code.Agda.Builtin.String.T_String_6] -> Bool) ->
  ([MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8744''45'cong'737'_156 = erased
-- Reflection.Debug.Filter._.∨-distrib-∧
d_'8744''45'distrib'45''8743'_158 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8744''45'distrib'45''8743'_158
  = coe
      MAlonzo.Code.Algebra.Lattice.Structures.d_'8744''45'distrib'45''8743'_3072
      (coe
         MAlonzo.Code.Algebra.Lattice.Structures.d_isDistributiveLattice_3154
         (coe
            MAlonzo.Code.Algebra.Lattice.Bundles.d_isBooleanAlgebra_718
            (coe d_Filter'45'Alg_68)))
-- Reflection.Debug.Filter._.∨-distribʳ-∧
d_'8744''45'distrib'691''45''8743'_160 ::
  ([MAlonzo.Code.Agda.Builtin.String.T_String_6] -> Bool) ->
  ([MAlonzo.Code.Agda.Builtin.String.T_String_6] -> Bool) ->
  ([MAlonzo.Code.Agda.Builtin.String.T_String_6] -> Bool) ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8744''45'distrib'691''45''8743'_160 = erased
-- Reflection.Debug.Filter._.∨-distribˡ-∧
d_'8744''45'distrib'737''45''8743'_162 ::
  ([MAlonzo.Code.Agda.Builtin.String.T_String_6] -> Bool) ->
  ([MAlonzo.Code.Agda.Builtin.String.T_String_6] -> Bool) ->
  ([MAlonzo.Code.Agda.Builtin.String.T_String_6] -> Bool) ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8744''45'distrib'737''45''8743'_162 = erased
-- Reflection.Debug.Filter._.∨-rawMagma
d_'8744''45'rawMagma_164 ::
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMagma_42
d_'8744''45'rawMagma_164
  = let v0 = d_Filter'45'Alg_68 in
    coe
      (let v1
             = coe
                 MAlonzo.Code.Algebra.Lattice.Bundles.du_distributiveLattice_790
                 (coe v0) in
       coe
         (let v2
                = coe
                    MAlonzo.Code.Algebra.Lattice.Bundles.du_lattice_664 (coe v1) in
          coe
            (coe
               MAlonzo.Code.Algebra.Lattice.Bundles.Raw.du_'8744''45'rawMagma_34
               (coe
                  MAlonzo.Code.Algebra.Lattice.Bundles.du_rawLattice_566 (coe v2)))))
-- Reflection.Debug.Filter._.⊤
d_'8868'_166 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] -> Bool
d_'8868'_166
  = coe
      MAlonzo.Code.Algebra.Lattice.Bundles.d_'8868'_714
      (coe d_Filter'45'Alg_68)
-- Reflection.Debug.Filter._.⊥
d_'8869'_168 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] -> Bool
d_'8869'_168
  = coe
      MAlonzo.Code.Algebra.Lattice.Bundles.d_'8869'_716
      (coe d_Filter'45'Alg_68)
-- Reflection.Debug.Filter._≣_
d__'8803'__170 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 -> Bool
d__'8803'__170 v0 v1
  = coe
      MAlonzo.Code.Relation.Nullary.Decidable.Core.d_'8970'_'8971'_140 ()
      erased
      (MAlonzo.Code.Data.String.Properties.d__'8799'__54
         (coe v0) (coe v1))
-- Reflection.Debug.Filter.contains
d_contains_176 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] -> Bool
d_contains_176 v0 v1
  = coe
      MAlonzo.Code.Data.List.Base.du_foldl_230
      (coe
         (\ v2 v3 ->
            MAlonzo.Code.Data.Bool.Base.d__'8744'__30
              (coe v2) (coe d__'8803'__170 (coe v0) (coe v3))))
      (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8) (coe v1)
-- Reflection.Debug.Filter.noneOf
d_noneOf_186 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] -> Bool
d_noneOf_186 v0
  = case coe v0 of
      []
        -> coe
             MAlonzo.Code.Algebra.Lattice.Bundles.d_'8868'_714
             (coe d_Filter'45'Alg_68)
      (:) v1 v2
        -> coe
             MAlonzo.Code.Algebra.Lattice.Bundles.d__'8743'__710
             d_Filter'45'Alg_68
             (coe
                MAlonzo.Code.Algebra.Lattice.Bundles.d_'172'__712
                d_Filter'45'Alg_68 (d_contains_176 (coe v1)))
             (d_noneOf_186 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Reflection.Debug.Filter.endsWith
d_endsWith_192 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] -> Bool
d_endsWith_192 v0 v1
  = let v2 = coe MAlonzo.Code.Data.List.Base.du_last_524 (coe v1) in
    coe
      (case coe v2 of
         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
           -> coe d__'8803'__170 (coe v0) (coe v3)
         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
           -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Reflection.Debug.Filter.beginsWith
d_beginsWith_212 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] -> Bool
d_beginsWith_212 v0 v1
  = let v2 = coe MAlonzo.Code.Data.List.Base.du_head_516 (coe v1) in
    coe
      (case coe v2 of
         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
           -> coe d__'8803'__170 (coe v0) (coe v3)
         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
           -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Reflection.Debug.DebugOptions
d_DebugOptions_232 = ()
data T_DebugOptions_232
  = C_DebugOptions'46'constructor_1897 [MAlonzo.Code.Agda.Builtin.String.T_String_6]
                                       T_DebugSelection_54
                                       ([MAlonzo.Code.Agda.Builtin.String.T_String_6] -> Bool)
                                       Integer MAlonzo.Code.Agda.Builtin.Char.T_Char_6
-- Reflection.Debug.DebugOptions.path
d_path_244 ::
  T_DebugOptions_232 -> [MAlonzo.Code.Agda.Builtin.String.T_String_6]
d_path_244 v0
  = case coe v0 of
      C_DebugOptions'46'constructor_1897 v1 v2 v3 v4 v5 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Reflection.Debug.DebugOptions.selection
d_selection_246 :: T_DebugOptions_232 -> T_DebugSelection_54
d_selection_246 v0
  = case coe v0 of
      C_DebugOptions'46'constructor_1897 v1 v2 v3 v4 v5 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Reflection.Debug.DebugOptions.filter
d_filter_248 ::
  T_DebugOptions_232 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] -> Bool
d_filter_248 v0
  = case coe v0 of
      C_DebugOptions'46'constructor_1897 v1 v2 v3 v4 v5 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Reflection.Debug.DebugOptions.level
d_level_250 :: T_DebugOptions_232 -> Integer
d_level_250 v0
  = case coe v0 of
      C_DebugOptions'46'constructor_1897 v1 v2 v3 v4 v5 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Reflection.Debug.DebugOptions.prefix
d_prefix_252 ::
  T_DebugOptions_232 -> MAlonzo.Code.Agda.Builtin.Char.T_Char_6
d_prefix_252 v0
  = case coe v0 of
      C_DebugOptions'46'constructor_1897 v1 v2 v3 v4 v5 -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Reflection.Debug.defaultDebugOptions
d_defaultDebugOptions_254 :: T_DebugOptions_232
d_defaultDebugOptions_254
  = coe
      C_DebugOptions'46'constructor_1897
      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16) (coe C_All_60)
      (coe
         MAlonzo.Code.Algebra.Lattice.Bundles.d_'8868'_714
         (coe d_Filter'45'Alg_68))
      (coe (100 :: Integer)) (coe '|')
-- Reflection.Debug.specializeDebugOptions
d_specializeDebugOptions_256 ::
  T_DebugOptions_232 -> T_DebugOptions_232 -> T_DebugOptions_232
d_specializeDebugOptions_256 v0 v1
  = case coe v0 of
      C_DebugOptions'46'constructor_1897 v2 v3 v4 v5 v6
        -> case coe v1 of
             C_DebugOptions'46'constructor_1897 v7 v8 v9 v10 v11
               -> coe
                    C_DebugOptions'46'constructor_1897
                    (coe
                       MAlonzo.Code.Data.List.Base.du__'43''43'__32 (coe v2) (coe v7))
                    (coe v8) (coe v9) (coe v10) (coe v11)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Reflection.Debug.debugOptionsPath
d_debugOptionsPath_264 ::
  T_DebugOptions_232 -> MAlonzo.Code.Agda.Builtin.String.T_String_6
d_debugOptionsPath_264 v0
  = case coe v0 of
      C_DebugOptions'46'constructor_1897 v1 v2 v3 v4 v5
        -> case coe v2 of
             C_FullPath_56
               -> coe
                    MAlonzo.Code.Data.String.Base.d_intersperse_30
                    ("/" :: Data.Text.Text) v1
             C_Last_58
               -> let v6 = coe MAlonzo.Code.Data.List.Base.du_last_524 (coe v1) in
                  coe
                    (case coe v6 of
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v7 -> coe v7
                       MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                         -> coe ("" :: Data.Text.Text)
                       _ -> MAlonzo.RTE.mazUnreachableError)
             C_All_60 -> coe ("allTactics" :: Data.Text.Text)
             C_Custom_62 v6 -> coe v6 v1
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Reflection.Debug.debugPrintPrefix
d_debugPrintPrefix_286 ::
  T_DebugOptions_232 ->
  MAlonzo.Code.Agda.Builtin.Reflection.T_ErrorPart_308
d_debugPrintPrefix_286 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Reflection.C_strErr_310
      (coe
         MAlonzo.Code.Data.String.Base.d_replicate_24
         (coe
            MAlonzo.Code.Data.List.Base.du_length_268 (d_path_244 (coe v0)))
         (coe d_prefix_252 (coe v0)))
-- Reflection.Debug._.filter
d_filter_292 ::
  T_DebugOptions_232 ->
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] -> Bool
d_filter_292 v0 = coe d_filter_248 (coe v0)
-- Reflection.Debug._.level
d_level_294 :: T_DebugOptions_232 -> Integer
d_level_294 v0 = coe d_level_250 (coe v0)
-- Reflection.Debug._.path
d_path_296 ::
  T_DebugOptions_232 -> [MAlonzo.Code.Agda.Builtin.String.T_String_6]
d_path_296 v0 = coe d_path_244 (coe v0)
-- Reflection.Debug._.prefix
d_prefix_298 ::
  T_DebugOptions_232 -> MAlonzo.Code.Agda.Builtin.Char.T_Char_6
d_prefix_298 v0 = coe d_prefix_252 (coe v0)
-- Reflection.Debug._.selection
d_selection_300 :: T_DebugOptions_232 -> T_DebugSelection_54
d_selection_300 v0 = coe d_selection_246 (coe v0)
