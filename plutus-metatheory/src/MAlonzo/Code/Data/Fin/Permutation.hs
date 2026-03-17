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

module MAlonzo.Code.Data.Fin.Permutation where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Data.Fin.Base
import qualified MAlonzo.Code.Data.Fin.Permutation.Components
import qualified MAlonzo.Code.Data.Fin.Properties
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Function.Bundles
import qualified MAlonzo.Code.Function.Construct.Composition
import qualified MAlonzo.Code.Function.Construct.Identity
import qualified MAlonzo.Code.Function.Construct.Symmetry
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core

-- Data.Fin.Permutation.Permutation
d_Permutation_12 :: Integer -> Integer -> ()
d_Permutation_12 = erased
-- Data.Fin.Permutation.Permutation′
d_Permutation'8242'_18 :: Integer -> ()
d_Permutation'8242'_18 = erased
-- Data.Fin.Permutation.permutation
d_permutation_26 ::
  Integer ->
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Data.Fin.Base.T_Fin_10) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Data.Fin.Base.T_Fin_10) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Function.Bundles.T_Inverse_2068
d_permutation_26 ~v0 ~v1 = du_permutation_26
du_permutation_26 ::
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Data.Fin.Base.T_Fin_10) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Data.Fin.Base.T_Fin_10) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Function.Bundles.T_Inverse_2068
du_permutation_26 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Function.Bundles.du_mk'8596''8347''8242'_2482 v0 v1
-- Data.Fin.Permutation._⟨$⟩ʳ_
d__'10216''36''10217''691'__28 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Function.Bundles.T_Inverse_2068 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10
d__'10216''36''10217''691'__28 ~v0 ~v1 v2
  = du__'10216''36''10217''691'__28 v2
du__'10216''36''10217''691'__28 ::
  MAlonzo.Code.Function.Bundles.T_Inverse_2068 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10
du__'10216''36''10217''691'__28 v0
  = coe MAlonzo.Code.Function.Bundles.d_to_2080 (coe v0)
-- Data.Fin.Permutation._⟨$⟩ˡ_
d__'10216''36''10217''737'__30 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Function.Bundles.T_Inverse_2068 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10
d__'10216''36''10217''737'__30 ~v0 ~v1 v2
  = du__'10216''36''10217''737'__30 v2
du__'10216''36''10217''737'__30 ::
  MAlonzo.Code.Function.Bundles.T_Inverse_2068 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10
du__'10216''36''10217''737'__30 v0
  = coe MAlonzo.Code.Function.Bundles.d_from_2082 (coe v0)
-- Data.Fin.Permutation.inverseˡ
d_inverse'737'_36 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Function.Bundles.T_Inverse_2068 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_inverse'737'_36 = erased
-- Data.Fin.Permutation.inverseʳ
d_inverse'691'_44 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Function.Bundles.T_Inverse_2068 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_inverse'691'_44 = erased
-- Data.Fin.Permutation._≈_
d__'8776'__48 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Function.Bundles.T_Inverse_2068 ->
  MAlonzo.Code.Function.Bundles.T_Inverse_2068 -> ()
d__'8776'__48 = erased
-- Data.Fin.Permutation.id
d_id_56 :: Integer -> MAlonzo.Code.Function.Bundles.T_Inverse_2068
d_id_56 ~v0 = du_id_56
du_id_56 :: MAlonzo.Code.Function.Bundles.T_Inverse_2068
du_id_56
  = coe MAlonzo.Code.Function.Construct.Identity.du_'8596''45'id_646
-- Data.Fin.Permutation.flip
d_flip_58 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Function.Bundles.T_Inverse_2068 ->
  MAlonzo.Code.Function.Bundles.T_Inverse_2068
d_flip_58 ~v0 ~v1 = du_flip_58
du_flip_58 ::
  MAlonzo.Code.Function.Bundles.T_Inverse_2068 ->
  MAlonzo.Code.Function.Bundles.T_Inverse_2068
du_flip_58
  = coe
      MAlonzo.Code.Function.Construct.Symmetry.du_'8596''45'sym_1196
-- Data.Fin.Permutation._∘ₚ_
d__'8728''8346'__60 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Function.Bundles.T_Inverse_2068 ->
  MAlonzo.Code.Function.Bundles.T_Inverse_2068 ->
  MAlonzo.Code.Function.Bundles.T_Inverse_2068
d__'8728''8346'__60 ~v0 ~v1 ~v2 v3 v4 = du__'8728''8346'__60 v3 v4
du__'8728''8346'__60 ::
  MAlonzo.Code.Function.Bundles.T_Inverse_2068 ->
  MAlonzo.Code.Function.Bundles.T_Inverse_2068 ->
  MAlonzo.Code.Function.Bundles.T_Inverse_2068
du__'8728''8346'__60 v0 v1
  = coe
      MAlonzo.Code.Function.Construct.Composition.du__'8596''45''8728'__2510
      (coe v1) (coe v0)
-- Data.Fin.Permutation.cast-id
d_cast'45'id_66 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Function.Bundles.T_Inverse_2068
d_cast'45'id_66 v0 v1 ~v2 = du_cast'45'id_66 v0 v1
du_cast'45'id_66 ::
  Integer -> Integer -> MAlonzo.Code.Function.Bundles.T_Inverse_2068
du_cast'45'id_66 v0 v1
  = coe
      du_permutation_26
      (coe MAlonzo.Code.Data.Fin.Base.du_cast_26 (coe v0))
      (coe MAlonzo.Code.Data.Fin.Base.du_cast_26 (coe v1)) erased erased
-- Data.Fin.Permutation.transpose
d_transpose_70 ::
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Function.Bundles.T_Inverse_2068
d_transpose_70 ~v0 v1 v2 = du_transpose_70 v1 v2
du_transpose_70 ::
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Function.Bundles.T_Inverse_2068
du_transpose_70 v0 v1
  = coe
      du_permutation_26
      (coe
         MAlonzo.Code.Data.Fin.Permutation.Components.du_transpose_10
         (coe v0) (coe v1))
      (coe
         MAlonzo.Code.Data.Fin.Permutation.Components.du_transpose_10
         (coe v1) (coe v0))
      erased erased
-- Data.Fin.Permutation.reverse
d_reverse_80 ::
  Integer -> MAlonzo.Code.Function.Bundles.T_Inverse_2068
d_reverse_80 v0
  = coe
      du_permutation_26
      (MAlonzo.Code.Data.Fin.Base.d_opposite_384 (coe v0))
      (MAlonzo.Code.Data.Fin.Base.d_opposite_384 (coe v0)) erased erased
-- Data.Fin.Permutation.remove
d_remove_82 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Function.Bundles.T_Inverse_2068 ->
  MAlonzo.Code.Function.Bundles.T_Inverse_2068
d_remove_82 ~v0 ~v1 v2 v3 = du_remove_82 v2 v3
du_remove_82 ::
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Function.Bundles.T_Inverse_2068 ->
  MAlonzo.Code.Function.Bundles.T_Inverse_2068
du_remove_82 v0 v1
  = coe
      du_permutation_26 (coe du_to_124 (coe v0) (coe v1))
      (coe du_from_128 (coe v0) (coe v1)) erased erased
-- Data.Fin.Permutation._.πʳ
d_π'691'_96 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Function.Bundles.T_Inverse_2068 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10
d_π'691'_96 ~v0 ~v1 ~v2 v3 = du_π'691'_96 v3
du_π'691'_96 ::
  MAlonzo.Code.Function.Bundles.T_Inverse_2068 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10
du_π'691'_96 v0 = coe du__'10216''36''10217''691'__28 (coe v0)
-- Data.Fin.Permutation._.πˡ
d_π'737'_100 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Function.Bundles.T_Inverse_2068 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10
d_π'737'_100 ~v0 ~v1 ~v2 v3 = du_π'737'_100 v3
du_π'737'_100 ::
  MAlonzo.Code.Function.Bundles.T_Inverse_2068 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10
du_π'737'_100 v0 = coe du__'10216''36''10217''737'__30 (coe v0)
-- Data.Fin.Permutation._.permute-≢
d_permute'45''8802'_108 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Function.Bundles.T_Inverse_2068 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_permute'45''8802'_108 = erased
-- Data.Fin.Permutation._.to-punchOut
d_to'45'punchOut_114 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Function.Bundles.T_Inverse_2068 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_to'45'punchOut_114 = erased
-- Data.Fin.Permutation._.from-punchOut
d_from'45'punchOut_118 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Function.Bundles.T_Inverse_2068 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_from'45'punchOut_118 = erased
-- Data.Fin.Permutation._.to
d_to_124 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Function.Bundles.T_Inverse_2068 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10
d_to_124 ~v0 ~v1 v2 v3 v4 = du_to_124 v2 v3 v4
du_to_124 ::
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Function.Bundles.T_Inverse_2068 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10
du_to_124 v0 v1 v2
  = coe
      MAlonzo.Code.Data.Fin.Base.du_punchOut_396 (coe du_π'691'_96 v1 v0)
      (coe
         du_π'691'_96 v1
         (coe MAlonzo.Code.Data.Fin.Base.du_punchIn_410 (coe v0) (coe v2)))
-- Data.Fin.Permutation._.from
d_from_128 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Function.Bundles.T_Inverse_2068 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10
d_from_128 ~v0 ~v1 v2 v3 v4 = du_from_128 v2 v3 v4
du_from_128 ::
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Function.Bundles.T_Inverse_2068 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10
du_from_128 v0 v1 v2
  = coe
      MAlonzo.Code.Data.Fin.Base.du_punchOut_396 (coe v0)
      (coe
         du_π'737'_100 v1
         (coe
            MAlonzo.Code.Data.Fin.Base.du_punchIn_410 (coe du_π'691'_96 v1 v0)
            (coe v2)))
-- Data.Fin.Permutation._.inverseʳ′
d_inverse'691''8242'_132 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Function.Bundles.T_Inverse_2068 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_inverse'691''8242'_132 = erased
-- Data.Fin.Permutation._.inverseˡ′
d_inverse'737''8242'_136 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Function.Bundles.T_Inverse_2068 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_inverse'737''8242'_136 = erased
-- Data.Fin.Permutation.lift₀
d_lift'8320'_140 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Function.Bundles.T_Inverse_2068 ->
  MAlonzo.Code.Function.Bundles.T_Inverse_2068
d_lift'8320'_140 ~v0 ~v1 v2 = du_lift'8320'_140 v2
du_lift'8320'_140 ::
  MAlonzo.Code.Function.Bundles.T_Inverse_2068 ->
  MAlonzo.Code.Function.Bundles.T_Inverse_2068
du_lift'8320'_140 v0
  = coe
      du_permutation_26 (coe du_to_152 (coe v0))
      (coe du_from_156 (coe v0)) erased erased
-- Data.Fin.Permutation._.to
d_to_152 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Function.Bundles.T_Inverse_2068 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10
d_to_152 ~v0 ~v1 v2 v3 = du_to_152 v2 v3
du_to_152 ::
  MAlonzo.Code.Function.Bundles.T_Inverse_2068 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10
du_to_152 v0 v1
  = case coe v1 of
      MAlonzo.Code.Data.Fin.Base.C_zero_12
        -> coe MAlonzo.Code.Data.Fin.Base.C_zero_12
      MAlonzo.Code.Data.Fin.Base.C_suc_16 v3
        -> coe
             MAlonzo.Code.Data.Fin.Base.C_suc_16
             (coe du__'10216''36''10217''691'__28 v0 v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Fin.Permutation._.from
d_from_156 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Function.Bundles.T_Inverse_2068 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10
d_from_156 ~v0 ~v1 v2 v3 = du_from_156 v2 v3
du_from_156 ::
  MAlonzo.Code.Function.Bundles.T_Inverse_2068 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10
du_from_156 v0 v1
  = case coe v1 of
      MAlonzo.Code.Data.Fin.Base.C_zero_12
        -> coe MAlonzo.Code.Data.Fin.Base.C_zero_12
      MAlonzo.Code.Data.Fin.Base.C_suc_16 v3
        -> coe
             MAlonzo.Code.Data.Fin.Base.C_suc_16
             (coe du__'10216''36''10217''737'__30 v0 v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Fin.Permutation._.inverseʳ′
d_inverse'691''8242'_160 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Function.Bundles.T_Inverse_2068 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_inverse'691''8242'_160 = erased
-- Data.Fin.Permutation._.inverseˡ′
d_inverse'737''8242'_164 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Function.Bundles.T_Inverse_2068 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_inverse'737''8242'_164 = erased
-- Data.Fin.Permutation.insert
d_insert_172 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Function.Bundles.T_Inverse_2068 ->
  MAlonzo.Code.Function.Bundles.T_Inverse_2068
d_insert_172 ~v0 ~v1 v2 v3 v4 = du_insert_172 v2 v3 v4
du_insert_172 ::
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Function.Bundles.T_Inverse_2068 ->
  MAlonzo.Code.Function.Bundles.T_Inverse_2068
du_insert_172 v0 v1 v2
  = coe
      du_permutation_26 (coe du_to_188 (coe v0) (coe v1) (coe v2))
      (coe du_from_204 (coe v0) (coe v1) (coe v2)) erased erased
-- Data.Fin.Permutation._.to
d_to_188 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Function.Bundles.T_Inverse_2068 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10
d_to_188 ~v0 ~v1 v2 v3 v4 v5 = du_to_188 v2 v3 v4 v5
du_to_188 ::
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Function.Bundles.T_Inverse_2068 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10
du_to_188 v0 v1 v2 v3
  = let v4
          = coe
              MAlonzo.Code.Data.Fin.Properties.du__'8799'__50 (coe v0)
              (coe v3) in
    coe
      (case coe v4 of
         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v5 v6
           -> if coe v5
                then coe seq (coe v6) (coe v1)
                else coe
                       seq (coe v6)
                       (coe
                          MAlonzo.Code.Data.Fin.Base.du_punchIn_410 (coe v1)
                          (coe
                             du__'10216''36''10217''691'__28 v2
                             (coe
                                MAlonzo.Code.Data.Fin.Base.du_punchOut_396 (coe v0) (coe v3))))
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Data.Fin.Permutation._.from
d_from_204 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Function.Bundles.T_Inverse_2068 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10
d_from_204 ~v0 ~v1 v2 v3 v4 v5 = du_from_204 v2 v3 v4 v5
du_from_204 ::
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Function.Bundles.T_Inverse_2068 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10
du_from_204 v0 v1 v2 v3
  = let v4
          = coe
              MAlonzo.Code.Data.Fin.Properties.du__'8799'__50 (coe v1)
              (coe v3) in
    coe
      (case coe v4 of
         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v5 v6
           -> if coe v5
                then coe seq (coe v6) (coe v0)
                else coe
                       seq (coe v6)
                       (coe
                          MAlonzo.Code.Data.Fin.Base.du_punchIn_410 (coe v0)
                          (coe
                             du__'10216''36''10217''737'__30 v2
                             (coe
                                MAlonzo.Code.Data.Fin.Base.du_punchOut_396 (coe v1) (coe v3))))
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Data.Fin.Permutation._.inverseʳ′
d_inverse'691''8242'_220 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Function.Bundles.T_Inverse_2068 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_inverse'691''8242'_220 = erased
-- Data.Fin.Permutation._.inverseˡ′
d_inverse'737''8242'_254 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Function.Bundles.T_Inverse_2068 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_inverse'737''8242'_254 = erased
-- Data.Fin.Permutation.swap
d_swap_288 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Function.Bundles.T_Inverse_2068 ->
  MAlonzo.Code.Function.Bundles.T_Inverse_2068
d_swap_288 ~v0 ~v1 v2 = du_swap_288 v2
du_swap_288 ::
  MAlonzo.Code.Function.Bundles.T_Inverse_2068 ->
  MAlonzo.Code.Function.Bundles.T_Inverse_2068
du_swap_288 v0
  = coe
      du__'8728''8346'__60
      (coe
         du_transpose_70 (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)
         (coe
            MAlonzo.Code.Data.Fin.Base.C_suc_16
            (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)))
      (coe du_lift'8320'_140 (coe du_lift'8320'_140 (coe v0)))
-- Data.Fin.Permutation._.πʳ
d_π'691'_302 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Function.Bundles.T_Inverse_2068 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10
d_π'691'_302 ~v0 ~v1 v2 = du_π'691'_302 v2
du_π'691'_302 ::
  MAlonzo.Code.Function.Bundles.T_Inverse_2068 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10
du_π'691'_302 v0 = coe du__'10216''36''10217''691'__28 (coe v0)
-- Data.Fin.Permutation._.πˡ
d_π'737'_306 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Function.Bundles.T_Inverse_2068 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10
d_π'737'_306 ~v0 ~v1 v2 = du_π'737'_306 v2
du_π'737'_306 ::
  MAlonzo.Code.Function.Bundles.T_Inverse_2068 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10
du_π'737'_306 v0 = coe du__'10216''36''10217''737'__30 (coe v0)
-- Data.Fin.Permutation._.punchIn-permute
d_punchIn'45'permute_314 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Function.Bundles.T_Inverse_2068 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_punchIn'45'permute_314 = erased
-- Data.Fin.Permutation._.punchIn-permute′
d_punchIn'45'permute'8242'_324 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Function.Bundles.T_Inverse_2068 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_punchIn'45'permute'8242'_324 = erased
-- Data.Fin.Permutation._.lift₀-remove
d_lift'8320''45'remove_330 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Function.Bundles.T_Inverse_2068 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_lift'8320''45'remove_330 = erased
-- Data.Fin.Permutation._._.punchOut-zero
d_punchOut'45'zero_348 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Function.Bundles.T_Inverse_2068 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_punchOut'45'zero_348 = erased
-- Data.Fin.Permutation.↔⇒≡
d_'8596''8658''8801'_356 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Function.Bundles.T_Inverse_2068 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8596''8658''8801'_356 = erased
-- Data.Fin.Permutation.fromPermutation
d_fromPermutation_374 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Function.Bundles.T_Inverse_2068 ->
  MAlonzo.Code.Function.Bundles.T_Inverse_2068
d_fromPermutation_374 ~v0 ~v1 v2 = du_fromPermutation_374 v2
du_fromPermutation_374 ::
  MAlonzo.Code.Function.Bundles.T_Inverse_2068 ->
  MAlonzo.Code.Function.Bundles.T_Inverse_2068
du_fromPermutation_374 v0 = coe v0
-- Data.Fin.Permutation.refute
d_refute_378 ::
  Integer ->
  Integer ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Function.Bundles.T_Inverse_2068 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_refute_378 = erased
-- Data.Fin.Permutation.lift₀-id
d_lift'8320''45'id_386 ::
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_lift'8320''45'id_386 = erased
-- Data.Fin.Permutation.lift₀-comp
d_lift'8320''45'comp_394 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Function.Bundles.T_Inverse_2068 ->
  MAlonzo.Code.Function.Bundles.T_Inverse_2068 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_lift'8320''45'comp_394 = erased
-- Data.Fin.Permutation.lift₀-cong
d_lift'8320''45'cong_410 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Function.Bundles.T_Inverse_2068 ->
  MAlonzo.Code.Function.Bundles.T_Inverse_2068 ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_lift'8320''45'cong_410 = erased
-- Data.Fin.Permutation.lift₀-transpose
d_lift'8320''45'transpose_430 ::
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_lift'8320''45'transpose_430 = erased
-- Data.Fin.Permutation.insert-punchIn
d_insert'45'punchIn_482 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Function.Bundles.T_Inverse_2068 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_insert'45'punchIn_482 = erased
-- Data.Fin.Permutation.insert-remove
d_insert'45'remove_524 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Function.Bundles.T_Inverse_2068 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_insert'45'remove_524 = erased
-- Data.Fin.Permutation.remove-insert
d_remove'45'insert_574 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Function.Bundles.T_Inverse_2068 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_remove'45'insert_574 = erased
