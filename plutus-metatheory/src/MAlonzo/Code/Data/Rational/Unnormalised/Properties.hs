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

module MAlonzo.Code.Data.Rational.Unnormalised.Properties where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.Unit
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Algebra.Apartness.Bundles
import qualified MAlonzo.Code.Algebra.Apartness.Structures
import qualified MAlonzo.Code.Algebra.Bundles
import qualified MAlonzo.Code.Algebra.Bundles.Raw
import qualified MAlonzo.Code.Algebra.Consequences.Setoid
import qualified MAlonzo.Code.Algebra.Construct.NaturalChoice.Base
import qualified MAlonzo.Code.Algebra.Construct.NaturalChoice.MaxOp
import qualified MAlonzo.Code.Algebra.Construct.NaturalChoice.MinMaxOp
import qualified MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp
import qualified MAlonzo.Code.Algebra.Lattice.Bundles
import qualified MAlonzo.Code.Algebra.Lattice.Bundles.Raw
import qualified MAlonzo.Code.Algebra.Lattice.Construct.NaturalChoice.MinMaxOp
import qualified MAlonzo.Code.Algebra.Lattice.Construct.NaturalChoice.MinOp
import qualified MAlonzo.Code.Algebra.Lattice.Structures
import qualified MAlonzo.Code.Algebra.Structures
import qualified MAlonzo.Code.Data.Bool.Base
import qualified MAlonzo.Code.Data.Integer.Base
import qualified MAlonzo.Code.Data.Integer.Properties
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Data.Rational.Unnormalised.Base
import qualified MAlonzo.Code.Data.Sign.Base
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Function.Base
import qualified MAlonzo.Code.Relation.Binary.Bundles
import qualified MAlonzo.Code.Relation.Binary.Consequences
import qualified MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd
import qualified MAlonzo.Code.Relation.Binary.Definitions
import qualified MAlonzo.Code.Relation.Binary.PropositionalEquality.Core
import qualified MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties
import qualified MAlonzo.Code.Relation.Binary.Reasoning.Base.Single
import qualified MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple
import qualified MAlonzo.Code.Relation.Binary.Reasoning.Syntax
import qualified MAlonzo.Code.Relation.Binary.Structures
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core
import qualified MAlonzo.Code.Relation.Nullary.Negation.Core

-- Data.Rational.Unnormalised.Properties.↥↧≡⇒≡
d_'8613''8615''8801''8658''8801'_118 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8613''8615''8801''8658''8801'_118 = erased
-- Data.Rational.Unnormalised.Properties./-cong
d_'47''45'cong_132 ::
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'47''45'cong_132 = erased
-- Data.Rational.Unnormalised.Properties.↥[n/d]≡n
d_'8613''91'n'47'd'93''8801'n_140 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8613''91'n'47'd'93''8801'n_140 = erased
-- Data.Rational.Unnormalised.Properties.↧[n/d]≡d
d_'8615''91'n'47'd'93''8801'd_152 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8615''91'n'47'd'93''8801'd_152 = erased
-- Data.Rational.Unnormalised.Properties.drop-*≡*
d_drop'45''42''8801''42'_162 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8771'__24 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_drop'45''42''8801''42'_162 = erased
-- Data.Rational.Unnormalised.Properties.≃-refl
d_'8771''45'refl_166 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8771'__24
d_'8771''45'refl_166 ~v0 = du_'8771''45'refl_166
du_'8771''45'refl_166 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8771'__24
du_'8771''45'refl_166
  = coe
      MAlonzo.Code.Data.Rational.Unnormalised.Base.C_'42''8801''42'_30
-- Data.Rational.Unnormalised.Properties.≃-reflexive
d_'8771''45'reflexive_168 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8771'__24
d_'8771''45'reflexive_168 ~v0 ~v1 ~v2 = du_'8771''45'reflexive_168
du_'8771''45'reflexive_168 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8771'__24
du_'8771''45'reflexive_168
  = coe
      MAlonzo.Code.Data.Rational.Unnormalised.Base.C_'42''8801''42'_30
-- Data.Rational.Unnormalised.Properties.≃-sym
d_'8771''45'sym_170 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8771'__24 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8771'__24
d_'8771''45'sym_170 ~v0 ~v1 v2 = du_'8771''45'sym_170 v2
du_'8771''45'sym_170 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8771'__24 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8771'__24
du_'8771''45'sym_170 v0
  = coe
      seq (coe v0)
      (coe
         MAlonzo.Code.Data.Rational.Unnormalised.Base.C_'42''8801''42'_30)
-- Data.Rational.Unnormalised.Properties.≃-trans
d_'8771''45'trans_174 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8771'__24 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8771'__24 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8771'__24
d_'8771''45'trans_174 ~v0 ~v1 ~v2 v3 v4
  = du_'8771''45'trans_174 v3 v4
du_'8771''45'trans_174 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8771'__24 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8771'__24 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8771'__24
du_'8771''45'trans_174 v0 v1
  = coe
      seq (coe v0)
      (coe
         seq (coe v1)
         (coe
            MAlonzo.Code.Data.Rational.Unnormalised.Base.C_'42''8801''42'_30))
-- Data.Rational.Unnormalised.Properties._≃?_
d__'8771''63'__194 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8771''63'__194 v0 v1
  = coe
      MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
      (\ v2 ->
         coe
           MAlonzo.Code.Data.Rational.Unnormalised.Base.C_'42''8801''42'_30)
      erased
      (coe
         MAlonzo.Code.Data.Integer.Properties.d__'8799'__2714
         (coe
            MAlonzo.Code.Data.Integer.Base.d__'42'__308
            (coe
               MAlonzo.Code.Data.Rational.Unnormalised.Base.d_numerator_14
               (coe v0))
            (coe
               MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
               (coe v1)))
         (coe
            MAlonzo.Code.Data.Integer.Base.d__'42'__308
            (coe
               MAlonzo.Code.Data.Rational.Unnormalised.Base.d_numerator_14
               (coe v1))
            (coe
               MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
               (coe v0))))
-- Data.Rational.Unnormalised.Properties.0≄1
d_0'8772'1_200 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8771'__24 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_0'8772'1_200 = erased
-- Data.Rational.Unnormalised.Properties.≃-≄-irreflexive
d_'8771''45''8772''45'irreflexive_202 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8771'__24 ->
  (MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8771'__24 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'8771''45''8772''45'irreflexive_202 = erased
-- Data.Rational.Unnormalised.Properties.≄-symmetric
d_'8772''45'symmetric_208 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  (MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8771'__24 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8771'__24 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'8772''45'symmetric_208 = erased
-- Data.Rational.Unnormalised.Properties.≄-cotransitive
d_'8772''45'cotransitive_214 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  (MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8771'__24 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_'8772''45'cotransitive_214 v0 v1 ~v2 v3
  = du_'8772''45'cotransitive_214 v0 v1 v3
du_'8772''45'cotransitive_214 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_'8772''45'cotransitive_214 v0 v1 v2
  = let v3
          = coe
              MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
              (\ v3 ->
                 coe
                   MAlonzo.Code.Data.Rational.Unnormalised.Base.C_'42''8801''42'_30)
              erased
              (coe
                 MAlonzo.Code.Data.Integer.Properties.d__'8799'__2714
                 (coe
                    MAlonzo.Code.Data.Integer.Base.d__'42'__308
                    (coe
                       MAlonzo.Code.Data.Rational.Unnormalised.Base.d_numerator_14
                       (coe v0))
                    (coe
                       MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                       (coe v2)))
                 (coe
                    MAlonzo.Code.Data.Integer.Base.d__'42'__308
                    (coe
                       MAlonzo.Code.Data.Rational.Unnormalised.Base.d_numerator_14
                       (coe v2))
                    (coe
                       MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                       (coe v0)))) in
    coe
      (let v4
             = coe
                 MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                 (\ v4 ->
                    coe
                      MAlonzo.Code.Data.Rational.Unnormalised.Base.C_'42''8801''42'_30)
                 erased
                 (coe
                    MAlonzo.Code.Data.Integer.Properties.d__'8799'__2714
                    (coe
                       MAlonzo.Code.Data.Integer.Base.d__'42'__308
                       (coe
                          MAlonzo.Code.Data.Rational.Unnormalised.Base.d_numerator_14
                          (coe v2))
                       (coe
                          MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                          (coe v1)))
                    (coe
                       MAlonzo.Code.Data.Integer.Base.d__'42'__308
                       (coe
                          MAlonzo.Code.Data.Rational.Unnormalised.Base.d_numerator_14
                          (coe v1))
                       (coe
                          MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                          (coe v2)))) in
       coe
         (case coe v3 of
            MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v5 v6
              -> if coe v5
                   then coe
                          seq (coe v6)
                          (case coe v4 of
                             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v7 v8
                               -> if coe v7
                                    then coe
                                           seq (coe v8)
                                           (coe
                                              MAlonzo.Code.Relation.Nullary.Negation.Core.du_contradiction_44
                                              erased)
                                    else coe
                                           seq (coe v8)
                                           (coe MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 erased)
                             _ -> MAlonzo.RTE.mazUnreachableError)
                   else coe
                          seq (coe v6) (coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 erased)
            _ -> MAlonzo.RTE.mazUnreachableError))
-- Data.Rational.Unnormalised.Properties.≃-isEquivalence
d_'8771''45'isEquivalence_260 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsEquivalence_26
d_'8771''45'isEquivalence_260
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_IsEquivalence'46'constructor_745
      (\ v0 -> coe du_'8771''45'refl_166)
      (\ v0 v1 v2 -> coe du_'8771''45'sym_170 v2)
      (\ v0 v1 v2 v3 v4 -> coe du_'8771''45'trans_174 v3 v4)
-- Data.Rational.Unnormalised.Properties.≃-isDecEquivalence
d_'8771''45'isDecEquivalence_262 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecEquivalence_44
d_'8771''45'isDecEquivalence_262
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_IsDecEquivalence'46'constructor_3083
      (coe d_'8771''45'isEquivalence_260) (coe d__'8771''63'__194)
-- Data.Rational.Unnormalised.Properties.≄-isApartnessRelation
d_'8772''45'isApartnessRelation_264 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsApartnessRelation_722
d_'8772''45'isApartnessRelation_264
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_IsApartnessRelation'46'constructor_32525
      erased
      (\ v0 v1 v2 v3 -> coe du_'8772''45'cotransitive_214 v0 v1 v3)
-- Data.Rational.Unnormalised.Properties.≄-tight
d_'8772''45'tight_266 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8772''45'tight_266 v0 v1
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         (\ v2 ->
            coe
              MAlonzo.Code.Relation.Nullary.Decidable.Core.du_decidable'45'stable_198
              (coe d__'8771''63'__194 (coe v0) (coe v1))))
      (coe (\ v2 v3 -> coe v3 v2))
-- Data.Rational.Unnormalised.Properties.≃-setoid
d_'8771''45'setoid_282 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44
d_'8771''45'setoid_282
  = coe
      MAlonzo.Code.Relation.Binary.Bundles.C_Setoid'46'constructor_761
      d_'8771''45'isEquivalence_260
-- Data.Rational.Unnormalised.Properties.≃-decSetoid
d_'8771''45'decSetoid_284 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_DecSetoid_86
d_'8771''45'decSetoid_284
  = coe
      MAlonzo.Code.Relation.Binary.Bundles.C_DecSetoid'46'constructor_1435
      d_'8771''45'isDecEquivalence_262
-- Data.Rational.Unnormalised.Properties.≃-Reasoning._IsRelatedTo_
d__IsRelatedTo__288 a0 a1 = ()
-- Data.Rational.Unnormalised.Properties.≃-Reasoning._∎
d__'8718'_290 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.T__IsRelatedTo__26
d__'8718'_290
  = let v0 = d_'8771''45'setoid_282 in
    coe
      (let v1
             = MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                 (coe
                    MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                    (coe v0)) in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_stop_54
               (coe v1))))
-- Data.Rational.Unnormalised.Properties.≃-Reasoning.begin_
d_begin__292 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.T__IsRelatedTo__26 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8771'__24
d_begin__292
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
      (\ v0 v1 v2 ->
         coe
           MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_start_36 v2)
-- Data.Rational.Unnormalised.Properties.≃-Reasoning.start
d_start_296 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.T__IsRelatedTo__26 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8771'__24
d_start_296 v0 v1 v2
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_start_36 v2
-- Data.Rational.Unnormalised.Properties.≃-Reasoning.step-≈
d_step'45''8776'_298 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.T__IsRelatedTo__26 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8771'__24 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.T__IsRelatedTo__26
d_step'45''8776'_298
  = let v0 = d_'8771''45'setoid_282 in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776'_372
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_trans_38
               (coe
                  MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                  (coe v0)))))
-- Data.Rational.Unnormalised.Properties.≃-Reasoning.step-≈-⟨
d_step'45''8776''45''10216'_300 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.T__IsRelatedTo__26 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8771'__24 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.T__IsRelatedTo__26
d_step'45''8776''45''10216'_300
  = let v0 = d_'8771''45'setoid_282 in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10216'_370
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_trans_38
               (coe
                  MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v0))))
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_sym_36
            (coe
               MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v0))))
-- Data.Rational.Unnormalised.Properties.≃-Reasoning.step-≈-⟩
d_step'45''8776''45''10217'_302 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.T__IsRelatedTo__26 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8771'__24 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.T__IsRelatedTo__26
d_step'45''8776''45''10217'_302
  = let v0 = d_'8771''45'setoid_282 in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''45''10217'_368
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_trans_38
               (coe
                  MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60
                  (coe v0)))))
-- Data.Rational.Unnormalised.Properties.≃-Reasoning.step-≈˘
d_step'45''8776''728'_304 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.T__IsRelatedTo__26 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8771'__24 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.T__IsRelatedTo__26
d_step'45''8776''728'_304
  = let v0 = d_'8771''45'setoid_282 in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8776''728'_374
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
            (coe
               MAlonzo.Code.Relation.Binary.Structures.d_trans_38
               (coe
                  MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v0))))
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_sym_36
            (coe
               MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v0))))
-- Data.Rational.Unnormalised.Properties.≃-Reasoning.step-≡
d_step'45''8801'_306 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.T__IsRelatedTo__26 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.T__IsRelatedTo__26
d_step'45''8801'_306
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801'_450
      (coe (\ v0 v1 v2 v3 v4 -> v4))
-- Data.Rational.Unnormalised.Properties.≃-Reasoning.step-≡-∣
d_step'45''8801''45''8739'_308 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.T__IsRelatedTo__26 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.T__IsRelatedTo__26
d_step'45''8801''45''8739'_308 ~v0 ~v1 v2
  = du_step'45''8801''45''8739'_308 v2
du_step'45''8801''45''8739'_308 ::
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.T__IsRelatedTo__26 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.T__IsRelatedTo__26
du_step'45''8801''45''8739'_308 v0 = coe v0
-- Data.Rational.Unnormalised.Properties.≃-Reasoning.step-≡-⟨
d_step'45''8801''45''10216'_310 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.T__IsRelatedTo__26 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.T__IsRelatedTo__26
d_step'45''8801''45''10216'_310
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10216'_448
      (coe (\ v0 v1 v2 v3 v4 -> v4))
-- Data.Rational.Unnormalised.Properties.≃-Reasoning.step-≡-⟩
d_step'45''8801''45''10217'_312 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.T__IsRelatedTo__26 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.T__IsRelatedTo__26
d_step'45''8801''45''10217'_312
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_436
      (coe (\ v0 v1 v2 v3 v4 -> v4))
-- Data.Rational.Unnormalised.Properties.≃-Reasoning.step-≡˘
d_step'45''8801''728'_314 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.T__IsRelatedTo__26 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.T__IsRelatedTo__26
d_step'45''8801''728'_314
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''728'_452
      (coe (\ v0 v1 v2 v3 v4 -> v4))
-- Data.Rational.Unnormalised.Properties.≃-Reasoning.stop
d_stop_316 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.T__IsRelatedTo__26
d_stop_316
  = let v0 = d_'8771''45'setoid_282 in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_stop_54
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_refl_34
            (coe
               MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v0))))
-- Data.Rational.Unnormalised.Properties.≃-Reasoning.∼-go
d_'8764''45'go_318 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8771'__24 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.T__IsRelatedTo__26 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.T__IsRelatedTo__26
d_'8764''45'go_318
  = let v0 = d_'8771''45'setoid_282 in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.du_'8764''45'go_40
         (coe
            MAlonzo.Code.Relation.Binary.Structures.d_trans_38
            (coe
               MAlonzo.Code.Relation.Binary.Bundles.d_isEquivalence_60 (coe v0))))
-- Data.Rational.Unnormalised.Properties.≃-Reasoning.≡-go
d_'8801''45'go_320 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.T__IsRelatedTo__26 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.T__IsRelatedTo__26
d_'8801''45'go_320 ~v0 ~v1 ~v2 ~v3 v4 = du_'8801''45'go_320 v4
du_'8801''45'go_320 ::
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.T__IsRelatedTo__26 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Single.T__IsRelatedTo__26
du_'8801''45'go_320 v0 = coe v0
-- Data.Rational.Unnormalised.Properties.↥p≡0⇒p≃0
d_'8613'p'8801'0'8658'p'8771'0_328 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8771'__24
d_'8613'p'8801'0'8658'p'8771'0_328 ~v0 ~v1
  = du_'8613'p'8801'0'8658'p'8771'0_328
du_'8613'p'8801'0'8658'p'8771'0_328 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8771'__24
du_'8613'p'8801'0'8658'p'8771'0_328
  = coe
      MAlonzo.Code.Data.Rational.Unnormalised.Base.C_'42''8801''42'_30
-- Data.Rational.Unnormalised.Properties.p≃0⇒↥p≡0
d_p'8771'0'8658''8613'p'8801'0_338 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8771'__24 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_p'8771'0'8658''8613'p'8801'0_338 = erased
-- Data.Rational.Unnormalised.Properties.↥p≡↥q≡0⇒p≃q
d_'8613'p'8801''8613'q'8801'0'8658'p'8771'q_352 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8771'__24
d_'8613'p'8801''8613'q'8801'0'8658'p'8771'q_352 ~v0 ~v1 ~v2 ~v3
  = du_'8613'p'8801''8613'q'8801'0'8658'p'8771'q_352
du_'8613'p'8801''8613'q'8801'0'8658'p'8771'q_352 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8771'__24
du_'8613'p'8801''8613'q'8801'0'8658'p'8771'q_352
  = coe
      du_'8771''45'trans_174 (coe du_'8613'p'8801'0'8658'p'8771'0_328)
      (coe
         du_'8771''45'sym_170 (coe du_'8613'p'8801'0'8658'p'8771'0_328))
-- Data.Rational.Unnormalised.Properties.neg-involutive-≡
d_neg'45'involutive'45''8801'_362 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_neg'45'involutive'45''8801'_362 = erased
-- Data.Rational.Unnormalised.Properties.neg-involutive
d_neg'45'involutive_370 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8771'__24
d_neg'45'involutive_370 ~v0 = du_neg'45'involutive_370
du_neg'45'involutive_370 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8771'__24
du_neg'45'involutive_370 = coe du_'8771''45'refl_166
-- Data.Rational.Unnormalised.Properties.-‿cong
d_'45''8255'cong_378 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8771'__24 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8771'__24
d_'45''8255'cong_378 v0 v1 v2
  = coe
      seq (coe v0)
      (coe
         seq (coe v1)
         (coe
            seq (coe v2)
            (coe
               MAlonzo.Code.Data.Rational.Unnormalised.Base.C_'42''8801''42'_30)))
-- Data.Rational.Unnormalised.Properties.neg-mono-<
d_neg'45'mono'45''60'_400 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'60'__46 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'60'__46
d_neg'45'mono'45''60'_400 v0 v1 v2
  = case coe v0 of
      MAlonzo.Code.Data.Rational.Unnormalised.Base.C_mkℚ'7512'_22 v3 v4
        -> case coe v1 of
             MAlonzo.Code.Data.Rational.Unnormalised.Base.C_mkℚ'7512'_22 v5 v6
               -> case coe v2 of
                    MAlonzo.Code.Data.Rational.Unnormalised.Base.C_'42''60''42'_52 v9
                      -> coe
                           MAlonzo.Code.Data.Rational.Unnormalised.Base.C_'42''60''42'_52
                           (let v10
                                  = coe
                                      MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_strictRelation_202 in
                            coe
                              (coe
                                 MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__126
                                 (coe v10)
                                 (coe
                                    MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                    (coe MAlonzo.Code.Data.Integer.Base.d_'45'__252 (coe v5))
                                    (coe
                                       MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                       (coe v0)))
                                 (coe
                                    MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                    (coe
                                       MAlonzo.Code.Data.Rational.Unnormalised.Base.d_numerator_14
                                       (coe
                                          MAlonzo.Code.Data.Rational.Unnormalised.Base.d_'45'__190
                                          (coe v0)))
                                    (coe
                                       MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                       (coe
                                          MAlonzo.Code.Data.Rational.Unnormalised.Base.d_'45'__190
                                          (coe v1))))
                                 (coe
                                    MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10216'_448
                                    (\ v11 v12 v13 v14 v15 -> v15)
                                    (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                       (coe MAlonzo.Code.Data.Integer.Base.d_'45'__252 (coe v5))
                                       (coe
                                          MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                          (coe v0)))
                                    (MAlonzo.Code.Data.Integer.Base.d_'45'__252
                                       (coe
                                          MAlonzo.Code.Data.Integer.Base.d__'42'__308 (coe v5)
                                          (coe
                                             MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                             (coe v0))))
                                    (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                       (coe
                                          MAlonzo.Code.Data.Rational.Unnormalised.Base.d_numerator_14
                                          (coe
                                             MAlonzo.Code.Data.Rational.Unnormalised.Base.d_'45'__190
                                             (coe v0)))
                                       (coe
                                          MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                          (coe
                                             MAlonzo.Code.Data.Rational.Unnormalised.Base.d_'45'__190
                                             (coe v1))))
                                    (coe
                                       MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''60'_312
                                       (coe
                                          MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'60''45'go_152
                                          (\ v11 v12 v13 v14 v15 ->
                                             coe
                                               MAlonzo.Code.Data.Integer.Properties.du_'60''45'trans_3008
                                               v14 v15)
                                          (coe
                                             MAlonzo.Code.Relation.Binary.PropositionalEquality.Core.du_resp'8322'_160)
                                          (\ v11 v12 v13 v14 v15 ->
                                             coe
                                               MAlonzo.Code.Data.Integer.Properties.du_'60''45''8804''45'trans_2994
                                               v14 v15))
                                       (MAlonzo.Code.Data.Integer.Base.d_'45'__252
                                          (coe
                                             MAlonzo.Code.Data.Integer.Base.d__'42'__308 (coe v5)
                                             (coe
                                                MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                                (coe v0))))
                                       (MAlonzo.Code.Data.Integer.Base.d_'45'__252
                                          (coe
                                             MAlonzo.Code.Data.Integer.Base.d__'42'__308 (coe v3)
                                             (coe
                                                MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                                (coe v1))))
                                       (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                          (coe
                                             MAlonzo.Code.Data.Rational.Unnormalised.Base.d_numerator_14
                                             (coe
                                                MAlonzo.Code.Data.Rational.Unnormalised.Base.d_'45'__190
                                                (coe v0)))
                                          (coe
                                             MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                             (coe
                                                MAlonzo.Code.Data.Rational.Unnormalised.Base.d_'45'__190
                                                (coe v1))))
                                       (coe
                                          MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_436
                                          (\ v11 v12 v13 v14 v15 -> v15)
                                          (MAlonzo.Code.Data.Integer.Base.d_'45'__252
                                             (coe
                                                MAlonzo.Code.Data.Integer.Base.d__'42'__308 (coe v3)
                                                (coe
                                                   MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                                   (coe v1))))
                                          (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                             (coe
                                                MAlonzo.Code.Data.Rational.Unnormalised.Base.d_numerator_14
                                                (coe
                                                   MAlonzo.Code.Data.Rational.Unnormalised.Base.d_'45'__190
                                                   (coe v0)))
                                             (coe
                                                MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                                (coe
                                                   MAlonzo.Code.Data.Rational.Unnormalised.Base.d_'45'__190
                                                   (coe v1))))
                                          (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                             (coe
                                                MAlonzo.Code.Data.Rational.Unnormalised.Base.d_numerator_14
                                                (coe
                                                   MAlonzo.Code.Data.Rational.Unnormalised.Base.d_'45'__190
                                                   (coe v0)))
                                             (coe
                                                MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                                (coe
                                                   MAlonzo.Code.Data.Rational.Unnormalised.Base.d_'45'__190
                                                   (coe v1))))
                                          (coe
                                             MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                                             (coe
                                                MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_stop_166
                                                (coe
                                                   MAlonzo.Code.Data.Integer.Properties.d_'8804''45'isPreorder_2822))
                                             (coe
                                                MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                (coe
                                                   MAlonzo.Code.Data.Rational.Unnormalised.Base.d_numerator_14
                                                   (coe
                                                      MAlonzo.Code.Data.Rational.Unnormalised.Base.d_'45'__190
                                                      (coe v0)))
                                                (coe
                                                   MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                                   (coe
                                                      MAlonzo.Code.Data.Rational.Unnormalised.Base.d_'45'__190
                                                      (coe v1)))))
                                          erased)
                                       (MAlonzo.Code.Data.Integer.Properties.d_neg'45'mono'45''60'_3324
                                          (coe
                                             MAlonzo.Code.Data.Integer.Base.d__'42'__308 (coe v3)
                                             (coe
                                                MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                                (coe v1)))
                                          (coe
                                             MAlonzo.Code.Data.Integer.Base.d__'42'__308 (coe v5)
                                             (coe
                                                MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                                (coe v0)))
                                          (coe v9)))
                                    erased)))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Rational.Unnormalised.Properties.neg-cancel-<
d_neg'45'cancel'45''60'_416 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'60'__46 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'60'__46
d_neg'45'cancel'45''60'_416 v0 v1 v2
  = case coe v0 of
      MAlonzo.Code.Data.Rational.Unnormalised.Base.C_mkℚ'7512'_22 v3 v4
        -> case coe v1 of
             MAlonzo.Code.Data.Rational.Unnormalised.Base.C_mkℚ'7512'_22 v5 v6
               -> case coe v2 of
                    MAlonzo.Code.Data.Rational.Unnormalised.Base.C_'42''60''42'_52 v9
                      -> coe
                           MAlonzo.Code.Data.Rational.Unnormalised.Base.C_'42''60''42'_52
                           (let v10
                                  = coe
                                      MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_strictRelation_202 in
                            coe
                              (coe
                                 MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__126
                                 (coe v10)
                                 (coe
                                    MAlonzo.Code.Data.Integer.Base.d__'42'__308 (coe v5)
                                    (coe
                                       MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                       (coe v0)))
                                 (coe
                                    MAlonzo.Code.Data.Integer.Base.d__'42'__308 (coe v3)
                                    (coe
                                       MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                       (coe v1)))
                                 (coe
                                    MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10216'_448
                                    (\ v11 v12 v13 v14 v15 -> v15)
                                    (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                       (coe v5)
                                       (coe
                                          MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                          (coe v0)))
                                    (MAlonzo.Code.Data.Integer.Base.d_'45'__252
                                       (coe
                                          MAlonzo.Code.Data.Integer.Base.d_'45'__252
                                          (coe
                                             MAlonzo.Code.Data.Integer.Base.d__'42'__308 (coe v5)
                                             (coe
                                                MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                                (coe v0)))))
                                    (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                       (coe v3)
                                       (coe
                                          MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                          (coe v1)))
                                    (coe
                                       MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_436
                                       (\ v11 v12 v13 v14 v15 -> v15)
                                       (MAlonzo.Code.Data.Integer.Base.d_'45'__252
                                          (coe
                                             MAlonzo.Code.Data.Integer.Base.d_'45'__252
                                             (coe
                                                MAlonzo.Code.Data.Integer.Base.d__'42'__308 (coe v5)
                                                (coe
                                                   MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                                   (coe v0)))))
                                       (MAlonzo.Code.Data.Integer.Base.d_'45'__252
                                          (coe
                                             MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                             (coe
                                                MAlonzo.Code.Data.Integer.Base.d_'45'__252 (coe v5))
                                             (coe
                                                MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                                (coe v0))))
                                       (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                          (coe v3)
                                          (coe
                                             MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                             (coe v1)))
                                       (coe
                                          MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''60'_312
                                          (coe
                                             MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'60''45'go_152
                                             (\ v11 v12 v13 v14 v15 ->
                                                coe
                                                  MAlonzo.Code.Data.Integer.Properties.du_'60''45'trans_3008
                                                  v14 v15)
                                             (coe
                                                MAlonzo.Code.Relation.Binary.PropositionalEquality.Core.du_resp'8322'_160)
                                             (\ v11 v12 v13 v14 v15 ->
                                                coe
                                                  MAlonzo.Code.Data.Integer.Properties.du_'60''45''8804''45'trans_2994
                                                  v14 v15))
                                          (MAlonzo.Code.Data.Integer.Base.d_'45'__252
                                             (coe
                                                MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                (coe
                                                   MAlonzo.Code.Data.Integer.Base.d_'45'__252
                                                   (coe v5))
                                                (coe
                                                   MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                                   (coe v0))))
                                          (MAlonzo.Code.Data.Integer.Base.d_'45'__252
                                             (coe
                                                MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                (coe
                                                   MAlonzo.Code.Data.Integer.Base.d_'45'__252
                                                   (coe v3))
                                                (coe
                                                   MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                                   (coe v1))))
                                          (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                             (coe v3)
                                             (coe
                                                MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                                (coe v1)))
                                          (coe
                                             MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10216'_448
                                             (\ v11 v12 v13 v14 v15 -> v15)
                                             (MAlonzo.Code.Data.Integer.Base.d_'45'__252
                                                (coe
                                                   MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                   (coe
                                                      MAlonzo.Code.Data.Integer.Base.d_'45'__252
                                                      (coe v3))
                                                   (coe
                                                      MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                                      (coe v1))))
                                             (MAlonzo.Code.Data.Integer.Base.d_'45'__252
                                                (coe
                                                   MAlonzo.Code.Data.Integer.Base.d_'45'__252
                                                   (coe
                                                      MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                      (coe v3)
                                                      (coe
                                                         MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                                         (coe v1)))))
                                             (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                (coe v3)
                                                (coe
                                                   MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                                   (coe v1)))
                                             (coe
                                                MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_436
                                                (\ v11 v12 v13 v14 v15 -> v15)
                                                (MAlonzo.Code.Data.Integer.Base.d_'45'__252
                                                   (coe
                                                      MAlonzo.Code.Data.Integer.Base.d_'45'__252
                                                      (coe
                                                         MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                         (coe v3)
                                                         (coe
                                                            MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                                            (coe v1)))))
                                                (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                   (coe v3)
                                                   (coe
                                                      MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                                      (coe v1)))
                                                (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                   (coe v3)
                                                   (coe
                                                      MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                                      (coe v1)))
                                                (coe
                                                   MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                                                   (coe
                                                      MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_stop_166
                                                      (coe
                                                         MAlonzo.Code.Data.Integer.Properties.d_'8804''45'isPreorder_2822))
                                                   (coe
                                                      MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                      (coe v3)
                                                      (coe
                                                         MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                                         (coe v1))))
                                                erased)
                                             erased)
                                          (MAlonzo.Code.Data.Integer.Properties.d_neg'45'mono'45''60'_3324
                                             (coe
                                                MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                (coe
                                                   MAlonzo.Code.Data.Rational.Unnormalised.Base.d_numerator_14
                                                   (coe
                                                      MAlonzo.Code.Data.Rational.Unnormalised.Base.d_'45'__190
                                                      (coe v0)))
                                                (coe
                                                   MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                                   (coe
                                                      MAlonzo.Code.Data.Rational.Unnormalised.Base.d_'45'__190
                                                      (coe v1))))
                                             (coe
                                                MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                (coe
                                                   MAlonzo.Code.Data.Rational.Unnormalised.Base.d_numerator_14
                                                   (coe
                                                      MAlonzo.Code.Data.Rational.Unnormalised.Base.d_'45'__190
                                                      (coe v1)))
                                                (coe
                                                   MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                                   (coe
                                                      MAlonzo.Code.Data.Rational.Unnormalised.Base.d_'45'__190
                                                      (coe v0))))
                                             (coe v9)))
                                       erased)
                                    erased)))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Rational.Unnormalised.Properties.drop-*≤*
d_drop'45''42''8804''42'_428 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8804'__38 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26
d_drop'45''42''8804''42'_428 ~v0 ~v1 v2
  = du_drop'45''42''8804''42'_428 v2
du_drop'45''42''8804''42'_428 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8804'__38 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26
du_drop'45''42''8804''42'_428 v0
  = case coe v0 of
      MAlonzo.Code.Data.Rational.Unnormalised.Base.C_'42''8804''42'_44 v3
        -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Rational.Unnormalised.Properties.≤-reflexive
d_'8804''45'reflexive_432 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8771'__24 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8804'__38
d_'8804''45'reflexive_432 v0 v1 v2
  = coe
      seq (coe v2)
      (coe
         MAlonzo.Code.Data.Rational.Unnormalised.Base.C_'42''8804''42'_44
         (coe
            MAlonzo.Code.Data.Integer.Properties.du_'8804''45'reflexive_2744
            (coe
               MAlonzo.Code.Data.Integer.Base.d__'42'__308
               (coe
                  MAlonzo.Code.Data.Rational.Unnormalised.Base.d_numerator_14
                  (coe v0))
               (coe
                  MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                  (coe v1)))))
-- Data.Rational.Unnormalised.Properties.≤-refl
d_'8804''45'refl_436 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8804'__38
d_'8804''45'refl_436 v0
  = coe
      d_'8804''45'reflexive_432 (coe v0) (coe v0)
      (coe du_'8771''45'refl_166)
-- Data.Rational.Unnormalised.Properties.≤-reflexive-≡
d_'8804''45'reflexive'45''8801'_438 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8804'__38
d_'8804''45'reflexive'45''8801'_438 v0 ~v1 ~v2
  = du_'8804''45'reflexive'45''8801'_438 v0
du_'8804''45'reflexive'45''8801'_438 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8804'__38
du_'8804''45'reflexive'45''8801'_438 v0
  = coe d_'8804''45'refl_436 (coe v0)
-- Data.Rational.Unnormalised.Properties.≤-trans
d_'8804''45'trans_440 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8804'__38 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8804'__38 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8804'__38
d_'8804''45'trans_440 v0 v1 v2 v3 v4
  = case coe v3 of
      MAlonzo.Code.Data.Rational.Unnormalised.Base.C_'42''8804''42'_44 v7
        -> case coe v4 of
             MAlonzo.Code.Data.Rational.Unnormalised.Base.C_'42''8804''42'_44 v10
               -> coe
                    MAlonzo.Code.Data.Rational.Unnormalised.Base.C_'42''8804''42'_44
                    (coe
                       MAlonzo.Code.Data.Integer.Properties.du_'42''45'cancel'691''45''8804''45'pos_5978
                       (coe
                          MAlonzo.Code.Data.Integer.Base.d__'42'__308
                          (coe
                             MAlonzo.Code.Data.Rational.Unnormalised.Base.d_numerator_14
                             (coe v0))
                          (coe
                             MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                             (coe v2)))
                       (coe
                          MAlonzo.Code.Data.Integer.Base.d__'42'__308
                          (coe
                             MAlonzo.Code.Data.Rational.Unnormalised.Base.d_numerator_14
                             (coe v2))
                          (coe
                             MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                             (coe v0)))
                       (coe
                          MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
                          (coe
                             MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_start_96
                             (coe
                                MAlonzo.Code.Data.Integer.Properties.d_'8804''45'isPreorder_2822)
                             (\ v11 v12 v13 ->
                                coe
                                  MAlonzo.Code.Data.Integer.Properties.du_'60''8658''8804'_2868
                                  v13))
                          (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                             (coe
                                MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                (coe
                                   MAlonzo.Code.Data.Rational.Unnormalised.Base.d_numerator_14
                                   (coe v0))
                                (coe
                                   MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                   (coe v2)))
                             (coe
                                MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                (coe v1)))
                          (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                             (coe
                                MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                (coe
                                   MAlonzo.Code.Data.Rational.Unnormalised.Base.d_numerator_14
                                   (coe v2))
                                (coe
                                   MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                   (coe v0)))
                             (coe
                                MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                (coe v1)))
                          (coe
                             MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_436
                             (\ v11 v12 v13 v14 v15 -> v15)
                             (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                (coe
                                   MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                   (coe
                                      MAlonzo.Code.Data.Rational.Unnormalised.Base.d_numerator_14
                                      (coe v0))
                                   (coe
                                      MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                      (coe v2)))
                                (coe
                                   MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                   (coe v1)))
                             (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                (coe
                                   MAlonzo.Code.Data.Rational.Unnormalised.Base.d_numerator_14
                                   (coe v0))
                                (coe
                                   MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                   (coe
                                      MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                      (coe v2))
                                   (coe
                                      MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                      (coe v1))))
                             (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                (coe
                                   MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                   (coe
                                      MAlonzo.Code.Data.Rational.Unnormalised.Base.d_numerator_14
                                      (coe v2))
                                   (coe
                                      MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                      (coe v0)))
                                (coe
                                   MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                   (coe v1)))
                             (coe
                                MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_436
                                (\ v11 v12 v13 v14 v15 -> v15)
                                (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                   (coe
                                      MAlonzo.Code.Data.Rational.Unnormalised.Base.d_numerator_14
                                      (coe v0))
                                   (coe
                                      MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                      (coe
                                         MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                         (coe v2))
                                      (coe
                                         MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                         (coe v1))))
                                (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                   (coe
                                      MAlonzo.Code.Data.Rational.Unnormalised.Base.d_numerator_14
                                      (coe v0))
                                   (coe
                                      MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                      (coe
                                         MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                         (coe v1))
                                      (coe
                                         MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                         (coe v2))))
                                (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                   (coe
                                      MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                      (coe
                                         MAlonzo.Code.Data.Rational.Unnormalised.Base.d_numerator_14
                                         (coe v2))
                                      (coe
                                         MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                         (coe v0)))
                                   (coe
                                      MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                      (coe v1)))
                                (coe
                                   MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10216'_448
                                   (\ v11 v12 v13 v14 v15 -> v15)
                                   (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                      (coe
                                         MAlonzo.Code.Data.Rational.Unnormalised.Base.d_numerator_14
                                         (coe v0))
                                      (coe
                                         MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                         (coe
                                            MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                            (coe v1))
                                         (coe
                                            MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                            (coe v2))))
                                   (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                      (coe
                                         MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                         (coe
                                            MAlonzo.Code.Data.Rational.Unnormalised.Base.d_numerator_14
                                            (coe v0))
                                         (coe
                                            MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                            (coe v1)))
                                      (coe
                                         MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                         (coe v2)))
                                   (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                      (coe
                                         MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                         (coe
                                            MAlonzo.Code.Data.Rational.Unnormalised.Base.d_numerator_14
                                            (coe v2))
                                         (coe
                                            MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                            (coe v0)))
                                      (coe
                                         MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                         (coe v1)))
                                   (coe
                                      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8804'_308
                                      (coe
                                         MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8804''45'go_138
                                         (coe
                                            MAlonzo.Code.Data.Integer.Properties.d_'8804''45'isPreorder_2822)
                                         (\ v11 v12 v13 v14 v15 ->
                                            coe
                                              MAlonzo.Code.Data.Integer.Properties.du_'8804''45''60''45'trans_2980
                                              v14 v15))
                                      (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                         (coe
                                            MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                            (coe
                                               MAlonzo.Code.Data.Rational.Unnormalised.Base.d_numerator_14
                                               (coe v0))
                                            (coe
                                               MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                               (coe v1)))
                                         (coe
                                            MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                            (coe v2)))
                                      (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                         (coe
                                            MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                            (coe
                                               MAlonzo.Code.Data.Rational.Unnormalised.Base.d_numerator_14
                                               (coe v1))
                                            (coe
                                               MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                               (coe v0)))
                                         (coe
                                            MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                            (coe v2)))
                                      (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                         (coe
                                            MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                            (coe
                                               MAlonzo.Code.Data.Rational.Unnormalised.Base.d_numerator_14
                                               (coe v2))
                                            (coe
                                               MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                               (coe v0)))
                                         (coe
                                            MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                            (coe v1)))
                                      (coe
                                         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_436
                                         (\ v11 v12 v13 v14 v15 -> v15)
                                         (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                            (coe
                                               MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                               (coe
                                                  MAlonzo.Code.Data.Rational.Unnormalised.Base.d_numerator_14
                                                  (coe v1))
                                               (coe
                                                  MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                                  (coe v0)))
                                            (coe
                                               MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                               (coe v2)))
                                         (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                            (coe
                                               MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                               (coe
                                                  MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                                  (coe v0))
                                               (coe
                                                  MAlonzo.Code.Data.Rational.Unnormalised.Base.d_numerator_14
                                                  (coe v1)))
                                            (coe
                                               MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                               (coe v2)))
                                         (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                            (coe
                                               MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                               (coe
                                                  MAlonzo.Code.Data.Rational.Unnormalised.Base.d_numerator_14
                                                  (coe v2))
                                               (coe
                                                  MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                                  (coe v0)))
                                            (coe
                                               MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                               (coe v1)))
                                         (coe
                                            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_436
                                            (\ v11 v12 v13 v14 v15 -> v15)
                                            (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                               (coe
                                                  MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                  (coe
                                                     MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                                     (coe v0))
                                                  (coe
                                                     MAlonzo.Code.Data.Rational.Unnormalised.Base.d_numerator_14
                                                     (coe v1)))
                                               (coe
                                                  MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                                  (coe v2)))
                                            (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                               (coe
                                                  MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                                  (coe v0))
                                               (coe
                                                  MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                  (coe
                                                     MAlonzo.Code.Data.Rational.Unnormalised.Base.d_numerator_14
                                                     (coe v1))
                                                  (coe
                                                     MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                                     (coe v2))))
                                            (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                               (coe
                                                  MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                  (coe
                                                     MAlonzo.Code.Data.Rational.Unnormalised.Base.d_numerator_14
                                                     (coe v2))
                                                  (coe
                                                     MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                                     (coe v0)))
                                               (coe
                                                  MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                                  (coe v1)))
                                            (coe
                                               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8804'_308
                                               (coe
                                                  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8804''45'go_138
                                                  (coe
                                                     MAlonzo.Code.Data.Integer.Properties.d_'8804''45'isPreorder_2822)
                                                  (\ v11 v12 v13 v14 v15 ->
                                                     coe
                                                       MAlonzo.Code.Data.Integer.Properties.du_'8804''45''60''45'trans_2980
                                                       v14 v15))
                                               (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                  (coe
                                                     MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                                     (coe v0))
                                                  (coe
                                                     MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                     (coe
                                                        MAlonzo.Code.Data.Rational.Unnormalised.Base.d_numerator_14
                                                        (coe v1))
                                                     (coe
                                                        MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                                        (coe v2))))
                                               (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                  (coe
                                                     MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                                     (coe v0))
                                                  (coe
                                                     MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                     (coe
                                                        MAlonzo.Code.Data.Rational.Unnormalised.Base.d_numerator_14
                                                        (coe v2))
                                                     (coe
                                                        MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                                        (coe v1))))
                                               (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                  (coe
                                                     MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                     (coe
                                                        MAlonzo.Code.Data.Rational.Unnormalised.Base.d_numerator_14
                                                        (coe v2))
                                                     (coe
                                                        MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                                        (coe v0)))
                                                  (coe
                                                     MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                                     (coe v1)))
                                               (coe
                                                  MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10216'_448
                                                  (\ v11 v12 v13 v14 v15 -> v15)
                                                  (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                     (coe
                                                        MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                                        (coe v0))
                                                     (coe
                                                        MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                        (coe
                                                           MAlonzo.Code.Data.Rational.Unnormalised.Base.d_numerator_14
                                                           (coe v2))
                                                        (coe
                                                           MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                                           (coe v1))))
                                                  (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                     (coe
                                                        MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                        (coe
                                                           MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                                           (coe v0))
                                                        (coe
                                                           MAlonzo.Code.Data.Rational.Unnormalised.Base.d_numerator_14
                                                           (coe v2)))
                                                     (coe
                                                        MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                                        (coe v1)))
                                                  (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                     (coe
                                                        MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                        (coe
                                                           MAlonzo.Code.Data.Rational.Unnormalised.Base.d_numerator_14
                                                           (coe v2))
                                                        (coe
                                                           MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                                           (coe v0)))
                                                     (coe
                                                        MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                                        (coe v1)))
                                                  (coe
                                                     MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_436
                                                     (\ v11 v12 v13 v14 v15 -> v15)
                                                     (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                        (coe
                                                           MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                           (coe
                                                              MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                                              (coe v0))
                                                           (coe
                                                              MAlonzo.Code.Data.Rational.Unnormalised.Base.d_numerator_14
                                                              (coe v2)))
                                                        (coe
                                                           MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                                           (coe v1)))
                                                     (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                        (coe
                                                           MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                           (coe
                                                              MAlonzo.Code.Data.Rational.Unnormalised.Base.d_numerator_14
                                                              (coe v2))
                                                           (coe
                                                              MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                                              (coe v0)))
                                                        (coe
                                                           MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                                           (coe v1)))
                                                     (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                        (coe
                                                           MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                           (coe
                                                              MAlonzo.Code.Data.Rational.Unnormalised.Base.d_numerator_14
                                                              (coe v2))
                                                           (coe
                                                              MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                                              (coe v0)))
                                                        (coe
                                                           MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                                           (coe v1)))
                                                     (coe
                                                        MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                                                        (coe
                                                           MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_stop_166
                                                           (coe
                                                              MAlonzo.Code.Data.Integer.Properties.d_'8804''45'isPreorder_2822))
                                                        (coe
                                                           MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                           (coe
                                                              MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                              (coe
                                                                 MAlonzo.Code.Data.Rational.Unnormalised.Base.d_numerator_14
                                                                 (coe v2))
                                                              (coe
                                                                 MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                                                 (coe v0)))
                                                           (coe
                                                              MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                                              (coe v1))))
                                                     erased)
                                                  erased)
                                               (coe
                                                  MAlonzo.Code.Data.Integer.Properties.du_'42''45'mono'737''45''8804''45'nonNeg_6076
                                                  (MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                                     (coe v0))
                                                  (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                     (coe
                                                        MAlonzo.Code.Data.Rational.Unnormalised.Base.d_numerator_14
                                                        (coe v1))
                                                     (coe
                                                        MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                                        (coe v2)))
                                                  (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                     (coe
                                                        MAlonzo.Code.Data.Rational.Unnormalised.Base.d_numerator_14
                                                        (coe v2))
                                                     (coe
                                                        MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                                        (coe v1)))
                                                  v10))
                                            erased)
                                         erased)
                                      (coe
                                         MAlonzo.Code.Data.Integer.Properties.du_'42''45'mono'691''45''8804''45'nonNeg_6034
                                         (coe
                                            MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                            (coe v2))
                                         (coe
                                            MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                            (coe
                                               MAlonzo.Code.Data.Rational.Unnormalised.Base.d_numerator_14
                                               (coe v0))
                                            (coe
                                               MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                               (coe v1)))
                                         (coe
                                            MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                            (coe
                                               MAlonzo.Code.Data.Rational.Unnormalised.Base.d_numerator_14
                                               (coe v1))
                                            (coe
                                               MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                               (coe v0)))
                                         (coe v7)))
                                   erased)
                                erased)
                             erased)))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Rational.Unnormalised.Properties.≤-antisym
d_'8804''45'antisym_474 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8804'__38 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8804'__38 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8771'__24
d_'8804''45'antisym_474 ~v0 ~v1 v2 v3
  = du_'8804''45'antisym_474 v2 v3
du_'8804''45'antisym_474 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8804'__38 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8804'__38 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8771'__24
du_'8804''45'antisym_474 v0 v1
  = coe
      seq (coe v0)
      (coe
         seq (coe v1)
         (coe
            MAlonzo.Code.Data.Rational.Unnormalised.Base.C_'42''8801''42'_30))
-- Data.Rational.Unnormalised.Properties.≤-total
d_'8804''45'total_480 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_'8804''45'total_480 v0 v1
  = coe
      MAlonzo.Code.Data.Sum.Base.du_'91'_'44'_'93''8242'_66
      (\ v2 ->
         coe
           MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
           (coe
              MAlonzo.Code.Data.Rational.Unnormalised.Base.C_'42''8804''42'_44
              v2))
      (\ v2 ->
         coe
           MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
           (coe
              MAlonzo.Code.Data.Rational.Unnormalised.Base.C_'42''8804''42'_44
              v2))
      (MAlonzo.Code.Data.Integer.Properties.d_'8804''45'total_2776
         (coe
            MAlonzo.Code.Data.Integer.Base.d__'42'__308
            (coe
               MAlonzo.Code.Data.Rational.Unnormalised.Base.d_numerator_14
               (coe v0))
            (coe
               MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
               (coe v1)))
         (coe
            MAlonzo.Code.Data.Integer.Base.d__'42'__308
            (coe
               MAlonzo.Code.Data.Rational.Unnormalised.Base.d_numerator_14
               (coe v1))
            (coe
               MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
               (coe v0))))
-- Data.Rational.Unnormalised.Properties.≤-respˡ-≃
d_'8804''45'resp'737''45''8771'_486 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8771'__24 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8804'__38 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8804'__38
d_'8804''45'resp'737''45''8771'_486 v0 v1 v2 v3
  = coe
      d_'8804''45'trans_440 (coe v2) (coe v1) (coe v0)
      (coe
         d_'8804''45'reflexive_432 (coe v2) (coe v1)
         (coe du_'8771''45'sym_170 (coe v3)))
-- Data.Rational.Unnormalised.Properties.≤-respʳ-≃
d_'8804''45'resp'691''45''8771'_490 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8771'__24 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8804'__38 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8804'__38
d_'8804''45'resp'691''45''8771'_490 v0 v1 v2 v3 v4
  = coe
      d_'8804''45'trans_440 (coe v0) (coe v1) (coe v2) (coe v4)
      (coe d_'8804''45'reflexive_432 (coe v1) (coe v2) (coe v3))
-- Data.Rational.Unnormalised.Properties.≤-resp₂-≃
d_'8804''45'resp'8322''45''8771'_496 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8804''45'resp'8322''45''8771'_496
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe d_'8804''45'resp'691''45''8771'_490)
      (coe d_'8804''45'resp'737''45''8771'_486)
-- Data.Rational.Unnormalised.Properties._≤?_
d__'8804''63'__498 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8804''63'__498 v0 v1
  = coe
      MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
      (coe
         MAlonzo.Code.Data.Rational.Unnormalised.Base.C_'42''8804''42'_44)
      (coe du_drop'45''42''8804''42'_428)
      (coe
         MAlonzo.Code.Data.Integer.Properties.d__'8804''63'__2794
         (coe
            MAlonzo.Code.Data.Integer.Base.d__'42'__308
            (coe
               MAlonzo.Code.Data.Rational.Unnormalised.Base.d_numerator_14
               (coe v0))
            (coe
               MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
               (coe v1)))
         (coe
            MAlonzo.Code.Data.Integer.Base.d__'42'__308
            (coe
               MAlonzo.Code.Data.Rational.Unnormalised.Base.d_numerator_14
               (coe v1))
            (coe
               MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
               (coe v0))))
-- Data.Rational.Unnormalised.Properties._≥?_
d__'8805''63'__504 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8805''63'__504 v0 v1 = coe d__'8804''63'__498 (coe v1) (coe v0)
-- Data.Rational.Unnormalised.Properties.≤-irrelevant
d_'8804''45'irrelevant_506 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8804'__38 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8804'__38 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8804''45'irrelevant_506 = erased
-- Data.Rational.Unnormalised.Properties.≤-isPreorder
d_'8804''45'isPreorder_512 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsPreorder_70
d_'8804''45'isPreorder_512
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_IsPreorder'46'constructor_4003
      (coe d_'8771''45'isEquivalence_260) (coe d_'8804''45'reflexive_432)
      (coe d_'8804''45'trans_440)
-- Data.Rational.Unnormalised.Properties.≤-isTotalPreorder
d_'8804''45'isTotalPreorder_514 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsTotalPreorder_124
d_'8804''45'isTotalPreorder_514
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_IsTotalPreorder'46'constructor_8325
      (coe d_'8804''45'isPreorder_512) (coe d_'8804''45'total_480)
-- Data.Rational.Unnormalised.Properties.≤-isPartialOrder
d_'8804''45'isPartialOrder_516 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsPartialOrder_236
d_'8804''45'isPartialOrder_516
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_IsPartialOrder'46'constructor_11935
      (coe d_'8804''45'isPreorder_512)
      (\ v0 v1 v2 v3 -> coe du_'8804''45'antisym_474 v2 v3)
-- Data.Rational.Unnormalised.Properties.≤-isTotalOrder
d_'8804''45'isTotalOrder_518 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsTotalOrder_468
d_'8804''45'isTotalOrder_518
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_IsTotalOrder'46'constructor_22821
      (coe d_'8804''45'isPartialOrder_516) (coe d_'8804''45'total_480)
-- Data.Rational.Unnormalised.Properties.≤-isDecTotalOrder
d_'8804''45'isDecTotalOrder_520 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecTotalOrder_524
d_'8804''45'isDecTotalOrder_520
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_IsDecTotalOrder'46'constructor_24961
      (coe d_'8804''45'isTotalOrder_518) (coe d__'8771''63'__194)
      (coe d__'8804''63'__498)
-- Data.Rational.Unnormalised.Properties.≤-preorder
d_'8804''45'preorder_522 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Preorder_136
d_'8804''45'preorder_522
  = coe
      MAlonzo.Code.Relation.Binary.Bundles.C_Preorder'46'constructor_2331
      d_'8804''45'isPreorder_512
-- Data.Rational.Unnormalised.Properties.≤-totalPreorder
d_'8804''45'totalPreorder_524 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_232
d_'8804''45'totalPreorder_524
  = coe
      MAlonzo.Code.Relation.Binary.Bundles.C_TotalPreorder'46'constructor_4405
      d_'8804''45'isTotalPreorder_514
-- Data.Rational.Unnormalised.Properties.≤-poset
d_'8804''45'poset_526 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Poset_480
d_'8804''45'poset_526
  = coe
      MAlonzo.Code.Relation.Binary.Bundles.C_Poset'46'constructor_9149
      d_'8804''45'isPartialOrder_516
-- Data.Rational.Unnormalised.Properties.≤-totalOrder
d_'8804''45'totalOrder_528 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalOrder_966
d_'8804''45'totalOrder_528
  = coe
      MAlonzo.Code.Relation.Binary.Bundles.C_TotalOrder'46'constructor_18801
      d_'8804''45'isTotalOrder_518
-- Data.Rational.Unnormalised.Properties.≤-decTotalOrder
d_'8804''45'decTotalOrder_530 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_DecTotalOrder_1076
d_'8804''45'decTotalOrder_530
  = coe
      MAlonzo.Code.Relation.Binary.Bundles.C_DecTotalOrder'46'constructor_21007
      d_'8804''45'isDecTotalOrder_520
-- Data.Rational.Unnormalised.Properties.≤-isPreorder-≡
d_'8804''45'isPreorder'45''8801'_532 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsPreorder_70
d_'8804''45'isPreorder'45''8801'_532
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_IsPreorder'46'constructor_4003
      (coe
         MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties.du_isEquivalence_396)
      (\ v0 v1 v2 -> coe du_'8804''45'reflexive'45''8801'_438 v0)
      (coe d_'8804''45'trans_440)
-- Data.Rational.Unnormalised.Properties.≤-isTotalPreorder-≡
d_'8804''45'isTotalPreorder'45''8801'_534 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsTotalPreorder_124
d_'8804''45'isTotalPreorder'45''8801'_534
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_IsTotalPreorder'46'constructor_8325
      (coe d_'8804''45'isPreorder'45''8801'_532)
      (coe d_'8804''45'total_480)
-- Data.Rational.Unnormalised.Properties.≤-preorder-≡
d_'8804''45'preorder'45''8801'_536 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_Preorder_136
d_'8804''45'preorder'45''8801'_536
  = coe
      MAlonzo.Code.Relation.Binary.Bundles.C_Preorder'46'constructor_2331
      d_'8804''45'isPreorder'45''8801'_532
-- Data.Rational.Unnormalised.Properties.≤-totalPreorder-≡
d_'8804''45'totalPreorder'45''8801'_538 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_TotalPreorder_232
d_'8804''45'totalPreorder'45''8801'_538
  = coe
      MAlonzo.Code.Relation.Binary.Bundles.C_TotalPreorder'46'constructor_4405
      d_'8804''45'isTotalPreorder'45''8801'_534
-- Data.Rational.Unnormalised.Properties.mono⇒cong
d_mono'8658'cong_542 ::
  (MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
   MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8) ->
  (MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
   MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
   MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8804'__38 ->
   MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8804'__38) ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8771'__24 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8771'__24
d_mono'8658'cong_542 v0
  = coe
      MAlonzo.Code.Relation.Binary.Consequences.du_mono'8658'cong_278
      (\ v1 v2 v3 -> coe du_'8771''45'sym_170 v3)
      (coe d_'8804''45'reflexive_432)
      (\ v1 v2 v3 v4 -> coe du_'8804''45'antisym_474 v3 v4) (coe v0)
-- Data.Rational.Unnormalised.Properties.antimono⇒cong
d_antimono'8658'cong_546 ::
  (MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
   MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8) ->
  (MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
   MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
   MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8804'__38 ->
   MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8804'__38) ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8771'__24 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8771'__24
d_antimono'8658'cong_546 v0
  = coe
      MAlonzo.Code.Relation.Binary.Consequences.du_antimono'8658'cong_292
      (\ v1 v2 v3 -> coe du_'8771''45'sym_170 v3)
      (coe d_'8804''45'reflexive_432)
      (\ v1 v2 v3 v4 -> coe du_'8804''45'antisym_474 v3 v4) (coe v0)
-- Data.Rational.Unnormalised.Properties.≤ᵇ⇒≤
d_'8804''7495''8658''8804'_548 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  AgdaAny ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8804'__38
d_'8804''7495''8658''8804'_548 v0 v1 ~v2
  = du_'8804''7495''8658''8804'_548 v0 v1
du_'8804''7495''8658''8804'_548 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8804'__38
du_'8804''7495''8658''8804'_548 v0 v1
  = coe
      MAlonzo.Code.Data.Rational.Unnormalised.Base.C_'42''8804''42'_44
      (coe
         MAlonzo.Code.Data.Integer.Properties.du_'8804''7495''8658''8804'_2842
         (coe
            MAlonzo.Code.Data.Integer.Base.d__'9667'__230
            (coe
               MAlonzo.Code.Data.Sign.Base.d__'42'__14
               (coe
                  MAlonzo.Code.Data.Integer.Base.d_sign_24
                  (coe
                     MAlonzo.Code.Data.Rational.Unnormalised.Base.d_numerator_14
                     (coe v0)))
               (coe
                  MAlonzo.Code.Data.Integer.Base.d_sign_24
                  (coe
                     MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                     (coe v1))))
            (coe
               mulInt
               (coe
                  MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18
                  (coe
                     MAlonzo.Code.Data.Rational.Unnormalised.Base.d_numerator_14
                     (coe v0)))
               (coe
                  MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18
                  (coe
                     MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                     (coe v1)))))
         (coe
            MAlonzo.Code.Data.Integer.Base.d__'9667'__230
            (coe
               MAlonzo.Code.Data.Sign.Base.d__'42'__14
               (coe
                  MAlonzo.Code.Data.Integer.Base.d_sign_24
                  (coe
                     MAlonzo.Code.Data.Rational.Unnormalised.Base.d_numerator_14
                     (coe v1)))
               (coe
                  MAlonzo.Code.Data.Integer.Base.d_sign_24
                  (coe
                     MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                     (coe v0))))
            (coe
               mulInt
               (coe
                  MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18
                  (coe
                     MAlonzo.Code.Data.Rational.Unnormalised.Base.d_numerator_14
                     (coe v1)))
               (coe
                  MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18
                  (coe
                     MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                     (coe v0))))))
-- Data.Rational.Unnormalised.Properties.≤⇒≤ᵇ
d_'8804''8658''8804''7495'_550 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8804'__38 ->
  AgdaAny
d_'8804''8658''8804''7495'_550 ~v0 ~v1 v2
  = du_'8804''8658''8804''7495'_550 v2
du_'8804''8658''8804''7495'_550 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8804'__38 ->
  AgdaAny
du_'8804''8658''8804''7495'_550 v0
  = coe
      MAlonzo.Code.Data.Integer.Properties.du_'8804''8658''8804''7495'_2850
      (coe du_drop'45''42''8804''42'_428 (coe v0))
-- Data.Rational.Unnormalised.Properties.drop-*<*
d_drop'45''42''60''42'_552 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'60'__46 ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50
d_drop'45''42''60''42'_552 ~v0 ~v1 v2
  = du_drop'45''42''60''42'_552 v2
du_drop'45''42''60''42'_552 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'60'__46 ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50
du_drop'45''42''60''42'_552 v0
  = case coe v0 of
      MAlonzo.Code.Data.Rational.Unnormalised.Base.C_'42''60''42'_52 v3
        -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Rational.Unnormalised.Properties.<⇒≤
d_'60''8658''8804'_556 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'60'__46 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8804'__38
d_'60''8658''8804'_556 ~v0 ~v1 v2 = du_'60''8658''8804'_556 v2
du_'60''8658''8804'_556 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'60'__46 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8804'__38
du_'60''8658''8804'_556 v0
  = case coe v0 of
      MAlonzo.Code.Data.Rational.Unnormalised.Base.C_'42''60''42'_52 v3
        -> coe
             MAlonzo.Code.Data.Rational.Unnormalised.Base.C_'42''8804''42'_44
             (coe
                MAlonzo.Code.Data.Integer.Properties.du_'60''8658''8804'_2868
                (coe v3))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Rational.Unnormalised.Properties.<⇒≢
d_'60''8658''8802'_560 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'60'__46 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'60''8658''8802'_560 = erased
-- Data.Rational.Unnormalised.Properties.<⇒≱
d_'60''8658''8817'_564 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'60'__46 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8804'__38 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'60''8658''8817'_564 = erased
-- Data.Rational.Unnormalised.Properties.≰⇒>
d_'8816''8658''62'_568 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  (MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8804'__38 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'60'__46
d_'8816''8658''62'_568 v0 v1 ~v2 = du_'8816''8658''62'_568 v0 v1
du_'8816''8658''62'_568 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'60'__46
du_'8816''8658''62'_568 v0 v1
  = coe
      MAlonzo.Code.Data.Rational.Unnormalised.Base.C_'42''60''42'_52
      (coe
         MAlonzo.Code.Data.Integer.Properties.du_'8816''8658''62'_2896
         (coe
            MAlonzo.Code.Data.Integer.Base.d__'42'__308
            (coe
               MAlonzo.Code.Data.Rational.Unnormalised.Base.d_numerator_14
               (coe v0))
            (coe
               MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
               (coe v1)))
         (coe
            MAlonzo.Code.Data.Integer.Base.d__'42'__308
            (coe
               MAlonzo.Code.Data.Rational.Unnormalised.Base.d_numerator_14
               (coe v1))
            (coe
               MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
               (coe v0))))
-- Data.Rational.Unnormalised.Properties.≮⇒≥
d_'8814''8658''8805'_572 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  (MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'60'__46 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8804'__38
d_'8814''8658''8805'_572 v0 v1 ~v2
  = du_'8814''8658''8805'_572 v0 v1
du_'8814''8658''8805'_572 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8804'__38
du_'8814''8658''8805'_572 v0 v1
  = coe
      MAlonzo.Code.Data.Rational.Unnormalised.Base.C_'42''8804''42'_44
      (coe
         MAlonzo.Code.Data.Integer.Properties.du_'8814''8658''8805'_2922
         (coe
            MAlonzo.Code.Data.Integer.Base.d__'42'__308
            (coe
               MAlonzo.Code.Data.Rational.Unnormalised.Base.d_numerator_14
               (coe v0))
            (coe
               MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
               (coe v1)))
         (coe
            MAlonzo.Code.Data.Integer.Base.d__'42'__308
            (coe
               MAlonzo.Code.Data.Rational.Unnormalised.Base.d_numerator_14
               (coe v1))
            (coe
               MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
               (coe v0))))
-- Data.Rational.Unnormalised.Properties.≰⇒≥
d_'8816''8658''8805'_576 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  (MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8804'__38 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8804'__38
d_'8816''8658''8805'_576 v0 v1 ~v2
  = du_'8816''8658''8805'_576 v0 v1
du_'8816''8658''8805'_576 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8804'__38
du_'8816''8658''8805'_576 v0 v1
  = coe
      du_'60''8658''8804'_556
      (coe du_'8816''8658''62'_568 (coe v0) (coe v1))
-- Data.Rational.Unnormalised.Properties.<-irrefl-≡
d_'60''45'irrefl'45''8801'_578 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'60'__46 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'60''45'irrefl'45''8801'_578 = erased
-- Data.Rational.Unnormalised.Properties.<-irrefl
d_'60''45'irrefl_582 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8771'__24 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'60'__46 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'60''45'irrefl_582 = erased
-- Data.Rational.Unnormalised.Properties.<-asym
d_'60''45'asym_588 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'60'__46 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'60'__46 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'60''45'asym_588 = erased
-- Data.Rational.Unnormalised.Properties.<-dense
d_'60''45'dense_592 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'60'__46 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'60''45'dense_592 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Data.Rational.Unnormalised.Base.C_'42''60''42'_52 v5
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe du_m_604 (coe v0) (coe v1))
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                (coe d_p'60'm_606 (coe v0) (coe v1) (coe v5))
                (coe d_m'60'q_608 (coe v0) (coe v1) (coe v5)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Rational.Unnormalised.Properties._.m
d_m_604 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8
d_m_604 v0 v1 ~v2 = du_m_604 v0 v1
du_m_604 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8
du_m_604 v0 v1
  = coe
      MAlonzo.Code.Data.Rational.Unnormalised.Base.C_mkℚ'7512'_22
      (coe
         MAlonzo.Code.Data.Integer.Base.d__'43'__276
         (coe
            MAlonzo.Code.Data.Rational.Unnormalised.Base.d_numerator_14
            (coe v0))
         (coe
            MAlonzo.Code.Data.Rational.Unnormalised.Base.d_numerator_14
            (coe v1)))
      (coe
         MAlonzo.Code.Data.Nat.Base.d_pred_192
         (coe
            addInt
            (coe
               MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominatorℕ_18
               (coe v0))
            (coe
               MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominatorℕ_18
               (coe v1))))
-- Data.Rational.Unnormalised.Properties._.p<m
d_p'60'm_606 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'60'__46
d_p'60'm_606 v0 v1 v2
  = coe
      MAlonzo.Code.Data.Rational.Unnormalised.Base.C_'42''60''42'_52
      (let v3
             = coe
                 MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_strictRelation_202 in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__126
            (coe v3)
            (coe
               MAlonzo.Code.Data.Integer.Base.d__'42'__308
               (coe
                  MAlonzo.Code.Data.Rational.Unnormalised.Base.d_numerator_14
                  (coe v0))
               (coe
                  MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                  (coe du_m_604 (coe v0) (coe v1))))
            (coe
               MAlonzo.Code.Data.Integer.Base.d__'42'__308
               (coe
                  MAlonzo.Code.Data.Rational.Unnormalised.Base.d_numerator_14
                  (coe du_m_604 (coe v0) (coe v1)))
               (coe
                  MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                  (coe v0)))
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_436
               (\ v4 v5 v6 v7 v8 -> v8)
               (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                  (coe
                     MAlonzo.Code.Data.Rational.Unnormalised.Base.d_numerator_14
                     (coe v0))
                  (coe
                     MAlonzo.Code.Data.Integer.Base.d__'43'__276
                     (coe
                        MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                        (coe v0))
                     (coe
                        MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                        (coe v1))))
               (MAlonzo.Code.Data.Integer.Base.d__'43'__276
                  (coe
                     MAlonzo.Code.Data.Integer.Base.d__'42'__308
                     (coe
                        MAlonzo.Code.Data.Rational.Unnormalised.Base.d_numerator_14
                        (coe v0))
                     (coe
                        MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                        (coe v0)))
                  (coe
                     MAlonzo.Code.Data.Integer.Base.d__'42'__308
                     (coe
                        MAlonzo.Code.Data.Rational.Unnormalised.Base.d_numerator_14
                        (coe v0))
                     (coe
                        MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                        (coe v1))))
               (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                  (coe
                     MAlonzo.Code.Data.Rational.Unnormalised.Base.d_numerator_14
                     (coe du_m_604 (coe v0) (coe v1)))
                  (coe
                     MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                     (coe v0)))
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''60'_312
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'60''45'go_152
                     (\ v4 v5 v6 v7 v8 ->
                        coe
                          MAlonzo.Code.Data.Integer.Properties.du_'60''45'trans_3008 v7 v8)
                     (coe
                        MAlonzo.Code.Relation.Binary.PropositionalEquality.Core.du_resp'8322'_160)
                     (\ v4 v5 v6 v7 v8 ->
                        coe
                          MAlonzo.Code.Data.Integer.Properties.du_'60''45''8804''45'trans_2994
                          v7 v8))
                  (MAlonzo.Code.Data.Integer.Base.d__'43'__276
                     (coe
                        MAlonzo.Code.Data.Integer.Base.d__'42'__308
                        (coe
                           MAlonzo.Code.Data.Rational.Unnormalised.Base.d_numerator_14
                           (coe v0))
                        (coe
                           MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                           (coe v0)))
                     (coe
                        MAlonzo.Code.Data.Integer.Base.d__'42'__308
                        (coe
                           MAlonzo.Code.Data.Rational.Unnormalised.Base.d_numerator_14
                           (coe v0))
                        (coe
                           MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                           (coe v1))))
                  (MAlonzo.Code.Data.Integer.Base.d__'43'__276
                     (coe
                        MAlonzo.Code.Data.Integer.Base.d__'42'__308
                        (coe
                           MAlonzo.Code.Data.Rational.Unnormalised.Base.d_numerator_14
                           (coe v0))
                        (coe
                           MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                           (coe v0)))
                     (coe
                        MAlonzo.Code.Data.Integer.Base.d__'42'__308
                        (coe
                           MAlonzo.Code.Data.Rational.Unnormalised.Base.d_numerator_14
                           (coe v1))
                        (coe
                           MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                           (coe v0))))
                  (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                     (coe
                        MAlonzo.Code.Data.Rational.Unnormalised.Base.d_numerator_14
                        (coe du_m_604 (coe v0) (coe v1)))
                     (coe
                        MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                        (coe v0)))
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10216'_448
                     (\ v4 v5 v6 v7 v8 -> v8)
                     (MAlonzo.Code.Data.Integer.Base.d__'43'__276
                        (coe
                           MAlonzo.Code.Data.Integer.Base.d__'42'__308
                           (coe
                              MAlonzo.Code.Data.Rational.Unnormalised.Base.d_numerator_14
                              (coe v0))
                           (coe
                              MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                              (coe v0)))
                        (coe
                           MAlonzo.Code.Data.Integer.Base.d__'42'__308
                           (coe
                              MAlonzo.Code.Data.Rational.Unnormalised.Base.d_numerator_14
                              (coe v1))
                           (coe
                              MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                              (coe v0))))
                     (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                        (coe
                           MAlonzo.Code.Data.Integer.Base.d__'43'__276
                           (coe
                              MAlonzo.Code.Data.Rational.Unnormalised.Base.d_numerator_14
                              (coe v0))
                           (coe
                              MAlonzo.Code.Data.Rational.Unnormalised.Base.d_numerator_14
                              (coe v1)))
                        (coe
                           MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                           (coe v0)))
                     (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                        (coe
                           MAlonzo.Code.Data.Rational.Unnormalised.Base.d_numerator_14
                           (coe du_m_604 (coe v0) (coe v1)))
                        (coe
                           MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                           (coe v0)))
                     (coe
                        MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                        (coe
                           MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_stop_166
                           (coe
                              MAlonzo.Code.Data.Integer.Properties.d_'8804''45'isPreorder_2822))
                        (coe
                           MAlonzo.Code.Data.Integer.Base.d__'42'__308
                           (coe
                              MAlonzo.Code.Data.Rational.Unnormalised.Base.d_numerator_14
                              (coe du_m_604 (coe v0) (coe v1)))
                           (coe
                              MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                              (coe v0))))
                     erased)
                  (MAlonzo.Code.Data.Integer.Properties.d_'43''45'mono'691''45''60'_4604
                     (coe
                        MAlonzo.Code.Data.Integer.Base.d__'42'__308
                        (coe
                           MAlonzo.Code.Data.Rational.Unnormalised.Base.d_numerator_14
                           (coe v0))
                        (coe
                           MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                           (coe v0)))
                     (coe
                        MAlonzo.Code.Data.Integer.Base.d__'42'__308
                        (coe
                           MAlonzo.Code.Data.Rational.Unnormalised.Base.d_numerator_14
                           (coe v0))
                        (coe
                           MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                           (coe v1)))
                     (coe
                        MAlonzo.Code.Data.Integer.Base.d__'42'__308
                        (coe
                           MAlonzo.Code.Data.Rational.Unnormalised.Base.d_numerator_14
                           (coe v1))
                        (coe
                           MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                           (coe v0)))
                     (coe v2)))
               erased)))
-- Data.Rational.Unnormalised.Properties._.m<q
d_m'60'q_608 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'60'__46
d_m'60'q_608 v0 v1 v2
  = coe
      MAlonzo.Code.Data.Rational.Unnormalised.Base.C_'42''60''42'_52
      (let v3
             = coe
                 MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_strictRelation_202 in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__126
            (coe v3)
            (coe
               MAlonzo.Code.Data.Integer.Base.d__'42'__308
               (coe
                  MAlonzo.Code.Data.Rational.Unnormalised.Base.d_numerator_14
                  (coe du_m_604 (coe v0) (coe v1)))
               (coe
                  MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                  (coe v1)))
            (coe
               MAlonzo.Code.Data.Integer.Base.d__'42'__308
               (coe
                  MAlonzo.Code.Data.Rational.Unnormalised.Base.d_numerator_14
                  (coe v1))
               (coe
                  MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                  (coe du_m_604 (coe v0) (coe v1))))
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_436
               (\ v4 v5 v6 v7 v8 -> v8)
               (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                  (coe
                     MAlonzo.Code.Data.Rational.Unnormalised.Base.d_numerator_14
                     (coe du_m_604 (coe v0) (coe v1)))
                  (coe
                     MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                     (coe v1)))
               (MAlonzo.Code.Data.Integer.Base.d__'43'__276
                  (coe
                     MAlonzo.Code.Data.Integer.Base.d__'42'__308
                     (coe
                        MAlonzo.Code.Data.Rational.Unnormalised.Base.d_numerator_14
                        (coe v0))
                     (coe
                        MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                        (coe v1)))
                  (coe
                     MAlonzo.Code.Data.Integer.Base.d__'42'__308
                     (coe
                        MAlonzo.Code.Data.Rational.Unnormalised.Base.d_numerator_14
                        (coe v1))
                     (coe
                        MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                        (coe v1))))
               (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                  (coe
                     MAlonzo.Code.Data.Rational.Unnormalised.Base.d_numerator_14
                     (coe v1))
                  (coe
                     MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                     (coe du_m_604 (coe v0) (coe v1))))
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''60'_312
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'60''45'go_152
                     (\ v4 v5 v6 v7 v8 ->
                        coe
                          MAlonzo.Code.Data.Integer.Properties.du_'60''45'trans_3008 v7 v8)
                     (coe
                        MAlonzo.Code.Relation.Binary.PropositionalEquality.Core.du_resp'8322'_160)
                     (\ v4 v5 v6 v7 v8 ->
                        coe
                          MAlonzo.Code.Data.Integer.Properties.du_'60''45''8804''45'trans_2994
                          v7 v8))
                  (MAlonzo.Code.Data.Integer.Base.d__'43'__276
                     (coe
                        MAlonzo.Code.Data.Integer.Base.d__'42'__308
                        (coe
                           MAlonzo.Code.Data.Rational.Unnormalised.Base.d_numerator_14
                           (coe v0))
                        (coe
                           MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                           (coe v1)))
                     (coe
                        MAlonzo.Code.Data.Integer.Base.d__'42'__308
                        (coe
                           MAlonzo.Code.Data.Rational.Unnormalised.Base.d_numerator_14
                           (coe v1))
                        (coe
                           MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                           (coe v1))))
                  (MAlonzo.Code.Data.Integer.Base.d__'43'__276
                     (coe
                        MAlonzo.Code.Data.Integer.Base.d__'42'__308
                        (coe
                           MAlonzo.Code.Data.Rational.Unnormalised.Base.d_numerator_14
                           (coe v1))
                        (coe
                           MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                           (coe v0)))
                     (coe
                        MAlonzo.Code.Data.Integer.Base.d__'42'__308
                        (coe
                           MAlonzo.Code.Data.Rational.Unnormalised.Base.d_numerator_14
                           (coe v1))
                        (coe
                           MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                           (coe v1))))
                  (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                     (coe
                        MAlonzo.Code.Data.Rational.Unnormalised.Base.d_numerator_14
                        (coe v1))
                     (coe
                        MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                        (coe du_m_604 (coe v0) (coe v1))))
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10216'_448
                     (\ v4 v5 v6 v7 v8 -> v8)
                     (MAlonzo.Code.Data.Integer.Base.d__'43'__276
                        (coe
                           MAlonzo.Code.Data.Integer.Base.d__'42'__308
                           (coe
                              MAlonzo.Code.Data.Rational.Unnormalised.Base.d_numerator_14
                              (coe v1))
                           (coe
                              MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                              (coe v0)))
                        (coe
                           MAlonzo.Code.Data.Integer.Base.d__'42'__308
                           (coe
                              MAlonzo.Code.Data.Rational.Unnormalised.Base.d_numerator_14
                              (coe v1))
                           (coe
                              MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                              (coe v1))))
                     (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                        (coe
                           MAlonzo.Code.Data.Rational.Unnormalised.Base.d_numerator_14
                           (coe v1))
                        (coe
                           MAlonzo.Code.Data.Integer.Base.d__'43'__276
                           (coe
                              MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                              (coe v0))
                           (coe
                              MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                              (coe v1))))
                     (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                        (coe
                           MAlonzo.Code.Data.Rational.Unnormalised.Base.d_numerator_14
                           (coe v1))
                        (coe
                           MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                           (coe du_m_604 (coe v0) (coe v1))))
                     (coe
                        MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                        (coe
                           MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_stop_166
                           (coe
                              MAlonzo.Code.Data.Integer.Properties.d_'8804''45'isPreorder_2822))
                        (coe
                           MAlonzo.Code.Data.Integer.Base.d__'42'__308
                           (coe
                              MAlonzo.Code.Data.Rational.Unnormalised.Base.d_numerator_14
                              (coe v1))
                           (coe
                              MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                              (coe du_m_604 (coe v0) (coe v1)))))
                     erased)
                  (coe
                     MAlonzo.Code.Data.Integer.Properties.d_'43''45'mono'737''45''60'_4628
                     (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                        (coe
                           MAlonzo.Code.Data.Rational.Unnormalised.Base.d_numerator_14
                           (coe v1))
                        (coe
                           MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                           (coe v1)))
                     (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                        (coe
                           MAlonzo.Code.Data.Rational.Unnormalised.Base.d_numerator_14
                           (coe v0))
                        (coe
                           MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                           (coe v1)))
                     (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                        (coe
                           MAlonzo.Code.Data.Rational.Unnormalised.Base.d_numerator_14
                           (coe v1))
                        (coe
                           MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                           (coe v0)))
                     v2))
               erased)))
-- Data.Rational.Unnormalised.Properties.≤-<-trans
d_'8804''45''60''45'trans_610 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8804'__38 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'60'__46 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'60'__46
d_'8804''45''60''45'trans_610 v0 v1 v2 v3 v4
  = case coe v3 of
      MAlonzo.Code.Data.Rational.Unnormalised.Base.C_'42''8804''42'_44 v7
        -> case coe v4 of
             MAlonzo.Code.Data.Rational.Unnormalised.Base.C_'42''60''42'_52 v10
               -> coe
                    MAlonzo.Code.Data.Rational.Unnormalised.Base.C_'42''60''42'_52
                    (coe
                       MAlonzo.Code.Data.Integer.Properties.du_'42''45'cancel'691''45''60''45'nonNeg_6284
                       (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                          (coe
                             MAlonzo.Code.Data.Rational.Unnormalised.Base.d_numerator_14
                             (coe v0))
                          (coe
                             MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                             (coe v2)))
                       (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                          (coe
                             MAlonzo.Code.Data.Rational.Unnormalised.Base.d_numerator_14
                             (coe v2))
                          (coe
                             MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                             (coe v0)))
                       (addInt
                          (coe (1 :: Integer))
                          (coe
                             MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator'45'1_16
                             (coe v1)))
                       (let v11
                              = coe
                                  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_strictRelation_202 in
                        coe
                          (coe
                             MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__126
                             (coe v11)
                             (coe
                                MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                (coe
                                   MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                   (coe du_n'8321'_626 (coe v0)) (coe du_d'8323'_636 (coe v2)))
                                (coe du_d'8322'_634 (coe v1)))
                             (coe
                                MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                (coe
                                   MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                   (coe du_n'8323'_630 (coe v2)) (coe du_d'8321'_632 (coe v0)))
                                (coe du_d'8322'_634 (coe v1)))
                             (coe
                                MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_436
                                (\ v12 v13 v14 v15 v16 -> v16)
                                (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                   (coe
                                      MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                      (coe du_n'8321'_626 (coe v0)) (coe du_d'8323'_636 (coe v2)))
                                   (coe du_d'8322'_634 (coe v1)))
                                (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                   (coe du_n'8321'_626 (coe v0))
                                   (coe
                                      MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                      (coe du_d'8323'_636 (coe v2)) (coe du_d'8322'_634 (coe v1))))
                                (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                   (coe
                                      MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                      (coe du_n'8323'_630 (coe v2)) (coe du_d'8321'_632 (coe v0)))
                                   (coe du_d'8322'_634 (coe v1)))
                                (coe
                                   MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_436
                                   (\ v12 v13 v14 v15 v16 -> v16)
                                   (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                      (coe du_n'8321'_626 (coe v0))
                                      (coe
                                         MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                         (coe du_d'8323'_636 (coe v2))
                                         (coe du_d'8322'_634 (coe v1))))
                                   (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                      (coe du_n'8321'_626 (coe v0))
                                      (coe
                                         MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                         (coe du_d'8322'_634 (coe v1))
                                         (coe du_d'8323'_636 (coe v2))))
                                   (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                      (coe
                                         MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                         (coe du_n'8323'_630 (coe v2))
                                         (coe du_d'8321'_632 (coe v0)))
                                      (coe du_d'8322'_634 (coe v1)))
                                   (coe
                                      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10216'_448
                                      (\ v12 v13 v14 v15 v16 -> v16)
                                      (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                         (coe du_n'8321'_626 (coe v0))
                                         (coe
                                            MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                            (coe du_d'8322'_634 (coe v1))
                                            (coe du_d'8323'_636 (coe v2))))
                                      (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                         (coe
                                            MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                            (coe du_n'8321'_626 (coe v0))
                                            (coe du_d'8322'_634 (coe v1)))
                                         (coe du_d'8323'_636 (coe v2)))
                                      (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                         (coe
                                            MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                            (coe du_n'8323'_630 (coe v2))
                                            (coe du_d'8321'_632 (coe v0)))
                                         (coe du_d'8322'_634 (coe v1)))
                                      (coe
                                         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8804'_308
                                         (coe
                                            MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8804''45'go_138
                                            (coe
                                               MAlonzo.Code.Data.Integer.Properties.d_'8804''45'isPreorder_2822)
                                            (\ v12 v13 v14 v15 v16 ->
                                               coe
                                                 MAlonzo.Code.Data.Integer.Properties.du_'8804''45''60''45'trans_2980
                                                 v15 v16))
                                         (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                            (coe
                                               MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                               (coe du_n'8321'_626 (coe v0))
                                               (coe du_d'8322'_634 (coe v1)))
                                            (coe du_d'8323'_636 (coe v2)))
                                         (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                            (coe
                                               MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                               (coe du_n'8322'_628 (coe v1))
                                               (coe du_d'8321'_632 (coe v0)))
                                            (coe du_d'8323'_636 (coe v2)))
                                         (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                            (coe
                                               MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                               (coe du_n'8323'_630 (coe v2))
                                               (coe du_d'8321'_632 (coe v0)))
                                            (coe du_d'8322'_634 (coe v1)))
                                         (coe
                                            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_436
                                            (\ v12 v13 v14 v15 v16 -> v16)
                                            (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                               (coe
                                                  MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                  (coe du_n'8322'_628 (coe v1))
                                                  (coe du_d'8321'_632 (coe v0)))
                                               (coe du_d'8323'_636 (coe v2)))
                                            (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                               (coe
                                                  MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                  (coe du_d'8321'_632 (coe v0))
                                                  (coe du_n'8322'_628 (coe v1)))
                                               (coe du_d'8323'_636 (coe v2)))
                                            (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                               (coe
                                                  MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                  (coe du_n'8323'_630 (coe v2))
                                                  (coe du_d'8321'_632 (coe v0)))
                                               (coe du_d'8322'_634 (coe v1)))
                                            (coe
                                               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_436
                                               (\ v12 v13 v14 v15 v16 -> v16)
                                               (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                  (coe
                                                     MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                     (coe du_d'8321'_632 (coe v0))
                                                     (coe du_n'8322'_628 (coe v1)))
                                                  (coe du_d'8323'_636 (coe v2)))
                                               (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                  (coe du_d'8321'_632 (coe v0))
                                                  (coe
                                                     MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                     (coe du_n'8322'_628 (coe v1))
                                                     (coe du_d'8323'_636 (coe v2))))
                                               (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                  (coe
                                                     MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                     (coe du_n'8323'_630 (coe v2))
                                                     (coe du_d'8321'_632 (coe v0)))
                                                  (coe du_d'8322'_634 (coe v1)))
                                               (coe
                                                  MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''60'_312
                                                  (coe
                                                     MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'60''45'go_152
                                                     (\ v12 v13 v14 v15 v16 ->
                                                        coe
                                                          MAlonzo.Code.Data.Integer.Properties.du_'60''45'trans_3008
                                                          v15 v16)
                                                     (coe
                                                        MAlonzo.Code.Relation.Binary.PropositionalEquality.Core.du_resp'8322'_160)
                                                     (\ v12 v13 v14 v15 v16 ->
                                                        coe
                                                          MAlonzo.Code.Data.Integer.Properties.du_'60''45''8804''45'trans_2994
                                                          v15 v16))
                                                  (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                     (coe du_d'8321'_632 (coe v0))
                                                     (coe
                                                        MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                        (coe du_n'8322'_628 (coe v1))
                                                        (coe du_d'8323'_636 (coe v2))))
                                                  (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                     (coe du_d'8321'_632 (coe v0))
                                                     (coe
                                                        MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                        (coe du_n'8323'_630 (coe v2))
                                                        (coe du_d'8322'_634 (coe v1))))
                                                  (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                     (coe
                                                        MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                        (coe du_n'8323'_630 (coe v2))
                                                        (coe du_d'8321'_632 (coe v0)))
                                                     (coe du_d'8322'_634 (coe v1)))
                                                  (coe
                                                     MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10216'_448
                                                     (\ v12 v13 v14 v15 v16 -> v16)
                                                     (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                        (coe du_d'8321'_632 (coe v0))
                                                        (coe
                                                           MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                           (coe du_n'8323'_630 (coe v2))
                                                           (coe du_d'8322'_634 (coe v1))))
                                                     (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                        (coe
                                                           MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                           (coe du_d'8321'_632 (coe v0))
                                                           (coe du_n'8323'_630 (coe v2)))
                                                        (coe du_d'8322'_634 (coe v1)))
                                                     (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                        (coe
                                                           MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                           (coe du_n'8323'_630 (coe v2))
                                                           (coe du_d'8321'_632 (coe v0)))
                                                        (coe du_d'8322'_634 (coe v1)))
                                                     (coe
                                                        MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_436
                                                        (\ v12 v13 v14 v15 v16 -> v16)
                                                        (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                           (coe
                                                              MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                              (coe du_d'8321'_632 (coe v0))
                                                              (coe du_n'8323'_630 (coe v2)))
                                                           (coe du_d'8322'_634 (coe v1)))
                                                        (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                           (coe
                                                              MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                              (coe du_n'8323'_630 (coe v2))
                                                              (coe du_d'8321'_632 (coe v0)))
                                                           (coe du_d'8322'_634 (coe v1)))
                                                        (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                           (coe
                                                              MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                              (coe du_n'8323'_630 (coe v2))
                                                              (coe du_d'8321'_632 (coe v0)))
                                                           (coe du_d'8322'_634 (coe v1)))
                                                        (coe
                                                           MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                                                           (coe
                                                              MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_stop_166
                                                              (coe
                                                                 MAlonzo.Code.Data.Integer.Properties.d_'8804''45'isPreorder_2822))
                                                           (coe
                                                              MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                              (coe
                                                                 MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                                 (coe du_n'8323'_630 (coe v2))
                                                                 (coe du_d'8321'_632 (coe v0)))
                                                              (coe du_d'8322'_634 (coe v1))))
                                                        erased)
                                                     erased)
                                                  (coe
                                                     MAlonzo.Code.Data.Integer.Properties.du_'42''45'mono'737''45''60''45'pos_6194
                                                     (coe
                                                        MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                                        (coe v0))
                                                     (coe
                                                        MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                        (coe
                                                           MAlonzo.Code.Data.Rational.Unnormalised.Base.d_numerator_14
                                                           (coe v1))
                                                        (coe
                                                           MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                                           (coe v2)))
                                                     (coe
                                                        MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                        (coe
                                                           MAlonzo.Code.Data.Rational.Unnormalised.Base.d_numerator_14
                                                           (coe v2))
                                                        (coe
                                                           MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                                           (coe v1)))
                                                     (coe v10)))
                                               erased)
                                            erased)
                                         (coe
                                            MAlonzo.Code.Data.Integer.Properties.du_'42''45'mono'691''45''8804''45'nonNeg_6034
                                            (coe
                                               MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                               (coe v2))
                                            (coe
                                               MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                               (coe
                                                  MAlonzo.Code.Data.Rational.Unnormalised.Base.d_numerator_14
                                                  (coe v0))
                                               (coe
                                                  MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                                  (coe v1)))
                                            (coe
                                               MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                               (coe
                                                  MAlonzo.Code.Data.Rational.Unnormalised.Base.d_numerator_14
                                                  (coe v1))
                                               (coe
                                                  MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                                  (coe v0)))
                                            (coe v7)))
                                      erased)
                                   erased)
                                erased))))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Rational.Unnormalised.Properties._.n₁
d_n'8321'_626 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50 -> Integer
d_n'8321'_626 v0 ~v1 ~v2 ~v3 ~v4 = du_n'8321'_626 v0
du_n'8321'_626 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 -> Integer
du_n'8321'_626 v0
  = coe
      MAlonzo.Code.Data.Rational.Unnormalised.Base.d_numerator_14
      (coe v0)
-- Data.Rational.Unnormalised.Properties._.n₂
d_n'8322'_628 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50 -> Integer
d_n'8322'_628 ~v0 v1 ~v2 ~v3 ~v4 = du_n'8322'_628 v1
du_n'8322'_628 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 -> Integer
du_n'8322'_628 v0
  = coe
      MAlonzo.Code.Data.Rational.Unnormalised.Base.d_numerator_14
      (coe v0)
-- Data.Rational.Unnormalised.Properties._.n₃
d_n'8323'_630 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50 -> Integer
d_n'8323'_630 ~v0 ~v1 v2 ~v3 ~v4 = du_n'8323'_630 v2
du_n'8323'_630 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 -> Integer
du_n'8323'_630 v0
  = coe
      MAlonzo.Code.Data.Rational.Unnormalised.Base.d_numerator_14
      (coe v0)
-- Data.Rational.Unnormalised.Properties._.d₁
d_d'8321'_632 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50 -> Integer
d_d'8321'_632 v0 ~v1 ~v2 ~v3 ~v4 = du_d'8321'_632 v0
du_d'8321'_632 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 -> Integer
du_d'8321'_632 v0
  = coe
      MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
      (coe v0)
-- Data.Rational.Unnormalised.Properties._.d₂
d_d'8322'_634 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50 -> Integer
d_d'8322'_634 ~v0 v1 ~v2 ~v3 ~v4 = du_d'8322'_634 v1
du_d'8322'_634 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 -> Integer
du_d'8322'_634 v0
  = coe
      MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
      (coe v0)
-- Data.Rational.Unnormalised.Properties._.d₃
d_d'8323'_636 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50 -> Integer
d_d'8323'_636 ~v0 ~v1 v2 ~v3 ~v4 = du_d'8323'_636 v2
du_d'8323'_636 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 -> Integer
du_d'8323'_636 v0
  = coe
      MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
      (coe v0)
-- Data.Rational.Unnormalised.Properties.<-≤-trans
d_'60''45''8804''45'trans_644 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'60'__46 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8804'__38 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'60'__46
d_'60''45''8804''45'trans_644 v0 v1 v2 v3 v4
  = case coe v3 of
      MAlonzo.Code.Data.Rational.Unnormalised.Base.C_'42''60''42'_52 v7
        -> case coe v4 of
             MAlonzo.Code.Data.Rational.Unnormalised.Base.C_'42''8804''42'_44 v10
               -> coe
                    MAlonzo.Code.Data.Rational.Unnormalised.Base.C_'42''60''42'_52
                    (coe
                       MAlonzo.Code.Data.Integer.Properties.du_'42''45'cancel'691''45''60''45'nonNeg_6284
                       (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                          (coe
                             MAlonzo.Code.Data.Rational.Unnormalised.Base.d_numerator_14
                             (coe v0))
                          (coe
                             MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                             (coe v2)))
                       (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                          (coe
                             MAlonzo.Code.Data.Rational.Unnormalised.Base.d_numerator_14
                             (coe v2))
                          (coe
                             MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                             (coe v0)))
                       (addInt
                          (coe (1 :: Integer))
                          (coe
                             MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator'45'1_16
                             (coe v1)))
                       (let v11
                              = coe
                                  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_strictRelation_202 in
                        coe
                          (coe
                             MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__126
                             (coe v11)
                             (coe
                                MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                (coe
                                   MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                   (coe du_n'8321'_660 (coe v0)) (coe du_d'8323'_670 (coe v2)))
                                (coe du_d'8322'_668 (coe v1)))
                             (coe
                                MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                (coe
                                   MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                   (coe du_n'8323'_664 (coe v2)) (coe du_d'8321'_666 (coe v0)))
                                (coe du_d'8322'_668 (coe v1)))
                             (coe
                                MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_436
                                (\ v12 v13 v14 v15 v16 -> v16)
                                (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                   (coe
                                      MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                      (coe du_n'8321'_660 (coe v0)) (coe du_d'8323'_670 (coe v2)))
                                   (coe du_d'8322'_668 (coe v1)))
                                (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                   (coe du_n'8321'_660 (coe v0))
                                   (coe
                                      MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                      (coe du_d'8323'_670 (coe v2)) (coe du_d'8322'_668 (coe v1))))
                                (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                   (coe
                                      MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                      (coe du_n'8323'_664 (coe v2)) (coe du_d'8321'_666 (coe v0)))
                                   (coe du_d'8322'_668 (coe v1)))
                                (coe
                                   MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_436
                                   (\ v12 v13 v14 v15 v16 -> v16)
                                   (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                      (coe du_n'8321'_660 (coe v0))
                                      (coe
                                         MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                         (coe du_d'8323'_670 (coe v2))
                                         (coe du_d'8322'_668 (coe v1))))
                                   (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                      (coe du_n'8321'_660 (coe v0))
                                      (coe
                                         MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                         (coe du_d'8322'_668 (coe v1))
                                         (coe du_d'8323'_670 (coe v2))))
                                   (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                      (coe
                                         MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                         (coe du_n'8323'_664 (coe v2))
                                         (coe du_d'8321'_666 (coe v0)))
                                      (coe du_d'8322'_668 (coe v1)))
                                   (coe
                                      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10216'_448
                                      (\ v12 v13 v14 v15 v16 -> v16)
                                      (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                         (coe du_n'8321'_660 (coe v0))
                                         (coe
                                            MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                            (coe du_d'8322'_668 (coe v1))
                                            (coe du_d'8323'_670 (coe v2))))
                                      (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                         (coe
                                            MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                            (coe du_n'8321'_660 (coe v0))
                                            (coe du_d'8322'_668 (coe v1)))
                                         (coe du_d'8323'_670 (coe v2)))
                                      (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                         (coe
                                            MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                            (coe du_n'8323'_664 (coe v2))
                                            (coe du_d'8321'_666 (coe v0)))
                                         (coe du_d'8322'_668 (coe v1)))
                                      (coe
                                         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''60'_312
                                         (coe
                                            MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'60''45'go_152
                                            (\ v12 v13 v14 v15 v16 ->
                                               coe
                                                 MAlonzo.Code.Data.Integer.Properties.du_'60''45'trans_3008
                                                 v15 v16)
                                            (coe
                                               MAlonzo.Code.Relation.Binary.PropositionalEquality.Core.du_resp'8322'_160)
                                            (\ v12 v13 v14 v15 v16 ->
                                               coe
                                                 MAlonzo.Code.Data.Integer.Properties.du_'60''45''8804''45'trans_2994
                                                 v15 v16))
                                         (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                            (coe
                                               MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                               (coe du_n'8321'_660 (coe v0))
                                               (coe du_d'8322'_668 (coe v1)))
                                            (coe du_d'8323'_670 (coe v2)))
                                         (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                            (coe
                                               MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                               (coe du_n'8322'_662 (coe v1))
                                               (coe du_d'8321'_666 (coe v0)))
                                            (coe du_d'8323'_670 (coe v2)))
                                         (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                            (coe
                                               MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                               (coe du_n'8323'_664 (coe v2))
                                               (coe du_d'8321'_666 (coe v0)))
                                            (coe du_d'8322'_668 (coe v1)))
                                         (coe
                                            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_436
                                            (\ v12 v13 v14 v15 v16 -> v16)
                                            (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                               (coe
                                                  MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                  (coe du_n'8322'_662 (coe v1))
                                                  (coe du_d'8321'_666 (coe v0)))
                                               (coe du_d'8323'_670 (coe v2)))
                                            (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                               (coe
                                                  MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                  (coe du_d'8321'_666 (coe v0))
                                                  (coe du_n'8322'_662 (coe v1)))
                                               (coe du_d'8323'_670 (coe v2)))
                                            (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                               (coe
                                                  MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                  (coe du_n'8323'_664 (coe v2))
                                                  (coe du_d'8321'_666 (coe v0)))
                                               (coe du_d'8322'_668 (coe v1)))
                                            (coe
                                               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_436
                                               (\ v12 v13 v14 v15 v16 -> v16)
                                               (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                  (coe
                                                     MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                     (coe du_d'8321'_666 (coe v0))
                                                     (coe du_n'8322'_662 (coe v1)))
                                                  (coe du_d'8323'_670 (coe v2)))
                                               (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                  (coe du_d'8321'_666 (coe v0))
                                                  (coe
                                                     MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                     (coe du_n'8322'_662 (coe v1))
                                                     (coe du_d'8323'_670 (coe v2))))
                                               (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                  (coe
                                                     MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                     (coe du_n'8323'_664 (coe v2))
                                                     (coe du_d'8321'_666 (coe v0)))
                                                  (coe du_d'8322'_668 (coe v1)))
                                               (coe
                                                  MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8804'_308
                                                  (coe
                                                     MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8804''45'go_138
                                                     (coe
                                                        MAlonzo.Code.Data.Integer.Properties.d_'8804''45'isPreorder_2822)
                                                     (\ v12 v13 v14 v15 v16 ->
                                                        coe
                                                          MAlonzo.Code.Data.Integer.Properties.du_'8804''45''60''45'trans_2980
                                                          v15 v16))
                                                  (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                     (coe du_d'8321'_666 (coe v0))
                                                     (coe
                                                        MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                        (coe du_n'8322'_662 (coe v1))
                                                        (coe du_d'8323'_670 (coe v2))))
                                                  (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                     (coe du_d'8321'_666 (coe v0))
                                                     (coe
                                                        MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                        (coe du_n'8323'_664 (coe v2))
                                                        (coe du_d'8322'_668 (coe v1))))
                                                  (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                     (coe
                                                        MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                        (coe du_n'8323'_664 (coe v2))
                                                        (coe du_d'8321'_666 (coe v0)))
                                                     (coe du_d'8322'_668 (coe v1)))
                                                  (coe
                                                     MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10216'_448
                                                     (\ v12 v13 v14 v15 v16 -> v16)
                                                     (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                        (coe du_d'8321'_666 (coe v0))
                                                        (coe
                                                           MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                           (coe du_n'8323'_664 (coe v2))
                                                           (coe du_d'8322'_668 (coe v1))))
                                                     (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                        (coe
                                                           MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                           (coe du_d'8321'_666 (coe v0))
                                                           (coe du_n'8323'_664 (coe v2)))
                                                        (coe du_d'8322'_668 (coe v1)))
                                                     (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                        (coe
                                                           MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                           (coe du_n'8323'_664 (coe v2))
                                                           (coe du_d'8321'_666 (coe v0)))
                                                        (coe du_d'8322'_668 (coe v1)))
                                                     (coe
                                                        MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_436
                                                        (\ v12 v13 v14 v15 v16 -> v16)
                                                        (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                           (coe
                                                              MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                              (coe du_d'8321'_666 (coe v0))
                                                              (coe du_n'8323'_664 (coe v2)))
                                                           (coe du_d'8322'_668 (coe v1)))
                                                        (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                           (coe
                                                              MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                              (coe du_n'8323'_664 (coe v2))
                                                              (coe du_d'8321'_666 (coe v0)))
                                                           (coe du_d'8322'_668 (coe v1)))
                                                        (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                           (coe
                                                              MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                              (coe du_n'8323'_664 (coe v2))
                                                              (coe du_d'8321'_666 (coe v0)))
                                                           (coe du_d'8322'_668 (coe v1)))
                                                        (coe
                                                           MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                                                           (coe
                                                              MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_stop_166
                                                              (coe
                                                                 MAlonzo.Code.Data.Integer.Properties.d_'8804''45'isPreorder_2822))
                                                           (coe
                                                              MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                              (coe
                                                                 MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                                 (coe du_n'8323'_664 (coe v2))
                                                                 (coe du_d'8321'_666 (coe v0)))
                                                              (coe du_d'8322'_668 (coe v1))))
                                                        erased)
                                                     erased)
                                                  (coe
                                                     MAlonzo.Code.Data.Integer.Properties.du_'42''45'mono'737''45''8804''45'nonNeg_6076
                                                     (MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                                        (coe v0))
                                                     (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                        (coe
                                                           MAlonzo.Code.Data.Rational.Unnormalised.Base.d_numerator_14
                                                           (coe v1))
                                                        (coe
                                                           MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                                           (coe v2)))
                                                     (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                        (coe
                                                           MAlonzo.Code.Data.Rational.Unnormalised.Base.d_numerator_14
                                                           (coe v2))
                                                        (coe
                                                           MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                                           (coe v1)))
                                                     v10))
                                               erased)
                                            erased)
                                         (coe
                                            MAlonzo.Code.Data.Integer.Properties.du_'42''45'mono'691''45''60''45'pos_6226
                                            (MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                               (coe v2))
                                            (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                               (coe
                                                  MAlonzo.Code.Data.Rational.Unnormalised.Base.d_numerator_14
                                                  (coe v0))
                                               (coe
                                                  MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                                  (coe v1)))
                                            (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                               (coe
                                                  MAlonzo.Code.Data.Rational.Unnormalised.Base.d_numerator_14
                                                  (coe v1))
                                               (coe
                                                  MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                                  (coe v0)))
                                            v7))
                                      erased)
                                   erased)
                                erased))))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Rational.Unnormalised.Properties._.n₁
d_n'8321'_660 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 -> Integer
d_n'8321'_660 v0 ~v1 ~v2 ~v3 ~v4 = du_n'8321'_660 v0
du_n'8321'_660 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 -> Integer
du_n'8321'_660 v0
  = coe
      MAlonzo.Code.Data.Rational.Unnormalised.Base.d_numerator_14
      (coe v0)
-- Data.Rational.Unnormalised.Properties._.n₂
d_n'8322'_662 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 -> Integer
d_n'8322'_662 ~v0 v1 ~v2 ~v3 ~v4 = du_n'8322'_662 v1
du_n'8322'_662 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 -> Integer
du_n'8322'_662 v0
  = coe
      MAlonzo.Code.Data.Rational.Unnormalised.Base.d_numerator_14
      (coe v0)
-- Data.Rational.Unnormalised.Properties._.n₃
d_n'8323'_664 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 -> Integer
d_n'8323'_664 ~v0 ~v1 v2 ~v3 ~v4 = du_n'8323'_664 v2
du_n'8323'_664 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 -> Integer
du_n'8323'_664 v0
  = coe
      MAlonzo.Code.Data.Rational.Unnormalised.Base.d_numerator_14
      (coe v0)
-- Data.Rational.Unnormalised.Properties._.d₁
d_d'8321'_666 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 -> Integer
d_d'8321'_666 v0 ~v1 ~v2 ~v3 ~v4 = du_d'8321'_666 v0
du_d'8321'_666 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 -> Integer
du_d'8321'_666 v0
  = coe
      MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
      (coe v0)
-- Data.Rational.Unnormalised.Properties._.d₂
d_d'8322'_668 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 -> Integer
d_d'8322'_668 ~v0 v1 ~v2 ~v3 ~v4 = du_d'8322'_668 v1
du_d'8322'_668 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 -> Integer
du_d'8322'_668 v0
  = coe
      MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
      (coe v0)
-- Data.Rational.Unnormalised.Properties._.d₃
d_d'8323'_670 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 -> Integer
d_d'8323'_670 ~v0 ~v1 v2 ~v3 ~v4 = du_d'8323'_670 v2
du_d'8323'_670 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 -> Integer
du_d'8323'_670 v0
  = coe
      MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
      (coe v0)
-- Data.Rational.Unnormalised.Properties.<-trans
d_'60''45'trans_678 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'60'__46 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'60'__46 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'60'__46
d_'60''45'trans_678 v0 v1 v2 v3
  = coe
      d_'8804''45''60''45'trans_610 (coe v0) (coe v1) (coe v2)
      (coe du_'60''8658''8804'_556 (coe v3))
-- Data.Rational.Unnormalised.Properties.<-cmp
d_'60''45'cmp_680 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Relation.Binary.Definitions.T_Tri_158
d_'60''45'cmp_680 v0 v1
  = let v2
          = MAlonzo.Code.Data.Integer.Properties.d_'60''45'cmp_3014
              (coe
                 MAlonzo.Code.Data.Integer.Base.d__'9667'__230
                 (coe
                    MAlonzo.Code.Data.Sign.Base.d__'42'__14
                    (coe
                       MAlonzo.Code.Data.Integer.Base.d_sign_24
                       (coe
                          MAlonzo.Code.Data.Rational.Unnormalised.Base.d_numerator_14
                          (coe v0)))
                    (coe
                       MAlonzo.Code.Data.Integer.Base.d_sign_24
                       (coe
                          MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                          (coe v1))))
                 (coe
                    mulInt
                    (coe
                       MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18
                       (coe
                          MAlonzo.Code.Data.Rational.Unnormalised.Base.d_numerator_14
                          (coe v0)))
                    (coe
                       MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18
                       (coe
                          MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                          (coe v1)))))
              (coe
                 MAlonzo.Code.Data.Integer.Base.d__'42'__308
                 (coe
                    MAlonzo.Code.Data.Rational.Unnormalised.Base.d_numerator_14
                    (coe v1))
                 (coe
                    MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                    (coe v0))) in
    coe
      (case coe v2 of
         MAlonzo.Code.Relation.Binary.Definitions.C_tri'60'_172 v3
           -> coe
                MAlonzo.Code.Relation.Binary.Definitions.C_tri'60'_172
                (coe
                   MAlonzo.Code.Data.Rational.Unnormalised.Base.C_'42''60''42'_52 v3)
         MAlonzo.Code.Relation.Binary.Definitions.C_tri'8776'_180 v4
           -> coe
                MAlonzo.Code.Relation.Binary.Definitions.C_tri'8776'_180
                (coe
                   MAlonzo.Code.Data.Rational.Unnormalised.Base.C_'42''8801''42'_30)
         MAlonzo.Code.Relation.Binary.Definitions.C_tri'62'_188 v5
           -> coe
                MAlonzo.Code.Relation.Binary.Definitions.C_tri'62'_188
                (coe
                   MAlonzo.Code.Data.Rational.Unnormalised.Base.C_'42''60''42'_52 v5)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Data.Rational.Unnormalised.Properties._<?_
d__'60''63'__720 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'60''63'__720 v0 v1
  = coe
      MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
      (coe
         MAlonzo.Code.Data.Rational.Unnormalised.Base.C_'42''60''42'_52)
      (coe du_drop'45''42''60''42'_552)
      (coe
         MAlonzo.Code.Data.Integer.Properties.d__'60''63'__3104
         (coe
            MAlonzo.Code.Data.Integer.Base.d__'42'__308
            (coe
               MAlonzo.Code.Data.Rational.Unnormalised.Base.d_numerator_14
               (coe v0))
            (coe
               MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
               (coe v1)))
         (coe
            MAlonzo.Code.Data.Integer.Base.d__'42'__308
            (coe
               MAlonzo.Code.Data.Rational.Unnormalised.Base.d_numerator_14
               (coe v1))
            (coe
               MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
               (coe v0))))
-- Data.Rational.Unnormalised.Properties._>?_
d__'62''63'__726 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'62''63'__726 v0 v1 = coe d__'60''63'__720 (coe v1) (coe v0)
-- Data.Rational.Unnormalised.Properties.<-irrelevant
d_'60''45'irrelevant_728 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'60'__46 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'60'__46 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'60''45'irrelevant_728 = erased
-- Data.Rational.Unnormalised.Properties.<-respʳ-≃
d_'60''45'resp'691''45''8771'_734 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8771'__24 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'60'__46 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'60'__46
d_'60''45'resp'691''45''8771'_734 v0 v1 v2 v3 v4
  = coe
      seq (coe v3)
      (case coe v4 of
         MAlonzo.Code.Data.Rational.Unnormalised.Base.C_'42''60''42'_52 v7
           -> coe
                MAlonzo.Code.Data.Rational.Unnormalised.Base.C_'42''60''42'_52
                (coe
                   MAlonzo.Code.Data.Integer.Properties.du_'42''45'cancel'691''45''60''45'nonNeg_6284
                   (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                      (coe
                         MAlonzo.Code.Data.Rational.Unnormalised.Base.d_numerator_14
                         (coe v0))
                      (coe
                         MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                         (coe v2)))
                   (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                      (coe
                         MAlonzo.Code.Data.Rational.Unnormalised.Base.d_numerator_14
                         (coe v2))
                      (coe
                         MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                         (coe v0)))
                   (addInt
                      (coe (1 :: Integer))
                      (coe
                         MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator'45'1_16
                         (coe v1)))
                   (let v8
                          = coe
                              MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_strictRelation_202 in
                    coe
                      (coe
                         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__126
                         (coe v8)
                         (coe
                            MAlonzo.Code.Data.Integer.Base.d__'42'__308
                            (coe
                               MAlonzo.Code.Data.Integer.Base.d__'42'__308
                               (coe du_n'8321'_750 (coe v0)) (coe du_d'8323'_760 (coe v2)))
                            (coe du_d'8322'_758 (coe v1)))
                         (coe
                            MAlonzo.Code.Data.Integer.Base.d__'42'__308
                            (coe
                               MAlonzo.Code.Data.Integer.Base.d__'42'__308
                               (coe du_n'8323'_754 (coe v2)) (coe du_d'8321'_756 (coe v0)))
                            (coe du_d'8322'_758 (coe v1)))
                         (coe
                            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_436
                            (\ v9 v10 v11 v12 v13 -> v13)
                            (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                               (coe
                                  MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                  (coe du_n'8321'_750 (coe v0)) (coe du_d'8323'_760 (coe v2)))
                               (coe du_d'8322'_758 (coe v1)))
                            (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                               (coe du_n'8321'_750 (coe v0))
                               (coe
                                  MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                  (coe du_d'8323'_760 (coe v2)) (coe du_d'8322'_758 (coe v1))))
                            (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                               (coe
                                  MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                  (coe du_n'8323'_754 (coe v2)) (coe du_d'8321'_756 (coe v0)))
                               (coe du_d'8322'_758 (coe v1)))
                            (coe
                               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_436
                               (\ v9 v10 v11 v12 v13 -> v13)
                               (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                  (coe du_n'8321'_750 (coe v0))
                                  (coe
                                     MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                     (coe du_d'8323'_760 (coe v2)) (coe du_d'8322'_758 (coe v1))))
                               (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                  (coe du_n'8321'_750 (coe v0))
                                  (coe
                                     MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                     (coe du_d'8322'_758 (coe v1)) (coe du_d'8323'_760 (coe v2))))
                               (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                  (coe
                                     MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                     (coe du_n'8323'_754 (coe v2)) (coe du_d'8321'_756 (coe v0)))
                                  (coe du_d'8322'_758 (coe v1)))
                               (coe
                                  MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10216'_448
                                  (\ v9 v10 v11 v12 v13 -> v13)
                                  (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                     (coe du_n'8321'_750 (coe v0))
                                     (coe
                                        MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                        (coe du_d'8322'_758 (coe v1))
                                        (coe du_d'8323'_760 (coe v2))))
                                  (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                     (coe
                                        MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                        (coe du_n'8321'_750 (coe v0)) (coe du_d'8322'_758 (coe v1)))
                                     (coe du_d'8323'_760 (coe v2)))
                                  (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                     (coe
                                        MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                        (coe du_n'8323'_754 (coe v2)) (coe du_d'8321'_756 (coe v0)))
                                     (coe du_d'8322'_758 (coe v1)))
                                  (coe
                                     MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''60'_312
                                     (coe
                                        MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'60''45'go_152
                                        (\ v9 v10 v11 v12 v13 ->
                                           coe
                                             MAlonzo.Code.Data.Integer.Properties.du_'60''45'trans_3008
                                             v12 v13)
                                        (coe
                                           MAlonzo.Code.Relation.Binary.PropositionalEquality.Core.du_resp'8322'_160)
                                        (\ v9 v10 v11 v12 v13 ->
                                           coe
                                             MAlonzo.Code.Data.Integer.Properties.du_'60''45''8804''45'trans_2994
                                             v12 v13))
                                     (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                        (coe
                                           MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                           (coe du_n'8321'_750 (coe v0))
                                           (coe du_d'8322'_758 (coe v1)))
                                        (coe du_d'8323'_760 (coe v2)))
                                     (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                        (coe
                                           MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                           (coe du_n'8322'_752 (coe v1))
                                           (coe du_d'8321'_756 (coe v0)))
                                        (coe du_d'8323'_760 (coe v2)))
                                     (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                        (coe
                                           MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                           (coe du_n'8323'_754 (coe v2))
                                           (coe du_d'8321'_756 (coe v0)))
                                        (coe du_d'8322'_758 (coe v1)))
                                     (coe
                                        MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_436
                                        (\ v9 v10 v11 v12 v13 -> v13)
                                        (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                           (coe
                                              MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                              (coe du_n'8322'_752 (coe v1))
                                              (coe du_d'8321'_756 (coe v0)))
                                           (coe du_d'8323'_760 (coe v2)))
                                        (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                           (coe du_n'8322'_752 (coe v1))
                                           (coe
                                              MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                              (coe du_d'8321'_756 (coe v0))
                                              (coe du_d'8323'_760 (coe v2))))
                                        (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                           (coe
                                              MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                              (coe du_n'8323'_754 (coe v2))
                                              (coe du_d'8321'_756 (coe v0)))
                                           (coe du_d'8322'_758 (coe v1)))
                                        (coe
                                           MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_436
                                           (\ v9 v10 v11 v12 v13 -> v13)
                                           (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                              (coe du_n'8322'_752 (coe v1))
                                              (coe
                                                 MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                 (coe du_d'8321'_756 (coe v0))
                                                 (coe du_d'8323'_760 (coe v2))))
                                           (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                              (coe du_n'8322'_752 (coe v1))
                                              (coe
                                                 MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                 (coe du_d'8323'_760 (coe v2))
                                                 (coe du_d'8321'_756 (coe v0))))
                                           (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                              (coe
                                                 MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                 (coe du_n'8323'_754 (coe v2))
                                                 (coe du_d'8321'_756 (coe v0)))
                                              (coe du_d'8322'_758 (coe v1)))
                                           (coe
                                              MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10216'_448
                                              (\ v9 v10 v11 v12 v13 -> v13)
                                              (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                 (coe du_n'8322'_752 (coe v1))
                                                 (coe
                                                    MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                    (coe du_d'8323'_760 (coe v2))
                                                    (coe du_d'8321'_756 (coe v0))))
                                              (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                 (coe
                                                    MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                    (coe du_n'8322'_752 (coe v1))
                                                    (coe du_d'8323'_760 (coe v2)))
                                                 (coe du_d'8321'_756 (coe v0)))
                                              (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                 (coe
                                                    MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                    (coe du_n'8323'_754 (coe v2))
                                                    (coe du_d'8321'_756 (coe v0)))
                                                 (coe du_d'8322'_758 (coe v1)))
                                              (coe
                                                 MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_436
                                                 (\ v9 v10 v11 v12 v13 -> v13)
                                                 (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                    (coe
                                                       MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                       (coe du_n'8322'_752 (coe v1))
                                                       (coe du_d'8323'_760 (coe v2)))
                                                    (coe du_d'8321'_756 (coe v0)))
                                                 (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                    (coe
                                                       MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                       (coe du_n'8323'_754 (coe v2))
                                                       (coe du_d'8322'_758 (coe v1)))
                                                    (coe du_d'8321'_756 (coe v0)))
                                                 (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                    (coe
                                                       MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                       (coe du_n'8323'_754 (coe v2))
                                                       (coe du_d'8321'_756 (coe v0)))
                                                    (coe du_d'8322'_758 (coe v1)))
                                                 (coe
                                                    MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_436
                                                    (\ v9 v10 v11 v12 v13 -> v13)
                                                    (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                       (coe
                                                          MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                          (coe du_n'8323'_754 (coe v2))
                                                          (coe du_d'8322'_758 (coe v1)))
                                                       (coe du_d'8321'_756 (coe v0)))
                                                    (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                       (coe du_n'8323'_754 (coe v2))
                                                       (coe
                                                          MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                          (coe du_d'8322'_758 (coe v1))
                                                          (coe du_d'8321'_756 (coe v0))))
                                                    (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                       (coe
                                                          MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                          (coe du_n'8323'_754 (coe v2))
                                                          (coe du_d'8321'_756 (coe v0)))
                                                       (coe du_d'8322'_758 (coe v1)))
                                                    (coe
                                                       MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_436
                                                       (\ v9 v10 v11 v12 v13 -> v13)
                                                       (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                          (coe du_n'8323'_754 (coe v2))
                                                          (coe
                                                             MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                             (coe du_d'8322'_758 (coe v1))
                                                             (coe du_d'8321'_756 (coe v0))))
                                                       (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                          (coe du_n'8323'_754 (coe v2))
                                                          (coe
                                                             MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                             (coe du_d'8321'_756 (coe v0))
                                                             (coe du_d'8322'_758 (coe v1))))
                                                       (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                          (coe
                                                             MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                             (coe du_n'8323'_754 (coe v2))
                                                             (coe du_d'8321'_756 (coe v0)))
                                                          (coe du_d'8322'_758 (coe v1)))
                                                       (coe
                                                          MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10216'_448
                                                          (\ v9 v10 v11 v12 v13 -> v13)
                                                          (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                             (coe du_n'8323'_754 (coe v2))
                                                             (coe
                                                                MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                                (coe du_d'8321'_756 (coe v0))
                                                                (coe du_d'8322'_758 (coe v1))))
                                                          (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                             (coe
                                                                MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                                (coe du_n'8323'_754 (coe v2))
                                                                (coe du_d'8321'_756 (coe v0)))
                                                             (coe du_d'8322'_758 (coe v1)))
                                                          (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                             (coe
                                                                MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                                (coe du_n'8323'_754 (coe v2))
                                                                (coe du_d'8321'_756 (coe v0)))
                                                             (coe du_d'8322'_758 (coe v1)))
                                                          (coe
                                                             MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                                                             (coe
                                                                MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_stop_166
                                                                (coe
                                                                   MAlonzo.Code.Data.Integer.Properties.d_'8804''45'isPreorder_2822))
                                                             (coe
                                                                MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                                (coe
                                                                   MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                                   (coe du_n'8323'_754 (coe v2))
                                                                   (coe du_d'8321'_756 (coe v0)))
                                                                (coe du_d'8322'_758 (coe v1))))
                                                          erased)
                                                       erased)
                                                    erased)
                                                 erased)
                                              erased)
                                           erased)
                                        erased)
                                     (coe
                                        MAlonzo.Code.Data.Integer.Properties.du_'42''45'mono'691''45''60''45'pos_6226
                                        (MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                           (coe v2))
                                        (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                           (coe
                                              MAlonzo.Code.Data.Rational.Unnormalised.Base.d_numerator_14
                                              (coe v0))
                                           (coe
                                              MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                              (coe v1)))
                                        (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                           (coe
                                              MAlonzo.Code.Data.Rational.Unnormalised.Base.d_numerator_14
                                              (coe v1))
                                           (coe
                                              MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                              (coe v0)))
                                        v7))
                                  erased)
                               erased)
                            erased))))
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Data.Rational.Unnormalised.Properties._.n₁
d_n'8321'_750 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50 -> Integer
d_n'8321'_750 v0 ~v1 ~v2 ~v3 ~v4 = du_n'8321'_750 v0
du_n'8321'_750 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 -> Integer
du_n'8321'_750 v0
  = coe
      MAlonzo.Code.Data.Rational.Unnormalised.Base.d_numerator_14
      (coe v0)
-- Data.Rational.Unnormalised.Properties._.n₂
d_n'8322'_752 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50 -> Integer
d_n'8322'_752 ~v0 v1 ~v2 ~v3 ~v4 = du_n'8322'_752 v1
du_n'8322'_752 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 -> Integer
du_n'8322'_752 v0
  = coe
      MAlonzo.Code.Data.Rational.Unnormalised.Base.d_numerator_14
      (coe v0)
-- Data.Rational.Unnormalised.Properties._.n₃
d_n'8323'_754 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50 -> Integer
d_n'8323'_754 ~v0 ~v1 v2 ~v3 ~v4 = du_n'8323'_754 v2
du_n'8323'_754 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 -> Integer
du_n'8323'_754 v0
  = coe
      MAlonzo.Code.Data.Rational.Unnormalised.Base.d_numerator_14
      (coe v0)
-- Data.Rational.Unnormalised.Properties._.d₁
d_d'8321'_756 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50 -> Integer
d_d'8321'_756 v0 ~v1 ~v2 ~v3 ~v4 = du_d'8321'_756 v0
du_d'8321'_756 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 -> Integer
du_d'8321'_756 v0
  = coe
      MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
      (coe v0)
-- Data.Rational.Unnormalised.Properties._.d₂
d_d'8322'_758 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50 -> Integer
d_d'8322'_758 ~v0 v1 ~v2 ~v3 ~v4 = du_d'8322'_758 v1
du_d'8322'_758 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 -> Integer
du_d'8322'_758 v0
  = coe
      MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
      (coe v0)
-- Data.Rational.Unnormalised.Properties._.d₃
d_d'8323'_760 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50 -> Integer
d_d'8323'_760 ~v0 ~v1 v2 ~v3 ~v4 = du_d'8323'_760 v2
du_d'8323'_760 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 -> Integer
du_d'8323'_760 v0
  = coe
      MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
      (coe v0)
-- Data.Rational.Unnormalised.Properties.<-respˡ-≃
d_'60''45'resp'737''45''8771'_770 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8771'__24 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'60'__46 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'60'__46
d_'60''45'resp'737''45''8771'_770 v0 v1 v2 v3 v4
  = coe
      d_neg'45'mono'45''60'_400
      (coe
         MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
         (\ v5 v6 -> v6)
         MAlonzo.Code.Data.Rational.Unnormalised.Base.d_'45'__190 v1 v0)
      (coe
         MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
         (\ v5 v6 -> v6)
         MAlonzo.Code.Data.Rational.Unnormalised.Base.d_'45'__190 v1 v2)
      (coe
         d_'60''45'resp'691''45''8771'_734
         (coe
            MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
            (\ v5 v6 -> v6)
            MAlonzo.Code.Data.Rational.Unnormalised.Base.d_'45'__190 v1 v0)
         (coe
            MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
            MAlonzo.Code.Data.Rational.Unnormalised.Base.d_'45'__190
            (\ v5 v6 -> v5) v1 v2)
         (coe
            MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
            (\ v5 v6 -> v6)
            MAlonzo.Code.Data.Rational.Unnormalised.Base.d_'45'__190 v1 v2)
         (coe d_'45''8255'cong_378 (coe v1) (coe v2) (coe v3))
         (coe d_neg'45'mono'45''60'_400 (coe v1) (coe v0) (coe v4)))
-- Data.Rational.Unnormalised.Properties.<-resp-≃
d_'60''45'resp'45''8771'_780 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'60''45'resp'45''8771'_780
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe d_'60''45'resp'691''45''8771'_734)
      (coe d_'60''45'resp'737''45''8771'_770)
-- Data.Rational.Unnormalised.Properties.<-isStrictPartialOrder-≡
d_'60''45'isStrictPartialOrder'45''8801'_782 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsStrictPartialOrder_354
d_'60''45'isStrictPartialOrder'45''8801'_782
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_IsStrictPartialOrder'46'constructor_16311
      (coe
         MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties.du_isEquivalence_396)
      d_'60''45'trans_678
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
         (coe (\ v0 v1 v2 v3 v4 -> v4)) (coe (\ v0 v1 v2 v3 v4 -> v4)))
-- Data.Rational.Unnormalised.Properties.<-isStrictPartialOrder
d_'60''45'isStrictPartialOrder_788 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsStrictPartialOrder_354
d_'60''45'isStrictPartialOrder_788
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_IsStrictPartialOrder'46'constructor_16311
      d_'8771''45'isEquivalence_260 d_'60''45'trans_678
      d_'60''45'resp'45''8771'_780
-- Data.Rational.Unnormalised.Properties.<-isStrictTotalOrder
d_'60''45'isStrictTotalOrder_790 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsStrictTotalOrder_600
d_'60''45'isStrictTotalOrder_790
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_IsStrictTotalOrder'46'constructor_27253
      (coe d_'60''45'isStrictPartialOrder_788) (coe d_'60''45'cmp_680)
-- Data.Rational.Unnormalised.Properties.<-isDenseLinearOrder
d_'60''45'isDenseLinearOrder_792 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsDenseLinearOrder_660
d_'60''45'isDenseLinearOrder_792
  = coe
      MAlonzo.Code.Relation.Binary.Structures.C_IsDenseLinearOrder'46'constructor_30431
      (coe d_'60''45'isStrictTotalOrder_790) (coe d_'60''45'dense_592)
-- Data.Rational.Unnormalised.Properties.<-strictPartialOrder-≡
d_'60''45'strictPartialOrder'45''8801'_794 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictPartialOrder_744
d_'60''45'strictPartialOrder'45''8801'_794
  = coe
      MAlonzo.Code.Relation.Binary.Bundles.C_StrictPartialOrder'46'constructor_14243
      d_'60''45'isStrictPartialOrder'45''8801'_782
-- Data.Rational.Unnormalised.Properties.<-strictPartialOrder
d_'60''45'strictPartialOrder_796 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictPartialOrder_744
d_'60''45'strictPartialOrder_796
  = coe
      MAlonzo.Code.Relation.Binary.Bundles.C_StrictPartialOrder'46'constructor_14243
      d_'60''45'isStrictPartialOrder_788
-- Data.Rational.Unnormalised.Properties.<-strictTotalOrder
d_'60''45'strictTotalOrder_798 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_StrictTotalOrder_1256
d_'60''45'strictTotalOrder_798
  = coe
      MAlonzo.Code.Relation.Binary.Bundles.C_StrictTotalOrder'46'constructor_24345
      d_'60''45'isStrictTotalOrder_790
-- Data.Rational.Unnormalised.Properties.<-denseLinearOrder
d_'60''45'denseLinearOrder_800 ::
  MAlonzo.Code.Relation.Binary.Bundles.T_DenseLinearOrder_1368
d_'60''45'denseLinearOrder_800
  = coe
      MAlonzo.Code.Relation.Binary.Bundles.C_DenseLinearOrder'46'constructor_26715
      d_'60''45'isDenseLinearOrder_792
-- Data.Rational.Unnormalised.Properties.≤-Reasoning.Triple._IsRelatedTo_
d__IsRelatedTo__806 a0 a1 = ()
-- Data.Rational.Unnormalised.Properties.≤-Reasoning.Triple._∎
d__'8718'_808 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78
d__'8718'_808
  = let v0 = d_'8804''45'isPreorder_512 in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_stop_166
            (coe v0)))
-- Data.Rational.Unnormalised.Properties.≤-Reasoning.Triple.<-go
d_'60''45'go_810 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'60'__46 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78
d_'60''45'go_810
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'60''45'go_152
      (coe d_'60''45'trans_678) (coe d_'60''45'resp'45''8771'_780)
      (coe d_'60''45''8804''45'trans_644)
-- Data.Rational.Unnormalised.Properties.≤-Reasoning.Triple.IsEquality
d_IsEquality_812 a0 a1 a2 = ()
-- Data.Rational.Unnormalised.Properties.≤-Reasoning.Triple.IsEquality?
d_IsEquality'63'_814 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_IsEquality'63'_814 v0 v1 v2
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_IsEquality'63'_224
      v2
-- Data.Rational.Unnormalised.Properties.≤-Reasoning.Triple.IsStrict
d_IsStrict_816 a0 a1 a2 = ()
-- Data.Rational.Unnormalised.Properties.≤-Reasoning.Triple.IsStrict?
d_IsStrict'63'_818 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_IsStrict'63'_818 v0 v1 v2
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_IsStrict'63'_188
      v2
-- Data.Rational.Unnormalised.Properties.≤-Reasoning.Triple.begin_
d_begin__820 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8804'__38
d_begin__820
  = let v0 = d_'8804''45'isPreorder_512 in
    coe
      (let v1 = \ v1 v2 v3 -> coe du_'60''8658''8804'_556 v3 in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_start_96
               (coe v0) (coe v1))))
-- Data.Rational.Unnormalised.Properties.≤-Reasoning.Triple.begin-contradiction_
d_begin'45'contradiction__822 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78 ->
  AgdaAny -> MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> AgdaAny
d_begin'45'contradiction__822 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin'45'contradiction__246
-- Data.Rational.Unnormalised.Properties.≤-Reasoning.Triple.begin_
d_begin__824 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78 ->
  AgdaAny ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8771'__24
d_begin__824
  = let v0
          = coe
              MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_eqRelation_238 in
    coe
      (\ v1 v2 v3 v4 ->
         coe
           MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__126
           (coe v0) v1 v2 v3)
-- Data.Rational.Unnormalised.Properties.≤-Reasoning.Triple.begin_
d_begin__826 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78 ->
  AgdaAny -> MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'60'__46
d_begin__826
  = let v0
          = coe
              MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_strictRelation_202 in
    coe
      (\ v1 v2 v3 v4 ->
         coe
           MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__126
           (coe v0) v1 v2 v3)
-- Data.Rational.Unnormalised.Properties.≤-Reasoning.Triple.eqRelation
d_eqRelation_828 ::
  MAlonzo.Code.Relation.Binary.Reasoning.Syntax.T_SubRelation_60
d_eqRelation_828
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_eqRelation_238
-- Data.Rational.Unnormalised.Properties.≤-Reasoning.Triple.extractEquality
d_extractEquality_832 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T_IsEquality_208 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8771'__24
d_extractEquality_832 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_extractEquality_234
      v2 v3
-- Data.Rational.Unnormalised.Properties.≤-Reasoning.Triple.extractStrict
d_extractStrict_834 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T_IsStrict_172 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'60'__46
d_extractStrict_834 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_extractStrict_198
      v2 v3
-- Data.Rational.Unnormalised.Properties.≤-Reasoning.Triple.start
d_start_842 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8804'__38
d_start_842
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_start_96
      (coe d_'8804''45'isPreorder_512)
      (\ v0 v1 v2 -> coe du_'60''8658''8804'_556 v2)
-- Data.Rational.Unnormalised.Properties.≤-Reasoning.Triple.step-<
d_step'45''60'_844 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'60'__46 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78
d_step'45''60'_844
  = let v0 = d_'60''45'trans_678 in
    coe
      (let v1 = d_'60''45'resp'45''8771'_780 in
       coe
         (let v2 = d_'60''45''8804''45'trans_644 in
          coe
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''60'_312
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'60''45'go_152
                  (coe v0) (coe v1) (coe v2)))))
-- Data.Rational.Unnormalised.Properties.≤-Reasoning.Triple.step-≡
d_step'45''8801'_854 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78
d_step'45''8801'_854
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801'_450
      (coe (\ v0 v1 v2 v3 v4 -> v4))
-- Data.Rational.Unnormalised.Properties.≤-Reasoning.Triple.step-≡-∣
d_step'45''8801''45''8739'_856 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78
d_step'45''8801''45''8739'_856 ~v0 ~v1 v2
  = du_step'45''8801''45''8739'_856 v2
du_step'45''8801''45''8739'_856 ::
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78
du_step'45''8801''45''8739'_856 v0 = coe v0
-- Data.Rational.Unnormalised.Properties.≤-Reasoning.Triple.step-≡-⟨
d_step'45''8801''45''10216'_858 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78
d_step'45''8801''45''10216'_858
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10216'_448
      (coe (\ v0 v1 v2 v3 v4 -> v4))
-- Data.Rational.Unnormalised.Properties.≤-Reasoning.Triple.step-≡-⟩
d_step'45''8801''45''10217'_860 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78
d_step'45''8801''45''10217'_860
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_436
      (coe (\ v0 v1 v2 v3 v4 -> v4))
-- Data.Rational.Unnormalised.Properties.≤-Reasoning.Triple.step-≡˘
d_step'45''8801''728'_862 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78
d_step'45''8801''728'_862
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''728'_452
      (coe (\ v0 v1 v2 v3 v4 -> v4))
-- Data.Rational.Unnormalised.Properties.≤-Reasoning.Triple.step-≤
d_step'45''8804'_864 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8804'__38 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78
d_step'45''8804'_864
  = let v0 = d_'8804''45'isPreorder_512 in
    coe
      (let v1 = d_'8804''45''60''45'trans_610 in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8804'_308
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8804''45'go_138
               (coe v0) (coe v1))))
-- Data.Rational.Unnormalised.Properties.≤-Reasoning.Triple.stop
d_stop_866 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78
d_stop_866
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_stop_166
      (coe d_'8804''45'isPreorder_512)
-- Data.Rational.Unnormalised.Properties.≤-Reasoning.Triple.strictRelation
d_strictRelation_870 ::
  MAlonzo.Code.Relation.Binary.Reasoning.Syntax.T_SubRelation_60
d_strictRelation_870
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_strictRelation_202
-- Data.Rational.Unnormalised.Properties.≤-Reasoning.Triple.≈-go
d_'8776''45'go_872 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8771'__24 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78
d_'8776''45'go_872
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8776''45'go_124
      (coe d_'8804''45'isPreorder_512) (coe d_'60''45'resp'45''8771'_780)
-- Data.Rational.Unnormalised.Properties.≤-Reasoning.Triple.≡-go
d_'8801''45'go_874 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78
d_'8801''45'go_874 ~v0 ~v1 ~v2 ~v3 v4 = du_'8801''45'go_874 v4
du_'8801''45'go_874 ::
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78
du_'8801''45'go_874 v0 = coe v0
-- Data.Rational.Unnormalised.Properties.≤-Reasoning.Triple.≤-go
d_'8804''45'go_876 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8804'__38 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78
d_'8804''45'go_876
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8804''45'go_138
      (coe d_'8804''45'isPreorder_512)
      (coe d_'8804''45''60''45'trans_610)
-- Data.Rational.Unnormalised.Properties.≤-Reasoning._.step-≃-⟨
d_step'45''8771''45''10216'_896 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8771'__24 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78
d_step'45''8771''45''10216'_896
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8771''45''10216'_390
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8776''45'go_124
         (coe d_'8804''45'isPreorder_512)
         (coe d_'60''45'resp'45''8771'_780))
      (\ v0 v1 v2 -> coe du_'8771''45'sym_170 v2)
-- Data.Rational.Unnormalised.Properties.≤-Reasoning._.step-≃-⟩
d_step'45''8771''45''10217'_898 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8771'__24 ->
  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.T__IsRelatedTo__78
d_step'45''8771''45''10217'_898
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8771''45''10217'_388
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8776''45'go_124
         (coe d_'8804''45'isPreorder_512)
         (coe d_'60''45'resp'45''8771'_780))
-- Data.Rational.Unnormalised.Properties.≥0⇒↥≥0
d_'8805'0'8658''8613''8805'0_904 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8804'__38 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26
d_'8805'0'8658''8613''8805'0_904 v0 ~v1 v2
  = du_'8805'0'8658''8613''8805'0_904 v0 v2
du_'8805'0'8658''8613''8805'0_904 ::
  Integer ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8804'__38 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26
du_'8805'0'8658''8613''8805'0_904 v0 v1
  = coe
      MAlonzo.Code.Data.Integer.Properties.du_'8804''45'trans_2752
      (coe du_drop'45''42''8804''42'_428 (coe v1))
      (coe
         MAlonzo.Code.Data.Integer.Properties.du_'8804''45'reflexive_2744
         (coe
            MAlonzo.Code.Data.Integer.Base.d__'42'__308 (coe v0)
            (coe MAlonzo.Code.Data.Integer.Base.d_1ℤ_16)))
-- Data.Rational.Unnormalised.Properties.>0⇒↥>0
d_'62'0'8658''8613''62'0_916 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'60'__46 ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50
d_'62'0'8658''8613''62'0_916 v0 ~v1 v2
  = du_'62'0'8658''8613''62'0_916 v0 v2
du_'62'0'8658''8613''62'0_916 ::
  Integer ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'60'__46 ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50
du_'62'0'8658''8613''62'0_916 v0 v1
  = coe
      MAlonzo.Code.Data.Integer.Properties.du_'60''45''8804''45'trans_2994
      (coe du_drop'45''42''60''42'_552 (coe v1))
      (coe
         MAlonzo.Code.Data.Integer.Properties.du_'8804''45'reflexive_2744
         (coe
            MAlonzo.Code.Data.Integer.Base.d__'42'__308 (coe v0)
            (coe MAlonzo.Code.Data.Integer.Base.d_1ℤ_16)))
-- Data.Rational.Unnormalised.Properties.positive⁻¹
d_positive'8315''185'_926 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Integer.Base.T_Positive_134 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'60'__46
d_positive'8315''185'_926 v0 ~v1 = du_positive'8315''185'_926 v0
du_positive'8315''185'_926 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'60'__46
du_positive'8315''185'_926 v0
  = coe
      seq (coe v0)
      (coe
         MAlonzo.Code.Data.Rational.Unnormalised.Base.C_'42''60''42'_52
         (coe
            MAlonzo.Code.Data.Integer.Base.C_'43''60''43'_72
            (coe
               MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
               (coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26))))
-- Data.Rational.Unnormalised.Properties.nonNegative⁻¹
d_nonNegative'8315''185'_932 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Integer.Base.T_NonNegative_144 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8804'__38
d_nonNegative'8315''185'_932 v0 ~v1
  = du_nonNegative'8315''185'_932 v0
du_nonNegative'8315''185'_932 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8804'__38
du_nonNegative'8315''185'_932 v0
  = case coe v0 of
      MAlonzo.Code.Data.Rational.Unnormalised.Base.C_mkℚ'7512'_22 v1 v2
        -> coe
             seq (coe v1)
             (coe
                MAlonzo.Code.Data.Rational.Unnormalised.Base.C_'42''8804''42'_44
                (coe
                   MAlonzo.Code.Data.Integer.Base.C_'43''8804''43'_48
                   (coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Rational.Unnormalised.Properties.negative⁻¹
d_negative'8315''185'_938 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Integer.Base.T_Negative_164 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'60'__46
d_negative'8315''185'_938 v0 ~v1 = du_negative'8315''185'_938 v0
du_negative'8315''185'_938 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'60'__46
du_negative'8315''185'_938 v0
  = coe
      seq (coe v0)
      (coe
         MAlonzo.Code.Data.Rational.Unnormalised.Base.C_'42''60''42'_52
         (coe MAlonzo.Code.Data.Integer.Base.C_'45''60''43'_64))
-- Data.Rational.Unnormalised.Properties.nonPositive⁻¹
d_nonPositive'8315''185'_944 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Integer.Base.T_NonPositive_154 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8804'__38
d_nonPositive'8315''185'_944 v0 ~v1
  = du_nonPositive'8315''185'_944 v0
du_nonPositive'8315''185'_944 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8804'__38
du_nonPositive'8315''185'_944 v0
  = case coe v0 of
      MAlonzo.Code.Data.Rational.Unnormalised.Base.C_mkℚ'7512'_22 v1 v2
        -> case coe v1 of
             0 -> coe
                    MAlonzo.Code.Data.Rational.Unnormalised.Base.C_'42''8804''42'_44
                    (coe
                       MAlonzo.Code.Data.Integer.Base.C_'43''8804''43'_48
                       (coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26))
             _ -> coe
                    MAlonzo.Code.Data.Rational.Unnormalised.Base.C_'42''8804''42'_44
                    (coe MAlonzo.Code.Data.Integer.Base.C_'45''8804''43'_40)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Rational.Unnormalised.Properties.pos⇒nonNeg
d_pos'8658'nonNeg_950 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Integer.Base.T_Positive_134 ->
  MAlonzo.Code.Data.Integer.Base.T_NonNegative_144
d_pos'8658'nonNeg_950 v0 ~v1 = du_pos'8658'nonNeg_950 v0
du_pos'8658'nonNeg_950 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Integer.Base.T_NonNegative_144
du_pos'8658'nonNeg_950 v0
  = case coe v0 of
      MAlonzo.Code.Data.Rational.Unnormalised.Base.C_mkℚ'7512'_22 v1 v2
        -> coe
             seq (coe v1)
             (coe
                MAlonzo.Code.Data.Integer.Base.C_NonNegative'46'constructor_1457
                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Rational.Unnormalised.Properties.neg⇒nonPos
d_neg'8658'nonPos_956 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Integer.Base.T_Negative_164 ->
  MAlonzo.Code.Data.Integer.Base.T_NonPositive_154
d_neg'8658'nonPos_956 v0 ~v1 = du_neg'8658'nonPos_956 v0
du_neg'8658'nonPos_956 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Integer.Base.T_NonPositive_154
du_neg'8658'nonPos_956 v0
  = case coe v0 of
      MAlonzo.Code.Data.Rational.Unnormalised.Base.C_mkℚ'7512'_22 v1 v2
        -> coe
             seq (coe v1)
             (coe
                MAlonzo.Code.Data.Integer.Base.C_NonPositive'46'constructor_1515
                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Rational.Unnormalised.Properties.neg<pos
d_neg'60'pos_964 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Integer.Base.T_Negative_164 ->
  MAlonzo.Code.Data.Integer.Base.T_Positive_134 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'60'__46
d_neg'60'pos_964 v0 v1 ~v2 ~v3 = du_neg'60'pos_964 v0 v1
du_neg'60'pos_964 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'60'__46
du_neg'60'pos_964 v0 v1
  = coe
      d_'60''45'trans_678 v0
      MAlonzo.Code.Data.Rational.Unnormalised.Base.d_0ℚ'7512'_108 v1
      (coe du_negative'8315''185'_938 (coe v0))
      (coe du_positive'8315''185'_926 (coe v1))
-- Data.Rational.Unnormalised.Properties.pos⇒nonZero
d_pos'8658'nonZero_972 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Integer.Base.T_Positive_134 ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112
d_pos'8658'nonZero_972 v0 ~v1 = du_pos'8658'nonZero_972 v0
du_pos'8658'nonZero_972 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112
du_pos'8658'nonZero_972 v0
  = coe
      seq (coe v0)
      (coe
         MAlonzo.Code.Data.Nat.Base.C_NonZero'46'constructor_3575
         (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
-- Data.Rational.Unnormalised.Properties.nonNeg∧nonPos⇒0
d_nonNeg'8743'nonPos'8658'0_976 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Integer.Base.T_NonNegative_144 ->
  MAlonzo.Code.Data.Integer.Base.T_NonPositive_154 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8771'__24
d_nonNeg'8743'nonPos'8658'0_976 v0 ~v1 ~v2
  = du_nonNeg'8743'nonPos'8658'0_976 v0
du_nonNeg'8743'nonPos'8658'0_976 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8771'__24
du_nonNeg'8743'nonPos'8658'0_976 v0
  = coe
      seq (coe v0)
      (coe
         MAlonzo.Code.Data.Rational.Unnormalised.Base.C_'42''8801''42'_30)
-- Data.Rational.Unnormalised.Properties.nonNeg<⇒pos
d_nonNeg'60''8658'pos_984 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Integer.Base.T_NonNegative_144 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'60'__46 ->
  MAlonzo.Code.Data.Integer.Base.T_Positive_134
d_nonNeg'60''8658'pos_984 v0 v1 ~v2 v3
  = du_nonNeg'60''8658'pos_984 v0 v1 v3
du_nonNeg'60''8658'pos_984 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'60'__46 ->
  MAlonzo.Code.Data.Integer.Base.T_Positive_134
du_nonNeg'60''8658'pos_984 v0 v1 v2
  = coe
      MAlonzo.Code.Data.Rational.Unnormalised.Base.d_positive_162
      (coe v1)
      (coe
         d_'8804''45''60''45'trans_610
         (coe MAlonzo.Code.Data.Rational.Unnormalised.Base.d_0ℚ'7512'_108)
         (coe v0) (coe v1) (coe du_nonNegative'8315''185'_932 (coe v0))
         (coe v2))
-- Data.Rational.Unnormalised.Properties.nonNeg≤⇒nonNeg
d_nonNeg'8804''8658'nonNeg_996 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Integer.Base.T_NonNegative_144 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8804'__38 ->
  MAlonzo.Code.Data.Integer.Base.T_NonNegative_144
d_nonNeg'8804''8658'nonNeg_996 v0 v1 ~v2 v3
  = du_nonNeg'8804''8658'nonNeg_996 v0 v1 v3
du_nonNeg'8804''8658'nonNeg_996 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8804'__38 ->
  MAlonzo.Code.Data.Integer.Base.T_NonNegative_144
du_nonNeg'8804''8658'nonNeg_996 v0 v1 v2
  = coe
      MAlonzo.Code.Data.Rational.Unnormalised.Base.d_nonNegative_186
      (coe v1)
      (coe
         d_'8804''45'trans_440
         (coe MAlonzo.Code.Data.Rational.Unnormalised.Base.d_0ℚ'7512'_108)
         (coe v0) (coe v1) (coe du_nonNegative'8315''185'_932 (coe v0))
         (coe v2))
-- Data.Rational.Unnormalised.Properties.neg⇒nonZero
d_neg'8658'nonZero_1004 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Integer.Base.T_Negative_164 ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112
d_neg'8658'nonZero_1004 v0 ~v1 = du_neg'8658'nonZero_1004 v0
du_neg'8658'nonZero_1004 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112
du_neg'8658'nonZero_1004 v0
  = coe
      seq (coe v0)
      (coe
         MAlonzo.Code.Data.Nat.Base.C_NonZero'46'constructor_3575
         (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
-- Data.Rational.Unnormalised.Properties.+-cong
d_'43''45'cong_1006 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8771'__24 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8771'__24 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8771'__24
d_'43''45'cong_1006 v0 v1 v2 v3 v4 v5
  = coe
      seq (coe v0)
      (coe
         seq (coe v1)
         (coe
            seq (coe v2)
            (coe
               seq (coe v3)
               (coe
                  seq (coe v4)
                  (coe
                     seq (coe v5)
                     (coe
                        MAlonzo.Code.Data.Rational.Unnormalised.Base.C_'42''8801''42'_30))))))
-- Data.Rational.Unnormalised.Properties._.↥x
d_'8613'x_1024 ::
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> Integer
d_'8613'x_1024 v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
  = du_'8613'x_1024 v0
du_'8613'x_1024 :: Integer -> Integer
du_'8613'x_1024 v0 = coe v0
-- Data.Rational.Unnormalised.Properties._.↧x
d_'8615'x_1026 ::
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> Integer
d_'8615'x_1026 v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
  = du_'8615'x_1026 v0 v1
du_'8615'x_1026 :: Integer -> Integer -> Integer
du_'8615'x_1026 v0 v1
  = coe
      MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
      (coe
         MAlonzo.Code.Data.Rational.Unnormalised.Base.C_mkℚ'7512'_22
         (coe v0) (coe v1))
-- Data.Rational.Unnormalised.Properties._.↥y
d_'8613'y_1028 ::
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> Integer
d_'8613'y_1028 ~v0 ~v1 v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
  = du_'8613'y_1028 v2
du_'8613'y_1028 :: Integer -> Integer
du_'8613'y_1028 v0 = coe v0
-- Data.Rational.Unnormalised.Properties._.↧y
d_'8615'y_1030 ::
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> Integer
d_'8615'y_1030 ~v0 ~v1 v2 v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
  = du_'8615'y_1030 v2 v3
du_'8615'y_1030 :: Integer -> Integer -> Integer
du_'8615'y_1030 v0 v1
  = coe
      MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
      (coe
         MAlonzo.Code.Data.Rational.Unnormalised.Base.C_mkℚ'7512'_22
         (coe v0) (coe v1))
-- Data.Rational.Unnormalised.Properties._.↥u
d_'8613'u_1032 ::
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> Integer
d_'8613'u_1032 ~v0 ~v1 ~v2 ~v3 v4 ~v5 ~v6 ~v7 ~v8 ~v9
  = du_'8613'u_1032 v4
du_'8613'u_1032 :: Integer -> Integer
du_'8613'u_1032 v0 = coe v0
-- Data.Rational.Unnormalised.Properties._.↧u
d_'8615'u_1034 ::
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> Integer
d_'8615'u_1034 ~v0 ~v1 ~v2 ~v3 v4 v5 ~v6 ~v7 ~v8 ~v9
  = du_'8615'u_1034 v4 v5
du_'8615'u_1034 :: Integer -> Integer -> Integer
du_'8615'u_1034 v0 v1
  = coe
      MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
      (coe
         MAlonzo.Code.Data.Rational.Unnormalised.Base.C_mkℚ'7512'_22
         (coe v0) (coe v1))
-- Data.Rational.Unnormalised.Properties._.↥v
d_'8613'v_1036 ::
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> Integer
d_'8613'v_1036 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 ~v7 ~v8 ~v9
  = du_'8613'v_1036 v6
du_'8613'v_1036 :: Integer -> Integer
du_'8613'v_1036 v0 = coe v0
-- Data.Rational.Unnormalised.Properties._.↧v
d_'8615'v_1038 ::
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> Integer
d_'8615'v_1038 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 ~v8 ~v9
  = du_'8615'v_1038 v6 v7
du_'8615'v_1038 :: Integer -> Integer -> Integer
du_'8615'v_1038 v0 v1
  = coe
      MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
      (coe
         MAlonzo.Code.Data.Rational.Unnormalised.Base.C_mkℚ'7512'_22
         (coe v0) (coe v1))
-- Data.Rational.Unnormalised.Properties.+-congʳ
d_'43''45'cong'691'_1070 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8771'__24 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8771'__24
d_'43''45'cong'691'_1070 v0 v1 v2 v3
  = coe
      d_'43''45'cong_1006 (coe v2) (coe v2) (coe v0) (coe v1)
      (coe du_'8771''45'refl_166) (coe v3)
-- Data.Rational.Unnormalised.Properties.+-congˡ
d_'43''45'cong'737'_1078 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8771'__24 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8771'__24
d_'43''45'cong'737'_1078 v0 v1 v2 v3
  = coe
      d_'43''45'cong_1006 (coe v0) (coe v1) (coe v2) (coe v2) (coe v3)
      (coe du_'8771''45'refl_166)
-- Data.Rational.Unnormalised.Properties.+-assoc-↥
d_'43''45'assoc'45''8613'_1084 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'43''45'assoc'45''8613'_1084 = erased
-- Data.Rational.Unnormalised.Properties.+-assoc-↧
d_'43''45'assoc'45''8615'_1108 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'43''45'assoc'45''8615'_1108 = erased
-- Data.Rational.Unnormalised.Properties.+-assoc-≡
d_'43''45'assoc'45''8801'_1116 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'43''45'assoc'45''8801'_1116 = erased
-- Data.Rational.Unnormalised.Properties.+-assoc
d_'43''45'assoc_1124 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8771'__24
d_'43''45'assoc_1124 ~v0 ~v1 ~v2 = du_'43''45'assoc_1124
du_'43''45'assoc_1124 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8771'__24
du_'43''45'assoc_1124 = coe du_'8771''45'reflexive_168
-- Data.Rational.Unnormalised.Properties.+-comm-↥
d_'43''45'comm'45''8613'_1132 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'43''45'comm'45''8613'_1132 = erased
-- Data.Rational.Unnormalised.Properties.+-comm-↧
d_'43''45'comm'45''8615'_1138 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'43''45'comm'45''8615'_1138 = erased
-- Data.Rational.Unnormalised.Properties.+-comm-≡
d_'43''45'comm'45''8801'_1144 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'43''45'comm'45''8801'_1144 = erased
-- Data.Rational.Unnormalised.Properties.+-comm
d_'43''45'comm_1150 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8771'__24
d_'43''45'comm_1150 ~v0 ~v1 = du_'43''45'comm_1150
du_'43''45'comm_1150 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8771'__24
du_'43''45'comm_1150 = coe du_'8771''45'reflexive_168
-- Data.Rational.Unnormalised.Properties.+-identityˡ-↥
d_'43''45'identity'737''45''8613'_1156 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'43''45'identity'737''45''8613'_1156 = erased
-- Data.Rational.Unnormalised.Properties.+-identityˡ-↧
d_'43''45'identity'737''45''8615'_1164 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'43''45'identity'737''45''8615'_1164 = erased
-- Data.Rational.Unnormalised.Properties.+-identityˡ-≡
d_'43''45'identity'737''45''8801'_1168 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'43''45'identity'737''45''8801'_1168 = erased
-- Data.Rational.Unnormalised.Properties.+-identityˡ
d_'43''45'identity'737'_1172 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8771'__24
d_'43''45'identity'737'_1172 ~v0 = du_'43''45'identity'737'_1172
du_'43''45'identity'737'_1172 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8771'__24
du_'43''45'identity'737'_1172 = coe du_'8771''45'reflexive_168
-- Data.Rational.Unnormalised.Properties.+-identityʳ-≡
d_'43''45'identity'691''45''8801'_1176 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'43''45'identity'691''45''8801'_1176 = erased
-- Data.Rational.Unnormalised.Properties.+-identityʳ
d_'43''45'identity'691'_1178 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8771'__24
d_'43''45'identity'691'_1178 ~v0 = du_'43''45'identity'691'_1178
du_'43''45'identity'691'_1178 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8771'__24
du_'43''45'identity'691'_1178 = coe du_'8771''45'reflexive_168
-- Data.Rational.Unnormalised.Properties.+-identity-≡
d_'43''45'identity'45''8801'_1182 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'43''45'identity'45''8801'_1182
  = coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased
-- Data.Rational.Unnormalised.Properties.+-identity
d_'43''45'identity_1184 :: MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'43''45'identity_1184
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (\ v0 -> coe du_'43''45'identity'737'_1172)
      (\ v0 -> coe du_'43''45'identity'691'_1178)
-- Data.Rational.Unnormalised.Properties.+-inverseˡ
d_'43''45'inverse'737'_1186 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8771'__24
d_'43''45'inverse'737'_1186 v0
  = coe
      seq (coe v0)
      (coe
         MAlonzo.Code.Data.Rational.Unnormalised.Base.C_'42''8801''42'_30)
-- Data.Rational.Unnormalised.Properties.+-inverseʳ
d_'43''45'inverse'691'_1200 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8771'__24
d_'43''45'inverse'691'_1200 v0
  = coe
      seq (coe v0)
      (coe
         MAlonzo.Code.Data.Rational.Unnormalised.Base.C_'42''8801''42'_30)
-- Data.Rational.Unnormalised.Properties.+-inverse
d_'43''45'inverse_1214 :: MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'43''45'inverse_1214
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe d_'43''45'inverse'737'_1186) (coe d_'43''45'inverse'691'_1200)
-- Data.Rational.Unnormalised.Properties.+-cancelˡ
d_'43''45'cancel'737'_1222 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8771'__24 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8771'__24
d_'43''45'cancel'737'_1222 v0 v1 v2 v3
  = let v4
          = coe
              MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_eqRelation_238 in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__126
         (coe v4) (coe v1) (coe v2)
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8771''45''10216'_390
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8776''45'go_124
               (coe d_'8804''45'isPreorder_512)
               (coe d_'60''45'resp'45''8771'_780))
            (\ v5 v6 v7 -> coe du_'8771''45'sym_170 v7) v1
            (MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'43'__196
               (coe v1)
               (coe MAlonzo.Code.Data.Rational.Unnormalised.Base.d_0ℚ'7512'_108))
            v2
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8771''45''10216'_390
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8776''45'go_124
                  (coe d_'8804''45'isPreorder_512)
                  (coe d_'60''45'resp'45''8771'_780))
               (\ v5 v6 v7 -> coe du_'8771''45'sym_170 v7)
               (MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'43'__196
                  (coe v1)
                  (coe MAlonzo.Code.Data.Rational.Unnormalised.Base.d_0ℚ'7512'_108))
               (MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'43'__196
                  (coe v1)
                  (coe
                     MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'45'__208 (coe v0)
                     (coe v0)))
               v2
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8771''45''10216'_390
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8776''45'go_124
                     (coe d_'8804''45'isPreorder_512)
                     (coe d_'60''45'resp'45''8771'_780))
                  (\ v5 v6 v7 -> coe du_'8771''45'sym_170 v7)
                  (MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'43'__196
                     (coe v1)
                     (coe
                        MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'45'__208 (coe v0)
                        (coe v0)))
                  (MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'45'__208
                     (coe
                        MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'43'__196 (coe v1)
                        (coe v0))
                     (coe v0))
                  v2
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8771''45''10217'_388
                     (coe
                        MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8776''45'go_124
                        (coe d_'8804''45'isPreorder_512)
                        (coe d_'60''45'resp'45''8771'_780))
                     (MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'45'__208
                        (coe
                           MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'43'__196 (coe v1)
                           (coe v0))
                        (coe v0))
                     (MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'45'__208
                        (coe
                           MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'43'__196 (coe v0)
                           (coe v1))
                        (coe v0))
                     v2
                     (coe
                        MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8771''45''10217'_388
                        (coe
                           MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8776''45'go_124
                           (coe d_'8804''45'isPreorder_512)
                           (coe d_'60''45'resp'45''8771'_780))
                        (MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'45'__208
                           (coe
                              MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'43'__196 (coe v0)
                              (coe v1))
                           (coe v0))
                        (MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'45'__208
                           (coe
                              MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'43'__196 (coe v0)
                              (coe v2))
                           (coe v0))
                        v2
                        (coe
                           MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8771''45''10217'_388
                           (coe
                              MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8776''45'go_124
                              (coe d_'8804''45'isPreorder_512)
                              (coe d_'60''45'resp'45''8771'_780))
                           (MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'45'__208
                              (coe
                                 MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'43'__196 (coe v0)
                                 (coe v2))
                              (coe v0))
                           (MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'45'__208
                              (coe
                                 MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'43'__196 (coe v2)
                                 (coe v0))
                              (coe v0))
                           v2
                           (coe
                              MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8771''45''10217'_388
                              (coe
                                 MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8776''45'go_124
                                 (coe d_'8804''45'isPreorder_512)
                                 (coe d_'60''45'resp'45''8771'_780))
                              (MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'45'__208
                                 (coe
                                    MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'43'__196
                                    (coe v2) (coe v0))
                                 (coe v0))
                              (MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'43'__196
                                 (coe v2)
                                 (coe
                                    MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'45'__208
                                    (coe v0) (coe v0)))
                              v2
                              (coe
                                 MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8771''45''10217'_388
                                 (coe
                                    MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8776''45'go_124
                                    (coe d_'8804''45'isPreorder_512)
                                    (coe d_'60''45'resp'45''8771'_780))
                                 (MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'43'__196
                                    (coe v2)
                                    (coe
                                       MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'45'__208
                                       (coe v0) (coe v0)))
                                 (MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'43'__196
                                    (coe v2)
                                    (coe
                                       MAlonzo.Code.Data.Rational.Unnormalised.Base.d_0ℚ'7512'_108))
                                 v2
                                 (coe
                                    MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8771''45''10217'_388
                                    (coe
                                       MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8776''45'go_124
                                       (coe d_'8804''45'isPreorder_512)
                                       (coe d_'60''45'resp'45''8771'_780))
                                    (MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'43'__196
                                       (coe v2)
                                       (coe
                                          MAlonzo.Code.Data.Rational.Unnormalised.Base.d_0ℚ'7512'_108))
                                    v2 v2
                                    (coe
                                       MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                                       (coe
                                          MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_stop_166
                                          (coe d_'8804''45'isPreorder_512))
                                       (coe v2))
                                    (coe du_'43''45'identity'691'_1178))
                                 (d_'43''45'cong'691'_1070
                                    (coe
                                       MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'45'__208
                                       (coe v0) (coe v0))
                                    (coe
                                       MAlonzo.Code.Data.Rational.Unnormalised.Base.d_0ℚ'7512'_108)
                                    (coe v2) (coe d_'43''45'inverse'691'_1200 (coe v0))))
                              (coe du_'43''45'assoc_1124))
                           (d_'43''45'cong'737'_1078
                              (coe
                                 MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'43'__196 (coe v0)
                                 (coe v2))
                              (coe
                                 MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'43'__196 (coe v2)
                                 (coe v0))
                              (coe
                                 MAlonzo.Code.Data.Rational.Unnormalised.Base.d_'45'__190 (coe v0))
                              (coe du_'43''45'comm_1150)))
                        (d_'43''45'cong'737'_1078
                           (coe
                              MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'43'__196 (coe v0)
                              (coe v1))
                           (coe
                              MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'43'__196 (coe v0)
                              (coe v2))
                           (coe
                              MAlonzo.Code.Data.Rational.Unnormalised.Base.d_'45'__190 (coe v0))
                           (coe v3)))
                     (d_'43''45'cong'737'_1078
                        (coe
                           MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'43'__196 (coe v1)
                           (coe v0))
                        (coe
                           MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'43'__196 (coe v0)
                           (coe v1))
                        (coe
                           MAlonzo.Code.Data.Rational.Unnormalised.Base.d_'45'__190 (coe v0))
                        (coe du_'43''45'comm_1150)))
                  (coe du_'43''45'assoc_1124))
               (d_'43''45'cong'691'_1070
                  (coe
                     MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'45'__208 (coe v0)
                     (coe v0))
                  (coe MAlonzo.Code.Data.Rational.Unnormalised.Base.d_0ℚ'7512'_108)
                  (coe v1) (coe d_'43''45'inverse'691'_1200 (coe v0))))
            (coe du_'43''45'identity'691'_1178)))
-- Data.Rational.Unnormalised.Properties.+-cancelʳ
d_'43''45'cancel'691'_1242 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8771'__24 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8771'__24
d_'43''45'cancel'691'_1242 v0 v1 v2 v3
  = coe
      d_'43''45'cancel'737'_1222 (coe v0) (coe v1) (coe v2)
      (let v4
             = coe
                 MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_eqRelation_238 in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__126
            (coe v4)
            (coe
               MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'43'__196 (coe v0)
               (coe v1))
            (coe
               MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'43'__196 (coe v0)
               (coe v2))
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8771''45''10217'_388
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8776''45'go_124
                  (coe d_'8804''45'isPreorder_512)
                  (coe d_'60''45'resp'45''8771'_780))
               (MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'43'__196
                  (coe v0) (coe v1))
               (MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'43'__196
                  (coe v1) (coe v0))
               (MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'43'__196
                  (coe v0) (coe v2))
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8771''45''10217'_388
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8776''45'go_124
                     (coe d_'8804''45'isPreorder_512)
                     (coe d_'60''45'resp'45''8771'_780))
                  (MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'43'__196
                     (coe v1) (coe v0))
                  (MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'43'__196
                     (coe v2) (coe v0))
                  (MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'43'__196
                     (coe v0) (coe v2))
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8771''45''10217'_388
                     (coe
                        MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8776''45'go_124
                        (coe d_'8804''45'isPreorder_512)
                        (coe d_'60''45'resp'45''8771'_780))
                     (MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'43'__196
                        (coe v2) (coe v0))
                     (MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'43'__196
                        (coe v0) (coe v2))
                     (MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'43'__196
                        (coe v0) (coe v2))
                     (coe
                        MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                        (coe
                           MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_stop_166
                           (coe d_'8804''45'isPreorder_512))
                        (coe
                           MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'43'__196 (coe v0)
                           (coe v2)))
                     (coe du_'43''45'comm_1150))
                  v3)
               (coe du_'43''45'comm_1150))))
-- Data.Rational.Unnormalised.Properties.p+p≃0⇒p≃0
d_p'43'p'8771'0'8658'p'8771'0_1258 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8771'__24 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8771'__24
d_p'43'p'8771'0'8658'p'8771'0_1258 v0 v1
  = coe
      seq (coe v0)
      (coe
         seq (coe v1)
         (coe
            MAlonzo.Code.Data.Rational.Unnormalised.Base.C_'42''8801''42'_30))
-- Data.Rational.Unnormalised.Properties.neg-distrib-+
d_neg'45'distrib'45''43'_1264 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_neg'45'distrib'45''43'_1264 = erased
-- Data.Rational.Unnormalised.Properties.p≃-p⇒p≃0
d_p'8771''45'p'8658'p'8771'0_1276 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8771'__24 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8771'__24
d_p'8771''45'p'8658'p'8771'0_1276 v0 v1
  = coe
      d_p'43'p'8771'0'8658'p'8771'0_1258 (coe v0)
      (let v2
             = coe
                 MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_eqRelation_238 in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__126
            (coe v2)
            (coe
               MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'43'__196 (coe v0)
               (coe v0))
            (coe MAlonzo.Code.Data.Rational.Unnormalised.Base.d_0ℚ'7512'_108)
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8771''45''10217'_388
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8776''45'go_124
                  (coe d_'8804''45'isPreorder_512)
                  (coe d_'60''45'resp'45''8771'_780))
               (MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'43'__196
                  (coe v0) (coe v0))
               (MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'45'__208
                  (coe v0) (coe v0))
               MAlonzo.Code.Data.Rational.Unnormalised.Base.d_0ℚ'7512'_108
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8771''45''10217'_388
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8776''45'go_124
                     (coe d_'8804''45'isPreorder_512)
                     (coe d_'60''45'resp'45''8771'_780))
                  (MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'45'__208
                     (coe v0) (coe v0))
                  MAlonzo.Code.Data.Rational.Unnormalised.Base.d_0ℚ'7512'_108
                  MAlonzo.Code.Data.Rational.Unnormalised.Base.d_0ℚ'7512'_108
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                     (coe
                        MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_stop_166
                        (coe d_'8804''45'isPreorder_512))
                     (coe MAlonzo.Code.Data.Rational.Unnormalised.Base.d_0ℚ'7512'_108))
                  (d_'43''45'inverse'691'_1200 (coe v0)))
               (d_'43''45'cong'691'_1070
                  (coe v0)
                  (coe
                     MAlonzo.Code.Data.Rational.Unnormalised.Base.d_'45'__190 (coe v0))
                  (coe v0) (coe v1)))))
-- Data.Rational.Unnormalised.Properties.lemma
d_lemma_1292 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_lemma_1292 = erased
-- Data.Rational.Unnormalised.Properties.+-monoʳ-≤
d_'43''45'mono'691''45''8804'_1314 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8804'__38 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8804'__38
d_'43''45'mono'691''45''8804'_1314 v0 v1 v2 v3
  = case coe v0 of
      MAlonzo.Code.Data.Rational.Unnormalised.Base.C_mkℚ'7512'_22 v4 v5
        -> case coe v1 of
             MAlonzo.Code.Data.Rational.Unnormalised.Base.C_mkℚ'7512'_22 v6 v7
               -> case coe v2 of
                    MAlonzo.Code.Data.Rational.Unnormalised.Base.C_mkℚ'7512'_22 v8 v9
                      -> case coe v3 of
                           MAlonzo.Code.Data.Rational.Unnormalised.Base.C_'42''8804''42'_44 v12
                             -> coe
                                  MAlonzo.Code.Data.Rational.Unnormalised.Base.C_'42''8804''42'_44
                                  (coe
                                     MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
                                     (coe
                                        MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_start_96
                                        (coe
                                           MAlonzo.Code.Data.Integer.Properties.d_'8804''45'isPreorder_2822)
                                        (\ v13 v14 v15 ->
                                           coe
                                             MAlonzo.Code.Data.Integer.Properties.du_'60''8658''8804'_2868
                                             v15))
                                     (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                        (coe
                                           MAlonzo.Code.Data.Rational.Unnormalised.Base.d_numerator_14
                                           (coe
                                              MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                                              (MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'43'__196
                                                 (coe v0))
                                              (\ v13 v14 -> v13) v1 v2))
                                        (coe
                                           MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                           (coe
                                              MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                                              (\ v13 v14 -> v14)
                                              (MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'43'__196
                                                 (coe v0))
                                              v1 v2)))
                                     (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                        (coe
                                           MAlonzo.Code.Data.Rational.Unnormalised.Base.d_numerator_14
                                           (coe
                                              MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                                              (\ v13 v14 -> v14)
                                              (MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'43'__196
                                                 (coe v0))
                                              v1 v2))
                                        (coe
                                           MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                           (coe
                                              MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                                              (MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'43'__196
                                                 (coe v0))
                                              (\ v13 v14 -> v13) v1 v2)))
                                     (coe
                                        MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_436
                                        (\ v13 v14 v15 v16 v17 -> v17)
                                        (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                           (coe
                                              MAlonzo.Code.Data.Rational.Unnormalised.Base.d_numerator_14
                                              (coe
                                                 MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'43'__196
                                                 (coe v0) (coe v1)))
                                           (coe
                                              MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                              (coe
                                                 MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'43'__196
                                                 (coe v0) (coe v2))))
                                        (MAlonzo.Code.Data.Integer.Base.d__'43'__276
                                           (coe
                                              MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                              (coe du_r'8322'_1328 (coe v4) (coe v5))
                                              (coe
                                                 MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                 (coe
                                                    MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                                    (coe v1))
                                                 (coe
                                                    MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                                    (coe v2))))
                                           (coe
                                              MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                              (coe
                                                 MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                 (coe
                                                    MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                                    (coe v0))
                                                 (coe
                                                    MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                                    (coe v0)))
                                              (coe
                                                 MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                 (coe v6)
                                                 (coe
                                                    MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                                    (coe v2)))))
                                        (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                           (coe
                                              MAlonzo.Code.Data.Rational.Unnormalised.Base.d_numerator_14
                                              (coe
                                                 MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                                                 (\ v13 v14 -> v14)
                                                 (MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'43'__196
                                                    (coe v0))
                                                 v1 v2))
                                           (coe
                                              MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                              (coe
                                                 MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                                                 (MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'43'__196
                                                    (coe v0))
                                                 (\ v13 v14 -> v13) v1 v2)))
                                        (coe
                                           MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8804'_308
                                           (coe
                                              MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8804''45'go_138
                                              (coe
                                                 MAlonzo.Code.Data.Integer.Properties.d_'8804''45'isPreorder_2822)
                                              (\ v13 v14 v15 v16 v17 ->
                                                 coe
                                                   MAlonzo.Code.Data.Integer.Properties.du_'8804''45''60''45'trans_2980
                                                   v16 v17))
                                           (MAlonzo.Code.Data.Integer.Base.d__'43'__276
                                              (coe
                                                 MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                 (coe du_r'8322'_1328 (coe v4) (coe v5))
                                                 (coe
                                                    MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                    (coe
                                                       MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                                       (coe v1))
                                                    (coe
                                                       MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                                       (coe v2))))
                                              (coe
                                                 MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                 (coe
                                                    MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                    (coe
                                                       MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                                       (coe v0))
                                                    (coe
                                                       MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                                       (coe v0)))
                                                 (coe
                                                    MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                    (coe v6)
                                                    (coe
                                                       MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                                       (coe v2)))))
                                           (MAlonzo.Code.Data.Integer.Base.d__'43'__276
                                              (coe
                                                 MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                 (coe du_r'8322'_1328 (coe v4) (coe v5))
                                                 (coe
                                                    MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                    (coe
                                                       MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                                       (coe v2))
                                                    (coe
                                                       MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                                       (coe v1))))
                                              (coe
                                                 MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                 (coe
                                                    MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                    (coe
                                                       MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                                       (coe v0))
                                                    (coe
                                                       MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                                       (coe v0)))
                                                 (coe
                                                    MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                    (coe v8)
                                                    (coe
                                                       MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                                       (coe v1)))))
                                           (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                              (coe
                                                 MAlonzo.Code.Data.Rational.Unnormalised.Base.d_numerator_14
                                                 (coe
                                                    MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                                                    (\ v13 v14 -> v14)
                                                    (MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'43'__196
                                                       (coe v0))
                                                    v1 v2))
                                              (coe
                                                 MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                                 (coe
                                                    MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                                                    (MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'43'__196
                                                       (coe v0))
                                                    (\ v13 v14 -> v13) v1 v2)))
                                           (coe
                                              MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_436
                                              (\ v13 v14 v15 v16 v17 -> v17)
                                              (MAlonzo.Code.Data.Integer.Base.d__'43'__276
                                                 (coe
                                                    MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                    (coe du_r'8322'_1328 (coe v4) (coe v5))
                                                    (coe
                                                       MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                       (coe
                                                          MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                                          (coe v2))
                                                       (coe
                                                          MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                                          (coe v1))))
                                                 (coe
                                                    MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                    (coe
                                                       MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                       (coe
                                                          MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                                          (coe v0))
                                                       (coe
                                                          MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                                          (coe v0)))
                                                    (coe
                                                       MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                       (coe v8)
                                                       (coe
                                                          MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                                          (coe v1)))))
                                              (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                 (coe
                                                    MAlonzo.Code.Data.Rational.Unnormalised.Base.d_numerator_14
                                                    (coe
                                                       MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'43'__196
                                                       (coe v0) (coe v2)))
                                                 (coe
                                                    MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                                    (coe
                                                       MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'43'__196
                                                       (coe v0) (coe v1))))
                                              (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                 (coe
                                                    MAlonzo.Code.Data.Rational.Unnormalised.Base.d_numerator_14
                                                    (coe
                                                       MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                                                       (\ v13 v14 -> v14)
                                                       (MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'43'__196
                                                          (coe v0))
                                                       v1 v2))
                                                 (coe
                                                    MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                                    (coe
                                                       MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                                                       (MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'43'__196
                                                          (coe v0))
                                                       (\ v13 v14 -> v13) v1 v2)))
                                              (let v13
                                                     = MAlonzo.Code.Data.Integer.Properties.d_'8804''45'isPreorder_2822 in
                                               coe
                                                 (coe
                                                    MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                                                    (coe
                                                       MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_stop_166
                                                       (coe v13))
                                                    (coe
                                                       MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                       (coe
                                                          MAlonzo.Code.Data.Rational.Unnormalised.Base.d_numerator_14
                                                          (coe
                                                             MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'43'__196
                                                             (coe v0) (coe v2)))
                                                       (coe
                                                          MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                                          (coe
                                                             MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'43'__196
                                                             (coe v0) (coe v1))))))
                                              erased)
                                           (d_leq_1330
                                              (coe v4) (coe v5) (coe v6) (coe v7) (coe v8) (coe v9)
                                              (coe v12)))
                                        erased))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Rational.Unnormalised.Properties._.r₂
d_r'8322'_1328 ::
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Data.Integer.Base.T__'8804'__26 -> Integer
d_r'8322'_1328 v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6 = du_r'8322'_1328 v0 v1
du_r'8322'_1328 :: Integer -> Integer -> Integer
du_r'8322'_1328 v0 v1
  = coe
      MAlonzo.Code.Data.Integer.Base.d__'42'__308 (coe v0)
      (coe
         MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
         (coe
            MAlonzo.Code.Data.Rational.Unnormalised.Base.C_mkℚ'7512'_22
            (coe v0) (coe v1)))
-- Data.Rational.Unnormalised.Properties._.leq
d_leq_1330 ::
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26 ->
  MAlonzo.Code.Data.Integer.Base.T__'8804'__26
d_leq_1330 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Data.Integer.Properties.d_'43''45'mono'45''8804'_4546
      (coe
         MAlonzo.Code.Data.Integer.Base.d__'42'__308
         (coe du_r'8322'_1328 (coe v0) (coe v1))
         (coe
            MAlonzo.Code.Data.Integer.Base.d__'42'__308
            (coe
               MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
               (coe
                  MAlonzo.Code.Data.Rational.Unnormalised.Base.C_mkℚ'7512'_22
                  (coe v2) (coe v3)))
            (coe
               MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
               (coe
                  MAlonzo.Code.Data.Rational.Unnormalised.Base.C_mkℚ'7512'_22
                  (coe v4) (coe v5)))))
      (coe
         MAlonzo.Code.Data.Integer.Base.d__'42'__308
         (coe du_r'8322'_1328 (coe v0) (coe v1))
         (coe
            MAlonzo.Code.Data.Integer.Base.d__'42'__308
            (coe
               MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
               (coe
                  MAlonzo.Code.Data.Rational.Unnormalised.Base.C_mkℚ'7512'_22
                  (coe v4) (coe v5)))
            (coe
               MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
               (coe
                  MAlonzo.Code.Data.Rational.Unnormalised.Base.C_mkℚ'7512'_22
                  (coe v2) (coe v3)))))
      (coe
         MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
         (MAlonzo.Code.Data.Integer.Base.d__'42'__308
            (coe
               MAlonzo.Code.Data.Integer.Base.d__'42'__308
               (coe
                  MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                  (coe
                     MAlonzo.Code.Data.Rational.Unnormalised.Base.C_mkℚ'7512'_22
                     (coe v0) (coe v1)))
               (coe
                  MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                  (coe
                     MAlonzo.Code.Data.Rational.Unnormalised.Base.C_mkℚ'7512'_22
                     (coe v0) (coe v1)))))
         (\ v7 v8 -> v7)
         (MAlonzo.Code.Data.Integer.Base.d__'42'__308
            (coe v2)
            (coe
               MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
               (coe
                  MAlonzo.Code.Data.Rational.Unnormalised.Base.C_mkℚ'7512'_22
                  (coe v4) (coe v5))))
         (MAlonzo.Code.Data.Integer.Base.d__'42'__308
            (coe v4)
            (coe
               MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
               (coe
                  MAlonzo.Code.Data.Rational.Unnormalised.Base.C_mkℚ'7512'_22
                  (coe v2) (coe v3)))))
      (coe
         MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
         (\ v7 v8 -> v8)
         (MAlonzo.Code.Data.Integer.Base.d__'42'__308
            (coe
               MAlonzo.Code.Data.Integer.Base.d__'42'__308
               (coe
                  MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                  (coe
                     MAlonzo.Code.Data.Rational.Unnormalised.Base.C_mkℚ'7512'_22
                     (coe v0) (coe v1)))
               (coe
                  MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                  (coe
                     MAlonzo.Code.Data.Rational.Unnormalised.Base.C_mkℚ'7512'_22
                     (coe v0) (coe v1)))))
         (MAlonzo.Code.Data.Integer.Base.d__'42'__308
            (coe v2)
            (coe
               MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
               (coe
                  MAlonzo.Code.Data.Rational.Unnormalised.Base.C_mkℚ'7512'_22
                  (coe v4) (coe v5))))
         (MAlonzo.Code.Data.Integer.Base.d__'42'__308
            (coe v4)
            (coe
               MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
               (coe
                  MAlonzo.Code.Data.Rational.Unnormalised.Base.C_mkℚ'7512'_22
                  (coe v2) (coe v3)))))
      (coe
         MAlonzo.Code.Data.Integer.Properties.du_'8804''45'reflexive_2744
         (coe
            MAlonzo.Code.Data.Integer.Base.d__'42'__308
            (coe du_r'8322'_1328 (coe v0) (coe v1))
            (coe
               MAlonzo.Code.Data.Integer.Base.d__'42'__308
               (coe
                  MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                  (coe
                     MAlonzo.Code.Data.Rational.Unnormalised.Base.C_mkℚ'7512'_22
                     (coe v2) (coe v3)))
               (coe
                  MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                  (coe
                     MAlonzo.Code.Data.Rational.Unnormalised.Base.C_mkℚ'7512'_22
                     (coe v4) (coe v5))))))
      (coe
         MAlonzo.Code.Data.Integer.Properties.du_'42''45'mono'737''45''8804''45'nonNeg_6076
         (MAlonzo.Code.Data.Integer.Base.d__'42'__308
            (coe
               MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
               (coe
                  MAlonzo.Code.Data.Rational.Unnormalised.Base.C_mkℚ'7512'_22
                  (coe v0) (coe v1)))
            (coe
               MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
               (coe
                  MAlonzo.Code.Data.Rational.Unnormalised.Base.C_mkℚ'7512'_22
                  (coe v0) (coe v1))))
         (MAlonzo.Code.Data.Integer.Base.d__'42'__308
            (coe v2)
            (coe
               MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
               (coe
                  MAlonzo.Code.Data.Rational.Unnormalised.Base.C_mkℚ'7512'_22
                  (coe v4) (coe v5))))
         (MAlonzo.Code.Data.Integer.Base.d__'42'__308
            (coe v4)
            (coe
               MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
               (coe
                  MAlonzo.Code.Data.Rational.Unnormalised.Base.C_mkℚ'7512'_22
                  (coe v2) (coe v3))))
         v6)
-- Data.Rational.Unnormalised.Properties.+-monoˡ-≤
d_'43''45'mono'737''45''8804'_1334 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8804'__38 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8804'__38
d_'43''45'mono'737''45''8804'_1334 v0 v1 v2
  = coe d_'43''45'mono'691''45''8804'_1314 (coe v0) (coe v1) (coe v2)
-- Data.Rational.Unnormalised.Properties.+-mono-≤
d_'43''45'mono'45''8804'_1350 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8804'__38 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8804'__38 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8804'__38
d_'43''45'mono'45''8804'_1350 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Relation.Binary.Consequences.du_mono'737''8743'mono'691''8658'mono'8322'_362
      (coe MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'43'__196)
      (coe d_'8804''45'trans_440)
      (coe d_'43''45'mono'691''45''8804'_1314)
      (coe d_'43''45'mono'737''45''8804'_1334) (coe v0) (coe v1) (coe v2)
      (coe v3)
-- Data.Rational.Unnormalised.Properties.p≤q⇒p≤r+q
d_p'8804'q'8658'p'8804'r'43'q_1356 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Integer.Base.T_NonNegative_144 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8804'__38 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8804'__38
d_p'8804'q'8658'p'8804'r'43'q_1356 v0 v1 v2 ~v3 v4
  = du_p'8804'q'8658'p'8804'r'43'q_1356 v0 v1 v2 v4
du_p'8804'q'8658'p'8804'r'43'q_1356 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8804'__38 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8804'__38
du_p'8804'q'8658'p'8804'r'43'q_1356 v0 v1 v2 v3
  = coe
      d_'43''45'mono'45''8804'_1350
      MAlonzo.Code.Data.Rational.Unnormalised.Base.d_0ℚ'7512'_108 v2 v0
      v1 (coe du_nonNegative'8315''185'_932 (coe v2)) v3
-- Data.Rational.Unnormalised.Properties.p≤q+p
d_p'8804'q'43'p_1374 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Integer.Base.T_NonNegative_144 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8804'__38
d_p'8804'q'43'p_1374 v0 v1 ~v2 = du_p'8804'q'43'p_1374 v0 v1
du_p'8804'q'43'p_1374 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8804'__38
du_p'8804'q'43'p_1374 v0 v1
  = coe
      du_p'8804'q'8658'p'8804'r'43'q_1356 (coe v0) (coe v0) (coe v1)
      (coe d_'8804''45'refl_436 (coe v0))
-- Data.Rational.Unnormalised.Properties.p≤p+q
d_p'8804'p'43'q_1386 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Integer.Base.T_NonNegative_144 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8804'__38
d_p'8804'p'43'q_1386 v0 v1 ~v2 = du_p'8804'p'43'q_1386 v0 v1
du_p'8804'p'43'q_1386 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8804'__38
du_p'8804'p'43'q_1386 v0 v1
  = coe du_p'8804'q'43'p_1374 (coe v0) (coe v1)
-- Data.Rational.Unnormalised.Properties.+-monoʳ-<
d_'43''45'mono'691''45''60'_1396 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'60'__46 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'60'__46
d_'43''45'mono'691''45''60'_1396 v0 v1 v2 v3
  = case coe v0 of
      MAlonzo.Code.Data.Rational.Unnormalised.Base.C_mkℚ'7512'_22 v4 v5
        -> case coe v1 of
             MAlonzo.Code.Data.Rational.Unnormalised.Base.C_mkℚ'7512'_22 v6 v7
               -> case coe v2 of
                    MAlonzo.Code.Data.Rational.Unnormalised.Base.C_mkℚ'7512'_22 v8 v9
                      -> case coe v3 of
                           MAlonzo.Code.Data.Rational.Unnormalised.Base.C_'42''60''42'_52 v12
                             -> coe
                                  MAlonzo.Code.Data.Rational.Unnormalised.Base.C_'42''60''42'_52
                                  (let v13
                                         = coe
                                             MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_strictRelation_202 in
                                   coe
                                     (coe
                                        MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__126
                                        (coe v13)
                                        (coe
                                           MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                           (coe
                                              MAlonzo.Code.Data.Rational.Unnormalised.Base.d_numerator_14
                                              (coe
                                                 MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'43'__196
                                                 (coe v0) (coe v1)))
                                           (coe
                                              MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                              (coe
                                                 MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'43'__196
                                                 (coe v0) (coe v2))))
                                        (coe
                                           MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                           (coe
                                              MAlonzo.Code.Data.Rational.Unnormalised.Base.d_numerator_14
                                              (coe
                                                 MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'43'__196
                                                 (coe v0) (coe v2)))
                                           (coe
                                              MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                              (coe
                                                 MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'43'__196
                                                 (coe v0) (coe v1))))
                                        (coe
                                           MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_436
                                           (\ v14 v15 v16 v17 v18 -> v18)
                                           (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                              (coe
                                                 MAlonzo.Code.Data.Rational.Unnormalised.Base.d_numerator_14
                                                 (coe
                                                    MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'43'__196
                                                    (coe v0) (coe v1)))
                                              (coe
                                                 MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                                 (coe
                                                    MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'43'__196
                                                    (coe v0) (coe v2))))
                                           (MAlonzo.Code.Data.Integer.Base.d__'43'__276
                                              (coe
                                                 MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                 (coe du_'8613'r'8615'r_1410 (coe v4) (coe v5))
                                                 (coe
                                                    MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                    (coe
                                                       MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                                       (coe v1))
                                                    (coe
                                                       MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                                       (coe v2))))
                                              (coe
                                                 MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                 (coe du_'8615'r'8615'r_1412 (coe v4) (coe v5))
                                                 (coe
                                                    MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                    (coe v6)
                                                    (coe
                                                       MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                                       (coe v2)))))
                                           (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                              (coe
                                                 MAlonzo.Code.Data.Rational.Unnormalised.Base.d_numerator_14
                                                 (coe
                                                    MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'43'__196
                                                    (coe v0) (coe v2)))
                                              (coe
                                                 MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                                 (coe
                                                    MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'43'__196
                                                    (coe v0) (coe v1))))
                                           (coe
                                              MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''60'_312
                                              (coe
                                                 MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'60''45'go_152
                                                 (\ v14 v15 v16 v17 v18 ->
                                                    coe
                                                      MAlonzo.Code.Data.Integer.Properties.du_'60''45'trans_3008
                                                      v17 v18)
                                                 (coe
                                                    MAlonzo.Code.Relation.Binary.PropositionalEquality.Core.du_resp'8322'_160)
                                                 (\ v14 v15 v16 v17 v18 ->
                                                    coe
                                                      MAlonzo.Code.Data.Integer.Properties.du_'60''45''8804''45'trans_2994
                                                      v17 v18))
                                              (MAlonzo.Code.Data.Integer.Base.d__'43'__276
                                                 (coe
                                                    MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                    (coe du_'8613'r'8615'r_1410 (coe v4) (coe v5))
                                                    (coe
                                                       MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                       (coe
                                                          MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                                          (coe v1))
                                                       (coe
                                                          MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                                          (coe v2))))
                                                 (coe
                                                    MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                    (coe du_'8615'r'8615'r_1412 (coe v4) (coe v5))
                                                    (coe
                                                       MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                       (coe v6)
                                                       (coe
                                                          MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                                          (coe v2)))))
                                              (MAlonzo.Code.Data.Integer.Base.d__'43'__276
                                                 (coe
                                                    MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                    (coe du_'8613'r'8615'r_1410 (coe v4) (coe v5))
                                                    (coe
                                                       MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                       (coe
                                                          MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                                          (coe v2))
                                                       (coe
                                                          MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                                          (coe v1))))
                                                 (coe
                                                    MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                    (coe du_'8615'r'8615'r_1412 (coe v4) (coe v5))
                                                    (coe
                                                       MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                       (coe v8)
                                                       (coe
                                                          MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                                          (coe v1)))))
                                              (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                 (coe
                                                    MAlonzo.Code.Data.Rational.Unnormalised.Base.d_numerator_14
                                                    (coe
                                                       MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'43'__196
                                                       (coe v0) (coe v2)))
                                                 (coe
                                                    MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                                    (coe
                                                       MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'43'__196
                                                       (coe v0) (coe v1))))
                                              (coe
                                                 MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10216'_448
                                                 (\ v14 v15 v16 v17 v18 -> v18)
                                                 (MAlonzo.Code.Data.Integer.Base.d__'43'__276
                                                    (coe
                                                       MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                       (coe
                                                          du_'8613'r'8615'r_1410 (coe v4) (coe v5))
                                                       (coe
                                                          MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                          (coe
                                                             MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                                             (coe v2))
                                                          (coe
                                                             MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                                             (coe v1))))
                                                    (coe
                                                       MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                       (coe
                                                          du_'8615'r'8615'r_1412 (coe v4) (coe v5))
                                                       (coe
                                                          MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                          (coe v8)
                                                          (coe
                                                             MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                                             (coe v1)))))
                                                 (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                    (coe
                                                       MAlonzo.Code.Data.Rational.Unnormalised.Base.d_numerator_14
                                                       (coe
                                                          MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'43'__196
                                                          (coe v0) (coe v2)))
                                                    (coe
                                                       MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                                       (coe
                                                          MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'43'__196
                                                          (coe v0) (coe v1))))
                                                 (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                    (coe
                                                       MAlonzo.Code.Data.Rational.Unnormalised.Base.d_numerator_14
                                                       (coe
                                                          MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'43'__196
                                                          (coe v0) (coe v2)))
                                                    (coe
                                                       MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                                       (coe
                                                          MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'43'__196
                                                          (coe v0) (coe v1))))
                                                 (coe
                                                    MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                                                    (coe
                                                       MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_stop_166
                                                       (coe
                                                          MAlonzo.Code.Data.Integer.Properties.d_'8804''45'isPreorder_2822))
                                                    (coe
                                                       MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                       (coe
                                                          MAlonzo.Code.Data.Rational.Unnormalised.Base.d_numerator_14
                                                          (coe
                                                             MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'43'__196
                                                             (coe v0) (coe v2)))
                                                       (coe
                                                          MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                                          (coe
                                                             MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'43'__196
                                                             (coe v0) (coe v1)))))
                                                 erased)
                                              (d_leq_1414
                                                 (coe v4) (coe v5) (coe v6) (coe v7) (coe v8)
                                                 (coe v9) (coe v12)))
                                           erased)))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Rational.Unnormalised.Properties._.↥r↧r
d_'8613'r'8615'r_1410 ::
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Data.Integer.Base.T__'60'__50 -> Integer
d_'8613'r'8615'r_1410 v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6
  = du_'8613'r'8615'r_1410 v0 v1
du_'8613'r'8615'r_1410 :: Integer -> Integer -> Integer
du_'8613'r'8615'r_1410 v0 v1
  = coe
      MAlonzo.Code.Data.Integer.Base.d__'42'__308 (coe v0)
      (coe
         MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
         (coe
            MAlonzo.Code.Data.Rational.Unnormalised.Base.C_mkℚ'7512'_22
            (coe v0) (coe v1)))
-- Data.Rational.Unnormalised.Properties._.↧r↧r
d_'8615'r'8615'r_1412 ::
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Data.Integer.Base.T__'60'__50 -> Integer
d_'8615'r'8615'r_1412 v0 v1 ~v2 ~v3 ~v4 ~v5 ~v6
  = du_'8615'r'8615'r_1412 v0 v1
du_'8615'r'8615'r_1412 :: Integer -> Integer -> Integer
du_'8615'r'8615'r_1412 v0 v1
  = coe
      MAlonzo.Code.Data.Integer.Base.d__'42'__308
      (coe
         MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
         (coe
            MAlonzo.Code.Data.Rational.Unnormalised.Base.C_mkℚ'7512'_22
            (coe v0) (coe v1)))
      (coe
         MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
         (coe
            MAlonzo.Code.Data.Rational.Unnormalised.Base.C_mkℚ'7512'_22
            (coe v0) (coe v1)))
-- Data.Rational.Unnormalised.Properties._.leq
d_leq_1414 ::
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50 ->
  MAlonzo.Code.Data.Integer.Base.T__'60'__50
d_leq_1414 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Data.Integer.Properties.d_'43''45'mono'45''8804''45''60'_4662
      (coe
         MAlonzo.Code.Data.Integer.Base.d__'42'__308
         (coe du_'8613'r'8615'r_1410 (coe v0) (coe v1))
         (coe
            MAlonzo.Code.Data.Integer.Base.d__'42'__308
            (coe
               MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
               (coe
                  MAlonzo.Code.Data.Rational.Unnormalised.Base.C_mkℚ'7512'_22
                  (coe v2) (coe v3)))
            (coe
               MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
               (coe
                  MAlonzo.Code.Data.Rational.Unnormalised.Base.C_mkℚ'7512'_22
                  (coe v4) (coe v5)))))
      (coe
         MAlonzo.Code.Data.Integer.Base.d__'42'__308
         (coe du_'8613'r'8615'r_1410 (coe v0) (coe v1))
         (coe
            MAlonzo.Code.Data.Integer.Base.d__'42'__308
            (coe
               MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
               (coe
                  MAlonzo.Code.Data.Rational.Unnormalised.Base.C_mkℚ'7512'_22
                  (coe v4) (coe v5)))
            (coe
               MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
               (coe
                  MAlonzo.Code.Data.Rational.Unnormalised.Base.C_mkℚ'7512'_22
                  (coe v2) (coe v3)))))
      (coe
         MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
         (MAlonzo.Code.Data.Integer.Base.d__'42'__308
            (coe du_'8615'r'8615'r_1412 (coe v0) (coe v1)))
         (\ v7 v8 -> v7)
         (MAlonzo.Code.Data.Integer.Base.d__'42'__308
            (coe v2)
            (coe
               MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
               (coe
                  MAlonzo.Code.Data.Rational.Unnormalised.Base.C_mkℚ'7512'_22
                  (coe v4) (coe v5))))
         (MAlonzo.Code.Data.Integer.Base.d__'42'__308
            (coe v4)
            (coe
               MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
               (coe
                  MAlonzo.Code.Data.Rational.Unnormalised.Base.C_mkℚ'7512'_22
                  (coe v2) (coe v3)))))
      (coe
         MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
         (\ v7 v8 -> v8)
         (MAlonzo.Code.Data.Integer.Base.d__'42'__308
            (coe du_'8615'r'8615'r_1412 (coe v0) (coe v1)))
         (MAlonzo.Code.Data.Integer.Base.d__'42'__308
            (coe v2)
            (coe
               MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
               (coe
                  MAlonzo.Code.Data.Rational.Unnormalised.Base.C_mkℚ'7512'_22
                  (coe v4) (coe v5))))
         (MAlonzo.Code.Data.Integer.Base.d__'42'__308
            (coe v4)
            (coe
               MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
               (coe
                  MAlonzo.Code.Data.Rational.Unnormalised.Base.C_mkℚ'7512'_22
                  (coe v2) (coe v3)))))
      (coe
         MAlonzo.Code.Data.Integer.Properties.du_'8804''45'reflexive_2744
         (coe
            MAlonzo.Code.Data.Integer.Base.d__'42'__308
            (coe du_'8613'r'8615'r_1410 (coe v0) (coe v1))
            (coe
               MAlonzo.Code.Data.Integer.Base.d__'42'__308
               (coe
                  MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                  (coe
                     MAlonzo.Code.Data.Rational.Unnormalised.Base.C_mkℚ'7512'_22
                     (coe v2) (coe v3)))
               (coe
                  MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                  (coe
                     MAlonzo.Code.Data.Rational.Unnormalised.Base.C_mkℚ'7512'_22
                     (coe v4) (coe v5))))))
      (coe
         MAlonzo.Code.Data.Integer.Properties.du_'42''45'mono'737''45''60''45'pos_6194
         (coe du_'8615'r'8615'r_1412 (coe v0) (coe v1))
         (coe
            MAlonzo.Code.Data.Integer.Base.d__'42'__308 (coe v2)
            (coe
               MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
               (coe
                  MAlonzo.Code.Data.Rational.Unnormalised.Base.C_mkℚ'7512'_22
                  (coe v4) (coe v5))))
         (coe
            MAlonzo.Code.Data.Integer.Base.d__'42'__308 (coe v4)
            (coe
               MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
               (coe
                  MAlonzo.Code.Data.Rational.Unnormalised.Base.C_mkℚ'7512'_22
                  (coe v2) (coe v3))))
         (coe v6))
-- Data.Rational.Unnormalised.Properties.+-monoˡ-<
d_'43''45'mono'737''45''60'_1418 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'60'__46 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'60'__46
d_'43''45'mono'737''45''60'_1418 v0 v1 v2
  = coe d_'43''45'mono'691''45''60'_1396 (coe v0) (coe v1) (coe v2)
-- Data.Rational.Unnormalised.Properties.+-mono-<
d_'43''45'mono'45''60'_1434 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'60'__46 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'60'__46 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'60'__46
d_'43''45'mono'45''60'_1434 v0 v1 v2 v3 v4 v5
  = coe
      d_'60''45'trans_678
      (MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'43'__196
         (coe v0) (coe v2))
      (coe
         MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
         (\ v6 v7 -> v7)
         (\ v6 ->
            MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'43'__196
              (coe v6) (coe v2))
         v0 v1)
      (MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'43'__196
         (coe v1) (coe v3))
      (coe d_'43''45'mono'737''45''60'_1418 v2 v0 v1 v4)
      (d_'43''45'mono'691''45''60'_1396
         (coe v1) (coe v2) (coe v3) (coe v5))
-- Data.Rational.Unnormalised.Properties.+-mono-≤-<
d_'43''45'mono'45''8804''45''60'_1448 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8804'__38 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'60'__46 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'60'__46
d_'43''45'mono'45''8804''45''60'_1448 v0 v1 v2 v3 v4 v5
  = coe
      d_'8804''45''60''45'trans_610
      (coe
         MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'43'__196 (coe v0)
         (coe v2))
      (coe
         MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
         (\ v6 v7 -> v7)
         (\ v6 ->
            MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'43'__196
              (coe v6) (coe v2))
         v0 v1)
      (coe
         MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'43'__196 (coe v1)
         (coe v3))
      (coe d_'43''45'mono'737''45''8804'_1334 v2 v0 v1 v4)
      (coe
         d_'43''45'mono'691''45''60'_1396 (coe v1) (coe v2) (coe v3)
         (coe v5))
-- Data.Rational.Unnormalised.Properties.+-mono-<-≤
d_'43''45'mono'45''60''45''8804'_1460 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'60'__46 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8804'__38 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'60'__46
d_'43''45'mono'45''60''45''8804'_1460 v0 v1 v2 v3 v4 v5
  = coe
      d_'60''45''8804''45'trans_644
      (coe
         MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'43'__196 (coe v0)
         (coe v2))
      (coe
         MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
         (\ v6 v7 -> v7)
         (\ v6 ->
            MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'43'__196
              (coe v6) (coe v2))
         v0 v1)
      (coe
         MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'43'__196 (coe v1)
         (coe v3))
      (coe d_'43''45'mono'737''45''60'_1418 v2 v0 v1 v4)
      (coe
         d_'43''45'mono'691''45''8804'_1314 (coe v1) (coe v2) (coe v3)
         (coe v5))
-- Data.Rational.Unnormalised.Properties.pos+pos⇒pos
d_pos'43'pos'8658'pos_1480 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Integer.Base.T_Positive_134 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Integer.Base.T_Positive_134 ->
  MAlonzo.Code.Data.Integer.Base.T_Positive_134
d_pos'43'pos'8658'pos_1480 v0 ~v1 v2 ~v3
  = du_pos'43'pos'8658'pos_1480 v0 v2
du_pos'43'pos'8658'pos_1480 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Integer.Base.T_Positive_134
du_pos'43'pos'8658'pos_1480 v0 v1
  = coe
      MAlonzo.Code.Data.Rational.Unnormalised.Base.d_positive_162
      (coe
         MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'43'__196 (coe v0)
         (coe v1))
      (coe
         d_'43''45'mono'45''60'_1434
         (coe MAlonzo.Code.Data.Rational.Unnormalised.Base.d_0ℚ'7512'_108)
         (coe v0)
         (coe MAlonzo.Code.Data.Rational.Unnormalised.Base.d_0ℚ'7512'_108)
         (coe v1) (coe du_positive'8315''185'_926 (coe v0))
         (coe du_positive'8315''185'_926 (coe v1)))
-- Data.Rational.Unnormalised.Properties.nonNeg+nonNeg⇒nonNeg
d_nonNeg'43'nonNeg'8658'nonNeg_1494 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Integer.Base.T_NonNegative_144 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Integer.Base.T_NonNegative_144 ->
  MAlonzo.Code.Data.Integer.Base.T_NonNegative_144
d_nonNeg'43'nonNeg'8658'nonNeg_1494 v0 ~v1 v2 ~v3
  = du_nonNeg'43'nonNeg'8658'nonNeg_1494 v0 v2
du_nonNeg'43'nonNeg'8658'nonNeg_1494 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Integer.Base.T_NonNegative_144
du_nonNeg'43'nonNeg'8658'nonNeg_1494 v0 v1
  = coe
      MAlonzo.Code.Data.Rational.Unnormalised.Base.d_nonNegative_186
      (coe
         MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'43'__196 (coe v0)
         (coe v1))
      (coe
         d_'43''45'mono'45''8804'_1350
         MAlonzo.Code.Data.Rational.Unnormalised.Base.d_0ℚ'7512'_108 v0
         MAlonzo.Code.Data.Rational.Unnormalised.Base.d_0ℚ'7512'_108 v1
         (coe du_nonNegative'8315''185'_932 (coe v0))
         (coe du_nonNegative'8315''185'_932 (coe v1)))
-- Data.Rational.Unnormalised.Properties.+-minus-telescope
d_'43''45'minus'45'telescope_1506 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8771'__24
d_'43''45'minus'45'telescope_1506 v0 v1 v2
  = let v3
          = coe
              MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_eqRelation_238 in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__126
         (coe v3)
         (coe
            MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'43'__196
            (coe
               MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'45'__208 (coe v0)
               (coe v1))
            (coe
               MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'45'__208 (coe v1)
               (coe v2)))
         (coe
            MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'45'__208 (coe v0)
            (coe v2))
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8771''45''10217'_388
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8776''45'go_124
               (coe d_'8804''45'isPreorder_512)
               (coe d_'60''45'resp'45''8771'_780))
            (MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'43'__196
               (coe
                  MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'45'__208 (coe v0)
                  (coe v1))
               (coe
                  MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'45'__208 (coe v1)
                  (coe v2)))
            (MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'45'__208
               (coe
                  MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'43'__196
                  (coe
                     MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'45'__208 (coe v0)
                     (coe v1))
                  (coe v1))
               (coe v2))
            (MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'45'__208
               (coe v0) (coe v2))
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8771''45''10217'_388
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8776''45'go_124
                  (coe d_'8804''45'isPreorder_512)
                  (coe d_'60''45'resp'45''8771'_780))
               (MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'45'__208
                  (coe
                     MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'43'__196
                     (coe
                        MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'45'__208 (coe v0)
                        (coe v1))
                     (coe v1))
                  (coe v2))
               (MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'45'__208
                  (coe
                     MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'43'__196 (coe v0)
                     (coe
                        MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'43'__196
                        (coe
                           MAlonzo.Code.Data.Rational.Unnormalised.Base.d_'45'__190 (coe v1))
                        (coe v1)))
                  (coe v2))
               (MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'45'__208
                  (coe v0) (coe v2))
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8771''45''10217'_388
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8776''45'go_124
                     (coe d_'8804''45'isPreorder_512)
                     (coe d_'60''45'resp'45''8771'_780))
                  (MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'45'__208
                     (coe
                        MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'43'__196 (coe v0)
                        (coe
                           MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'43'__196
                           (coe
                              MAlonzo.Code.Data.Rational.Unnormalised.Base.d_'45'__190 (coe v1))
                           (coe v1)))
                     (coe v2))
                  (MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'45'__208
                     (coe
                        MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'43'__196 (coe v0)
                        (coe MAlonzo.Code.Data.Rational.Unnormalised.Base.d_0ℚ'7512'_108))
                     (coe v2))
                  (MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'45'__208
                     (coe v0) (coe v2))
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8771''45''10217'_388
                     (coe
                        MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8776''45'go_124
                        (coe d_'8804''45'isPreorder_512)
                        (coe d_'60''45'resp'45''8771'_780))
                     (MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'45'__208
                        (coe
                           MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'43'__196 (coe v0)
                           (coe MAlonzo.Code.Data.Rational.Unnormalised.Base.d_0ℚ'7512'_108))
                        (coe v2))
                     (MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'45'__208
                        (coe v0) (coe v2))
                     (MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'45'__208
                        (coe v0) (coe v2))
                     (coe
                        MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                        (coe
                           MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_stop_166
                           (coe d_'8804''45'isPreorder_512))
                        (coe
                           MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'45'__208 (coe v0)
                           (coe v2)))
                     (d_'43''45'cong'737'_1078
                        (coe
                           MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'43'__196 (coe v0)
                           (coe MAlonzo.Code.Data.Rational.Unnormalised.Base.d_0ℚ'7512'_108))
                        (coe v0)
                        (coe
                           MAlonzo.Code.Data.Rational.Unnormalised.Base.d_'45'__190 (coe v2))
                        (coe du_'43''45'identity'691'_1178)))
                  (d_'43''45'cong'737'_1078
                     (coe
                        MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'43'__196 (coe v0)
                        (coe
                           MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'43'__196
                           (coe
                              MAlonzo.Code.Data.Rational.Unnormalised.Base.d_'45'__190 (coe v1))
                           (coe v1)))
                     (coe
                        MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'43'__196 (coe v0)
                        (coe MAlonzo.Code.Data.Rational.Unnormalised.Base.d_0ℚ'7512'_108))
                     (coe
                        MAlonzo.Code.Data.Rational.Unnormalised.Base.d_'45'__190 (coe v2))
                     (coe
                        d_'43''45'cong'691'_1070
                        (coe
                           MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'43'__196
                           (coe
                              MAlonzo.Code.Data.Rational.Unnormalised.Base.d_'45'__190 (coe v1))
                           (coe v1))
                        (coe MAlonzo.Code.Data.Rational.Unnormalised.Base.d_0ℚ'7512'_108)
                        (coe v0) (coe d_'43''45'inverse'737'_1186 (coe v1)))))
               (d_'43''45'cong'737'_1078
                  (coe
                     MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'43'__196
                     (coe
                        MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'43'__196 (coe v0)
                        (coe
                           MAlonzo.Code.Data.Rational.Unnormalised.Base.d_'45'__190 (coe v1)))
                     (coe v1))
                  (coe
                     MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'43'__196 (coe v0)
                     (coe
                        MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'43'__196
                        (coe
                           MAlonzo.Code.Data.Rational.Unnormalised.Base.d_'45'__190 (coe v1))
                        (coe v1)))
                  (coe
                     MAlonzo.Code.Data.Rational.Unnormalised.Base.d_'45'__190 (coe v2))
                  (coe du_'43''45'assoc_1124)))
            (coe du_'8771''45'sym_170 (coe du_'43''45'assoc_1124))))
-- Data.Rational.Unnormalised.Properties.p≃q⇒p-q≃0
d_p'8771'q'8658'p'45'q'8771'0_1522 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8771'__24 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8771'__24
d_p'8771'q'8658'p'45'q'8771'0_1522 v0 v1 v2
  = let v3
          = coe
              MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_eqRelation_238 in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__126
         (coe v3)
         (coe
            MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'45'__208 (coe v0)
            (coe v1))
         (coe MAlonzo.Code.Data.Rational.Unnormalised.Base.d_0ℚ'7512'_108)
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8771''45''10217'_388
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8776''45'go_124
               (coe d_'8804''45'isPreorder_512)
               (coe d_'60''45'resp'45''8771'_780))
            (MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'45'__208
               (coe v0) (coe v1))
            (MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'45'__208
               (coe v1) (coe v1))
            MAlonzo.Code.Data.Rational.Unnormalised.Base.d_0ℚ'7512'_108
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8771''45''10217'_388
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8776''45'go_124
                  (coe d_'8804''45'isPreorder_512)
                  (coe d_'60''45'resp'45''8771'_780))
               (MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'45'__208
                  (coe v1) (coe v1))
               MAlonzo.Code.Data.Rational.Unnormalised.Base.d_0ℚ'7512'_108
               MAlonzo.Code.Data.Rational.Unnormalised.Base.d_0ℚ'7512'_108
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_stop_166
                     (coe d_'8804''45'isPreorder_512))
                  (coe MAlonzo.Code.Data.Rational.Unnormalised.Base.d_0ℚ'7512'_108))
               (d_'43''45'inverse'691'_1200 (coe v1)))
            (d_'43''45'cong'737'_1078
               (coe v0) (coe v1)
               (coe
                  MAlonzo.Code.Data.Rational.Unnormalised.Base.d_'45'__190 (coe v1))
               (coe v2))))
-- Data.Rational.Unnormalised.Properties.p-q≃0⇒p≃q
d_p'45'q'8771'0'8658'p'8771'q_1538 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8771'__24 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8771'__24
d_p'45'q'8771'0'8658'p'8771'q_1538 v0 v1 v2
  = let v3
          = coe
              MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_eqRelation_238 in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__126
         (coe v3) (coe v0) (coe v1)
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10216'_448
            (\ v4 v5 v6 v7 v8 -> v8) v0
            (MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'43'__196
               (coe v0)
               (coe MAlonzo.Code.Data.Rational.Unnormalised.Base.d_0ℚ'7512'_108))
            v1
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8771''45''10217'_388
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8776''45'go_124
                  (coe d_'8804''45'isPreorder_512)
                  (coe d_'60''45'resp'45''8771'_780))
               (MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'43'__196
                  (coe v0)
                  (coe MAlonzo.Code.Data.Rational.Unnormalised.Base.d_0ℚ'7512'_108))
               (MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'43'__196
                  (coe v0)
                  (coe
                     MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'43'__196
                     (coe
                        MAlonzo.Code.Data.Rational.Unnormalised.Base.d_'45'__190 (coe v1))
                     (coe v1)))
               v1
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10216'_448
                  (\ v4 v5 v6 v7 v8 -> v8)
                  (MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'43'__196
                     (coe v0)
                     (coe
                        MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'43'__196
                        (coe
                           MAlonzo.Code.Data.Rational.Unnormalised.Base.d_'45'__190 (coe v1))
                        (coe v1)))
                  (MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'43'__196
                     (coe
                        MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'45'__208 (coe v0)
                        (coe v1))
                     (coe v1))
                  v1
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8771''45''10217'_388
                     (coe
                        MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8776''45'go_124
                        (coe d_'8804''45'isPreorder_512)
                        (coe d_'60''45'resp'45''8771'_780))
                     (MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'43'__196
                        (coe
                           MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'45'__208 (coe v0)
                           (coe v1))
                        (coe v1))
                     (MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'43'__196
                        (coe MAlonzo.Code.Data.Rational.Unnormalised.Base.d_0ℚ'7512'_108)
                        (coe v1))
                     v1
                     (coe
                        MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_436
                        (\ v4 v5 v6 v7 v8 -> v8)
                        (MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'43'__196
                           (coe MAlonzo.Code.Data.Rational.Unnormalised.Base.d_0ℚ'7512'_108)
                           (coe v1))
                        v1 v1
                        (coe
                           MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                           (coe
                              MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_stop_166
                              (coe d_'8804''45'isPreorder_512))
                           (coe v1))
                        erased)
                     (d_'43''45'cong'737'_1078
                        (coe
                           MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'45'__208 (coe v0)
                           (coe v1))
                        (coe MAlonzo.Code.Data.Rational.Unnormalised.Base.d_0ℚ'7512'_108)
                        (coe v1) (coe v2)))
                  erased)
               (d_'43''45'cong'691'_1070
                  (coe MAlonzo.Code.Data.Rational.Unnormalised.Base.d_0ℚ'7512'_108)
                  (coe
                     MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'43'__196
                     (coe
                        MAlonzo.Code.Data.Rational.Unnormalised.Base.d_'45'__190 (coe v1))
                     (coe v1))
                  (coe v0)
                  (coe
                     du_'8771''45'sym_170 (coe d_'43''45'inverse'737'_1186 (coe v1)))))
            erased))
-- Data.Rational.Unnormalised.Properties.neg-mono-≤
d_neg'45'mono'45''8804'_1550 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8804'__38 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8804'__38
d_neg'45'mono'45''8804'_1550 v0 v1 v2
  = case coe v0 of
      MAlonzo.Code.Data.Rational.Unnormalised.Base.C_mkℚ'7512'_22 v3 v4
        -> case coe v1 of
             MAlonzo.Code.Data.Rational.Unnormalised.Base.C_mkℚ'7512'_22 v5 v6
               -> case coe v2 of
                    MAlonzo.Code.Data.Rational.Unnormalised.Base.C_'42''8804''42'_44 v9
                      -> coe
                           MAlonzo.Code.Data.Rational.Unnormalised.Base.C_'42''8804''42'_44
                           (coe
                              MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
                              (coe
                                 MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_start_96
                                 (coe
                                    MAlonzo.Code.Data.Integer.Properties.d_'8804''45'isPreorder_2822)
                                 (\ v10 v11 v12 ->
                                    coe
                                      MAlonzo.Code.Data.Integer.Properties.du_'60''8658''8804'_2868
                                      v12))
                              (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                 (coe
                                    MAlonzo.Code.Data.Rational.Unnormalised.Base.d_numerator_14
                                    (coe
                                       MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                                       (\ v10 v11 -> v11)
                                       MAlonzo.Code.Data.Rational.Unnormalised.Base.d_'45'__190 v0
                                       v1))
                                 (coe
                                    MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                    (coe
                                       MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                                       MAlonzo.Code.Data.Rational.Unnormalised.Base.d_'45'__190
                                       (\ v10 v11 -> v10) v0 v1)))
                              (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                 (coe
                                    MAlonzo.Code.Data.Rational.Unnormalised.Base.d_numerator_14
                                    (coe
                                       MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                                       MAlonzo.Code.Data.Rational.Unnormalised.Base.d_'45'__190
                                       (\ v10 v11 -> v10) v0 v1))
                                 (coe
                                    MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                    (coe
                                       MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                                       (\ v10 v11 -> v11)
                                       MAlonzo.Code.Data.Rational.Unnormalised.Base.d_'45'__190 v0
                                       v1)))
                              (coe
                                 MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10216'_448
                                 (\ v10 v11 v12 v13 v14 -> v14)
                                 (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                    (coe MAlonzo.Code.Data.Integer.Base.d_'45'__252 (coe v5))
                                    (coe
                                       MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                       (coe v0)))
                                 (MAlonzo.Code.Data.Integer.Base.d_'45'__252
                                    (coe
                                       MAlonzo.Code.Data.Integer.Base.d__'42'__308 (coe v5)
                                       (coe
                                          MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                          (coe v0))))
                                 (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                    (coe
                                       MAlonzo.Code.Data.Rational.Unnormalised.Base.d_numerator_14
                                       (coe
                                          MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                                          MAlonzo.Code.Data.Rational.Unnormalised.Base.d_'45'__190
                                          (\ v10 v11 -> v10) v0 v1))
                                    (coe
                                       MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                       (coe
                                          MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                                          (\ v10 v11 -> v11)
                                          MAlonzo.Code.Data.Rational.Unnormalised.Base.d_'45'__190
                                          v0 v1)))
                                 (coe
                                    MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8804'_308
                                    (coe
                                       MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8804''45'go_138
                                       (coe
                                          MAlonzo.Code.Data.Integer.Properties.d_'8804''45'isPreorder_2822)
                                       (\ v10 v11 v12 v13 v14 ->
                                          coe
                                            MAlonzo.Code.Data.Integer.Properties.du_'8804''45''60''45'trans_2980
                                            v13 v14))
                                    (MAlonzo.Code.Data.Integer.Base.d_'45'__252
                                       (coe
                                          MAlonzo.Code.Data.Integer.Base.d__'42'__308 (coe v5)
                                          (coe
                                             MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                             (coe v0))))
                                    (MAlonzo.Code.Data.Integer.Base.d_'45'__252
                                       (coe
                                          MAlonzo.Code.Data.Integer.Base.d__'42'__308 (coe v3)
                                          (coe
                                             MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                             (coe v1))))
                                    (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                       (coe
                                          MAlonzo.Code.Data.Rational.Unnormalised.Base.d_numerator_14
                                          (coe
                                             MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                                             MAlonzo.Code.Data.Rational.Unnormalised.Base.d_'45'__190
                                             (\ v10 v11 -> v10) v0 v1))
                                       (coe
                                          MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                          (coe
                                             MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                                             (\ v10 v11 -> v11)
                                             MAlonzo.Code.Data.Rational.Unnormalised.Base.d_'45'__190
                                             v0 v1)))
                                    (coe
                                       MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_436
                                       (\ v10 v11 v12 v13 v14 -> v14)
                                       (MAlonzo.Code.Data.Integer.Base.d_'45'__252
                                          (coe
                                             MAlonzo.Code.Data.Integer.Base.d__'42'__308 (coe v3)
                                             (coe
                                                MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                                (coe v1))))
                                       (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                          (coe MAlonzo.Code.Data.Integer.Base.d_'45'__252 (coe v3))
                                          (coe
                                             MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                             (coe v1)))
                                       (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                          (coe
                                             MAlonzo.Code.Data.Rational.Unnormalised.Base.d_numerator_14
                                             (coe
                                                MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                                                MAlonzo.Code.Data.Rational.Unnormalised.Base.d_'45'__190
                                                (\ v10 v11 -> v10) v0 v1))
                                          (coe
                                             MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                             (coe
                                                MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                                                (\ v10 v11 -> v11)
                                                MAlonzo.Code.Data.Rational.Unnormalised.Base.d_'45'__190
                                                v0 v1)))
                                       (let v10
                                              = MAlonzo.Code.Data.Integer.Properties.d_'8804''45'isPreorder_2822 in
                                        coe
                                          (coe
                                             MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                                             (coe
                                                MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_stop_166
                                                (coe v10))
                                             (coe
                                                MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                (coe
                                                   MAlonzo.Code.Data.Integer.Base.d_'45'__252
                                                   (coe v3))
                                                (coe
                                                   MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                                   (coe v1)))))
                                       erased)
                                    (coe
                                       MAlonzo.Code.Data.Integer.Properties.du_neg'45'mono'45''8804'_3294
                                       (coe
                                          MAlonzo.Code.Data.Integer.Base.d__'42'__308 (coe v5)
                                          (coe
                                             MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                             (coe v0)))
                                       (coe v9)))
                                 erased))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Rational.Unnormalised.Properties.neg-cancel-≤
d_neg'45'cancel'45''8804'_1566 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8804'__38 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8804'__38
d_neg'45'cancel'45''8804'_1566 v0 v1 v2
  = case coe v0 of
      MAlonzo.Code.Data.Rational.Unnormalised.Base.C_mkℚ'7512'_22 v3 v4
        -> case coe v1 of
             MAlonzo.Code.Data.Rational.Unnormalised.Base.C_mkℚ'7512'_22 v5 v6
               -> case coe v2 of
                    MAlonzo.Code.Data.Rational.Unnormalised.Base.C_'42''8804''42'_44 v9
                      -> coe
                           MAlonzo.Code.Data.Rational.Unnormalised.Base.C_'42''8804''42'_44
                           (coe
                              MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
                              (coe
                                 MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_start_96
                                 (coe
                                    MAlonzo.Code.Data.Integer.Properties.d_'8804''45'isPreorder_2822)
                                 (\ v10 v11 v12 ->
                                    coe
                                      MAlonzo.Code.Data.Integer.Properties.du_'60''8658''8804'_2868
                                      v12))
                              (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                 (coe v5)
                                 (coe
                                    MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                    (coe v0)))
                              (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                 (coe v3)
                                 (coe
                                    MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                    (coe v1)))
                              (coe
                                 MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10216'_448
                                 (\ v10 v11 v12 v13 v14 -> v14)
                                 (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                    (coe v5)
                                    (coe
                                       MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                       (coe v0)))
                                 (MAlonzo.Code.Data.Integer.Base.d_'45'__252
                                    (coe
                                       MAlonzo.Code.Data.Integer.Base.d_'45'__252
                                       (coe
                                          MAlonzo.Code.Data.Integer.Base.d__'42'__308 (coe v5)
                                          (coe
                                             MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                             (coe v0)))))
                                 (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                    (coe v3)
                                    (coe
                                       MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                       (coe v1)))
                                 (coe
                                    MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_436
                                    (\ v10 v11 v12 v13 v14 -> v14)
                                    (MAlonzo.Code.Data.Integer.Base.d_'45'__252
                                       (coe
                                          MAlonzo.Code.Data.Integer.Base.d_'45'__252
                                          (coe
                                             MAlonzo.Code.Data.Integer.Base.d__'42'__308 (coe v5)
                                             (coe
                                                MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                                (coe v0)))))
                                    (MAlonzo.Code.Data.Integer.Base.d_'45'__252
                                       (coe
                                          MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                          (coe MAlonzo.Code.Data.Integer.Base.d_'45'__252 (coe v5))
                                          (coe
                                             MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                             (coe v0))))
                                    (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                       (coe v3)
                                       (coe
                                          MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                          (coe v1)))
                                    (coe
                                       MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8804'_308
                                       (coe
                                          MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8804''45'go_138
                                          (coe
                                             MAlonzo.Code.Data.Integer.Properties.d_'8804''45'isPreorder_2822)
                                          (\ v10 v11 v12 v13 v14 ->
                                             coe
                                               MAlonzo.Code.Data.Integer.Properties.du_'8804''45''60''45'trans_2980
                                               v13 v14))
                                       (MAlonzo.Code.Data.Integer.Base.d_'45'__252
                                          (coe
                                             MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                             (coe
                                                MAlonzo.Code.Data.Integer.Base.d_'45'__252 (coe v5))
                                             (coe
                                                MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                                (coe v0))))
                                       (MAlonzo.Code.Data.Integer.Base.d_'45'__252
                                          (coe
                                             MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                             (coe
                                                MAlonzo.Code.Data.Integer.Base.d_'45'__252 (coe v3))
                                             (coe
                                                MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                                (coe v1))))
                                       (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                          (coe v3)
                                          (coe
                                             MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                             (coe v1)))
                                       (coe
                                          MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10216'_448
                                          (\ v10 v11 v12 v13 v14 -> v14)
                                          (MAlonzo.Code.Data.Integer.Base.d_'45'__252
                                             (coe
                                                MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                (coe
                                                   MAlonzo.Code.Data.Integer.Base.d_'45'__252
                                                   (coe v3))
                                                (coe
                                                   MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                                   (coe v1))))
                                          (MAlonzo.Code.Data.Integer.Base.d_'45'__252
                                             (coe
                                                MAlonzo.Code.Data.Integer.Base.d_'45'__252
                                                (coe
                                                   MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                   (coe v3)
                                                   (coe
                                                      MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                                      (coe v1)))))
                                          (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                             (coe v3)
                                             (coe
                                                MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                                (coe v1)))
                                          (coe
                                             MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_436
                                             (\ v10 v11 v12 v13 v14 -> v14)
                                             (MAlonzo.Code.Data.Integer.Base.d_'45'__252
                                                (coe
                                                   MAlonzo.Code.Data.Integer.Base.d_'45'__252
                                                   (coe
                                                      MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                      (coe v3)
                                                      (coe
                                                         MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                                         (coe v1)))))
                                             (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                (coe v3)
                                                (coe
                                                   MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                                   (coe v1)))
                                             (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                (coe v3)
                                                (coe
                                                   MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                                   (coe v1)))
                                             (let v10
                                                    = MAlonzo.Code.Data.Integer.Properties.d_'8804''45'isPreorder_2822 in
                                              coe
                                                (coe
                                                   MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                                                   (coe
                                                      MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_stop_166
                                                      (coe v10))
                                                   (coe
                                                      MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                      (coe v3)
                                                      (coe
                                                         MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                                         (coe v1)))))
                                             erased)
                                          erased)
                                       (coe
                                          MAlonzo.Code.Data.Integer.Properties.du_neg'45'mono'45''8804'_3294
                                          (coe
                                             MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                             (coe
                                                MAlonzo.Code.Data.Rational.Unnormalised.Base.d_numerator_14
                                                (coe
                                                   MAlonzo.Code.Data.Rational.Unnormalised.Base.d_'45'__190
                                                   (coe v1)))
                                             (coe
                                                MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                                (coe
                                                   MAlonzo.Code.Data.Rational.Unnormalised.Base.d_'45'__190
                                                   (coe v0))))
                                          (coe v9)))
                                    erased)
                                 erased))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Rational.Unnormalised.Properties.p≤q⇒p-q≤0
d_p'8804'q'8658'p'45'q'8804'0_1582 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8804'__38 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8804'__38
d_p'8804'q'8658'p'45'q'8804'0_1582 v0 v1 v2
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_start_96
         (coe d_'8804''45'isPreorder_512)
         (\ v3 v4 v5 -> coe du_'60''8658''8804'_556 v5))
      (MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'45'__208
         (coe v0) (coe v1))
      MAlonzo.Code.Data.Rational.Unnormalised.Base.d_0ℚ'7512'_108
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8804'_308
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8804''45'go_138
            (coe d_'8804''45'isPreorder_512)
            (coe d_'8804''45''60''45'trans_610))
         (MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'45'__208
            (coe v0) (coe v1))
         (MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'45'__208
            (coe v1) (coe v1))
         MAlonzo.Code.Data.Rational.Unnormalised.Base.d_0ℚ'7512'_108
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8771''45''10217'_388
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8776''45'go_124
               (coe d_'8804''45'isPreorder_512)
               (coe d_'60''45'resp'45''8771'_780))
            (MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'45'__208
               (coe v1) (coe v1))
            MAlonzo.Code.Data.Rational.Unnormalised.Base.d_0ℚ'7512'_108
            MAlonzo.Code.Data.Rational.Unnormalised.Base.d_0ℚ'7512'_108
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_stop_166
                  (coe d_'8804''45'isPreorder_512))
               (coe MAlonzo.Code.Data.Rational.Unnormalised.Base.d_0ℚ'7512'_108))
            (d_'43''45'inverse'691'_1200 (coe v1)))
         (coe
            d_'43''45'mono'737''45''8804'_1334
            (MAlonzo.Code.Data.Rational.Unnormalised.Base.d_'45'__190 (coe v1))
            v0 v1 v2))
-- Data.Rational.Unnormalised.Properties.p-q≤0⇒p≤q
d_p'45'q'8804'0'8658'p'8804'q_1598 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8804'__38 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8804'__38
d_p'45'q'8804'0'8658'p'8804'q_1598 v0 v1 v2
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_start_96
         (coe d_'8804''45'isPreorder_512)
         (\ v3 v4 v5 -> coe du_'60''8658''8804'_556 v5))
      v0 v1
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10216'_448
         (\ v3 v4 v5 v6 v7 -> v7) v0
         (MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'43'__196
            (coe v0)
            (coe MAlonzo.Code.Data.Rational.Unnormalised.Base.d_0ℚ'7512'_108))
         v1
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8771''45''10217'_388
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8776''45'go_124
               (coe d_'8804''45'isPreorder_512)
               (coe d_'60''45'resp'45''8771'_780))
            (MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'43'__196
               (coe v0)
               (coe MAlonzo.Code.Data.Rational.Unnormalised.Base.d_0ℚ'7512'_108))
            (MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'43'__196
               (coe v0)
               (coe
                  MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'43'__196
                  (coe
                     MAlonzo.Code.Data.Rational.Unnormalised.Base.d_'45'__190 (coe v1))
                  (coe v1)))
            v1
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10216'_448
               (\ v3 v4 v5 v6 v7 -> v7)
               (MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'43'__196
                  (coe v0)
                  (coe
                     MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'43'__196
                     (coe
                        MAlonzo.Code.Data.Rational.Unnormalised.Base.d_'45'__190 (coe v1))
                     (coe v1)))
               (MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'43'__196
                  (coe
                     MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'45'__208 (coe v0)
                     (coe v1))
                  (coe v1))
               v1
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8804'_308
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8804''45'go_138
                     (coe d_'8804''45'isPreorder_512)
                     (coe d_'8804''45''60''45'trans_610))
                  (MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'43'__196
                     (coe
                        MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'45'__208 (coe v0)
                        (coe v1))
                     (coe v1))
                  (MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'43'__196
                     (coe MAlonzo.Code.Data.Rational.Unnormalised.Base.d_0ℚ'7512'_108)
                     (coe v1))
                  v1
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_436
                     (\ v3 v4 v5 v6 v7 -> v7)
                     (MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'43'__196
                        (coe MAlonzo.Code.Data.Rational.Unnormalised.Base.d_0ℚ'7512'_108)
                        (coe v1))
                     v1 v1
                     (coe
                        MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                        (coe
                           MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_stop_166
                           (coe d_'8804''45'isPreorder_512))
                        (coe v1))
                     erased)
                  (coe
                     d_'43''45'mono'737''45''8804'_1334 v1
                     (MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'45'__208
                        (coe v0) (coe v1))
                     MAlonzo.Code.Data.Rational.Unnormalised.Base.d_0ℚ'7512'_108 v2))
               erased)
            (d_'43''45'cong'691'_1070
               (coe MAlonzo.Code.Data.Rational.Unnormalised.Base.d_0ℚ'7512'_108)
               (coe
                  MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'43'__196
                  (coe
                     MAlonzo.Code.Data.Rational.Unnormalised.Base.d_'45'__190 (coe v1))
                  (coe v1))
               (coe v0)
               (coe
                  du_'8771''45'sym_170 (coe d_'43''45'inverse'737'_1186 (coe v1)))))
         erased)
-- Data.Rational.Unnormalised.Properties.p≤q⇒0≤q-p
d_p'8804'q'8658'0'8804'q'45'p_1614 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8804'__38 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8804'__38
d_p'8804'q'8658'0'8804'q'45'p_1614 v0 v1 v2
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_start_96
         (coe d_'8804''45'isPreorder_512)
         (\ v3 v4 v5 -> coe du_'60''8658''8804'_556 v5))
      MAlonzo.Code.Data.Rational.Unnormalised.Base.d_0ℚ'7512'_108
      (MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'45'__208
         (coe v1) (coe v0))
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8771''45''10217'_388
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8776''45'go_124
            (coe d_'8804''45'isPreorder_512)
            (coe d_'60''45'resp'45''8771'_780))
         MAlonzo.Code.Data.Rational.Unnormalised.Base.d_0ℚ'7512'_108
         (MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'45'__208
            (coe v0) (coe v0))
         (MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'45'__208
            (coe v1) (coe v0))
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8804'_308
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8804''45'go_138
               (coe d_'8804''45'isPreorder_512)
               (coe d_'8804''45''60''45'trans_610))
            (MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'45'__208
               (coe v0) (coe v0))
            (MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'45'__208
               (coe v1) (coe v0))
            (MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'45'__208
               (coe v1) (coe v0))
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_stop_166
                  (coe d_'8804''45'isPreorder_512))
               (coe
                  MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'45'__208 (coe v1)
                  (coe v0)))
            (coe
               d_'43''45'mono'737''45''8804'_1334
               (MAlonzo.Code.Data.Rational.Unnormalised.Base.d_'45'__190 (coe v0))
               v0 v1 v2))
         (coe
            du_'8771''45'sym_170 (coe d_'43''45'inverse'691'_1200 (coe v0))))
-- Data.Rational.Unnormalised.Properties.0≤q-p⇒p≤q
d_0'8804'q'45'p'8658'p'8804'q_1630 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8804'__38 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8804'__38
d_0'8804'q'45'p'8658'p'8804'q_1630 v0 v1 v2
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_start_96
         (coe d_'8804''45'isPreorder_512)
         (\ v3 v4 v5 -> coe du_'60''8658''8804'_556 v5))
      v0 v1
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10216'_448
         (\ v3 v4 v5 v6 v7 -> v7) v0
         (MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'43'__196
            (coe MAlonzo.Code.Data.Rational.Unnormalised.Base.d_0ℚ'7512'_108)
            (coe v0))
         v1
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8804'_308
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8804''45'go_138
               (coe d_'8804''45'isPreorder_512)
               (coe d_'8804''45''60''45'trans_610))
            (MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'43'__196
               (coe MAlonzo.Code.Data.Rational.Unnormalised.Base.d_0ℚ'7512'_108)
               (coe v0))
            (MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'43'__196
               (coe
                  MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'45'__208 (coe v1)
                  (coe v0))
               (coe v0))
            v1
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_436
               (\ v3 v4 v5 v6 v7 -> v7)
               (MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'43'__196
                  (coe
                     MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'45'__208 (coe v1)
                     (coe v0))
                  (coe v0))
               (MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'43'__196
                  (coe v1)
                  (coe
                     MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'43'__196
                     (coe
                        MAlonzo.Code.Data.Rational.Unnormalised.Base.d_'45'__190 (coe v0))
                     (coe v0)))
               v1
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8771''45''10217'_388
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8776''45'go_124
                     (coe d_'8804''45'isPreorder_512)
                     (coe d_'60''45'resp'45''8771'_780))
                  (MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'43'__196
                     (coe v1)
                     (coe
                        MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'43'__196
                        (coe
                           MAlonzo.Code.Data.Rational.Unnormalised.Base.d_'45'__190 (coe v0))
                        (coe v0)))
                  (MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'43'__196
                     (coe v1)
                     (coe MAlonzo.Code.Data.Rational.Unnormalised.Base.d_0ℚ'7512'_108))
                  v1
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_436
                     (\ v3 v4 v5 v6 v7 -> v7)
                     (MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'43'__196
                        (coe v1)
                        (coe MAlonzo.Code.Data.Rational.Unnormalised.Base.d_0ℚ'7512'_108))
                     v1 v1
                     (coe
                        MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                        (coe
                           MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_stop_166
                           (coe d_'8804''45'isPreorder_512))
                        (coe v1))
                     erased)
                  (d_'43''45'cong'691'_1070
                     (coe
                        MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'43'__196
                        (coe
                           MAlonzo.Code.Data.Rational.Unnormalised.Base.d_'45'__190 (coe v0))
                        (coe v0))
                     (coe MAlonzo.Code.Data.Rational.Unnormalised.Base.d_0ℚ'7512'_108)
                     (coe v1) (coe d_'43''45'inverse'737'_1186 (coe v0))))
               erased)
            (coe
               d_'43''45'mono'737''45''8804'_1334 v0
               MAlonzo.Code.Data.Rational.Unnormalised.Base.d_0ℚ'7512'_108
               (MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'45'__208
                  (coe v1) (coe v0))
               v2))
         erased)
-- Data.Rational.Unnormalised.Properties.+-isMagma
d_'43''45'isMagma_1642 ::
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176
d_'43''45'isMagma_1642
  = coe
      MAlonzo.Code.Algebra.Structures.C_IsMagma'46'constructor_1867
      (coe d_'8771''45'isEquivalence_260) (coe d_'43''45'cong_1006)
-- Data.Rational.Unnormalised.Properties.+-isSemigroup
d_'43''45'isSemigroup_1644 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_470
d_'43''45'isSemigroup_1644
  = coe
      MAlonzo.Code.Algebra.Structures.C_IsSemigroup'46'constructor_9889
      (coe d_'43''45'isMagma_1642)
      (\ v0 v1 v2 -> coe du_'43''45'assoc_1124)
-- Data.Rational.Unnormalised.Properties.+-0-isMonoid
d_'43''45'0'45'isMonoid_1646 ::
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_684
d_'43''45'0'45'isMonoid_1646
  = coe
      MAlonzo.Code.Algebra.Structures.C_IsMonoid'46'constructor_15345
      (coe d_'43''45'isSemigroup_1644) (coe d_'43''45'identity_1184)
-- Data.Rational.Unnormalised.Properties.+-0-isCommutativeMonoid
d_'43''45'0'45'isCommutativeMonoid_1648 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_734
d_'43''45'0'45'isCommutativeMonoid_1648
  = coe
      MAlonzo.Code.Algebra.Structures.C_IsCommutativeMonoid'46'constructor_17167
      (coe d_'43''45'0'45'isMonoid_1646)
      (\ v0 v1 -> coe du_'43''45'comm_1150)
-- Data.Rational.Unnormalised.Properties.+-0-isGroup
d_'43''45'0'45'isGroup_1650 ::
  MAlonzo.Code.Algebra.Structures.T_IsGroup_1034
d_'43''45'0'45'isGroup_1650
  = coe
      MAlonzo.Code.Algebra.Structures.C_IsGroup'46'constructor_26435
      (coe d_'43''45'0'45'isMonoid_1646) (coe d_'43''45'inverse_1214)
      (coe d_'45''8255'cong_378)
-- Data.Rational.Unnormalised.Properties.+-0-isAbelianGroup
d_'43''45'0'45'isAbelianGroup_1652 ::
  MAlonzo.Code.Algebra.Structures.T_IsAbelianGroup_1130
d_'43''45'0'45'isAbelianGroup_1652
  = coe
      MAlonzo.Code.Algebra.Structures.C_IsAbelianGroup'46'constructor_31913
      (coe d_'43''45'0'45'isGroup_1650)
      (\ v0 v1 -> coe du_'43''45'comm_1150)
-- Data.Rational.Unnormalised.Properties.+-magma
d_'43''45'magma_1654 :: MAlonzo.Code.Algebra.Bundles.T_Magma_72
d_'43''45'magma_1654
  = coe
      MAlonzo.Code.Algebra.Bundles.C_Magma'46'constructor_1323
      MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'43'__196
      d_'43''45'isMagma_1642
-- Data.Rational.Unnormalised.Properties.+-semigroup
d_'43''45'semigroup_1656 ::
  MAlonzo.Code.Algebra.Bundles.T_Semigroup_540
d_'43''45'semigroup_1656
  = coe
      MAlonzo.Code.Algebra.Bundles.C_Semigroup'46'constructor_9837
      MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'43'__196
      d_'43''45'isSemigroup_1644
-- Data.Rational.Unnormalised.Properties.+-0-monoid
d_'43''45'0'45'monoid_1658 ::
  MAlonzo.Code.Algebra.Bundles.T_Monoid_886
d_'43''45'0'45'monoid_1658
  = coe
      MAlonzo.Code.Algebra.Bundles.C_Monoid'46'constructor_16201
      MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'43'__196
      MAlonzo.Code.Data.Rational.Unnormalised.Base.d_0ℚ'7512'_108
      d_'43''45'0'45'isMonoid_1646
-- Data.Rational.Unnormalised.Properties.+-0-commutativeMonoid
d_'43''45'0'45'commutativeMonoid_1660 ::
  MAlonzo.Code.Algebra.Bundles.T_CommutativeMonoid_966
d_'43''45'0'45'commutativeMonoid_1660
  = coe
      MAlonzo.Code.Algebra.Bundles.C_CommutativeMonoid'46'constructor_17975
      MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'43'__196
      MAlonzo.Code.Data.Rational.Unnormalised.Base.d_0ℚ'7512'_108
      d_'43''45'0'45'isCommutativeMonoid_1648
-- Data.Rational.Unnormalised.Properties.+-0-group
d_'43''45'0'45'group_1662 ::
  MAlonzo.Code.Algebra.Bundles.T_Group_1524
d_'43''45'0'45'group_1662
  = coe
      MAlonzo.Code.Algebra.Bundles.C_Group'46'constructor_27347
      MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'43'__196
      MAlonzo.Code.Data.Rational.Unnormalised.Base.d_0ℚ'7512'_108
      MAlonzo.Code.Data.Rational.Unnormalised.Base.d_'45'__190
      d_'43''45'0'45'isGroup_1650
-- Data.Rational.Unnormalised.Properties.+-0-abelianGroup
d_'43''45'0'45'abelianGroup_1664 ::
  MAlonzo.Code.Algebra.Bundles.T_AbelianGroup_1640
d_'43''45'0'45'abelianGroup_1664
  = coe
      MAlonzo.Code.Algebra.Bundles.C_AbelianGroup'46'constructor_29899
      MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'43'__196
      MAlonzo.Code.Data.Rational.Unnormalised.Base.d_0ℚ'7512'_108
      MAlonzo.Code.Data.Rational.Unnormalised.Base.d_'45'__190
      d_'43''45'0'45'isAbelianGroup_1652
-- Data.Rational.Unnormalised.Properties.*-cong
d_'42''45'cong_1666 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8771'__24 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8771'__24 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8771'__24
d_'42''45'cong_1666 v0 v1 v2 v3 v4 v5
  = coe
      seq (coe v0)
      (coe
         seq (coe v1)
         (coe
            seq (coe v2)
            (coe
               seq (coe v3)
               (coe
                  seq (coe v4)
                  (coe
                     seq (coe v5)
                     (coe
                        MAlonzo.Code.Data.Rational.Unnormalised.Base.C_'42''8801''42'_30))))))
-- Data.Rational.Unnormalised.Properties.*-congˡ
d_'42''45'cong'737'_1700 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8771'__24 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8771'__24
d_'42''45'cong'737'_1700 v0 v1 v2 v3
  = coe
      d_'42''45'cong_1666 (coe v0) (coe v0) (coe v1) (coe v2)
      (coe du_'8771''45'refl_166) (coe v3)
-- Data.Rational.Unnormalised.Properties.*-congʳ
d_'42''45'cong'691'_1706 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8771'__24 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8771'__24
d_'42''45'cong'691'_1706 v0 v1 v2 v3
  = coe
      d_'42''45'cong_1666 (coe v1) (coe v2) (coe v0) (coe v0) (coe v3)
      (coe du_'8771''45'refl_166)
-- Data.Rational.Unnormalised.Properties.*-assoc-↥
d_'42''45'assoc'45''8613'_1712 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'assoc'45''8613'_1712 = erased
-- Data.Rational.Unnormalised.Properties.*-assoc-↧
d_'42''45'assoc'45''8615'_1720 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'assoc'45''8615'_1720 = erased
-- Data.Rational.Unnormalised.Properties.*-assoc-≡
d_'42''45'assoc'45''8801'_1728 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'assoc'45''8801'_1728 = erased
-- Data.Rational.Unnormalised.Properties.*-assoc
d_'42''45'assoc_1736 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8771'__24
d_'42''45'assoc_1736 ~v0 ~v1 ~v2 = du_'42''45'assoc_1736
du_'42''45'assoc_1736 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8771'__24
du_'42''45'assoc_1736 = coe du_'8771''45'reflexive_168
-- Data.Rational.Unnormalised.Properties.*-comm-↥
d_'42''45'comm'45''8613'_1744 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'comm'45''8613'_1744 = erased
-- Data.Rational.Unnormalised.Properties.*-comm-↧
d_'42''45'comm'45''8615'_1750 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'comm'45''8615'_1750 = erased
-- Data.Rational.Unnormalised.Properties.*-comm-≡
d_'42''45'comm'45''8801'_1756 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'comm'45''8801'_1756 = erased
-- Data.Rational.Unnormalised.Properties.*-comm
d_'42''45'comm_1762 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8771'__24
d_'42''45'comm_1762 ~v0 ~v1 = du_'42''45'comm_1762
du_'42''45'comm_1762 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8771'__24
du_'42''45'comm_1762 = coe du_'8771''45'reflexive_168
-- Data.Rational.Unnormalised.Properties.*-identityˡ-≡
d_'42''45'identity'737''45''8801'_1768 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'identity'737''45''8801'_1768 = erased
-- Data.Rational.Unnormalised.Properties.*-identityʳ-≡
d_'42''45'identity'691''45''8801'_1772 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'42''45'identity'691''45''8801'_1772 = erased
-- Data.Rational.Unnormalised.Properties.*-identity-≡
d_'42''45'identity'45''8801'_1774 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'42''45'identity'45''8801'_1774
  = coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased
-- Data.Rational.Unnormalised.Properties.*-identityˡ
d_'42''45'identity'737'_1776 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8771'__24
d_'42''45'identity'737'_1776 ~v0 = du_'42''45'identity'737'_1776
du_'42''45'identity'737'_1776 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8771'__24
du_'42''45'identity'737'_1776 = coe du_'8771''45'reflexive_168
-- Data.Rational.Unnormalised.Properties.*-identityʳ
d_'42''45'identity'691'_1780 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8771'__24
d_'42''45'identity'691'_1780 ~v0 = du_'42''45'identity'691'_1780
du_'42''45'identity'691'_1780 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8771'__24
du_'42''45'identity'691'_1780 = coe du_'8771''45'reflexive_168
-- Data.Rational.Unnormalised.Properties.*-identity
d_'42''45'identity_1784 :: MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'42''45'identity_1784
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (\ v0 -> coe du_'42''45'identity'737'_1776)
      (\ v0 -> coe du_'42''45'identity'691'_1780)
-- Data.Rational.Unnormalised.Properties.*-inverseˡ
d_'42''45'inverse'737'_1790 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8771'__24
d_'42''45'inverse'737'_1790 v0 ~v1
  = du_'42''45'inverse'737'_1790 v0
du_'42''45'inverse'737'_1790 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8771'__24
du_'42''45'inverse'737'_1790 v0
  = case coe v0 of
      MAlonzo.Code.Data.Rational.Unnormalised.Base.C_mkℚ'7512'_22 v1 v2
        -> case coe v1 of
             _ | coe geqInt (coe v1) (coe (1 :: Integer)) ->
                 coe
                   MAlonzo.Code.Data.Rational.Unnormalised.Base.C_'42''8801''42'_30
             _ -> coe
                    du_'42''45'inverse'737'_1790
                    (coe
                       MAlonzo.Code.Data.Rational.Unnormalised.Base.C_mkℚ'7512'_22
                       (coe subInt (coe (0 :: Integer)) (coe v1)) (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Rational.Unnormalised.Properties.*-inverseʳ
d_'42''45'inverse'691'_1816 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8771'__24
d_'42''45'inverse'691'_1816 v0 ~v1
  = du_'42''45'inverse'691'_1816 v0
du_'42''45'inverse'691'_1816 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8771'__24
du_'42''45'inverse'691'_1816 v0
  = coe
      du_'8771''45'trans_174 (coe du_'42''45'comm_1762)
      (coe du_'42''45'inverse'737'_1790 (coe v0))
-- Data.Rational.Unnormalised.Properties.≄⇒invertible
d_'8772''8658'invertible_1820 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  (MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8771'__24 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8772''8658'invertible_1820 v0 v1 ~v2
  = du_'8772''8658'invertible_1820 v0 v1
du_'8772''8658'invertible_1820 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8772''8658'invertible_1820 v0 v1
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Data.Rational.Unnormalised.Base.du_1'47'__218
         (coe
            MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'45'__208 (coe v0)
            (coe v1)))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
         (coe
            du_'42''45'inverse'737'_1790
            (coe
               MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'45'__208 (coe v0)
               (coe v1)))
         (coe
            du_'42''45'inverse'691'_1816
            (coe
               MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'45'__208 (coe v0)
               (coe v1))))
-- Data.Rational.Unnormalised.Properties.*-zeroˡ
d_'42''45'zero'737'_1834 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8771'__24
d_'42''45'zero'737'_1834 v0
  = coe
      seq (coe v0)
      (coe
         MAlonzo.Code.Data.Rational.Unnormalised.Base.C_'42''8801''42'_30)
-- Data.Rational.Unnormalised.Properties.*-zeroʳ
d_'42''45'zero'691'_1838 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8771'__24
d_'42''45'zero'691'_1838
  = coe
      MAlonzo.Code.Algebra.Consequences.Setoid.du_comm'8743'ze'737''8658'ze'691'_380
      (coe d_'8771''45'setoid_282)
      (coe MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'42'__202)
      (\ v0 v1 -> coe du_'42''45'comm_1762)
      (coe MAlonzo.Code.Data.Rational.Unnormalised.Base.d_0ℚ'7512'_108)
      (coe d_'42''45'zero'737'_1834)
-- Data.Rational.Unnormalised.Properties.*-zero
d_'42''45'zero_1840 :: MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'42''45'zero_1840
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe d_'42''45'zero'737'_1834) (coe d_'42''45'zero'691'_1838)
-- Data.Rational.Unnormalised.Properties.invertible⇒≄
d_invertible'8658''8772'_1842 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8771'__24 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_invertible'8658''8772'_1842 = erased
-- Data.Rational.Unnormalised.Properties.*-distribˡ-+
d_'42''45'distrib'737''45''43'_1860 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8771'__24
d_'42''45'distrib'737''45''43'_1860 v0 v1 v2
  = coe
      seq (coe v0)
      (coe
         seq (coe v1)
         (coe
            seq (coe v2)
            (coe
               MAlonzo.Code.Data.Rational.Unnormalised.Base.C_'42''8801''42'_30)))
-- Data.Rational.Unnormalised.Properties.*-distribʳ-+
d_'42''45'distrib'691''45''43'_1898 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8771'__24
d_'42''45'distrib'691''45''43'_1898
  = coe
      MAlonzo.Code.Algebra.Consequences.Setoid.du_comm'8743'distr'737''8658'distr'691'_536
      (coe d_'8771''45'setoid_282)
      (coe MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'42'__202)
      (coe MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'43'__196)
      (coe d_'43''45'cong_1006) (\ v0 v1 -> coe du_'42''45'comm_1762)
      (coe d_'42''45'distrib'737''45''43'_1860)
-- Data.Rational.Unnormalised.Properties.*-distrib-+
d_'42''45'distrib'45''43'_1900 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'42''45'distrib'45''43'_1900
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe d_'42''45'distrib'737''45''43'_1860)
      (coe d_'42''45'distrib'691''45''43'_1898)
-- Data.Rational.Unnormalised.Properties.neg-distribˡ-*
d_neg'45'distrib'737''45''42'_1906 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8771'__24
d_neg'45'distrib'737''45''42'_1906 v0 v1
  = coe
      seq (coe v0)
      (coe
         seq (coe v1)
         (coe
            MAlonzo.Code.Data.Rational.Unnormalised.Base.C_'42''8801''42'_30))
-- Data.Rational.Unnormalised.Properties.neg-distribʳ-*
d_neg'45'distrib'691''45''42'_1918 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8771'__24
d_neg'45'distrib'691''45''42'_1918 v0 v1
  = coe
      seq (coe v0)
      (coe
         seq (coe v1)
         (coe
            MAlonzo.Code.Data.Rational.Unnormalised.Base.C_'42''8801''42'_30))
-- Data.Rational.Unnormalised.Properties.*-cancelˡ-/
d_'42''45'cancel'737''45''47'_1936 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8771'__24
d_'42''45'cancel'737''45''47'_1936 ~v0 ~v1 ~v2 ~v3 ~v4
  = du_'42''45'cancel'737''45''47'_1936
du_'42''45'cancel'737''45''47'_1936 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8771'__24
du_'42''45'cancel'737''45''47'_1936
  = coe
      MAlonzo.Code.Data.Rational.Unnormalised.Base.C_'42''8801''42'_30
-- Data.Rational.Unnormalised.Properties.*-cancelʳ-/
d_'42''45'cancel'691''45''47'_1968 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8771'__24
d_'42''45'cancel'691''45''47'_1968 ~v0 ~v1 ~v2 ~v3 ~v4
  = du_'42''45'cancel'691''45''47'_1968
du_'42''45'cancel'691''45''47'_1968 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8771'__24
du_'42''45'cancel'691''45''47'_1968
  = coe du_'42''45'cancel'737''45''47'_1936
-- Data.Rational.Unnormalised.Properties.reorder₁
d_reorder'8321'_1992 ::
  Integer ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reorder'8321'_1992 = erased
-- Data.Rational.Unnormalised.Properties.reorder₂
d_reorder'8322'_2014 ::
  Integer ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reorder'8322'_2014 = erased
-- Data.Rational.Unnormalised.Properties.+▹-nonNeg
d_'43''9657''45'nonNeg_2030 ::
  Integer -> MAlonzo.Code.Data.Integer.Base.T_NonNegative_144
d_'43''9657''45'nonNeg_2030 v0
  = coe
      seq (coe v0)
      (coe
         MAlonzo.Code.Data.Integer.Base.C_NonNegative'46'constructor_1457
         (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
-- Data.Rational.Unnormalised.Properties.*-cancelʳ-≤-pos
d_'42''45'cancel'691''45''8804''45'pos_2036 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Integer.Base.T_Positive_134 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8804'__38 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8804'__38
d_'42''45'cancel'691''45''8804''45'pos_2036 v0 v1 v2 ~v3 v4
  = du_'42''45'cancel'691''45''8804''45'pos_2036 v0 v1 v2 v4
du_'42''45'cancel'691''45''8804''45'pos_2036 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8804'__38 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8804'__38
du_'42''45'cancel'691''45''8804''45'pos_2036 v0 v1 v2 v3
  = case coe v0 of
      MAlonzo.Code.Data.Rational.Unnormalised.Base.C_mkℚ'7512'_22 v4 v5
        -> case coe v1 of
             MAlonzo.Code.Data.Rational.Unnormalised.Base.C_mkℚ'7512'_22 v6 v7
               -> case coe v2 of
                    MAlonzo.Code.Data.Rational.Unnormalised.Base.C_mkℚ'7512'_22 v8 v9
                      -> case coe v3 of
                           MAlonzo.Code.Data.Rational.Unnormalised.Base.C_'42''8804''42'_44 v12
                             -> coe
                                  MAlonzo.Code.Data.Rational.Unnormalised.Base.C_'42''8804''42'_44
                                  (coe
                                     MAlonzo.Code.Data.Integer.Properties.du_'42''45'cancel'691''45''8804''45'pos_5978
                                     (coe
                                        MAlonzo.Code.Data.Integer.Base.d__'42'__308 (coe v4)
                                        (coe
                                           MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                           (coe v1)))
                                     (coe
                                        MAlonzo.Code.Data.Integer.Base.d__'42'__308 (coe v6)
                                        (coe
                                           MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                           (coe v0)))
                                     (coe
                                        MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
                                        (coe
                                           MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_start_96
                                           (coe
                                              MAlonzo.Code.Data.Integer.Properties.d_'8804''45'isPreorder_2822)
                                           (\ v13 v14 v15 ->
                                              coe
                                                MAlonzo.Code.Data.Integer.Properties.du_'60''8658''8804'_2868
                                                v15))
                                        (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                           (coe
                                              MAlonzo.Code.Data.Integer.Base.d__'42'__308 (coe v4)
                                              (coe
                                                 MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                                 (coe v1)))
                                           (coe
                                              MAlonzo.Code.Data.Integer.Base.d__'42'__308 (coe v8)
                                              (coe
                                                 MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                                 (coe v2))))
                                        (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                           (coe
                                              MAlonzo.Code.Data.Integer.Base.d__'42'__308 (coe v6)
                                              (coe
                                                 MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                                 (coe v0)))
                                           (coe
                                              MAlonzo.Code.Data.Integer.Base.d__'42'__308 (coe v8)
                                              (coe
                                                 MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                                 (coe v2))))
                                        (coe
                                           MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_436
                                           (\ v13 v14 v15 v16 v17 -> v17)
                                           (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                              (coe
                                                 MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                 (coe v4)
                                                 (coe
                                                    MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                                    (coe v1)))
                                              (coe
                                                 MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                 (coe v8)
                                                 (coe
                                                    MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                                    (coe v2))))
                                           (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                              (coe
                                                 MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                 (coe v4) (coe v8))
                                              (coe
                                                 MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                 (coe
                                                    MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                                    (coe v1))
                                                 (coe
                                                    MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                                    (coe v2))))
                                           (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                              (coe
                                                 MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                 (coe v6)
                                                 (coe
                                                    MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                                    (coe v0)))
                                              (coe
                                                 MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                 (coe v8)
                                                 (coe
                                                    MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                                    (coe v2))))
                                           (coe
                                              MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8804'_308
                                              (coe
                                                 MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8804''45'go_138
                                                 (coe
                                                    MAlonzo.Code.Data.Integer.Properties.d_'8804''45'isPreorder_2822)
                                                 (\ v13 v14 v15 v16 v17 ->
                                                    coe
                                                      MAlonzo.Code.Data.Integer.Properties.du_'8804''45''60''45'trans_2980
                                                      v16 v17))
                                              (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                 (coe
                                                    MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                    (coe v4) (coe v8))
                                                 (coe
                                                    MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                    (coe
                                                       MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                                       (coe v1))
                                                    (coe
                                                       MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                                       (coe v2))))
                                              (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                 (coe
                                                    MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                    (coe v6) (coe v8))
                                                 (coe
                                                    MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                    (coe
                                                       MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                                       (coe v0))
                                                    (coe
                                                       MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                                       (coe v2))))
                                              (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                 (coe
                                                    MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                    (coe v6)
                                                    (coe
                                                       MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                                       (coe v0)))
                                                 (coe
                                                    MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                    (coe v8)
                                                    (coe
                                                       MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                                       (coe v2))))
                                              (coe
                                                 MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_436
                                                 (\ v13 v14 v15 v16 v17 -> v17)
                                                 (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                    (coe
                                                       MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                       (coe v6) (coe v8))
                                                    (coe
                                                       MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                       (coe
                                                          MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                                          (coe v0))
                                                       (coe
                                                          MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                                          (coe v2))))
                                                 (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                    (coe
                                                       MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                       (coe v6)
                                                       (coe
                                                          MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                                          (coe v0)))
                                                    (coe
                                                       MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                       (coe v8)
                                                       (coe
                                                          MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                                          (coe v2))))
                                                 (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                    (coe
                                                       MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                       (coe v6)
                                                       (coe
                                                          MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                                          (coe v0)))
                                                    (coe
                                                       MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                       (coe v8)
                                                       (coe
                                                          MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                                          (coe v2))))
                                                 (let v13
                                                        = MAlonzo.Code.Data.Integer.Properties.d_'8804''45'isPreorder_2822 in
                                                  coe
                                                    (coe
                                                       MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                                                       (coe
                                                          MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_stop_166
                                                          (coe v13))
                                                       (coe
                                                          MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                          (coe
                                                             MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                             (coe v6)
                                                             (coe
                                                                MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                                                (coe v0)))
                                                          (coe
                                                             MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                             (coe v8)
                                                             (coe
                                                                MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                                                (coe v2))))))
                                                 erased)
                                              v12)
                                           erased)))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Rational.Unnormalised.Properties.*-cancelˡ-≤-pos
d_'42''45'cancel'737''45''8804''45'pos_2054 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Integer.Base.T_Positive_134 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8804'__38 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8804'__38
d_'42''45'cancel'737''45''8804''45'pos_2054 v0 v1 v2 ~v3
  = du_'42''45'cancel'737''45''8804''45'pos_2054 v0 v1 v2
du_'42''45'cancel'737''45''8804''45'pos_2054 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8804'__38 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8804'__38
du_'42''45'cancel'737''45''8804''45'pos_2054 v0 v1 v2
  = coe
      du_'42''45'cancel'691''45''8804''45'pos_2036 (coe v0) (coe v1)
      (coe v2)
-- Data.Rational.Unnormalised.Properties.*-cancelʳ-≤-neg
d_'42''45'cancel'691''45''8804''45'neg_2074 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Integer.Base.T_Negative_164 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8804'__38 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8804'__38
d_'42''45'cancel'691''45''8804''45'neg_2074 v0 v1 v2 ~v3 v4
  = du_'42''45'cancel'691''45''8804''45'neg_2074 v0 v1 v2 v4
du_'42''45'cancel'691''45''8804''45'neg_2074 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8804'__38 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8804'__38
du_'42''45'cancel'691''45''8804''45'neg_2074 v0 v1 v2 v3
  = coe
      seq (coe v2)
      (coe
         d_neg'45'cancel'45''8804'_1566 (coe v0) (coe v1)
         (coe
            du_'42''45'cancel'691''45''8804''45'pos_2036
            (coe
               MAlonzo.Code.Data.Rational.Unnormalised.Base.d_'45'__190 (coe v0))
            (coe
               MAlonzo.Code.Data.Rational.Unnormalised.Base.d_'45'__190 (coe v1))
            (coe
               MAlonzo.Code.Data.Rational.Unnormalised.Base.d_'45'__190 (coe v2))
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_start_96
                  (coe d_'8804''45'isPreorder_512)
                  (\ v4 v5 v6 -> coe du_'60''8658''8804'_556 v6))
               (MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'42'__202
                  (coe
                     MAlonzo.Code.Data.Rational.Unnormalised.Base.d_'45'__190 (coe v0))
                  (coe
                     MAlonzo.Code.Data.Rational.Unnormalised.Base.d_'45'__190 (coe v2)))
               (MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'42'__202
                  (coe
                     MAlonzo.Code.Data.Rational.Unnormalised.Base.d_'45'__190 (coe v1))
                  (coe
                     MAlonzo.Code.Data.Rational.Unnormalised.Base.d_'45'__190 (coe v2)))
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8771''45''10216'_390
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8776''45'go_124
                     (coe d_'8804''45'isPreorder_512)
                     (coe d_'60''45'resp'45''8771'_780))
                  (\ v4 v5 v6 -> coe du_'8771''45'sym_170 v6)
                  (MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'42'__202
                     (coe
                        MAlonzo.Code.Data.Rational.Unnormalised.Base.d_'45'__190 (coe v0))
                     (coe
                        MAlonzo.Code.Data.Rational.Unnormalised.Base.d_'45'__190 (coe v2)))
                  (MAlonzo.Code.Data.Rational.Unnormalised.Base.d_'45'__190
                     (coe
                        MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'42'__202 (coe v0)
                        (coe
                           MAlonzo.Code.Data.Rational.Unnormalised.Base.d_'45'__190
                           (coe v2))))
                  (MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'42'__202
                     (coe
                        MAlonzo.Code.Data.Rational.Unnormalised.Base.d_'45'__190 (coe v1))
                     (coe
                        MAlonzo.Code.Data.Rational.Unnormalised.Base.d_'45'__190 (coe v2)))
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8771''45''10216'_390
                     (coe
                        MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8776''45'go_124
                        (coe d_'8804''45'isPreorder_512)
                        (coe d_'60''45'resp'45''8771'_780))
                     (\ v4 v5 v6 -> coe du_'8771''45'sym_170 v6)
                     (MAlonzo.Code.Data.Rational.Unnormalised.Base.d_'45'__190
                        (coe
                           MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'42'__202 (coe v0)
                           (coe
                              MAlonzo.Code.Data.Rational.Unnormalised.Base.d_'45'__190
                              (coe v2))))
                     (MAlonzo.Code.Data.Rational.Unnormalised.Base.d_'45'__190
                        (coe
                           MAlonzo.Code.Data.Rational.Unnormalised.Base.d_'45'__190
                           (coe
                              MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'42'__202 (coe v0)
                              (coe v2))))
                     (MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'42'__202
                        (coe
                           MAlonzo.Code.Data.Rational.Unnormalised.Base.d_'45'__190 (coe v1))
                        (coe
                           MAlonzo.Code.Data.Rational.Unnormalised.Base.d_'45'__190 (coe v2)))
                     (coe
                        MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8771''45''10217'_388
                        (coe
                           MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8776''45'go_124
                           (coe d_'8804''45'isPreorder_512)
                           (coe d_'60''45'resp'45''8771'_780))
                        (MAlonzo.Code.Data.Rational.Unnormalised.Base.d_'45'__190
                           (coe
                              MAlonzo.Code.Data.Rational.Unnormalised.Base.d_'45'__190
                              (coe
                                 MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'42'__202 (coe v0)
                                 (coe v2))))
                        (MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'42'__202
                           (coe v0) (coe v2))
                        (MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'42'__202
                           (coe
                              MAlonzo.Code.Data.Rational.Unnormalised.Base.d_'45'__190 (coe v1))
                           (coe
                              MAlonzo.Code.Data.Rational.Unnormalised.Base.d_'45'__190 (coe v2)))
                        (coe
                           MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8804'_308
                           (coe
                              MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8804''45'go_138
                              (coe d_'8804''45'isPreorder_512)
                              (coe d_'8804''45''60''45'trans_610))
                           (MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'42'__202
                              (coe v0) (coe v2))
                           (MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'42'__202
                              (coe v1) (coe v2))
                           (MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'42'__202
                              (coe
                                 MAlonzo.Code.Data.Rational.Unnormalised.Base.d_'45'__190 (coe v1))
                              (coe
                                 MAlonzo.Code.Data.Rational.Unnormalised.Base.d_'45'__190 (coe v2)))
                           (coe
                              MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8771''45''10216'_390
                              (coe
                                 MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8776''45'go_124
                                 (coe d_'8804''45'isPreorder_512)
                                 (coe d_'60''45'resp'45''8771'_780))
                              (\ v4 v5 v6 -> coe du_'8771''45'sym_170 v6)
                              (MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'42'__202
                                 (coe v1) (coe v2))
                              (MAlonzo.Code.Data.Rational.Unnormalised.Base.d_'45'__190
                                 (coe
                                    MAlonzo.Code.Data.Rational.Unnormalised.Base.d_'45'__190
                                    (coe
                                       MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'42'__202
                                       (coe v1) (coe v2))))
                              (MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'42'__202
                                 (coe
                                    MAlonzo.Code.Data.Rational.Unnormalised.Base.d_'45'__190
                                    (coe v1))
                                 (coe
                                    MAlonzo.Code.Data.Rational.Unnormalised.Base.d_'45'__190
                                    (coe v2)))
                              (coe
                                 MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8771''45''10217'_388
                                 (coe
                                    MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8776''45'go_124
                                    (coe d_'8804''45'isPreorder_512)
                                    (coe d_'60''45'resp'45''8771'_780))
                                 (MAlonzo.Code.Data.Rational.Unnormalised.Base.d_'45'__190
                                    (coe
                                       MAlonzo.Code.Data.Rational.Unnormalised.Base.d_'45'__190
                                       (coe
                                          MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'42'__202
                                          (coe v1) (coe v2))))
                                 (MAlonzo.Code.Data.Rational.Unnormalised.Base.d_'45'__190
                                    (coe
                                       MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'42'__202
                                       (coe v1)
                                       (coe
                                          MAlonzo.Code.Data.Rational.Unnormalised.Base.d_'45'__190
                                          (coe v2))))
                                 (MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'42'__202
                                    (coe
                                       MAlonzo.Code.Data.Rational.Unnormalised.Base.d_'45'__190
                                       (coe v1))
                                    (coe
                                       MAlonzo.Code.Data.Rational.Unnormalised.Base.d_'45'__190
                                       (coe v2)))
                                 (coe
                                    MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8771''45''10217'_388
                                    (coe
                                       MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8776''45'go_124
                                       (coe d_'8804''45'isPreorder_512)
                                       (coe d_'60''45'resp'45''8771'_780))
                                    (MAlonzo.Code.Data.Rational.Unnormalised.Base.d_'45'__190
                                       (coe
                                          MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'42'__202
                                          (coe v1)
                                          (coe
                                             MAlonzo.Code.Data.Rational.Unnormalised.Base.d_'45'__190
                                             (coe v2))))
                                    (MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'42'__202
                                       (coe
                                          MAlonzo.Code.Data.Rational.Unnormalised.Base.d_'45'__190
                                          (coe v1))
                                       (coe
                                          MAlonzo.Code.Data.Rational.Unnormalised.Base.d_'45'__190
                                          (coe v2)))
                                    (MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'42'__202
                                       (coe
                                          MAlonzo.Code.Data.Rational.Unnormalised.Base.d_'45'__190
                                          (coe v1))
                                       (coe
                                          MAlonzo.Code.Data.Rational.Unnormalised.Base.d_'45'__190
                                          (coe v2)))
                                    (coe
                                       MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                                       (coe
                                          MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_stop_166
                                          (coe d_'8804''45'isPreorder_512))
                                       (coe
                                          MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'42'__202
                                          (coe
                                             MAlonzo.Code.Data.Rational.Unnormalised.Base.d_'45'__190
                                             (coe v1))
                                          (coe
                                             MAlonzo.Code.Data.Rational.Unnormalised.Base.d_'45'__190
                                             (coe v2))))
                                    (d_neg'45'distrib'737''45''42'_1906
                                       (coe v1)
                                       (coe
                                          MAlonzo.Code.Data.Rational.Unnormalised.Base.d_'45'__190
                                          (coe v2))))
                                 (d_'45''8255'cong_378
                                    (coe
                                       MAlonzo.Code.Data.Rational.Unnormalised.Base.d_'45'__190
                                       (coe
                                          MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'42'__202
                                          (coe v1) (coe v2)))
                                    (coe
                                       MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'42'__202
                                       (coe v1)
                                       (coe
                                          MAlonzo.Code.Data.Rational.Unnormalised.Base.d_'45'__190
                                          (coe v2)))
                                    (coe d_neg'45'distrib'691''45''42'_1918 (coe v1) (coe v2))))
                              (coe du_neg'45'involutive_370))
                           v3)
                        (coe du_neg'45'involutive_370))
                     (d_'45''8255'cong_378
                        (coe
                           MAlonzo.Code.Data.Rational.Unnormalised.Base.d_'45'__190
                           (coe
                              MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'42'__202 (coe v0)
                              (coe v2)))
                        (coe
                           MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'42'__202 (coe v0)
                           (coe
                              MAlonzo.Code.Data.Rational.Unnormalised.Base.d_'45'__190 (coe v2)))
                        (coe d_neg'45'distrib'691''45''42'_1918 (coe v0) (coe v2))))
                  (d_neg'45'distrib'737''45''42'_1906
                     (coe v0)
                     (coe
                        MAlonzo.Code.Data.Rational.Unnormalised.Base.d_'45'__190
                        (coe v2)))))))
-- Data.Rational.Unnormalised.Properties.*-cancelˡ-≤-neg
d_'42''45'cancel'737''45''8804''45'neg_2092 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Integer.Base.T_Negative_164 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8804'__38 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8804'__38
d_'42''45'cancel'737''45''8804''45'neg_2092 v0 v1 v2 ~v3
  = du_'42''45'cancel'737''45''8804''45'neg_2092 v0 v1 v2
du_'42''45'cancel'737''45''8804''45'neg_2092 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8804'__38 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8804'__38
du_'42''45'cancel'737''45''8804''45'neg_2092 v0 v1 v2
  = coe
      du_'42''45'cancel'691''45''8804''45'neg_2074 (coe v0) (coe v1)
      (coe v2)
-- Data.Rational.Unnormalised.Properties.*-monoˡ-≤-nonNeg
d_'42''45'mono'737''45''8804''45'nonNeg_2114 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Integer.Base.T_NonNegative_144 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8804'__38 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8804'__38
d_'42''45'mono'737''45''8804''45'nonNeg_2114 v0 ~v1 v2 v3 v4
  = du_'42''45'mono'737''45''8804''45'nonNeg_2114 v0 v2 v3 v4
du_'42''45'mono'737''45''8804''45'nonNeg_2114 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8804'__38 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8804'__38
du_'42''45'mono'737''45''8804''45'nonNeg_2114 v0 v1 v2 v3
  = case coe v0 of
      MAlonzo.Code.Data.Rational.Unnormalised.Base.C_mkℚ'7512'_22 v4 v5
        -> case coe v1 of
             MAlonzo.Code.Data.Rational.Unnormalised.Base.C_mkℚ'7512'_22 v6 v7
               -> case coe v2 of
                    MAlonzo.Code.Data.Rational.Unnormalised.Base.C_mkℚ'7512'_22 v8 v9
                      -> case coe v3 of
                           MAlonzo.Code.Data.Rational.Unnormalised.Base.C_'42''8804''42'_44 v12
                             -> coe
                                  MAlonzo.Code.Data.Rational.Unnormalised.Base.C_'42''8804''42'_44
                                  (coe
                                     MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
                                     (coe
                                        MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_start_96
                                        (coe
                                           MAlonzo.Code.Data.Integer.Properties.d_'8804''45'isPreorder_2822)
                                        (\ v13 v14 v15 ->
                                           coe
                                             MAlonzo.Code.Data.Integer.Properties.du_'60''8658''8804'_2868
                                             v15))
                                     (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                        (coe
                                           MAlonzo.Code.Data.Rational.Unnormalised.Base.d_numerator_14
                                           (coe
                                              MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                                              (\ v13 ->
                                                 MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'42'__202
                                                   (coe v13) (coe v0))
                                              (\ v13 v14 -> v13) v1 v2))
                                        (coe
                                           MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                           (coe
                                              MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                                              (\ v13 v14 -> v14)
                                              (\ v13 ->
                                                 MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'42'__202
                                                   (coe v13) (coe v0))
                                              v1 v2)))
                                     (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                        (coe
                                           MAlonzo.Code.Data.Rational.Unnormalised.Base.d_numerator_14
                                           (coe
                                              MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                                              (\ v13 v14 -> v14)
                                              (\ v13 ->
                                                 MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'42'__202
                                                   (coe v13) (coe v0))
                                              v1 v2))
                                        (coe
                                           MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                           (coe
                                              MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                                              (\ v13 ->
                                                 MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'42'__202
                                                   (coe v13) (coe v0))
                                              (\ v13 v14 -> v13) v1 v2)))
                                     (coe
                                        MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_436
                                        (\ v13 v14 v15 v16 v17 -> v17)
                                        (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                           (coe
                                              MAlonzo.Code.Data.Integer.Base.d__'42'__308 (coe v6)
                                              (coe v4))
                                           (coe
                                              MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                              (coe
                                                 MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                                 (coe v2))
                                              (coe
                                                 MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                                 (coe v0))))
                                        (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                           (coe du_l'8321'_2130 (coe v6) (coe v8) (coe v9))
                                           (coe
                                              MAlonzo.Code.Data.Integer.Base.d__'42'__308 (coe v4)
                                              (coe
                                                 MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                                 (coe v0))))
                                        (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                           (coe
                                              MAlonzo.Code.Data.Rational.Unnormalised.Base.d_numerator_14
                                              (coe
                                                 MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                                                 (\ v13 v14 -> v14)
                                                 (\ v13 ->
                                                    MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'42'__202
                                                      (coe v13) (coe v0))
                                                 v1 v2))
                                           (coe
                                              MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                              (coe
                                                 MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                                                 (\ v13 ->
                                                    MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'42'__202
                                                      (coe v13) (coe v0))
                                                 (\ v13 v14 -> v13) v1 v2)))
                                        (coe
                                           MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10216'_448
                                           (\ v13 v14 v15 v16 v17 -> v17)
                                           (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                              (coe du_l'8321'_2130 (coe v6) (coe v8) (coe v9))
                                              (coe
                                                 MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                 (coe v4)
                                                 (coe
                                                    MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                                    (coe v0))))
                                           (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                              (coe du_l'8321'_2130 (coe v6) (coe v8) (coe v9))
                                              (coe
                                                 mulInt (coe v4)
                                                 (coe
                                                    MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominatorℕ_18
                                                    (coe v0))))
                                           (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                              (coe
                                                 MAlonzo.Code.Data.Rational.Unnormalised.Base.d_numerator_14
                                                 (coe
                                                    MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                                                    (\ v13 v14 -> v14)
                                                    (\ v13 ->
                                                       MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'42'__202
                                                         (coe v13) (coe v0))
                                                    v1 v2))
                                              (coe
                                                 MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                                 (coe
                                                    MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                                                    (\ v13 ->
                                                       MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'42'__202
                                                         (coe v13) (coe v0))
                                                    (\ v13 v14 -> v13) v1 v2)))
                                           (coe
                                              MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8804'_308
                                              (coe
                                                 MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8804''45'go_138
                                                 (coe
                                                    MAlonzo.Code.Data.Integer.Properties.d_'8804''45'isPreorder_2822)
                                                 (\ v13 v14 v15 v16 v17 ->
                                                    coe
                                                      MAlonzo.Code.Data.Integer.Properties.du_'8804''45''60''45'trans_2980
                                                      v16 v17))
                                              (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                 (coe du_l'8321'_2130 (coe v6) (coe v8) (coe v9))
                                                 (coe
                                                    mulInt (coe v4)
                                                    (coe
                                                       MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominatorℕ_18
                                                       (coe v0))))
                                              (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                 (coe du_l'8322'_2132 (coe v6) (coe v7) (coe v8))
                                                 (coe
                                                    mulInt (coe v4)
                                                    (coe
                                                       MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominatorℕ_18
                                                       (coe v0))))
                                              (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                 (coe
                                                    MAlonzo.Code.Data.Rational.Unnormalised.Base.d_numerator_14
                                                    (coe
                                                       MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                                                       (\ v13 v14 -> v14)
                                                       (\ v13 ->
                                                          MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'42'__202
                                                            (coe v13) (coe v0))
                                                       v1 v2))
                                                 (coe
                                                    MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                                    (coe
                                                       MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                                                       (\ v13 ->
                                                          MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'42'__202
                                                            (coe v13) (coe v0))
                                                       (\ v13 v14 -> v13) v1 v2)))
                                              (coe
                                                 MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_436
                                                 (\ v13 v14 v15 v16 v17 -> v17)
                                                 (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                    (coe du_l'8322'_2132 (coe v6) (coe v7) (coe v8))
                                                    (coe
                                                       mulInt (coe v4)
                                                       (coe
                                                          MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominatorℕ_18
                                                          (coe v0))))
                                                 (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                    (coe du_l'8322'_2132 (coe v6) (coe v7) (coe v8))
                                                    (coe
                                                       MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                       (coe v4)
                                                       (coe
                                                          MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                                          (coe v0))))
                                                 (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                    (coe
                                                       MAlonzo.Code.Data.Rational.Unnormalised.Base.d_numerator_14
                                                       (coe
                                                          MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                                                          (\ v13 v14 -> v14)
                                                          (\ v13 ->
                                                             MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'42'__202
                                                               (coe v13) (coe v0))
                                                          v1 v2))
                                                    (coe
                                                       MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                                       (coe
                                                          MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                                                          (\ v13 ->
                                                             MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'42'__202
                                                               (coe v13) (coe v0))
                                                          (\ v13 v14 -> v13) v1 v2)))
                                                 (coe
                                                    MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_436
                                                    (\ v13 v14 v15 v16 v17 -> v17)
                                                    (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                       (coe
                                                          du_l'8322'_2132 (coe v6) (coe v7)
                                                          (coe v8))
                                                       (coe
                                                          MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                          (coe v4)
                                                          (coe
                                                             MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                                             (coe v0))))
                                                    (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                       (coe
                                                          MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                          (coe v8) (coe v4))
                                                       (coe
                                                          MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                          (coe
                                                             MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                                             (coe v1))
                                                          (coe
                                                             MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                                             (coe v0))))
                                                    (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                       (coe
                                                          MAlonzo.Code.Data.Rational.Unnormalised.Base.d_numerator_14
                                                          (coe
                                                             MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                                                             (\ v13 v14 -> v14)
                                                             (\ v13 ->
                                                                MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'42'__202
                                                                  (coe v13) (coe v0))
                                                             v1 v2))
                                                       (coe
                                                          MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                                          (coe
                                                             MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                                                             (\ v13 ->
                                                                MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'42'__202
                                                                  (coe v13) (coe v0))
                                                             (\ v13 v14 -> v13) v1 v2)))
                                                    (let v13
                                                           = MAlonzo.Code.Data.Integer.Properties.d_'8804''45'isPreorder_2822 in
                                                     coe
                                                       (coe
                                                          MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                                                          (coe
                                                             MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_stop_166
                                                             (coe v13))
                                                          (coe
                                                             MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                             (coe
                                                                MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                                (coe v8) (coe v4))
                                                             (coe
                                                                MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                                (coe
                                                                   MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                                                   (coe v1))
                                                                (coe
                                                                   MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                                                   (coe v0))))))
                                                    erased)
                                                 erased)
                                              (coe
                                                 MAlonzo.Code.Data.Integer.Properties.du_'42''45'mono'691''45''8804''45'nonNeg_6034
                                                 (coe
                                                    mulInt (coe v4)
                                                    (coe
                                                       MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominatorℕ_18
                                                       (coe v0)))
                                                 (coe
                                                    MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                    (coe v6)
                                                    (coe
                                                       MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                                       (coe v2)))
                                                 (coe
                                                    MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                    (coe v8)
                                                    (coe
                                                       MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                                       (coe v1)))
                                                 (coe v12)))
                                           erased)
                                        erased))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Rational.Unnormalised.Properties._.l₁
d_l'8321'_2130 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T_NonNegative_144 ->
  Integer ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Data.Integer.Base.T__'8804'__26 -> Integer
d_l'8321'_2130 ~v0 ~v1 ~v2 v3 ~v4 v5 v6 ~v7
  = du_l'8321'_2130 v3 v5 v6
du_l'8321'_2130 :: Integer -> Integer -> Integer -> Integer
du_l'8321'_2130 v0 v1 v2
  = coe
      MAlonzo.Code.Data.Integer.Base.d__'42'__308 (coe v0)
      (coe
         MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
         (coe
            MAlonzo.Code.Data.Rational.Unnormalised.Base.C_mkℚ'7512'_22
            (coe v1) (coe v2)))
-- Data.Rational.Unnormalised.Properties._.l₂
d_l'8322'_2132 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T_NonNegative_144 ->
  Integer ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Data.Integer.Base.T__'8804'__26 -> Integer
d_l'8322'_2132 ~v0 ~v1 ~v2 v3 v4 v5 ~v6 ~v7
  = du_l'8322'_2132 v3 v4 v5
du_l'8322'_2132 :: Integer -> Integer -> Integer -> Integer
du_l'8322'_2132 v0 v1 v2
  = coe
      MAlonzo.Code.Data.Integer.Base.d__'42'__308 (coe v2)
      (coe
         MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
         (coe
            MAlonzo.Code.Data.Rational.Unnormalised.Base.C_mkℚ'7512'_22
            (coe v0) (coe v1)))
-- Data.Rational.Unnormalised.Properties.*-monoʳ-≤-nonNeg
d_'42''45'mono'691''45''8804''45'nonNeg_2144 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Integer.Base.T_NonNegative_144 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8804'__38 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8804'__38
d_'42''45'mono'691''45''8804''45'nonNeg_2144 v0 ~v1 v2 v3
  = du_'42''45'mono'691''45''8804''45'nonNeg_2144 v0 v2 v3
du_'42''45'mono'691''45''8804''45'nonNeg_2144 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8804'__38 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8804'__38
du_'42''45'mono'691''45''8804''45'nonNeg_2144 v0 v1 v2
  = coe
      du_'42''45'mono'737''45''8804''45'nonNeg_2114 (coe v0) (coe v1)
      (coe v2)
-- Data.Rational.Unnormalised.Properties.*-mono-≤-nonNeg
d_'42''45'mono'45''8804''45'nonNeg_2172 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Integer.Base.T_NonNegative_144 ->
  MAlonzo.Code.Data.Integer.Base.T_NonNegative_144 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8804'__38 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8804'__38 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8804'__38
d_'42''45'mono'45''8804''45'nonNeg_2172 v0 v1 v2 v3 ~v4 ~v5 v6 v7
  = du_'42''45'mono'45''8804''45'nonNeg_2172 v0 v1 v2 v3 v6 v7
du_'42''45'mono'45''8804''45'nonNeg_2172 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8804'__38 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8804'__38 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8804'__38
du_'42''45'mono'45''8804''45'nonNeg_2172 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_start_96
         (coe d_'8804''45'isPreorder_512)
         (\ v6 v7 v8 -> coe du_'60''8658''8804'_556 v8))
      (MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'42'__202
         (coe v0) (coe v2))
      (MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'42'__202
         (coe v1) (coe v3))
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8804'_308
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8804''45'go_138
            (coe d_'8804''45'isPreorder_512)
            (coe d_'8804''45''60''45'trans_610))
         (MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'42'__202
            (coe v0) (coe v2))
         (MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'42'__202
            (coe v1) (coe v2))
         (MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'42'__202
            (coe v1) (coe v3))
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8804'_308
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8804''45'go_138
               (coe d_'8804''45'isPreorder_512)
               (coe d_'8804''45''60''45'trans_610))
            (MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'42'__202
               (coe v1) (coe v2))
            (MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'42'__202
               (coe v1) (coe v3))
            (MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'42'__202
               (coe v1) (coe v3))
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_stop_166
                  (coe d_'8804''45'isPreorder_512))
               (coe
                  MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'42'__202 (coe v1)
                  (coe v3)))
            (coe du_'42''45'mono'691''45''8804''45'nonNeg_2144 v1 v2 v3 v5))
         (coe
            du_'42''45'mono'737''45''8804''45'nonNeg_2114 (coe v2) (coe v0)
            (coe v1) (coe v4)))
-- Data.Rational.Unnormalised.Properties.*-monoˡ-≤-nonPos
d_'42''45'mono'737''45''8804''45'nonPos_2196 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Integer.Base.T_NonPositive_154 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8804'__38 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8804'__38
d_'42''45'mono'737''45''8804''45'nonPos_2196 v0 ~v1 v2 v3 v4
  = du_'42''45'mono'737''45''8804''45'nonPos_2196 v0 v2 v3 v4
du_'42''45'mono'737''45''8804''45'nonPos_2196 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8804'__38 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8804'__38
du_'42''45'mono'737''45''8804''45'nonPos_2196 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_start_96
         (coe d_'8804''45'isPreorder_512)
         (\ v4 v5 v6 -> coe du_'60''8658''8804'_556 v6))
      (coe
         MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
         (\ v4 v5 -> v5)
         (\ v4 ->
            MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'42'__202
              (coe v4) (coe v0))
         v1 v2)
      (coe
         MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
         (\ v4 ->
            MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'42'__202
              (coe v4) (coe v0))
         (\ v4 v5 -> v4) v1 v2)
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8771''45''10216'_390
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8776''45'go_124
            (coe d_'8804''45'isPreorder_512)
            (coe d_'60''45'resp'45''8771'_780))
         (\ v4 v5 v6 -> coe du_'8771''45'sym_170 v6)
         (MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'42'__202
            (coe v2) (coe v0))
         (MAlonzo.Code.Data.Rational.Unnormalised.Base.d_'45'__190
            (coe
               MAlonzo.Code.Data.Rational.Unnormalised.Base.d_'45'__190
               (coe
                  MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'42'__202 (coe v2)
                  (coe v0))))
         (coe
            MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
            (\ v4 ->
               MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'42'__202
                 (coe v4) (coe v0))
            (\ v4 v5 -> v4) v1 v2)
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8771''45''10217'_388
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8776''45'go_124
               (coe d_'8804''45'isPreorder_512)
               (coe d_'60''45'resp'45''8771'_780))
            (MAlonzo.Code.Data.Rational.Unnormalised.Base.d_'45'__190
               (coe
                  MAlonzo.Code.Data.Rational.Unnormalised.Base.d_'45'__190
                  (coe
                     MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'42'__202 (coe v2)
                     (coe v0))))
            (MAlonzo.Code.Data.Rational.Unnormalised.Base.d_'45'__190
               (coe
                  MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'42'__202 (coe v2)
                  (coe
                     MAlonzo.Code.Data.Rational.Unnormalised.Base.d_'45'__190
                     (coe v0))))
            (coe
               MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
               (\ v4 ->
                  MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'42'__202
                    (coe v4) (coe v0))
               (\ v4 v5 -> v4) v1 v2)
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8804'_308
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8804''45'go_138
                  (coe d_'8804''45'isPreorder_512)
                  (coe d_'8804''45''60''45'trans_610))
               (MAlonzo.Code.Data.Rational.Unnormalised.Base.d_'45'__190
                  (coe
                     MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'42'__202 (coe v2)
                     (coe
                        MAlonzo.Code.Data.Rational.Unnormalised.Base.d_'45'__190
                        (coe v0))))
               (MAlonzo.Code.Data.Rational.Unnormalised.Base.d_'45'__190
                  (coe
                     MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'42'__202 (coe v1)
                     (coe
                        MAlonzo.Code.Data.Rational.Unnormalised.Base.d_'45'__190
                        (coe v0))))
               (coe
                  MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                  (\ v4 ->
                     MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'42'__202
                       (coe v4) (coe v0))
                  (\ v4 v5 -> v4) v1 v2)
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8771''45''10216'_390
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8776''45'go_124
                     (coe d_'8804''45'isPreorder_512)
                     (coe d_'60''45'resp'45''8771'_780))
                  (\ v4 v5 v6 -> coe du_'8771''45'sym_170 v6)
                  (MAlonzo.Code.Data.Rational.Unnormalised.Base.d_'45'__190
                     (coe
                        MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'42'__202 (coe v1)
                        (coe
                           MAlonzo.Code.Data.Rational.Unnormalised.Base.d_'45'__190
                           (coe v0))))
                  (MAlonzo.Code.Data.Rational.Unnormalised.Base.d_'45'__190
                     (coe
                        MAlonzo.Code.Data.Rational.Unnormalised.Base.d_'45'__190
                        (coe
                           MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'42'__202 (coe v1)
                           (coe v0))))
                  (coe
                     MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                     (\ v4 ->
                        MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'42'__202
                          (coe v4) (coe v0))
                     (\ v4 v5 -> v4) v1 v2)
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8771''45''10217'_388
                     (coe
                        MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8776''45'go_124
                        (coe d_'8804''45'isPreorder_512)
                        (coe d_'60''45'resp'45''8771'_780))
                     (MAlonzo.Code.Data.Rational.Unnormalised.Base.d_'45'__190
                        (coe
                           MAlonzo.Code.Data.Rational.Unnormalised.Base.d_'45'__190
                           (coe
                              MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'42'__202 (coe v1)
                              (coe v0))))
                     (MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'42'__202
                        (coe v1) (coe v0))
                     (coe
                        MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                        (\ v4 ->
                           MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'42'__202
                             (coe v4) (coe v0))
                        (\ v4 v5 -> v4) v1 v2)
                     (coe
                        MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                        (coe
                           MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_stop_166
                           (coe d_'8804''45'isPreorder_512))
                        (coe
                           MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'42'__202 (coe v1)
                           (coe v0)))
                     (coe du_neg'45'involutive_370))
                  (d_'45''8255'cong_378
                     (coe
                        MAlonzo.Code.Data.Rational.Unnormalised.Base.d_'45'__190
                        (coe
                           MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'42'__202 (coe v1)
                           (coe v0)))
                     (coe
                        MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'42'__202 (coe v1)
                        (coe
                           MAlonzo.Code.Data.Rational.Unnormalised.Base.d_'45'__190 (coe v0)))
                     (coe d_neg'45'distrib'691''45''42'_1918 (coe v1) (coe v0))))
               (d_neg'45'mono'45''8804'_1550
                  (coe
                     MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                     (\ v4 ->
                        MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'42'__202
                          (coe v4)
                          (coe
                             MAlonzo.Code.Data.Rational.Unnormalised.Base.d_'45'__190 (coe v0)))
                     (\ v4 v5 -> v4) v1 v2)
                  (coe
                     MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                     (\ v4 v5 -> v5)
                     (\ v4 ->
                        MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'42'__202
                          (coe v4)
                          (coe
                             MAlonzo.Code.Data.Rational.Unnormalised.Base.d_'45'__190 (coe v0)))
                     v1 v2)
                  (coe
                     du_'42''45'mono'737''45''8804''45'nonNeg_2114
                     (coe
                        MAlonzo.Code.Data.Rational.Unnormalised.Base.d_'45'__190 (coe v0))
                     (coe v1) (coe v2) (coe v3))))
            (d_'45''8255'cong_378
               (coe
                  MAlonzo.Code.Data.Rational.Unnormalised.Base.d_'45'__190
                  (coe
                     MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'42'__202 (coe v2)
                     (coe v0)))
               (coe
                  MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'42'__202 (coe v2)
                  (coe
                     MAlonzo.Code.Data.Rational.Unnormalised.Base.d_'45'__190 (coe v0)))
               (coe d_neg'45'distrib'691''45''42'_1918 (coe v2) (coe v0))))
         (coe du_neg'45'involutive_370))
-- Data.Rational.Unnormalised.Properties._.-r≥0
d_'45'r'8805'0_2210 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Integer.Base.T_NonPositive_154 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8804'__38 ->
  MAlonzo.Code.Data.Integer.Base.T_NonNegative_144
d_'45'r'8805'0_2210 v0 ~v1 ~v2 ~v3 ~v4 = du_'45'r'8805'0_2210 v0
du_'45'r'8805'0_2210 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Integer.Base.T_NonNegative_144
du_'45'r'8805'0_2210 v0
  = coe
      MAlonzo.Code.Data.Rational.Unnormalised.Base.d_nonNegative_186
      (coe
         MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
         MAlonzo.Code.Data.Rational.Unnormalised.Base.d_'45'__190
         (\ v1 v2 -> v1) v0
         MAlonzo.Code.Data.Rational.Unnormalised.Base.d_0ℚ'7512'_108)
      (coe
         d_neg'45'mono'45''8804'_1550 (coe v0)
         (coe MAlonzo.Code.Data.Rational.Unnormalised.Base.d_0ℚ'7512'_108)
         (coe du_nonPositive'8315''185'_944 (coe v0)))
-- Data.Rational.Unnormalised.Properties.*-monoʳ-≤-nonPos
d_'42''45'mono'691''45''8804''45'nonPos_2218 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Integer.Base.T_NonPositive_154 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8804'__38 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8804'__38
d_'42''45'mono'691''45''8804''45'nonPos_2218 v0 ~v1 v2 v3
  = du_'42''45'mono'691''45''8804''45'nonPos_2218 v0 v2 v3
du_'42''45'mono'691''45''8804''45'nonPos_2218 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8804'__38 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8804'__38
du_'42''45'mono'691''45''8804''45'nonPos_2218 v0 v1 v2
  = coe
      du_'42''45'mono'737''45''8804''45'nonPos_2196 (coe v0) (coe v1)
      (coe v2)
-- Data.Rational.Unnormalised.Properties.*-monoˡ-<-pos
d_'42''45'mono'737''45''60''45'pos_2240 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Integer.Base.T_Positive_134 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'60'__46 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'60'__46
d_'42''45'mono'737''45''60''45'pos_2240 v0 ~v1 v2 v3 v4
  = du_'42''45'mono'737''45''60''45'pos_2240 v0 v2 v3 v4
du_'42''45'mono'737''45''60''45'pos_2240 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'60'__46 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'60'__46
du_'42''45'mono'737''45''60''45'pos_2240 v0 v1 v2 v3
  = case coe v0 of
      MAlonzo.Code.Data.Rational.Unnormalised.Base.C_mkℚ'7512'_22 v4 v5
        -> case coe v1 of
             MAlonzo.Code.Data.Rational.Unnormalised.Base.C_mkℚ'7512'_22 v6 v7
               -> case coe v2 of
                    MAlonzo.Code.Data.Rational.Unnormalised.Base.C_mkℚ'7512'_22 v8 v9
                      -> case coe v3 of
                           MAlonzo.Code.Data.Rational.Unnormalised.Base.C_'42''60''42'_52 v12
                             -> coe
                                  MAlonzo.Code.Data.Rational.Unnormalised.Base.C_'42''60''42'_52
                                  (let v13
                                         = coe
                                             MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_strictRelation_202 in
                                   coe
                                     (coe
                                        MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__126
                                        (coe v13)
                                        (coe
                                           MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                           (coe
                                              MAlonzo.Code.Data.Integer.Base.d__'42'__308 (coe v6)
                                              (coe v4))
                                           (coe
                                              MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                              (coe
                                                 MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                                 (coe v2))
                                              (coe
                                                 MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                                 (coe v0))))
                                        (coe
                                           MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                           (coe
                                              MAlonzo.Code.Data.Integer.Base.d__'42'__308 (coe v8)
                                              (coe v4))
                                           (coe
                                              MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                              (coe
                                                 MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                                 (coe v1))
                                              (coe
                                                 MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                                 (coe v0))))
                                        (coe
                                           MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_436
                                           (\ v14 v15 v16 v17 v18 -> v18)
                                           (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                              (coe
                                                 MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                 (coe v6) (coe v4))
                                              (coe
                                                 MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                 (coe
                                                    MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                                    (coe v2))
                                                 (coe
                                                    MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                                    (coe v0))))
                                           (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                              (coe
                                                 MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                 (coe
                                                    MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                    (coe v6)
                                                    (coe
                                                       MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                                       (coe v2)))
                                                 (coe v4))
                                              (coe
                                                 MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                                 (coe v0)))
                                           (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                              (coe
                                                 MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                 (coe v8) (coe v4))
                                              (coe
                                                 MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                 (coe
                                                    MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                                    (coe v1))
                                                 (coe
                                                    MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                                    (coe v0))))
                                           (coe
                                              MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''60'_312
                                              (coe
                                                 MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'60''45'go_152
                                                 (\ v14 v15 v16 v17 v18 ->
                                                    coe
                                                      MAlonzo.Code.Data.Integer.Properties.du_'60''45'trans_3008
                                                      v17 v18)
                                                 (coe
                                                    MAlonzo.Code.Relation.Binary.PropositionalEquality.Core.du_resp'8322'_160)
                                                 (\ v14 v15 v16 v17 v18 ->
                                                    coe
                                                      MAlonzo.Code.Data.Integer.Properties.du_'60''45''8804''45'trans_2994
                                                      v17 v18))
                                              (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                 (coe
                                                    MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                    (coe
                                                       MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                       (coe v6)
                                                       (coe
                                                          MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                                          (coe v2)))
                                                    (coe v4))
                                                 (coe
                                                    MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                                    (coe v0)))
                                              (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                 (coe
                                                    MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                    (coe
                                                       MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                       (coe v8)
                                                       (coe
                                                          MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                                          (coe v1)))
                                                    (coe v4))
                                                 (coe
                                                    MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                                    (coe v0)))
                                              (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                 (coe
                                                    MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                    (coe v8) (coe v4))
                                                 (coe
                                                    MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                    (coe
                                                       MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                                       (coe v1))
                                                    (coe
                                                       MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                                       (coe v0))))
                                              (coe
                                                 MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10216'_448
                                                 (\ v14 v15 v16 v17 v18 -> v18)
                                                 (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                    (coe
                                                       MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                       (coe
                                                          MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                          (coe v8)
                                                          (coe
                                                             MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                                             (coe v1)))
                                                       (coe v4))
                                                    (coe
                                                       MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                                       (coe v0)))
                                                 (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                    (coe
                                                       MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                       (coe v8) (coe v4))
                                                    (coe
                                                       MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                       (coe
                                                          MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                                          (coe v1))
                                                       (coe
                                                          MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                                          (coe v0))))
                                                 (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                    (coe
                                                       MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                       (coe v8) (coe v4))
                                                    (coe
                                                       MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                       (coe
                                                          MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                                          (coe v1))
                                                       (coe
                                                          MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                                          (coe v0))))
                                                 (coe
                                                    MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                                                    (coe
                                                       MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_stop_166
                                                       (coe
                                                          MAlonzo.Code.Data.Integer.Properties.d_'8804''45'isPreorder_2822))
                                                    (coe
                                                       MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                       (coe
                                                          MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                          (coe v8) (coe v4))
                                                       (coe
                                                          MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                          (coe
                                                             MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                                             (coe v1))
                                                          (coe
                                                             MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                                             (coe v0)))))
                                                 erased)
                                              (coe
                                                 MAlonzo.Code.Data.Integer.Properties.du_'42''45'mono'691''45''60''45'pos_6226
                                                 (MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                                    (coe v0))
                                                 (coe
                                                    MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                                                    (\ v14 ->
                                                       MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                         (coe v14) (coe v4))
                                                    (\ v14 v15 -> v14)
                                                    (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                       (coe v6)
                                                       (coe
                                                          MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                                          (coe v2)))
                                                    (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                       (coe v8)
                                                       (coe
                                                          MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                                          (coe v1))))
                                                 (coe
                                                    MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                                                    (\ v14 v15 -> v15)
                                                    (\ v14 ->
                                                       MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                         (coe v14) (coe v4))
                                                    (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                       (coe v6)
                                                       (coe
                                                          MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                                          (coe v2)))
                                                    (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                       (coe v8)
                                                       (coe
                                                          MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                                          (coe v1))))
                                                 (coe
                                                    MAlonzo.Code.Data.Integer.Properties.du_'42''45'mono'691''45''60''45'pos_6226
                                                    v4
                                                    (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                       (coe v6)
                                                       (coe
                                                          MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                                          (coe v2)))
                                                    (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                       (coe v8)
                                                       (coe
                                                          MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                                          (coe v1)))
                                                    v12)))
                                           erased)))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Rational.Unnormalised.Properties.*-monoʳ-<-pos
d_'42''45'mono'691''45''60''45'pos_2260 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Integer.Base.T_Positive_134 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'60'__46 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'60'__46
d_'42''45'mono'691''45''60''45'pos_2260 v0 ~v1 v2 v3
  = du_'42''45'mono'691''45''60''45'pos_2260 v0 v2 v3
du_'42''45'mono'691''45''60''45'pos_2260 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'60'__46 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'60'__46
du_'42''45'mono'691''45''60''45'pos_2260 v0 v1 v2
  = coe
      du_'42''45'mono'737''45''60''45'pos_2240 (coe v0) (coe v1) (coe v2)
-- Data.Rational.Unnormalised.Properties.*-mono-<-nonNeg
d_'42''45'mono'45''60''45'nonNeg_2288 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Integer.Base.T_NonNegative_144 ->
  MAlonzo.Code.Data.Integer.Base.T_NonNegative_144 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'60'__46 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'60'__46 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'60'__46
d_'42''45'mono'45''60''45'nonNeg_2288 v0 v1 v2 v3 ~v4 ~v5 v6 v7
  = du_'42''45'mono'45''60''45'nonNeg_2288 v0 v1 v2 v3 v6 v7
du_'42''45'mono'45''60''45'nonNeg_2288 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'60'__46 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'60'__46 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'60'__46
du_'42''45'mono'45''60''45'nonNeg_2288 v0 v1 v2 v3 v4 v5
  = let v6
          = coe
              MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_strictRelation_202 in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__126
         (coe v6)
         (coe
            MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'42'__202 (coe v0)
            (coe v2))
         (coe
            MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'42'__202 (coe v1)
            (coe v3))
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8804'_308
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8804''45'go_138
               (coe d_'8804''45'isPreorder_512)
               (coe d_'8804''45''60''45'trans_610))
            (MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'42'__202
               (coe v0) (coe v2))
            (MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'42'__202
               (coe v1) (coe v2))
            (MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'42'__202
               (coe v1) (coe v3))
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''60'_312
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'60''45'go_152
                  (coe d_'60''45'trans_678) (coe d_'60''45'resp'45''8771'_780)
                  (coe d_'60''45''8804''45'trans_644))
               (MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'42'__202
                  (coe v1) (coe v2))
               (MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'42'__202
                  (coe v1) (coe v3))
               (MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'42'__202
                  (coe v1) (coe v3))
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_stop_166
                     (coe d_'8804''45'isPreorder_512))
                  (coe
                     MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'42'__202 (coe v1)
                     (coe v3)))
               (coe du_'42''45'mono'691''45''60''45'pos_2260 v1 v2 v3 v5))
            (coe
               du_'42''45'mono'737''45''8804''45'nonNeg_2114 (coe v2) (coe v0)
               (coe v1) (coe du_'60''8658''8804'_556 (coe v4)))))
-- Data.Rational.Unnormalised.Properties.*-cancelʳ-<-nonNeg
d_'42''45'cancel'691''45''60''45'nonNeg_2310 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Integer.Base.T_NonNegative_144 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'60'__46 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'60'__46
d_'42''45'cancel'691''45''60''45'nonNeg_2310 v0 v1 v2 ~v3 v4
  = du_'42''45'cancel'691''45''60''45'nonNeg_2310 v0 v1 v2 v4
du_'42''45'cancel'691''45''60''45'nonNeg_2310 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'60'__46 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'60'__46
du_'42''45'cancel'691''45''60''45'nonNeg_2310 v0 v1 v2 v3
  = case coe v0 of
      MAlonzo.Code.Data.Rational.Unnormalised.Base.C_mkℚ'7512'_22 v4 v5
        -> case coe v1 of
             MAlonzo.Code.Data.Rational.Unnormalised.Base.C_mkℚ'7512'_22 v6 v7
               -> case coe v2 of
                    MAlonzo.Code.Data.Rational.Unnormalised.Base.C_mkℚ'7512'_22 v8 v9
                      -> case coe v3 of
                           MAlonzo.Code.Data.Rational.Unnormalised.Base.C_'42''60''42'_52 v12
                             -> coe
                                  MAlonzo.Code.Data.Rational.Unnormalised.Base.C_'42''60''42'_52
                                  (coe
                                     MAlonzo.Code.Data.Integer.Properties.du_'42''45'cancel'691''45''60''45'nonNeg_6284
                                     (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                        (coe v4)
                                        (coe
                                           MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                           (coe v1)))
                                     (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                        (coe v6)
                                        (coe
                                           MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                           (coe v0)))
                                     (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                        (coe v8)
                                        (coe
                                           MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                           (coe v2)))
                                     (let v13
                                            = coe
                                                MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_strictRelation_202 in
                                      coe
                                        (coe
                                           MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__126
                                           (coe v13)
                                           (coe
                                              MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                              (coe
                                                 MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                 (coe v4)
                                                 (coe
                                                    MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                                    (coe v1)))
                                              (coe
                                                 MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                 (coe v8)
                                                 (coe
                                                    MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                                    (coe v2))))
                                           (coe
                                              MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                              (coe
                                                 MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                 (coe v6)
                                                 (coe
                                                    MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                                    (coe v0)))
                                              (coe
                                                 MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                 (coe v8)
                                                 (coe
                                                    MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                                    (coe v2))))
                                           (coe
                                              MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_436
                                              (\ v14 v15 v16 v17 v18 -> v18)
                                              (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                 (coe
                                                    MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                    (coe v4)
                                                    (coe
                                                       MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                                       (coe v1)))
                                                 (coe
                                                    MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                    (coe v8)
                                                    (coe
                                                       MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                                       (coe v2))))
                                              (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                 (coe
                                                    MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                    (coe v4) (coe v8))
                                                 (coe
                                                    MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                    (coe
                                                       MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                                       (coe v1))
                                                    (coe
                                                       MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                                       (coe v2))))
                                              (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                 (coe
                                                    MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                    (coe v6)
                                                    (coe
                                                       MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                                       (coe v0)))
                                                 (coe
                                                    MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                    (coe v8)
                                                    (coe
                                                       MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                                       (coe v2))))
                                              (coe
                                                 MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''60'_312
                                                 (coe
                                                    MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'60''45'go_152
                                                    (\ v14 v15 v16 v17 v18 ->
                                                       coe
                                                         MAlonzo.Code.Data.Integer.Properties.du_'60''45'trans_3008
                                                         v17 v18)
                                                    (coe
                                                       MAlonzo.Code.Relation.Binary.PropositionalEquality.Core.du_resp'8322'_160)
                                                    (\ v14 v15 v16 v17 v18 ->
                                                       coe
                                                         MAlonzo.Code.Data.Integer.Properties.du_'60''45''8804''45'trans_2994
                                                         v17 v18))
                                                 (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                    (coe
                                                       MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                       (coe v4) (coe v8))
                                                    (coe
                                                       MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                       (coe
                                                          MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                                          (coe v1))
                                                       (coe
                                                          MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                                          (coe v2))))
                                                 (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                    (coe
                                                       MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                       (coe v6) (coe v8))
                                                    (coe
                                                       MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                       (coe
                                                          MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                                          (coe v0))
                                                       (coe
                                                          MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                                          (coe v2))))
                                                 (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                    (coe
                                                       MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                       (coe v6)
                                                       (coe
                                                          MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                                          (coe v0)))
                                                    (coe
                                                       MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                       (coe v8)
                                                       (coe
                                                          MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                                          (coe v2))))
                                                 (coe
                                                    MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_436
                                                    (\ v14 v15 v16 v17 v18 -> v18)
                                                    (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                       (coe
                                                          MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                          (coe v6) (coe v8))
                                                       (coe
                                                          MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                          (coe
                                                             MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                                             (coe v0))
                                                          (coe
                                                             MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                                             (coe v2))))
                                                    (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                       (coe
                                                          MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                          (coe v6)
                                                          (coe
                                                             MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                                             (coe v0)))
                                                       (coe
                                                          MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                          (coe v8)
                                                          (coe
                                                             MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                                             (coe v2))))
                                                    (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                       (coe
                                                          MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                          (coe v6)
                                                          (coe
                                                             MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                                             (coe v0)))
                                                       (coe
                                                          MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                          (coe v8)
                                                          (coe
                                                             MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                                             (coe v2))))
                                                    (coe
                                                       MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                                                       (coe
                                                          MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_stop_166
                                                          (coe
                                                             MAlonzo.Code.Data.Integer.Properties.d_'8804''45'isPreorder_2822))
                                                       (coe
                                                          MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                          (coe
                                                             MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                             (coe v6)
                                                             (coe
                                                                MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                                                (coe v0)))
                                                          (coe
                                                             MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                                             (coe v8)
                                                             (coe
                                                                MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                                                (coe v2)))))
                                                    erased)
                                                 v12)
                                              erased))))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Rational.Unnormalised.Properties.*-cancelˡ-<-nonNeg
d_'42''45'cancel'737''45''60''45'nonNeg_2328 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Integer.Base.T_NonNegative_144 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'60'__46 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'60'__46
d_'42''45'cancel'737''45''60''45'nonNeg_2328 v0 v1 v2 ~v3
  = du_'42''45'cancel'737''45''60''45'nonNeg_2328 v0 v1 v2
du_'42''45'cancel'737''45''60''45'nonNeg_2328 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'60'__46 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'60'__46
du_'42''45'cancel'737''45''60''45'nonNeg_2328 v0 v1 v2
  = coe
      du_'42''45'cancel'691''45''60''45'nonNeg_2310 (coe v0) (coe v1)
      (coe v2)
-- Data.Rational.Unnormalised.Properties.*-monoˡ-<-neg
d_'42''45'mono'737''45''60''45'neg_2350 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Integer.Base.T_Negative_164 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'60'__46 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'60'__46
d_'42''45'mono'737''45''60''45'neg_2350 v0 ~v1 v2 v3 v4
  = du_'42''45'mono'737''45''60''45'neg_2350 v0 v2 v3 v4
du_'42''45'mono'737''45''60''45'neg_2350 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'60'__46 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'60'__46
du_'42''45'mono'737''45''60''45'neg_2350 v0 v1 v2 v3
  = let v4
          = coe
              MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_strictRelation_202 in
    coe
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__126
         (coe v4)
         (coe
            MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'42'__202 (coe v2)
            (coe v0))
         (coe
            MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'42'__202 (coe v1)
            (coe v0))
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8771''45''10216'_390
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8776''45'go_124
               (coe d_'8804''45'isPreorder_512)
               (coe d_'60''45'resp'45''8771'_780))
            (\ v5 v6 v7 -> coe du_'8771''45'sym_170 v7)
            (MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'42'__202
               (coe v2) (coe v0))
            (MAlonzo.Code.Data.Rational.Unnormalised.Base.d_'45'__190
               (coe
                  MAlonzo.Code.Data.Rational.Unnormalised.Base.d_'45'__190
                  (coe
                     MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'42'__202 (coe v2)
                     (coe v0))))
            (MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'42'__202
               (coe v1) (coe v0))
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8771''45''10217'_388
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8776''45'go_124
                  (coe d_'8804''45'isPreorder_512)
                  (coe d_'60''45'resp'45''8771'_780))
               (MAlonzo.Code.Data.Rational.Unnormalised.Base.d_'45'__190
                  (coe
                     MAlonzo.Code.Data.Rational.Unnormalised.Base.d_'45'__190
                     (coe
                        MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'42'__202 (coe v2)
                        (coe v0))))
               (MAlonzo.Code.Data.Rational.Unnormalised.Base.d_'45'__190
                  (coe
                     MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'42'__202 (coe v2)
                     (coe
                        MAlonzo.Code.Data.Rational.Unnormalised.Base.d_'45'__190
                        (coe v0))))
               (MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'42'__202
                  (coe v1) (coe v0))
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''60'_312
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'60''45'go_152
                     (coe d_'60''45'trans_678) (coe d_'60''45'resp'45''8771'_780)
                     (coe d_'60''45''8804''45'trans_644))
                  (MAlonzo.Code.Data.Rational.Unnormalised.Base.d_'45'__190
                     (coe
                        MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'42'__202 (coe v2)
                        (coe
                           MAlonzo.Code.Data.Rational.Unnormalised.Base.d_'45'__190
                           (coe v0))))
                  (MAlonzo.Code.Data.Rational.Unnormalised.Base.d_'45'__190
                     (coe
                        MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'42'__202 (coe v1)
                        (coe
                           MAlonzo.Code.Data.Rational.Unnormalised.Base.d_'45'__190
                           (coe v0))))
                  (MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'42'__202
                     (coe v1) (coe v0))
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8771''45''10216'_390
                     (coe
                        MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8776''45'go_124
                        (coe d_'8804''45'isPreorder_512)
                        (coe d_'60''45'resp'45''8771'_780))
                     (\ v5 v6 v7 -> coe du_'8771''45'sym_170 v7)
                     (MAlonzo.Code.Data.Rational.Unnormalised.Base.d_'45'__190
                        (coe
                           MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'42'__202 (coe v1)
                           (coe
                              MAlonzo.Code.Data.Rational.Unnormalised.Base.d_'45'__190
                              (coe v0))))
                     (MAlonzo.Code.Data.Rational.Unnormalised.Base.d_'45'__190
                        (coe
                           MAlonzo.Code.Data.Rational.Unnormalised.Base.d_'45'__190
                           (coe
                              MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'42'__202 (coe v1)
                              (coe v0))))
                     (MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'42'__202
                        (coe v1) (coe v0))
                     (coe
                        MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8771''45''10217'_388
                        (coe
                           MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8776''45'go_124
                           (coe d_'8804''45'isPreorder_512)
                           (coe d_'60''45'resp'45''8771'_780))
                        (MAlonzo.Code.Data.Rational.Unnormalised.Base.d_'45'__190
                           (coe
                              MAlonzo.Code.Data.Rational.Unnormalised.Base.d_'45'__190
                              (coe
                                 MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'42'__202 (coe v1)
                                 (coe v0))))
                        (MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'42'__202
                           (coe v1) (coe v0))
                        (MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'42'__202
                           (coe v1) (coe v0))
                        (coe
                           MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                           (coe
                              MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_stop_166
                              (coe d_'8804''45'isPreorder_512))
                           (coe
                              MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'42'__202 (coe v1)
                              (coe v0)))
                        (coe du_neg'45'involutive_370))
                     (d_'45''8255'cong_378
                        (coe
                           MAlonzo.Code.Data.Rational.Unnormalised.Base.d_'45'__190
                           (coe
                              MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'42'__202 (coe v1)
                              (coe v0)))
                        (coe
                           MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'42'__202 (coe v1)
                           (coe
                              MAlonzo.Code.Data.Rational.Unnormalised.Base.d_'45'__190 (coe v0)))
                        (coe d_neg'45'distrib'691''45''42'_1918 (coe v1) (coe v0))))
                  (d_neg'45'mono'45''60'_400
                     (coe
                        MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                        (\ v5 ->
                           MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'42'__202
                             (coe v5)
                             (coe
                                MAlonzo.Code.Data.Rational.Unnormalised.Base.d_'45'__190 (coe v0)))
                        (\ v5 v6 -> v5) v1 v2)
                     (coe
                        MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                        (\ v5 v6 -> v6)
                        (\ v5 ->
                           MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'42'__202
                             (coe v5)
                             (coe
                                MAlonzo.Code.Data.Rational.Unnormalised.Base.d_'45'__190 (coe v0)))
                        v1 v2)
                     (coe
                        du_'42''45'mono'737''45''60''45'pos_2240
                        (coe
                           MAlonzo.Code.Data.Rational.Unnormalised.Base.d_'45'__190 (coe v0))
                        (coe v1) (coe v2) (coe v3))))
               (d_'45''8255'cong_378
                  (coe
                     MAlonzo.Code.Data.Rational.Unnormalised.Base.d_'45'__190
                     (coe
                        MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'42'__202 (coe v2)
                        (coe v0)))
                  (coe
                     MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'42'__202 (coe v2)
                     (coe
                        MAlonzo.Code.Data.Rational.Unnormalised.Base.d_'45'__190 (coe v0)))
                  (coe d_neg'45'distrib'691''45''42'_1918 (coe v2) (coe v0))))
            (coe du_neg'45'involutive_370)))
-- Data.Rational.Unnormalised.Properties._.-r>0
d_'45'r'62'0_2364 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Integer.Base.T_Negative_164 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'60'__46 ->
  MAlonzo.Code.Data.Integer.Base.T_Positive_134
d_'45'r'62'0_2364 v0 ~v1 ~v2 ~v3 ~v4 = du_'45'r'62'0_2364 v0
du_'45'r'62'0_2364 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Integer.Base.T_Positive_134
du_'45'r'62'0_2364 v0
  = coe
      MAlonzo.Code.Data.Rational.Unnormalised.Base.d_positive_162
      (coe
         MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
         MAlonzo.Code.Data.Rational.Unnormalised.Base.d_'45'__190
         (\ v1 v2 -> v1) v0
         MAlonzo.Code.Data.Rational.Unnormalised.Base.d_0ℚ'7512'_108)
      (coe
         d_neg'45'mono'45''60'_400 (coe v0)
         (coe MAlonzo.Code.Data.Rational.Unnormalised.Base.d_0ℚ'7512'_108)
         (coe du_negative'8315''185'_938 (coe v0)))
-- Data.Rational.Unnormalised.Properties.*-monoʳ-<-neg
d_'42''45'mono'691''45''60''45'neg_2372 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Integer.Base.T_Negative_164 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'60'__46 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'60'__46
d_'42''45'mono'691''45''60''45'neg_2372 v0 ~v1 v2 v3
  = du_'42''45'mono'691''45''60''45'neg_2372 v0 v2 v3
du_'42''45'mono'691''45''60''45'neg_2372 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'60'__46 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'60'__46
du_'42''45'mono'691''45''60''45'neg_2372 v0 v1 v2
  = coe
      du_'42''45'mono'737''45''60''45'neg_2350 (coe v0) (coe v1) (coe v2)
-- Data.Rational.Unnormalised.Properties.*-cancelˡ-<-nonPos
d_'42''45'cancel'737''45''60''45'nonPos_2392 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Integer.Base.T_NonPositive_154 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'60'__46 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'60'__46
d_'42''45'cancel'737''45''60''45'nonPos_2392 v0 v1 v2 ~v3 v4
  = du_'42''45'cancel'737''45''60''45'nonPos_2392 v0 v1 v2 v4
du_'42''45'cancel'737''45''60''45'nonPos_2392 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'60'__46 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'60'__46
du_'42''45'cancel'737''45''60''45'nonPos_2392 v0 v1 v2 v3
  = coe
      du_'42''45'cancel'737''45''60''45'nonNeg_2328 v1 v0
      (MAlonzo.Code.Data.Rational.Unnormalised.Base.d_'45'__190 (coe v2))
      (let v4
             = coe
                 MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_strictRelation_202 in
       coe
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__126
            (coe v4)
            (coe
               MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'42'__202
               (coe
                  MAlonzo.Code.Data.Rational.Unnormalised.Base.d_'45'__190 (coe v2))
               (coe v1))
            (coe
               MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'42'__202
               (coe
                  MAlonzo.Code.Data.Rational.Unnormalised.Base.d_'45'__190 (coe v2))
               (coe v0))
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8771''45''10216'_390
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8776''45'go_124
                  (coe d_'8804''45'isPreorder_512)
                  (coe d_'60''45'resp'45''8771'_780))
               (\ v5 v6 v7 -> coe du_'8771''45'sym_170 v7)
               (MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'42'__202
                  (coe
                     MAlonzo.Code.Data.Rational.Unnormalised.Base.d_'45'__190 (coe v2))
                  (coe v1))
               (MAlonzo.Code.Data.Rational.Unnormalised.Base.d_'45'__190
                  (coe
                     MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'42'__202 (coe v2)
                     (coe v1)))
               (MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'42'__202
                  (coe
                     MAlonzo.Code.Data.Rational.Unnormalised.Base.d_'45'__190 (coe v2))
                  (coe v0))
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''60'_312
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'60''45'go_152
                     (coe d_'60''45'trans_678) (coe d_'60''45'resp'45''8771'_780)
                     (coe d_'60''45''8804''45'trans_644))
                  (MAlonzo.Code.Data.Rational.Unnormalised.Base.d_'45'__190
                     (coe
                        MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'42'__202 (coe v2)
                        (coe v1)))
                  (MAlonzo.Code.Data.Rational.Unnormalised.Base.d_'45'__190
                     (coe
                        MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'42'__202 (coe v2)
                        (coe v0)))
                  (MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'42'__202
                     (coe
                        MAlonzo.Code.Data.Rational.Unnormalised.Base.d_'45'__190 (coe v2))
                     (coe v0))
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8771''45''10217'_388
                     (coe
                        MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8776''45'go_124
                        (coe d_'8804''45'isPreorder_512)
                        (coe d_'60''45'resp'45''8771'_780))
                     (MAlonzo.Code.Data.Rational.Unnormalised.Base.d_'45'__190
                        (coe
                           MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'42'__202 (coe v2)
                           (coe v0)))
                     (MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'42'__202
                        (coe
                           MAlonzo.Code.Data.Rational.Unnormalised.Base.d_'45'__190 (coe v2))
                        (coe v0))
                     (MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'42'__202
                        (coe
                           MAlonzo.Code.Data.Rational.Unnormalised.Base.d_'45'__190 (coe v2))
                        (coe v0))
                     (coe
                        MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                        (coe
                           MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_stop_166
                           (coe d_'8804''45'isPreorder_512))
                        (coe
                           MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'42'__202
                           (coe
                              MAlonzo.Code.Data.Rational.Unnormalised.Base.d_'45'__190 (coe v2))
                           (coe v0)))
                     (d_neg'45'distrib'737''45''42'_1906 (coe v2) (coe v0)))
                  (d_neg'45'mono'45''60'_400
                     (coe
                        MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'42'__202 (coe v2)
                        (coe v0))
                     (coe
                        MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'42'__202 (coe v2)
                        (coe v1))
                     (coe v3)))
               (d_neg'45'distrib'737''45''42'_1906 (coe v2) (coe v1)))))
-- Data.Rational.Unnormalised.Properties._.-r≥0
d_'45'r'8805'0_2406 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Integer.Base.T_NonPositive_154 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'60'__46 ->
  MAlonzo.Code.Data.Integer.Base.T_NonNegative_144
d_'45'r'8805'0_2406 ~v0 ~v1 v2 ~v3 ~v4 = du_'45'r'8805'0_2406 v2
du_'45'r'8805'0_2406 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Integer.Base.T_NonNegative_144
du_'45'r'8805'0_2406 v0
  = coe
      MAlonzo.Code.Data.Rational.Unnormalised.Base.d_nonNegative_186
      (coe
         MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
         MAlonzo.Code.Data.Rational.Unnormalised.Base.d_'45'__190
         (\ v1 v2 -> v1) v0
         MAlonzo.Code.Data.Rational.Unnormalised.Base.d_0ℚ'7512'_108)
      (coe
         d_neg'45'mono'45''8804'_1550 (coe v0)
         (coe MAlonzo.Code.Data.Rational.Unnormalised.Base.d_0ℚ'7512'_108)
         (coe du_nonPositive'8315''185'_944 (coe v0)))
-- Data.Rational.Unnormalised.Properties.*-cancelʳ-<-nonPos
d_'42''45'cancel'691''45''60''45'nonPos_2412 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Integer.Base.T_NonPositive_154 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'60'__46 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'60'__46
d_'42''45'cancel'691''45''60''45'nonPos_2412 v0 v1 v2 ~v3
  = du_'42''45'cancel'691''45''60''45'nonPos_2412 v0 v1 v2
du_'42''45'cancel'691''45''60''45'nonPos_2412 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'60'__46 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'60'__46
du_'42''45'cancel'691''45''60''45'nonPos_2412 v0 v1 v2
  = coe
      du_'42''45'cancel'737''45''60''45'nonPos_2392 (coe v0) (coe v1)
      (coe v2)
-- Data.Rational.Unnormalised.Properties.pos*pos⇒pos
d_pos'42'pos'8658'pos_2436 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Integer.Base.T_Positive_134 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Integer.Base.T_Positive_134 ->
  MAlonzo.Code.Data.Integer.Base.T_Positive_134
d_pos'42'pos'8658'pos_2436 v0 ~v1 v2 ~v3
  = du_pos'42'pos'8658'pos_2436 v0 v2
du_pos'42'pos'8658'pos_2436 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Integer.Base.T_Positive_134
du_pos'42'pos'8658'pos_2436 v0 v1
  = coe
      MAlonzo.Code.Data.Rational.Unnormalised.Base.d_positive_162
      (coe
         MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'42'__202 (coe v0)
         (coe v1))
      (coe
         du_'42''45'mono'45''60''45'nonNeg_2288
         (coe MAlonzo.Code.Data.Rational.Unnormalised.Base.d_0ℚ'7512'_108)
         (coe v0)
         (coe MAlonzo.Code.Data.Rational.Unnormalised.Base.d_0ℚ'7512'_108)
         (coe v1) (coe du_positive'8315''185'_926 (coe v0))
         (coe du_positive'8315''185'_926 (coe v1)))
-- Data.Rational.Unnormalised.Properties.nonNeg*nonNeg⇒nonNeg
d_nonNeg'42'nonNeg'8658'nonNeg_2450 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Integer.Base.T_NonNegative_144 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Integer.Base.T_NonNegative_144 ->
  MAlonzo.Code.Data.Integer.Base.T_NonNegative_144
d_nonNeg'42'nonNeg'8658'nonNeg_2450 v0 ~v1 v2 ~v3
  = du_nonNeg'42'nonNeg'8658'nonNeg_2450 v0 v2
du_nonNeg'42'nonNeg'8658'nonNeg_2450 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Integer.Base.T_NonNegative_144
du_nonNeg'42'nonNeg'8658'nonNeg_2450 v0 v1
  = coe
      MAlonzo.Code.Data.Rational.Unnormalised.Base.d_nonNegative_186
      (coe
         MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'42'__202 (coe v0)
         (coe v1))
      (coe
         du_'42''45'mono'45''8804''45'nonNeg_2172
         (coe MAlonzo.Code.Data.Rational.Unnormalised.Base.d_0ℚ'7512'_108)
         (coe v0)
         (coe MAlonzo.Code.Data.Rational.Unnormalised.Base.d_0ℚ'7512'_108)
         (coe v1) (coe du_nonNegative'8315''185'_932 (coe v0))
         (coe du_nonNegative'8315''185'_932 (coe v1)))
-- Data.Rational.Unnormalised.Properties.*-isMagma
d_'42''45'isMagma_2456 ::
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176
d_'42''45'isMagma_2456
  = coe
      MAlonzo.Code.Algebra.Structures.C_IsMagma'46'constructor_1867
      (coe d_'8771''45'isEquivalence_260) (coe d_'42''45'cong_1666)
-- Data.Rational.Unnormalised.Properties.*-isSemigroup
d_'42''45'isSemigroup_2458 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_470
d_'42''45'isSemigroup_2458
  = coe
      MAlonzo.Code.Algebra.Structures.C_IsSemigroup'46'constructor_9889
      (coe d_'42''45'isMagma_2456)
      (\ v0 v1 v2 -> coe du_'42''45'assoc_1736)
-- Data.Rational.Unnormalised.Properties.*-1-isMonoid
d_'42''45'1'45'isMonoid_2460 ::
  MAlonzo.Code.Algebra.Structures.T_IsMonoid_684
d_'42''45'1'45'isMonoid_2460
  = coe
      MAlonzo.Code.Algebra.Structures.C_IsMonoid'46'constructor_15345
      (coe d_'42''45'isSemigroup_2458) (coe d_'42''45'identity_1784)
-- Data.Rational.Unnormalised.Properties.*-1-isCommutativeMonoid
d_'42''45'1'45'isCommutativeMonoid_2462 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeMonoid_734
d_'42''45'1'45'isCommutativeMonoid_2462
  = coe
      MAlonzo.Code.Algebra.Structures.C_IsCommutativeMonoid'46'constructor_17167
      (coe d_'42''45'1'45'isMonoid_2460)
      (\ v0 v1 -> coe du_'42''45'comm_1762)
-- Data.Rational.Unnormalised.Properties.+-*-isRing
d_'43''45''42''45'isRing_2464 ::
  MAlonzo.Code.Algebra.Structures.T_IsRing_2670
d_'43''45''42''45'isRing_2464
  = coe
      MAlonzo.Code.Algebra.Structures.C_IsRing'46'constructor_96155
      (coe d_'43''45'0'45'isAbelianGroup_1652) (coe d_'42''45'cong_1666)
      (\ v0 v1 v2 -> coe du_'42''45'assoc_1736)
      (coe d_'42''45'identity_1784) (coe d_'42''45'distrib'45''43'_1900)
-- Data.Rational.Unnormalised.Properties.+-*-isCommutativeRing
d_'43''45''42''45'isCommutativeRing_2466 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeRing_2816
d_'43''45''42''45'isCommutativeRing_2466
  = coe
      MAlonzo.Code.Algebra.Structures.C_IsCommutativeRing'46'constructor_102067
      (coe d_'43''45''42''45'isRing_2464)
      (\ v0 v1 -> coe du_'42''45'comm_1762)
-- Data.Rational.Unnormalised.Properties.+-*-isHeytingCommutativeRing
d_'43''45''42''45'isHeytingCommutativeRing_2468 ::
  MAlonzo.Code.Algebra.Apartness.Structures.T_IsHeytingCommutativeRing_160
d_'43''45''42''45'isHeytingCommutativeRing_2468
  = coe
      MAlonzo.Code.Algebra.Apartness.Structures.C_IsHeytingCommutativeRing'46'constructor_4849
      (coe d_'43''45''42''45'isCommutativeRing_2466)
      (coe d_'8772''45'isApartnessRelation_264)
      (\ v0 v1 v2 -> coe du_'8772''8658'invertible_1820 v0 v1) erased
-- Data.Rational.Unnormalised.Properties.+-*-isHeytingField
d_'43''45''42''45'isHeytingField_2470 ::
  MAlonzo.Code.Algebra.Apartness.Structures.T_IsHeytingField_464
d_'43''45''42''45'isHeytingField_2470
  = coe
      MAlonzo.Code.Algebra.Apartness.Structures.C_IsHeytingField'46'constructor_16575
      (coe d_'43''45''42''45'isHeytingCommutativeRing_2468)
      (coe d_'8772''45'tight_266)
-- Data.Rational.Unnormalised.Properties.*-magma
d_'42''45'magma_2472 :: MAlonzo.Code.Algebra.Bundles.T_Magma_72
d_'42''45'magma_2472
  = coe
      MAlonzo.Code.Algebra.Bundles.C_Magma'46'constructor_1323
      MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'42'__202
      d_'42''45'isMagma_2456
-- Data.Rational.Unnormalised.Properties.*-semigroup
d_'42''45'semigroup_2474 ::
  MAlonzo.Code.Algebra.Bundles.T_Semigroup_540
d_'42''45'semigroup_2474
  = coe
      MAlonzo.Code.Algebra.Bundles.C_Semigroup'46'constructor_9837
      MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'42'__202
      d_'42''45'isSemigroup_2458
-- Data.Rational.Unnormalised.Properties.*-1-monoid
d_'42''45'1'45'monoid_2476 ::
  MAlonzo.Code.Algebra.Bundles.T_Monoid_886
d_'42''45'1'45'monoid_2476
  = coe
      MAlonzo.Code.Algebra.Bundles.C_Monoid'46'constructor_16201
      MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'42'__202
      MAlonzo.Code.Data.Rational.Unnormalised.Base.d_1ℚ'7512'_110
      d_'42''45'1'45'isMonoid_2460
-- Data.Rational.Unnormalised.Properties.*-1-commutativeMonoid
d_'42''45'1'45'commutativeMonoid_2478 ::
  MAlonzo.Code.Algebra.Bundles.T_CommutativeMonoid_966
d_'42''45'1'45'commutativeMonoid_2478
  = coe
      MAlonzo.Code.Algebra.Bundles.C_CommutativeMonoid'46'constructor_17975
      MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'42'__202
      MAlonzo.Code.Data.Rational.Unnormalised.Base.d_1ℚ'7512'_110
      d_'42''45'1'45'isCommutativeMonoid_2462
-- Data.Rational.Unnormalised.Properties.+-*-ring
d_'43''45''42''45'ring_2480 ::
  MAlonzo.Code.Algebra.Bundles.T_Ring_3838
d_'43''45''42''45'ring_2480
  = coe
      MAlonzo.Code.Algebra.Bundles.C_Ring'46'constructor_69425
      MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'43'__196
      MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'42'__202
      MAlonzo.Code.Data.Rational.Unnormalised.Base.d_'45'__190
      MAlonzo.Code.Data.Rational.Unnormalised.Base.d_0ℚ'7512'_108
      MAlonzo.Code.Data.Rational.Unnormalised.Base.d_1ℚ'7512'_110
      d_'43''45''42''45'isRing_2464
-- Data.Rational.Unnormalised.Properties.+-*-commutativeRing
d_'43''45''42''45'commutativeRing_2482 ::
  MAlonzo.Code.Algebra.Bundles.T_CommutativeRing_4054
d_'43''45''42''45'commutativeRing_2482
  = coe
      MAlonzo.Code.Algebra.Bundles.C_CommutativeRing'46'constructor_73489
      MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'43'__196
      MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'42'__202
      MAlonzo.Code.Data.Rational.Unnormalised.Base.d_'45'__190
      MAlonzo.Code.Data.Rational.Unnormalised.Base.d_0ℚ'7512'_108
      MAlonzo.Code.Data.Rational.Unnormalised.Base.d_1ℚ'7512'_110
      d_'43''45''42''45'isCommutativeRing_2466
-- Data.Rational.Unnormalised.Properties.+-*-heytingCommutativeRing
d_'43''45''42''45'heytingCommutativeRing_2484 ::
  MAlonzo.Code.Algebra.Apartness.Bundles.T_HeytingCommutativeRing_12
d_'43''45''42''45'heytingCommutativeRing_2484
  = coe
      MAlonzo.Code.Algebra.Apartness.Bundles.C_HeytingCommutativeRing'46'constructor_657
      MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'43'__196
      MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'42'__202
      MAlonzo.Code.Data.Rational.Unnormalised.Base.d_'45'__190
      MAlonzo.Code.Data.Rational.Unnormalised.Base.d_0ℚ'7512'_108
      MAlonzo.Code.Data.Rational.Unnormalised.Base.d_1ℚ'7512'_110
      d_'43''45''42''45'isHeytingCommutativeRing_2468
-- Data.Rational.Unnormalised.Properties.+-*-heytingField
d_'43''45''42''45'heytingField_2486 ::
  MAlonzo.Code.Algebra.Apartness.Bundles.T_HeytingField_208
d_'43''45''42''45'heytingField_2486
  = coe
      MAlonzo.Code.Algebra.Apartness.Bundles.C_HeytingField'46'constructor_4995
      MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'43'__196
      MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'42'__202
      MAlonzo.Code.Data.Rational.Unnormalised.Base.d_'45'__190
      MAlonzo.Code.Data.Rational.Unnormalised.Base.d_0ℚ'7512'_108
      MAlonzo.Code.Data.Rational.Unnormalised.Base.d_1ℚ'7512'_110
      d_'43''45''42''45'isHeytingField_2470
-- Data.Rational.Unnormalised.Properties.p>1⇒p≢0
d_p'62'1'8658'p'8802'0_2488 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'60'__46 ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112
d_p'62'1'8658'p'8802'0_2488 v0 ~v1
  = du_p'62'1'8658'p'8802'0_2488 v0
du_p'62'1'8658'p'8802'0_2488 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112
du_p'62'1'8658'p'8802'0_2488 v0
  = coe du_pos'8658'nonZero_972 (coe v0)
-- Data.Rational.Unnormalised.Properties.1/nonZero⇒nonZero
d_1'47'nonZero'8658'nonZero_2498 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112
d_1'47'nonZero'8658'nonZero_2498 v0 ~v1
  = du_1'47'nonZero'8658'nonZero_2498 v0
du_1'47'nonZero'8658'nonZero_2498 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112
du_1'47'nonZero'8658'nonZero_2498 v0
  = case coe v0 of
      MAlonzo.Code.Data.Rational.Unnormalised.Base.C_mkℚ'7512'_22 v1 v2
        -> coe
             seq (coe v1)
             (coe
                MAlonzo.Code.Data.Nat.Base.C_NonZero'46'constructor_3575
                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Rational.Unnormalised.Properties.1/-involutive-≡
d_1'47''45'involutive'45''8801'_2504 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_1'47''45'involutive'45''8801'_2504 = erased
-- Data.Rational.Unnormalised.Properties.1/-involutive
d_1'47''45'involutive_2518 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8771'__24
d_1'47''45'involutive_2518 ~v0 ~v1 = du_1'47''45'involutive_2518
du_1'47''45'involutive_2518 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8771'__24
du_1'47''45'involutive_2518 = coe du_'8771''45'reflexive_168
-- Data.Rational.Unnormalised.Properties.1/pos⇒pos
d_1'47'pos'8658'pos_2526 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Integer.Base.T_Positive_134 ->
  MAlonzo.Code.Data.Integer.Base.T_Positive_134
d_1'47'pos'8658'pos_2526 v0 ~v1 = du_1'47'pos'8658'pos_2526 v0
du_1'47'pos'8658'pos_2526 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Integer.Base.T_Positive_134
du_1'47'pos'8658'pos_2526 v0
  = coe
      seq (coe v0)
      (coe
         MAlonzo.Code.Data.Integer.Base.C_Positive'46'constructor_1399
         (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
-- Data.Rational.Unnormalised.Properties.1/neg⇒neg
d_1'47'neg'8658'neg_2536 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Integer.Base.T_Negative_164 ->
  MAlonzo.Code.Data.Integer.Base.T_Negative_164
d_1'47'neg'8658'neg_2536 v0 ~v1 = du_1'47'neg'8658'neg_2536 v0
du_1'47'neg'8658'neg_2536 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Integer.Base.T_Negative_164
du_1'47'neg'8658'neg_2536 v0
  = coe
      seq (coe v0)
      (coe
         MAlonzo.Code.Data.Integer.Base.C_Negative'46'constructor_1573
         (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
-- Data.Rational.Unnormalised.Properties.p>1⇒1/p<1
d_p'62'1'8658'1'47'p'60'1_2546 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'60'__46 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'60'__46
d_p'62'1'8658'1'47'p'60'1_2546 v0 v1
  = coe du_lemma'8242'_2560 (coe v0) (coe v1)
-- Data.Rational.Unnormalised.Properties._.lemma′
d_lemma'8242'_2560 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'60'__46 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'60'__46 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'60'__46
d_lemma'8242'_2560 ~v0 ~v1 v2 ~v3 v4 = du_lemma'8242'_2560 v2 v4
du_lemma'8242'_2560 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'60'__46 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'60'__46
du_lemma'8242'_2560 v0 v1
  = case coe v0 of
      MAlonzo.Code.Data.Rational.Unnormalised.Base.C_mkℚ'7512'_22 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Data.Rational.Unnormalised.Base.C_'42''60''42'_52 v6
               -> coe
                    MAlonzo.Code.Data.Rational.Unnormalised.Base.C_'42''60''42'_52
                    (let v7
                           = coe
                               MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_strictRelation_202 in
                     coe
                       (coe
                          MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__126
                          (coe v7)
                          (coe
                             MAlonzo.Code.Data.Integer.Base.d__'42'__308
                             (coe
                                MAlonzo.Code.Data.Rational.Unnormalised.Base.d_numerator_14
                                (coe
                                   MAlonzo.Code.Data.Rational.Unnormalised.Base.du_1'47'__218
                                   (coe v0)))
                             (coe MAlonzo.Code.Data.Integer.Base.d_1ℤ_16))
                          (coe
                             MAlonzo.Code.Data.Integer.Base.d__'42'__308
                             (coe
                                MAlonzo.Code.Data.Rational.Unnormalised.Base.d_numerator_14
                                (coe MAlonzo.Code.Data.Rational.Unnormalised.Base.d_1ℚ'7512'_110))
                             (coe
                                MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                (coe
                                   MAlonzo.Code.Data.Rational.Unnormalised.Base.du_1'47'__218
                                   (coe v0))))
                          (coe
                             MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_436
                             (\ v8 v9 v10 v11 v12 -> v12)
                             (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                (coe addInt (coe (1 :: Integer)) (coe v3))
                                (coe MAlonzo.Code.Data.Integer.Base.d_1ℤ_16))
                             (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                (coe MAlonzo.Code.Data.Integer.Base.d_1ℤ_16)
                                (coe addInt (coe (1 :: Integer)) (coe v3)))
                             (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                (coe
                                   MAlonzo.Code.Data.Rational.Unnormalised.Base.d_numerator_14
                                   (coe
                                      MAlonzo.Code.Data.Rational.Unnormalised.Base.d_1ℚ'7512'_110))
                                (coe
                                   MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                   (coe
                                      MAlonzo.Code.Data.Rational.Unnormalised.Base.du_1'47'__218
                                      (coe v0))))
                             (coe
                                MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''60'_312
                                (coe
                                   MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'60''45'go_152
                                   (\ v8 v9 v10 v11 v12 ->
                                      coe
                                        MAlonzo.Code.Data.Integer.Properties.du_'60''45'trans_3008
                                        v11 v12)
                                   (coe
                                      MAlonzo.Code.Relation.Binary.PropositionalEquality.Core.du_resp'8322'_160)
                                   (\ v8 v9 v10 v11 v12 ->
                                      coe
                                        MAlonzo.Code.Data.Integer.Properties.du_'60''45''8804''45'trans_2994
                                        v11 v12))
                                (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                   (coe MAlonzo.Code.Data.Integer.Base.d_1ℤ_16)
                                   (coe addInt (coe (1 :: Integer)) (coe v3)))
                                (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                   (coe v2) (coe MAlonzo.Code.Data.Integer.Base.d_1ℤ_16))
                                (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                   (coe
                                      MAlonzo.Code.Data.Rational.Unnormalised.Base.d_numerator_14
                                      (coe
                                         MAlonzo.Code.Data.Rational.Unnormalised.Base.d_1ℚ'7512'_110))
                                   (coe
                                      MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                      (coe
                                         MAlonzo.Code.Data.Rational.Unnormalised.Base.du_1'47'__218
                                         (coe v0))))
                                (coe
                                   MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_436
                                   (\ v8 v9 v10 v11 v12 -> v12)
                                   (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                      (coe v2) (coe MAlonzo.Code.Data.Integer.Base.d_1ℤ_16))
                                   (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                      (coe MAlonzo.Code.Data.Integer.Base.d_1ℤ_16) (coe v2))
                                   (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                      (coe
                                         MAlonzo.Code.Data.Rational.Unnormalised.Base.d_numerator_14
                                         (coe
                                            MAlonzo.Code.Data.Rational.Unnormalised.Base.d_1ℚ'7512'_110))
                                      (coe
                                         MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                         (coe
                                            MAlonzo.Code.Data.Rational.Unnormalised.Base.du_1'47'__218
                                            (coe v0))))
                                   (coe
                                      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                                      (coe
                                         MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_stop_166
                                         (coe
                                            MAlonzo.Code.Data.Integer.Properties.d_'8804''45'isPreorder_2822))
                                      (coe
                                         MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                         (coe
                                            MAlonzo.Code.Data.Rational.Unnormalised.Base.d_numerator_14
                                            (coe
                                               MAlonzo.Code.Data.Rational.Unnormalised.Base.d_1ℚ'7512'_110))
                                         (coe
                                            MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                            (coe
                                               MAlonzo.Code.Data.Rational.Unnormalised.Base.du_1'47'__218
                                               (coe v0)))))
                                   erased)
                                v6)
                             erased)))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Rational.Unnormalised.Properties.1/-antimono-≤-pos
d_1'47''45'antimono'45''8804''45'pos_2580 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Integer.Base.T_Positive_134 ->
  MAlonzo.Code.Data.Integer.Base.T_Positive_134 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8804'__38 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8804'__38
d_1'47''45'antimono'45''8804''45'pos_2580 v0 v1 ~v2 ~v3 v4
  = du_1'47''45'antimono'45''8804''45'pos_2580 v0 v1 v4
du_1'47''45'antimono'45''8804''45'pos_2580 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8804'__38 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8804'__38
du_1'47''45'antimono'45''8804''45'pos_2580 v0 v1 v2
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_start_96
         (coe d_'8804''45'isPreorder_512)
         (\ v3 v4 v5 -> coe du_'60''8658''8804'_556 v5))
      (coe
         MAlonzo.Code.Data.Rational.Unnormalised.Base.du_1'47'__218
         (coe v1))
      (coe
         MAlonzo.Code.Data.Rational.Unnormalised.Base.du_1'47'__218
         (coe v0))
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8771''45''10216'_390
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8776''45'go_124
            (coe d_'8804''45'isPreorder_512)
            (coe d_'60''45'resp'45''8771'_780))
         (\ v3 v4 v5 -> coe du_'8771''45'sym_170 v5)
         (coe du_1'47'q_2598 v1 erased)
         (MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'42'__202
            (coe MAlonzo.Code.Data.Rational.Unnormalised.Base.d_1ℚ'7512'_110)
            (coe du_1'47'q_2598 v1 erased))
         (coe
            MAlonzo.Code.Data.Rational.Unnormalised.Base.du_1'47'__218
            (coe v0))
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8771''45''10216'_390
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8776''45'go_124
               (coe d_'8804''45'isPreorder_512)
               (coe d_'60''45'resp'45''8771'_780))
            (\ v3 v4 v5 -> coe du_'8771''45'sym_170 v5)
            (MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'42'__202
               (coe MAlonzo.Code.Data.Rational.Unnormalised.Base.d_1ℚ'7512'_110)
               (coe du_1'47'q_2598 v1 erased))
            (MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'42'__202
               (coe
                  MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'42'__202
                  (coe du_1'47'p_2596 v0 erased) (coe v0))
               (coe du_1'47'q_2598 v1 erased))
            (coe
               MAlonzo.Code.Data.Rational.Unnormalised.Base.du_1'47'__218
               (coe v0))
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8804'_308
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8804''45'go_138
                  (coe d_'8804''45'isPreorder_512)
                  (coe d_'8804''45''60''45'trans_610))
               (MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'42'__202
                  (coe
                     MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'42'__202
                     (coe du_1'47'p_2596 v0 erased) (coe v0))
                  (coe du_1'47'q_2598 v1 erased))
               (MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'42'__202
                  (coe
                     MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'42'__202
                     (coe du_1'47'p_2596 v0 erased) (coe v1))
                  (coe du_1'47'q_2598 v1 erased))
               (coe
                  MAlonzo.Code.Data.Rational.Unnormalised.Base.du_1'47'__218
                  (coe v0))
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8771''45''10217'_388
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8776''45'go_124
                     (coe d_'8804''45'isPreorder_512)
                     (coe d_'60''45'resp'45''8771'_780))
                  (MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'42'__202
                     (coe
                        MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'42'__202
                        (coe du_1'47'p_2596 v0 erased) (coe v1))
                     (coe du_1'47'q_2598 v1 erased))
                  (MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'42'__202
                     (coe du_1'47'p_2596 v0 erased)
                     (coe
                        MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'42'__202 (coe v1)
                        (coe du_1'47'q_2598 v1 erased)))
                  (coe
                     MAlonzo.Code.Data.Rational.Unnormalised.Base.du_1'47'__218
                     (coe v0))
                  (coe
                     MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8771''45''10217'_388
                     (coe
                        MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8776''45'go_124
                        (coe d_'8804''45'isPreorder_512)
                        (coe d_'60''45'resp'45''8771'_780))
                     (MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'42'__202
                        (coe du_1'47'p_2596 v0 erased)
                        (coe
                           MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'42'__202 (coe v1)
                           (coe du_1'47'q_2598 v1 erased)))
                     (MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'42'__202
                        (coe du_1'47'p_2596 v0 erased)
                        (coe MAlonzo.Code.Data.Rational.Unnormalised.Base.d_1ℚ'7512'_110))
                     (coe
                        MAlonzo.Code.Data.Rational.Unnormalised.Base.du_1'47'__218
                        (coe v0))
                     (coe
                        MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8771''45''10217'_388
                        (coe
                           MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8776''45'go_124
                           (coe d_'8804''45'isPreorder_512)
                           (coe d_'60''45'resp'45''8771'_780))
                        (MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'42'__202
                           (coe du_1'47'p_2596 v0 erased)
                           (coe MAlonzo.Code.Data.Rational.Unnormalised.Base.d_1ℚ'7512'_110))
                        (coe du_1'47'p_2596 v0 erased)
                        (coe
                           MAlonzo.Code.Data.Rational.Unnormalised.Base.du_1'47'__218
                           (coe v0))
                        (coe
                           MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                           (coe
                              MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_stop_166
                              (coe d_'8804''45'isPreorder_512))
                           (coe du_1'47'p_2596 v0 erased))
                        (coe du_'42''45'identity'691'_1780))
                     (d_'42''45'cong'737'_1700
                        (coe du_1'47'p_2596 v0 erased)
                        (coe
                           MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'42'__202 (coe v1)
                           (coe
                              MAlonzo.Code.Data.Rational.Unnormalised.Base.du_1'47'__218
                              (coe v1)))
                        (coe MAlonzo.Code.Data.Rational.Unnormalised.Base.d_1ℚ'7512'_110)
                        (coe du_'42''45'inverse'691'_1816 (coe v1))))
                  (coe du_'42''45'assoc_1736))
               (coe
                  du_'42''45'mono'737''45''8804''45'nonNeg_2114
                  (coe du_1'47'q_2598 v1 erased)
                  (coe
                     MAlonzo.Code.Function.Base.du__'45''10216'_'8739'_292
                     (MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'42'__202
                        (coe du_1'47'p_2596 v0 erased))
                     (\ v3 v4 -> v3) v0 v1)
                  (coe
                     MAlonzo.Code.Function.Base.du_'8739'_'10217''45'__298
                     (\ v3 v4 -> v4)
                     (MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'42'__202
                        (coe du_1'47'p_2596 v0 erased))
                     v0 v1)
                  (coe
                     du_'42''45'mono'691''45''8804''45'nonNeg_2144
                     (coe du_1'47'p_2596 v0 erased) v0 v1 v2)))
            (d_'42''45'cong'691'_1706
               (coe du_1'47'q_2598 v1 erased)
               (coe
                  MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'42'__202
                  (coe
                     MAlonzo.Code.Data.Rational.Unnormalised.Base.du_1'47'__218
                     (coe v0))
                  (coe v0))
               (coe MAlonzo.Code.Data.Rational.Unnormalised.Base.d_1ℚ'7512'_110)
               (coe du_'42''45'inverse'737'_1790 (coe v0))))
         (coe du_'42''45'identity'737'_1776))
-- Data.Rational.Unnormalised.Properties._.1/p
d_1'47'p_2596 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Integer.Base.T_Positive_134 ->
  MAlonzo.Code.Data.Integer.Base.T_Positive_134 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8804'__38 ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8
d_1'47'p_2596 v0 ~v1 ~v2 ~v3 ~v4 = du_1'47'p_2596 v0
du_1'47'p_2596 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8
du_1'47'p_2596 v0 v1
  = coe
      MAlonzo.Code.Data.Rational.Unnormalised.Base.du_1'47'__218 (coe v0)
-- Data.Rational.Unnormalised.Properties._.1/q
d_1'47'q_2598 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Integer.Base.T_Positive_134 ->
  MAlonzo.Code.Data.Integer.Base.T_Positive_134 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8804'__38 ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8
d_1'47'q_2598 ~v0 v1 ~v2 ~v3 ~v4 = du_1'47'q_2598 v1
du_1'47'q_2598 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8
du_1'47'q_2598 v0 v1
  = coe
      MAlonzo.Code.Data.Rational.Unnormalised.Base.du_1'47'__218 (coe v0)
-- Data.Rational.Unnormalised.Properties.p≤q⇒p⊔q≃q
d_p'8804'q'8658'p'8852'q'8771'q_2604 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8804'__38 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8771'__24
d_p'8804'q'8658'p'8852'q'8771'q_2604 v0 v1 ~v2
  = du_p'8804'q'8658'p'8852'q'8771'q_2604 v0 v1
du_p'8804'q'8658'p'8852'q'8771'q_2604 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8771'__24
du_p'8804'q'8658'p'8852'q'8771'q_2604 v0 v1
  = case coe v0 of
      MAlonzo.Code.Data.Rational.Unnormalised.Base.C_mkℚ'7512'_22 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Data.Rational.Unnormalised.Base.C_mkℚ'7512'_22 v4 v5
               -> let v6
                        = MAlonzo.Code.Data.Integer.Base.d__'8804''7495'__110
                            (coe
                               MAlonzo.Code.Data.Integer.Base.d__'9667'__230
                               (coe
                                  MAlonzo.Code.Data.Sign.Base.d__'42'__14
                                  (coe MAlonzo.Code.Data.Integer.Base.d_sign_24 (coe v2))
                                  (coe
                                     MAlonzo.Code.Data.Integer.Base.d_sign_24
                                     (coe
                                        MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                        (coe v1))))
                               (coe
                                  mulInt
                                  (coe MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18 (coe v2))
                                  (coe
                                     MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18
                                     (coe
                                        MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                        (coe v1)))))
                            (coe
                               MAlonzo.Code.Data.Integer.Base.d__'42'__308 (coe v4)
                               (coe
                                  MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                  (coe v0))) in
                  coe
                    (if coe v6
                       then coe du_'8771''45'refl_166
                       else coe
                              MAlonzo.Code.Relation.Nullary.Negation.Core.du_contradiction_44
                              erased)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Rational.Unnormalised.Properties.p≥q⇒p⊔q≃p
d_p'8805'q'8658'p'8852'q'8771'p_2632 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8804'__38 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8771'__24
d_p'8805'q'8658'p'8852'q'8771'p_2632 v0 v1 v2
  = case coe v0 of
      MAlonzo.Code.Data.Rational.Unnormalised.Base.C_mkℚ'7512'_22 v3 v4
        -> case coe v1 of
             MAlonzo.Code.Data.Rational.Unnormalised.Base.C_mkℚ'7512'_22 v5 v6
               -> let v7
                        = MAlonzo.Code.Data.Integer.Base.d__'8804''7495'__110
                            (coe
                               MAlonzo.Code.Data.Integer.Base.d__'9667'__230
                               (coe
                                  MAlonzo.Code.Data.Sign.Base.d__'42'__14
                                  (coe MAlonzo.Code.Data.Integer.Base.d_sign_24 (coe v3))
                                  (coe
                                     MAlonzo.Code.Data.Integer.Base.d_sign_24
                                     (coe
                                        MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                        (coe v1))))
                               (coe
                                  mulInt
                                  (coe MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18 (coe v3))
                                  (coe
                                     MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18
                                     (coe
                                        MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                        (coe v1)))))
                            (coe
                               MAlonzo.Code.Data.Integer.Base.d__'42'__308 (coe v5)
                               (coe
                                  MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                  (coe v0))) in
                  coe
                    (if coe v7
                       then coe
                              du_'8804''45'antisym_474 (coe v2)
                              (coe
                                 du_'8804''7495''8658''8804'_548 (coe v0)
                                 (coe
                                    MAlonzo.Code.Data.Bool.Base.du_if_then_else__44 (coe v7)
                                    (coe v1) (coe v0)))
                       else coe du_'8771''45'refl_166)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Rational.Unnormalised.Properties.p≤q⇒p⊓q≃p
d_p'8804'q'8658'p'8851'q'8771'p_2662 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8804'__38 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8771'__24
d_p'8804'q'8658'p'8851'q'8771'p_2662 v0 v1 ~v2
  = du_p'8804'q'8658'p'8851'q'8771'p_2662 v0 v1
du_p'8804'q'8658'p'8851'q'8771'p_2662 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8771'__24
du_p'8804'q'8658'p'8851'q'8771'p_2662 v0 v1
  = case coe v0 of
      MAlonzo.Code.Data.Rational.Unnormalised.Base.C_mkℚ'7512'_22 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Data.Rational.Unnormalised.Base.C_mkℚ'7512'_22 v4 v5
               -> let v6
                        = MAlonzo.Code.Data.Integer.Base.d__'8804''7495'__110
                            (coe
                               MAlonzo.Code.Data.Integer.Base.d__'9667'__230
                               (coe
                                  MAlonzo.Code.Data.Sign.Base.d__'42'__14
                                  (coe MAlonzo.Code.Data.Integer.Base.d_sign_24 (coe v2))
                                  (coe
                                     MAlonzo.Code.Data.Integer.Base.d_sign_24
                                     (coe
                                        MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                        (coe v1))))
                               (coe
                                  mulInt
                                  (coe MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18 (coe v2))
                                  (coe
                                     MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18
                                     (coe
                                        MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                        (coe v1)))))
                            (coe
                               MAlonzo.Code.Data.Integer.Base.d__'42'__308 (coe v4)
                               (coe
                                  MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                  (coe v0))) in
                  coe
                    (if coe v6
                       then coe du_'8771''45'refl_166
                       else coe
                              MAlonzo.Code.Relation.Nullary.Negation.Core.du_contradiction_44
                              erased)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Rational.Unnormalised.Properties.p≥q⇒p⊓q≃q
d_p'8805'q'8658'p'8851'q'8771'q_2690 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8804'__38 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8771'__24
d_p'8805'q'8658'p'8851'q'8771'q_2690 v0 v1 v2
  = case coe v0 of
      MAlonzo.Code.Data.Rational.Unnormalised.Base.C_mkℚ'7512'_22 v3 v4
        -> case coe v1 of
             MAlonzo.Code.Data.Rational.Unnormalised.Base.C_mkℚ'7512'_22 v5 v6
               -> let v7
                        = MAlonzo.Code.Data.Integer.Base.d__'8804''7495'__110
                            (coe
                               MAlonzo.Code.Data.Integer.Base.d__'9667'__230
                               (coe
                                  MAlonzo.Code.Data.Sign.Base.d__'42'__14
                                  (coe MAlonzo.Code.Data.Integer.Base.d_sign_24 (coe v3))
                                  (coe
                                     MAlonzo.Code.Data.Integer.Base.d_sign_24
                                     (coe
                                        MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                        (coe v1))))
                               (coe
                                  mulInt
                                  (coe MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18 (coe v3))
                                  (coe
                                     MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18
                                     (coe
                                        MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                        (coe v1)))))
                            (coe
                               MAlonzo.Code.Data.Integer.Base.d__'42'__308 (coe v5)
                               (coe
                                  MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                  (coe v0))) in
                  coe
                    (if coe v7
                       then coe
                              du_'8804''45'antisym_474
                              (coe
                                 du_'8804''7495''8658''8804'_548
                                 (coe
                                    MAlonzo.Code.Data.Bool.Base.du_if_then_else__44 (coe v7)
                                    (coe v0) (coe v1))
                                 (coe v1))
                              (coe v2)
                       else coe du_'8771''45'refl_166)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Rational.Unnormalised.Properties.⊓-operator
d_'8851''45'operator_2720 ::
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MinOperator_106
d_'8851''45'operator_2720
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.C_MinOperator'46'constructor_1157
      (coe MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'8851'__254)
      (\ v0 v1 v2 -> coe du_p'8804'q'8658'p'8851'q'8771'p_2662 v0 v1)
      (coe d_p'8805'q'8658'p'8851'q'8771'q_2690)
-- Data.Rational.Unnormalised.Properties.⊔-operator
d_'8852''45'operator_2722 ::
  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.T_MaxOperator_136
d_'8852''45'operator_2722
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.C_MaxOperator'46'constructor_1701
      (coe MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'8852'__244)
      (\ v0 v1 v2 -> coe du_p'8804'q'8658'p'8852'q'8771'q_2604 v0 v1)
      (coe d_p'8805'q'8658'p'8852'q'8771'p_2632)
-- Data.Rational.Unnormalised.Properties.⊓-⊔-properties.x⊓y≤x
d_x'8851'y'8804'x_2734 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8804'__38
d_x'8851'y'8804'x_2734
  = let v0 = d_'8804''45'totalPreorder_524 in
    coe
      (let v1 = d_'8852''45'operator_2722 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8851'y'8804'x_2838
            (coe
               MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_760
               (coe v0))
            (coe
               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_182
               (coe v1))))
-- Data.Rational.Unnormalised.Properties.⊓-⊔-properties.x≤y⇒x⊓z≤y
d_x'8804'y'8658'x'8851'z'8804'y_2736 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8804'__38 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8804'__38
d_x'8804'y'8658'x'8851'z'8804'y_2736
  = let v0 = d_'8804''45'totalPreorder_524 in
    coe
      (let v1 = d_'8852''45'operator_2722 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8804'y'8658'x'8851'z'8804'y_3190
            (coe
               MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_760
               (coe v0))
            (coe
               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_182
               (coe v1))))
-- Data.Rational.Unnormalised.Properties.⊓-⊔-properties.x≤y⇒z⊓x≤y
d_x'8804'y'8658'z'8851'x'8804'y_2738 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8804'__38 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8804'__38
d_x'8804'y'8658'z'8851'x'8804'y_2738
  = let v0 = d_'8804''45'totalPreorder_524 in
    coe
      (let v1 = d_'8852''45'operator_2722 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8804'y'8658'z'8851'x'8804'y_3202
            (coe
               MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_760
               (coe v0))
            (coe
               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_182
               (coe v1))))
-- Data.Rational.Unnormalised.Properties.⊓-⊔-properties.x≤y⇒x⊓z≤y
d_x'8804'y'8658'x'8851'z'8804'y_2740 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8804'__38 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8804'__38
d_x'8804'y'8658'x'8851'z'8804'y_2740
  = let v0 = d_'8804''45'totalPreorder_524 in
    coe
      (let v1 = d_'8851''45'operator_2720 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8804'y'8658'x'8851'z'8804'y_3190
            (coe v0) (coe v1)))
-- Data.Rational.Unnormalised.Properties.⊓-⊔-properties.x≤y⇒z⊓x≤y
d_x'8804'y'8658'z'8851'x'8804'y_2742 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8804'__38 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8804'__38
d_x'8804'y'8658'z'8851'x'8804'y_2742
  = let v0 = d_'8804''45'totalPreorder_524 in
    coe
      (let v1 = d_'8851''45'operator_2720 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8804'y'8658'z'8851'x'8804'y_3202
            (coe v0) (coe v1)))
-- Data.Rational.Unnormalised.Properties.⊓-⊔-properties.x≤y⊓z⇒x≤y
d_x'8804'y'8851'z'8658'x'8804'y_2744 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8804'__38 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8804'__38
d_x'8804'y'8851'z'8658'x'8804'y_2744
  = let v0 = d_'8804''45'totalPreorder_524 in
    coe
      (let v1 = d_'8851''45'operator_2720 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8804'y'8851'z'8658'x'8804'y_3214
            (coe v0) (coe v1)))
-- Data.Rational.Unnormalised.Properties.⊓-⊔-properties.x≤y⊓z⇒x≤z
d_x'8804'y'8851'z'8658'x'8804'z_2746 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8804'__38 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8804'__38
d_x'8804'y'8851'z'8658'x'8804'z_2746
  = let v0 = d_'8804''45'totalPreorder_524 in
    coe
      (let v1 = d_'8851''45'operator_2720 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8804'y'8851'z'8658'x'8804'z_3228
            (coe v0) (coe v1)))
-- Data.Rational.Unnormalised.Properties.⊓-⊔-properties.x⊓y≤y
d_x'8851'y'8804'y_2748 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8804'__38
d_x'8851'y'8804'y_2748
  = let v0 = d_'8804''45'totalPreorder_524 in
    coe
      (let v1 = d_'8852''45'operator_2722 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8851'y'8804'y_2864
            (coe
               MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_760
               (coe v0))
            (coe
               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_182
               (coe v1))))
-- Data.Rational.Unnormalised.Properties.⊓-⊔-properties.x⊓y≈x⇒x≤y
d_x'8851'y'8776'x'8658'x'8804'y_2750 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8771'__24 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8804'__38
d_x'8851'y'8776'x'8658'x'8804'y_2750
  = let v0 = d_'8804''45'totalPreorder_524 in
    coe
      (let v1 = d_'8851''45'operator_2720 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8851'y'8776'x'8658'x'8804'y_3098
            (coe v0) (coe v1)))
-- Data.Rational.Unnormalised.Properties.⊓-⊔-properties.x⊓y≈y⇒y≤x
d_x'8851'y'8776'y'8658'y'8804'x_2752 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8771'__24 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8804'__38
d_x'8851'y'8776'y'8658'y'8804'x_2752
  = let v0 = d_'8804''45'totalPreorder_524 in
    coe
      (let v1 = d_'8851''45'operator_2720 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8851'y'8776'y'8658'y'8804'x_3130
            (coe v0) (coe v1)))
-- Data.Rational.Unnormalised.Properties.⊓-⊔-properties.x⊓y≤x
d_x'8851'y'8804'x_2754 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8804'__38
d_x'8851'y'8804'x_2754
  = let v0 = d_'8804''45'totalPreorder_524 in
    coe
      (let v1 = d_'8851''45'operator_2720 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8851'y'8804'x_2838
            (coe v0) (coe v1)))
-- Data.Rational.Unnormalised.Properties.⊓-⊔-properties.x⊓y≤x⊔y
d_x'8851'y'8804'x'8852'y_2756 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8804'__38
d_x'8851'y'8804'x'8852'y_2756
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinMaxOp.du_x'8851'y'8804'x'8852'y_3354
      (coe d_'8804''45'totalPreorder_524) (coe d_'8851''45'operator_2720)
      (coe d_'8852''45'operator_2722)
-- Data.Rational.Unnormalised.Properties.⊓-⊔-properties.x⊓y≤y
d_x'8851'y'8804'y_2758 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8804'__38
d_x'8851'y'8804'y_2758
  = let v0 = d_'8804''45'totalPreorder_524 in
    coe
      (let v1 = d_'8851''45'operator_2720 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8851'y'8804'y_2864
            (coe v0) (coe v1)))
-- Data.Rational.Unnormalised.Properties.⊓-⊔-properties.x⊓y≈x⇒x≤y
d_x'8851'y'8776'x'8658'x'8804'y_2760 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8771'__24 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8804'__38
d_x'8851'y'8776'x'8658'x'8804'y_2760
  = let v0 = d_'8804''45'totalPreorder_524 in
    coe
      (let v1 = d_'8852''45'operator_2722 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8851'y'8776'x'8658'x'8804'y_3098
            (coe
               MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_760
               (coe v0))
            (coe
               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_182
               (coe v1))))
-- Data.Rational.Unnormalised.Properties.⊓-⊔-properties.x⊓y≈y⇒y≤x
d_x'8851'y'8776'y'8658'y'8804'x_2762 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8771'__24 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8804'__38
d_x'8851'y'8776'y'8658'y'8804'x_2762
  = let v0 = d_'8804''45'totalPreorder_524 in
    coe
      (let v1 = d_'8852''45'operator_2722 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8851'y'8776'y'8658'y'8804'x_3130
            (coe
               MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_760
               (coe v0))
            (coe
               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_182
               (coe v1))))
-- Data.Rational.Unnormalised.Properties.⊓-⊔-properties.x≤y⊓z⇒x≤y
d_x'8804'y'8851'z'8658'x'8804'y_2764 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8804'__38 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8804'__38
d_x'8804'y'8851'z'8658'x'8804'y_2764
  = let v0 = d_'8804''45'totalPreorder_524 in
    coe
      (let v1 = d_'8852''45'operator_2722 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8804'y'8851'z'8658'x'8804'y_3214
            (coe
               MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_760
               (coe v0))
            (coe
               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_182
               (coe v1))))
-- Data.Rational.Unnormalised.Properties.⊓-⊔-properties.x≤y⊓z⇒x≤z
d_x'8804'y'8851'z'8658'x'8804'z_2766 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8804'__38 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8804'__38
d_x'8804'y'8851'z'8658'x'8804'z_2766
  = let v0 = d_'8804''45'totalPreorder_524 in
    coe
      (let v1 = d_'8852''45'operator_2722 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8804'y'8851'z'8658'x'8804'z_3228
            (coe
               MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_760
               (coe v0))
            (coe
               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_182
               (coe v1))))
-- Data.Rational.Unnormalised.Properties.⊓-⊔-properties.⊓-absorbs-⊔
d_'8851''45'absorbs'45''8852'_2768 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8771'__24
d_'8851''45'absorbs'45''8852'_2768
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinMaxOp.du_'8851''45'absorbs'45''8852'_3208
      (coe d_'8804''45'totalPreorder_524) (coe d_'8851''45'operator_2720)
      (coe d_'8852''45'operator_2722)
-- Data.Rational.Unnormalised.Properties.⊓-⊔-properties.⊓-assoc
d_'8851''45'assoc_2770 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8771'__24
d_'8851''45'assoc_2770
  = let v0 = d_'8804''45'totalPreorder_524 in
    coe
      (let v1 = d_'8851''45'operator_2720 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'assoc_2974
            (coe v0) (coe v1)))
-- Data.Rational.Unnormalised.Properties.⊓-⊔-properties.⊓-band
d_'8851''45'band_2772 :: MAlonzo.Code.Algebra.Bundles.T_Band_600
d_'8851''45'band_2772
  = let v0 = d_'8804''45'totalPreorder_524 in
    coe
      (let v1 = d_'8851''45'operator_2720 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'band_3082
            (coe v0) (coe v1)))
-- Data.Rational.Unnormalised.Properties.⊓-⊔-properties.⊓-comm
d_'8851''45'comm_2774 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8771'__24
d_'8851''45'comm_2774
  = let v0 = d_'8804''45'totalPreorder_524 in
    coe
      (let v1 = d_'8851''45'operator_2720 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'comm_2886
            (coe v0) (coe v1)))
-- Data.Rational.Unnormalised.Properties.⊓-⊔-properties.⊓-commutativeSemigroup
d_'8851''45'commutativeSemigroup_2776 ::
  MAlonzo.Code.Algebra.Bundles.T_CommutativeSemigroup_666
d_'8851''45'commutativeSemigroup_2776
  = let v0 = d_'8804''45'totalPreorder_524 in
    coe
      (let v1 = d_'8851''45'operator_2720 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'commutativeSemigroup_3084
            (coe v0) (coe v1)))
-- Data.Rational.Unnormalised.Properties.⊓-⊔-properties.⊓-cong
d_'8851''45'cong_2778 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8771'__24 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8771'__24 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8771'__24
d_'8851''45'cong_2778
  = let v0 = d_'8804''45'totalPreorder_524 in
    coe
      (let v1 = d_'8851''45'operator_2720 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'cong_2960
            (coe v0) (coe v1)))
-- Data.Rational.Unnormalised.Properties.⊓-⊔-properties.⊓-congʳ
d_'8851''45'cong'691'_2780 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8771'__24 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8771'__24
d_'8851''45'cong'691'_2780
  = let v0 = d_'8804''45'totalPreorder_524 in
    coe
      (let v1 = d_'8851''45'operator_2720 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'cong'691'_2950
            (coe v0) (coe v1)))
-- Data.Rational.Unnormalised.Properties.⊓-⊔-properties.⊓-congˡ
d_'8851''45'cong'737'_2782 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8771'__24 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8771'__24
d_'8851''45'cong'737'_2782
  = let v0 = d_'8804''45'totalPreorder_524 in
    coe
      (let v1 = d_'8851''45'operator_2720 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'cong'737'_2912
            (coe v0) (coe v1)))
-- Data.Rational.Unnormalised.Properties.⊓-⊔-properties.⊓-distrib-⊔
d_'8851''45'distrib'45''8852'_2784 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8851''45'distrib'45''8852'_2784
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinMaxOp.du_'8851''45'distrib'45''8852'_3174
      (coe d_'8804''45'totalPreorder_524) (coe d_'8851''45'operator_2720)
      (coe d_'8852''45'operator_2722)
-- Data.Rational.Unnormalised.Properties.⊓-⊔-properties.⊓-distribʳ-⊔
d_'8851''45'distrib'691''45''8852'_2786 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8771'__24
d_'8851''45'distrib'691''45''8852'_2786
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinMaxOp.du_'8851''45'distrib'691''45''8852'_3172
      (coe d_'8804''45'totalPreorder_524) (coe d_'8851''45'operator_2720)
      (coe d_'8852''45'operator_2722)
-- Data.Rational.Unnormalised.Properties.⊓-⊔-properties.⊓-distribˡ-⊔
d_'8851''45'distrib'737''45''8852'_2788 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8771'__24
d_'8851''45'distrib'737''45''8852'_2788
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinMaxOp.du_'8851''45'distrib'737''45''8852'_3144
      (coe d_'8804''45'totalPreorder_524) (coe d_'8851''45'operator_2720)
      (coe d_'8852''45'operator_2722)
-- Data.Rational.Unnormalised.Properties.⊓-⊔-properties.⊓-glb
d_'8851''45'glb_2790 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8804'__38 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8804'__38 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8804'__38
d_'8851''45'glb_2790
  = let v0 = d_'8804''45'totalPreorder_524 in
    coe
      (let v1 = d_'8851''45'operator_2720 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'glb_3308
            (coe v0) (coe v1)))
-- Data.Rational.Unnormalised.Properties.⊓-⊔-properties.⊓-idem
d_'8851''45'idem_2792 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8771'__24
d_'8851''45'idem_2792
  = let v0 = d_'8804''45'totalPreorder_524 in
    coe
      (let v1 = d_'8851''45'operator_2720 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'idem_3014
            (coe v0) (coe v1)))
-- Data.Rational.Unnormalised.Properties.⊓-⊔-properties.⊓-isBand
d_'8851''45'isBand_2800 ::
  MAlonzo.Code.Algebra.Structures.T_IsBand_506
d_'8851''45'isBand_2800
  = let v0 = d_'8804''45'totalPreorder_524 in
    coe
      (let v1 = d_'8851''45'operator_2720 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'isBand_3064
            (coe v0) (coe v1)))
-- Data.Rational.Unnormalised.Properties.⊓-⊔-properties.⊓-isCommutativeSemigroup
d_'8851''45'isCommutativeSemigroup_2802 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_546
d_'8851''45'isCommutativeSemigroup_2802
  = let v0 = d_'8804''45'totalPreorder_524 in
    coe
      (let v1 = d_'8851''45'operator_2720 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'isCommutativeSemigroup_3066
            (coe v0) (coe v1)))
-- Data.Rational.Unnormalised.Properties.⊓-⊔-properties.⊓-isMagma
d_'8851''45'isMagma_2804 ::
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176
d_'8851''45'isMagma_2804
  = let v0 = d_'8804''45'totalPreorder_524 in
    coe
      (let v1 = d_'8851''45'operator_2720 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'isMagma_3060
            (coe v0) (coe v1)))
-- Data.Rational.Unnormalised.Properties.⊓-⊔-properties.⊓-isSelectiveMagma
d_'8851''45'isSelectiveMagma_2808 ::
  MAlonzo.Code.Algebra.Structures.T_IsSelectiveMagma_434
d_'8851''45'isSelectiveMagma_2808
  = let v0 = d_'8804''45'totalPreorder_524 in
    coe
      (let v1 = d_'8851''45'operator_2720 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'isSelectiveMagma_3068
            (coe v0) (coe v1)))
-- Data.Rational.Unnormalised.Properties.⊓-⊔-properties.⊓-isSemigroup
d_'8851''45'isSemigroup_2810 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_470
d_'8851''45'isSemigroup_2810
  = let v0 = d_'8804''45'totalPreorder_524 in
    coe
      (let v1 = d_'8851''45'operator_2720 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'isSemigroup_3062
            (coe v0) (coe v1)))
-- Data.Rational.Unnormalised.Properties.⊓-⊔-properties.⊓-magma
d_'8851''45'magma_2812 :: MAlonzo.Code.Algebra.Bundles.T_Magma_72
d_'8851''45'magma_2812
  = let v0 = d_'8804''45'totalPreorder_524 in
    coe
      (let v1 = d_'8851''45'operator_2720 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'magma_3078
            (coe v0) (coe v1)))
-- Data.Rational.Unnormalised.Properties.⊓-⊔-properties.⊓-mono-≤
d_'8851''45'mono'45''8804'_2814 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8804'__38 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8804'__38 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8804'__38
d_'8851''45'mono'45''8804'_2814
  = let v0 = d_'8804''45'totalPreorder_524 in
    coe
      (let v1 = d_'8851''45'operator_2720 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'mono'45''8804'_3236
            (coe v0) (coe v1)))
-- Data.Rational.Unnormalised.Properties.⊓-⊔-properties.⊓-monoʳ-≤
d_'8851''45'mono'691''45''8804'_2818 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8804'__38 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8804'__38
d_'8851''45'mono'691''45''8804'_2818
  = let v0 = d_'8804''45'totalPreorder_524 in
    coe
      (let v1 = d_'8851''45'operator_2720 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'mono'691''45''8804'_3296
            (coe v0) (coe v1)))
-- Data.Rational.Unnormalised.Properties.⊓-⊔-properties.⊓-monoˡ-≤
d_'8851''45'mono'737''45''8804'_2820 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8804'__38 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8804'__38
d_'8851''45'mono'737''45''8804'_2820
  = let v0 = d_'8804''45'totalPreorder_524 in
    coe
      (let v1 = d_'8851''45'operator_2720 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'mono'737''45''8804'_3286
            (coe v0) (coe v1)))
-- Data.Rational.Unnormalised.Properties.⊓-⊔-properties.⊓-sel
d_'8851''45'sel_2824 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_'8851''45'sel_2824
  = let v0 = d_'8804''45'totalPreorder_524 in
    coe
      (let v1 = d_'8851''45'operator_2720 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'sel_3018
            (coe v0) (coe v1)))
-- Data.Rational.Unnormalised.Properties.⊓-⊔-properties.⊓-selectiveMagma
d_'8851''45'selectiveMagma_2826 ::
  MAlonzo.Code.Algebra.Bundles.T_SelectiveMagma_126
d_'8851''45'selectiveMagma_2826
  = let v0 = d_'8804''45'totalPreorder_524 in
    coe
      (let v1 = d_'8851''45'operator_2720 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'selectiveMagma_3086
            (coe v0) (coe v1)))
-- Data.Rational.Unnormalised.Properties.⊓-⊔-properties.⊓-semigroup
d_'8851''45'semigroup_2828 ::
  MAlonzo.Code.Algebra.Bundles.T_Semigroup_540
d_'8851''45'semigroup_2828
  = let v0 = d_'8804''45'totalPreorder_524 in
    coe
      (let v1 = d_'8851''45'operator_2720 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'semigroup_3080
            (coe v0) (coe v1)))
-- Data.Rational.Unnormalised.Properties.⊓-⊔-properties.⊓-triangulate
d_'8851''45'triangulate_2830 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8771'__24
d_'8851''45'triangulate_2830
  = let v0 = d_'8804''45'totalPreorder_524 in
    coe
      (let v1 = d_'8851''45'operator_2720 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'triangulate_3322
            (coe v0) (coe v1)))
-- Data.Rational.Unnormalised.Properties.⊓-⊔-properties.⊓-⊔-absorptive
d_'8851''45''8852''45'absorptive_2838 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8851''45''8852''45'absorptive_2838
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinMaxOp.du_'8851''45''8852''45'absorptive_3254
      (coe d_'8804''45'totalPreorder_524) (coe d_'8851''45'operator_2720)
      (coe d_'8852''45'operator_2722)
-- Data.Rational.Unnormalised.Properties.⊓-⊔-properties.⊔-absorbs-⊓
d_'8852''45'absorbs'45''8851'_2840 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8771'__24
d_'8852''45'absorbs'45''8851'_2840
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinMaxOp.du_'8852''45'absorbs'45''8851'_3230
      (coe d_'8804''45'totalPreorder_524) (coe d_'8851''45'operator_2720)
      (coe d_'8852''45'operator_2722)
-- Data.Rational.Unnormalised.Properties.⊓-⊔-properties.⊓-assoc
d_'8851''45'assoc_2842 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8771'__24
d_'8851''45'assoc_2842
  = let v0 = d_'8804''45'totalPreorder_524 in
    coe
      (let v1 = d_'8852''45'operator_2722 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'assoc_2974
            (coe
               MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_760
               (coe v0))
            (coe
               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_182
               (coe v1))))
-- Data.Rational.Unnormalised.Properties.⊓-⊔-properties.⊓-band
d_'8851''45'band_2844 :: MAlonzo.Code.Algebra.Bundles.T_Band_600
d_'8851''45'band_2844
  = let v0 = d_'8804''45'totalPreorder_524 in
    coe
      (let v1 = d_'8852''45'operator_2722 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'band_3082
            (coe
               MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_760
               (coe v0))
            (coe
               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_182
               (coe v1))))
-- Data.Rational.Unnormalised.Properties.⊓-⊔-properties.⊓-comm
d_'8851''45'comm_2846 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8771'__24
d_'8851''45'comm_2846
  = let v0 = d_'8804''45'totalPreorder_524 in
    coe
      (let v1 = d_'8852''45'operator_2722 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'comm_2886
            (coe
               MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_760
               (coe v0))
            (coe
               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_182
               (coe v1))))
-- Data.Rational.Unnormalised.Properties.⊓-⊔-properties.⊓-commutativeSemigroup
d_'8851''45'commutativeSemigroup_2848 ::
  MAlonzo.Code.Algebra.Bundles.T_CommutativeSemigroup_666
d_'8851''45'commutativeSemigroup_2848
  = let v0 = d_'8804''45'totalPreorder_524 in
    coe
      (let v1 = d_'8852''45'operator_2722 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'commutativeSemigroup_3084
            (coe
               MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_760
               (coe v0))
            (coe
               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_182
               (coe v1))))
-- Data.Rational.Unnormalised.Properties.⊓-⊔-properties.⊓-cong
d_'8851''45'cong_2850 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8771'__24 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8771'__24 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8771'__24
d_'8851''45'cong_2850
  = let v0 = d_'8804''45'totalPreorder_524 in
    coe
      (let v1 = d_'8852''45'operator_2722 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'cong_2960
            (coe
               MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_760
               (coe v0))
            (coe
               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_182
               (coe v1))))
-- Data.Rational.Unnormalised.Properties.⊓-⊔-properties.⊓-congʳ
d_'8851''45'cong'691'_2852 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8771'__24 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8771'__24
d_'8851''45'cong'691'_2852
  = let v0 = d_'8804''45'totalPreorder_524 in
    coe
      (let v1 = d_'8852''45'operator_2722 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'cong'691'_2950
            (coe
               MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_760
               (coe v0))
            (coe
               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_182
               (coe v1))))
-- Data.Rational.Unnormalised.Properties.⊓-⊔-properties.⊓-congˡ
d_'8851''45'cong'737'_2854 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8771'__24 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8771'__24
d_'8851''45'cong'737'_2854
  = let v0 = d_'8804''45'totalPreorder_524 in
    coe
      (let v1 = d_'8852''45'operator_2722 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'cong'737'_2912
            (coe
               MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_760
               (coe v0))
            (coe
               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_182
               (coe v1))))
-- Data.Rational.Unnormalised.Properties.⊓-⊔-properties.⊔-distrib-⊓
d_'8852''45'distrib'45''8851'_2856 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8852''45'distrib'45''8851'_2856
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinMaxOp.du_'8852''45'distrib'45''8851'_3206
      (coe d_'8804''45'totalPreorder_524) (coe d_'8851''45'operator_2720)
      (coe d_'8852''45'operator_2722)
-- Data.Rational.Unnormalised.Properties.⊓-⊔-properties.⊔-distribʳ-⊓
d_'8852''45'distrib'691''45''8851'_2858 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8771'__24
d_'8852''45'distrib'691''45''8851'_2858
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinMaxOp.du_'8852''45'distrib'691''45''8851'_3204
      (coe d_'8804''45'totalPreorder_524) (coe d_'8851''45'operator_2720)
      (coe d_'8852''45'operator_2722)
-- Data.Rational.Unnormalised.Properties.⊓-⊔-properties.⊔-distribˡ-⊓
d_'8852''45'distrib'737''45''8851'_2860 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8771'__24
d_'8852''45'distrib'737''45''8851'_2860
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinMaxOp.du_'8852''45'distrib'737''45''8851'_3176
      (coe d_'8804''45'totalPreorder_524) (coe d_'8851''45'operator_2720)
      (coe d_'8852''45'operator_2722)
-- Data.Rational.Unnormalised.Properties.⊓-⊔-properties.⊓-idem
d_'8851''45'idem_2862 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8771'__24
d_'8851''45'idem_2862
  = let v0 = d_'8804''45'totalPreorder_524 in
    coe
      (let v1 = d_'8852''45'operator_2722 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'idem_3014
            (coe
               MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_760
               (coe v0))
            (coe
               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_182
               (coe v1))))
-- Data.Rational.Unnormalised.Properties.⊓-⊔-properties.⊓-isBand
d_'8851''45'isBand_2870 ::
  MAlonzo.Code.Algebra.Structures.T_IsBand_506
d_'8851''45'isBand_2870
  = let v0 = d_'8804''45'totalPreorder_524 in
    coe
      (let v1 = d_'8852''45'operator_2722 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'isBand_3064
            (coe
               MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_760
               (coe v0))
            (coe
               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_182
               (coe v1))))
-- Data.Rational.Unnormalised.Properties.⊓-⊔-properties.⊓-isCommutativeSemigroup
d_'8851''45'isCommutativeSemigroup_2872 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeSemigroup_546
d_'8851''45'isCommutativeSemigroup_2872
  = let v0 = d_'8804''45'totalPreorder_524 in
    coe
      (let v1 = d_'8852''45'operator_2722 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'isCommutativeSemigroup_3066
            (coe
               MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_760
               (coe v0))
            (coe
               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_182
               (coe v1))))
-- Data.Rational.Unnormalised.Properties.⊓-⊔-properties.⊓-isMagma
d_'8851''45'isMagma_2874 ::
  MAlonzo.Code.Algebra.Structures.T_IsMagma_176
d_'8851''45'isMagma_2874
  = let v0 = d_'8804''45'totalPreorder_524 in
    coe
      (let v1 = d_'8852''45'operator_2722 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'isMagma_3060
            (coe
               MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_760
               (coe v0))
            (coe
               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_182
               (coe v1))))
-- Data.Rational.Unnormalised.Properties.⊓-⊔-properties.⊓-isSelectiveMagma
d_'8851''45'isSelectiveMagma_2878 ::
  MAlonzo.Code.Algebra.Structures.T_IsSelectiveMagma_434
d_'8851''45'isSelectiveMagma_2878
  = let v0 = d_'8804''45'totalPreorder_524 in
    coe
      (let v1 = d_'8852''45'operator_2722 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'isSelectiveMagma_3068
            (coe
               MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_760
               (coe v0))
            (coe
               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_182
               (coe v1))))
-- Data.Rational.Unnormalised.Properties.⊓-⊔-properties.⊓-isSemigroup
d_'8851''45'isSemigroup_2880 ::
  MAlonzo.Code.Algebra.Structures.T_IsSemigroup_470
d_'8851''45'isSemigroup_2880
  = let v0 = d_'8804''45'totalPreorder_524 in
    coe
      (let v1 = d_'8852''45'operator_2722 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'isSemigroup_3062
            (coe
               MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_760
               (coe v0))
            (coe
               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_182
               (coe v1))))
-- Data.Rational.Unnormalised.Properties.⊓-⊔-properties.⊓-glb
d_'8851''45'glb_2882 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8804'__38 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8804'__38 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8804'__38
d_'8851''45'glb_2882
  = let v0 = d_'8804''45'totalPreorder_524 in
    coe
      (let v1 = d_'8852''45'operator_2722 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'glb_3308
            (coe
               MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_760
               (coe v0))
            (coe
               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_182
               (coe v1))))
-- Data.Rational.Unnormalised.Properties.⊓-⊔-properties.⊓-magma
d_'8851''45'magma_2884 :: MAlonzo.Code.Algebra.Bundles.T_Magma_72
d_'8851''45'magma_2884
  = let v0 = d_'8804''45'totalPreorder_524 in
    coe
      (let v1 = d_'8852''45'operator_2722 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'magma_3078
            (coe
               MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_760
               (coe v0))
            (coe
               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_182
               (coe v1))))
-- Data.Rational.Unnormalised.Properties.⊓-⊔-properties.⊓-mono-≤
d_'8851''45'mono'45''8804'_2886 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8804'__38 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8804'__38 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8804'__38
d_'8851''45'mono'45''8804'_2886
  = let v0 = d_'8804''45'totalPreorder_524 in
    coe
      (let v1 = d_'8852''45'operator_2722 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'mono'45''8804'_3236
            (coe
               MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_760
               (coe v0))
            (coe
               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_182
               (coe v1))))
-- Data.Rational.Unnormalised.Properties.⊓-⊔-properties.⊓-monoʳ-≤
d_'8851''45'mono'691''45''8804'_2890 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8804'__38 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8804'__38
d_'8851''45'mono'691''45''8804'_2890
  = let v0 = d_'8804''45'totalPreorder_524 in
    coe
      (let v1 = d_'8852''45'operator_2722 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'mono'691''45''8804'_3296
            (coe
               MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_760
               (coe v0))
            (coe
               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_182
               (coe v1))))
-- Data.Rational.Unnormalised.Properties.⊓-⊔-properties.⊓-monoˡ-≤
d_'8851''45'mono'737''45''8804'_2892 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8804'__38 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8804'__38
d_'8851''45'mono'737''45''8804'_2892
  = let v0 = d_'8804''45'totalPreorder_524 in
    coe
      (let v1 = d_'8852''45'operator_2722 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'mono'737''45''8804'_3286
            (coe
               MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_760
               (coe v0))
            (coe
               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_182
               (coe v1))))
-- Data.Rational.Unnormalised.Properties.⊓-⊔-properties.⊓-sel
d_'8851''45'sel_2894 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_'8851''45'sel_2894
  = let v0 = d_'8804''45'totalPreorder_524 in
    coe
      (let v1 = d_'8852''45'operator_2722 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'sel_3018
            (coe
               MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_760
               (coe v0))
            (coe
               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_182
               (coe v1))))
-- Data.Rational.Unnormalised.Properties.⊓-⊔-properties.⊓-selectiveMagma
d_'8851''45'selectiveMagma_2896 ::
  MAlonzo.Code.Algebra.Bundles.T_SelectiveMagma_126
d_'8851''45'selectiveMagma_2896
  = let v0 = d_'8804''45'totalPreorder_524 in
    coe
      (let v1 = d_'8852''45'operator_2722 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'selectiveMagma_3086
            (coe
               MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_760
               (coe v0))
            (coe
               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_182
               (coe v1))))
-- Data.Rational.Unnormalised.Properties.⊓-⊔-properties.⊓-semigroup
d_'8851''45'semigroup_2898 ::
  MAlonzo.Code.Algebra.Bundles.T_Semigroup_540
d_'8851''45'semigroup_2898
  = let v0 = d_'8804''45'totalPreorder_524 in
    coe
      (let v1 = d_'8852''45'operator_2722 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'semigroup_3080
            (coe
               MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_760
               (coe v0))
            (coe
               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_182
               (coe v1))))
-- Data.Rational.Unnormalised.Properties.⊓-⊔-properties.⊓-triangulate
d_'8851''45'triangulate_2900 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8771'__24
d_'8851''45'triangulate_2900
  = let v0 = d_'8804''45'totalPreorder_524 in
    coe
      (let v1 = d_'8852''45'operator_2722 in
       coe
         (coe
            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'triangulate_3322
            (coe
               MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_760
               (coe v0))
            (coe
               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_182
               (coe v1))))
-- Data.Rational.Unnormalised.Properties.⊓-⊔-properties.⊔-⊓-absorptive
d_'8852''45''8851''45'absorptive_2908 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8852''45''8851''45'absorptive_2908
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinMaxOp.du_'8852''45''8851''45'absorptive_3252
      (coe d_'8804''45'totalPreorder_524) (coe d_'8851''45'operator_2720)
      (coe d_'8852''45'operator_2722)
-- Data.Rational.Unnormalised.Properties.⊓-⊔-latticeProperties.⊓-isSemilattice
d_'8851''45'isSemilattice_2912 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_588
d_'8851''45'isSemilattice_2912
  = let v0 = d_'8804''45'totalPreorder_524 in
    coe
      (let v1 = d_'8851''45'operator_2720 in
       coe
         (coe
            MAlonzo.Code.Algebra.Lattice.Construct.NaturalChoice.MinOp.du_'8851''45'isSemilattice_610
            (coe v0) (coe v1)))
-- Data.Rational.Unnormalised.Properties.⊓-⊔-latticeProperties.⊓-semilattice
d_'8851''45'semilattice_2914 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_Semilattice_10
d_'8851''45'semilattice_2914
  = let v0 = d_'8804''45'totalPreorder_524 in
    coe
      (let v1 = d_'8851''45'operator_2720 in
       coe
         (coe
            MAlonzo.Code.Algebra.Lattice.Construct.NaturalChoice.MinOp.du_'8851''45'semilattice_612
            (coe v0) (coe v1)))
-- Data.Rational.Unnormalised.Properties.⊓-⊔-latticeProperties.⊓-⊔-distributiveLattice
d_'8851''45''8852''45'distributiveLattice_2916 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_DistributiveLattice_584
d_'8851''45''8852''45'distributiveLattice_2916
  = coe
      MAlonzo.Code.Algebra.Lattice.Construct.NaturalChoice.MinMaxOp.du_'8851''45''8852''45'distributiveLattice_816
      (coe d_'8804''45'totalPreorder_524) (coe d_'8851''45'operator_2720)
      (coe d_'8852''45'operator_2722)
-- Data.Rational.Unnormalised.Properties.⊓-⊔-latticeProperties.⊓-⊔-isDistributiveLattice
d_'8851''45''8852''45'isDistributiveLattice_2918 ::
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsDistributiveLattice_3058
d_'8851''45''8852''45'isDistributiveLattice_2918
  = coe
      MAlonzo.Code.Algebra.Lattice.Construct.NaturalChoice.MinMaxOp.du_'8851''45''8852''45'isDistributiveLattice_806
      (coe d_'8804''45'totalPreorder_524) (coe d_'8851''45'operator_2720)
      (coe d_'8852''45'operator_2722)
-- Data.Rational.Unnormalised.Properties.⊓-⊔-latticeProperties.⊓-⊔-isLattice
d_'8851''45''8852''45'isLattice_2920 ::
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsLattice_2984
d_'8851''45''8852''45'isLattice_2920
  = coe
      MAlonzo.Code.Algebra.Lattice.Construct.NaturalChoice.MinMaxOp.du_'8851''45''8852''45'isLattice_804
      (coe d_'8804''45'totalPreorder_524) (coe d_'8851''45'operator_2720)
      (coe d_'8852''45'operator_2722)
-- Data.Rational.Unnormalised.Properties.⊓-⊔-latticeProperties.⊓-⊔-lattice
d_'8851''45''8852''45'lattice_2922 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_Lattice_500
d_'8851''45''8852''45'lattice_2922
  = coe
      MAlonzo.Code.Algebra.Lattice.Construct.NaturalChoice.MinMaxOp.du_'8851''45''8852''45'lattice_812
      (coe d_'8804''45'totalPreorder_524) (coe d_'8851''45'operator_2720)
      (coe d_'8852''45'operator_2722)
-- Data.Rational.Unnormalised.Properties.⊓-⊔-latticeProperties.⊓-isSemilattice
d_'8851''45'isSemilattice_2924 ::
  MAlonzo.Code.Algebra.Structures.T_IsCommutativeBand_588
d_'8851''45'isSemilattice_2924
  = let v0 = d_'8804''45'totalPreorder_524 in
    coe
      (let v1 = d_'8852''45'operator_2722 in
       coe
         (coe
            MAlonzo.Code.Algebra.Lattice.Construct.NaturalChoice.MinOp.du_'8851''45'isSemilattice_610
            (coe
               MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_760
               (coe v0))
            (coe
               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_182
               (coe v1))))
-- Data.Rational.Unnormalised.Properties.⊓-⊔-latticeProperties.⊓-semilattice
d_'8851''45'semilattice_2926 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_Semilattice_10
d_'8851''45'semilattice_2926
  = let v0 = d_'8804''45'totalPreorder_524 in
    coe
      (let v1 = d_'8852''45'operator_2722 in
       coe
         (coe
            MAlonzo.Code.Algebra.Lattice.Construct.NaturalChoice.MinOp.du_'8851''45'semilattice_612
            (coe
               MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_760
               (coe v0))
            (coe
               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_182
               (coe v1))))
-- Data.Rational.Unnormalised.Properties.⊓-⊔-latticeProperties.⊔-⊓-distributiveLattice
d_'8852''45''8851''45'distributiveLattice_2928 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_DistributiveLattice_584
d_'8852''45''8851''45'distributiveLattice_2928
  = coe
      MAlonzo.Code.Algebra.Lattice.Construct.NaturalChoice.MinMaxOp.du_'8852''45''8851''45'distributiveLattice_814
      (coe d_'8804''45'totalPreorder_524) (coe d_'8851''45'operator_2720)
      (coe d_'8852''45'operator_2722)
-- Data.Rational.Unnormalised.Properties.⊓-⊔-latticeProperties.⊔-⊓-isDistributiveLattice
d_'8852''45''8851''45'isDistributiveLattice_2930 ::
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsDistributiveLattice_3058
d_'8852''45''8851''45'isDistributiveLattice_2930
  = coe
      MAlonzo.Code.Algebra.Lattice.Construct.NaturalChoice.MinMaxOp.du_'8852''45''8851''45'isDistributiveLattice_808
      (coe d_'8804''45'totalPreorder_524) (coe d_'8851''45'operator_2720)
      (coe d_'8852''45'operator_2722)
-- Data.Rational.Unnormalised.Properties.⊓-⊔-latticeProperties.⊔-⊓-isLattice
d_'8852''45''8851''45'isLattice_2932 ::
  MAlonzo.Code.Algebra.Lattice.Structures.T_IsLattice_2984
d_'8852''45''8851''45'isLattice_2932
  = coe
      MAlonzo.Code.Algebra.Lattice.Construct.NaturalChoice.MinMaxOp.du_'8852''45''8851''45'isLattice_802
      (coe d_'8804''45'totalPreorder_524) (coe d_'8851''45'operator_2720)
      (coe d_'8852''45'operator_2722)
-- Data.Rational.Unnormalised.Properties.⊓-⊔-latticeProperties.⊔-⊓-lattice
d_'8852''45''8851''45'lattice_2934 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.T_Lattice_500
d_'8852''45''8851''45'lattice_2934
  = coe
      MAlonzo.Code.Algebra.Lattice.Construct.NaturalChoice.MinMaxOp.du_'8852''45''8851''45'lattice_810
      (coe d_'8804''45'totalPreorder_524) (coe d_'8851''45'operator_2720)
      (coe d_'8852''45'operator_2722)
-- Data.Rational.Unnormalised.Properties.⊓-rawMagma
d_'8851''45'rawMagma_2936 ::
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMagma_42
d_'8851''45'rawMagma_2936
  = coe
      MAlonzo.Code.Algebra.Bundles.du_rawMagma_116
      (coe
         MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'magma_3078
         (coe d_'8804''45'totalPreorder_524)
         (coe d_'8851''45'operator_2720))
-- Data.Rational.Unnormalised.Properties.⊔-rawMagma
d_'8852''45'rawMagma_2938 ::
  MAlonzo.Code.Algebra.Bundles.Raw.T_RawMagma_42
d_'8852''45'rawMagma_2938
  = coe
      MAlonzo.Code.Algebra.Bundles.du_rawMagma_116
      (let v0 = d_'8804''45'totalPreorder_524 in
       coe
         (let v1 = d_'8852''45'operator_2722 in
          coe
            (coe
               MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_'8851''45'magma_3078
               (coe
                  MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_760
                  (coe v0))
               (coe
                  MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_182
                  (coe v1)))))
-- Data.Rational.Unnormalised.Properties.⊔-⊓-rawLattice
d_'8852''45''8851''45'rawLattice_2940 ::
  MAlonzo.Code.Algebra.Lattice.Bundles.Raw.T_RawLattice_12
d_'8852''45''8851''45'rawLattice_2940
  = coe
      MAlonzo.Code.Algebra.Lattice.Bundles.du_rawLattice_566
      (coe
         MAlonzo.Code.Algebra.Lattice.Construct.NaturalChoice.MinMaxOp.du_'8852''45''8851''45'lattice_810
         (coe d_'8804''45'totalPreorder_524) (coe d_'8851''45'operator_2720)
         (coe d_'8852''45'operator_2722))
-- Data.Rational.Unnormalised.Properties.mono-≤-distrib-⊔
d_mono'45''8804''45'distrib'45''8852'_2948 ::
  (MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
   MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8) ->
  (MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
   MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
   MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8804'__38 ->
   MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8804'__38) ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8771'__24
d_mono'45''8804''45'distrib'45''8852'_2948 v0 v1
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MaxOp.du_mono'45''8804''45'distrib'45''8852'_190
      (coe d_'8804''45'totalPreorder_524) (coe d_'8852''45'operator_2722)
      (coe v0) (coe d_mono'8658'cong_542 v0 v1) (coe v1)
-- Data.Rational.Unnormalised.Properties.mono-≤-distrib-⊓
d_mono'45''8804''45'distrib'45''8851'_2958 ::
  (MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
   MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8) ->
  (MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
   MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
   MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8804'__38 ->
   MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8804'__38) ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8771'__24
d_mono'45''8804''45'distrib'45''8851'_2958 v0 v1
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_mono'45''8804''45'distrib'45''8851'_3144
      (coe d_'8804''45'totalPreorder_524) (coe d_'8851''45'operator_2720)
      (coe v0) (coe d_mono'8658'cong_542 v0 v1) (coe v1)
-- Data.Rational.Unnormalised.Properties.antimono-≤-distrib-⊓
d_antimono'45''8804''45'distrib'45''8851'_2968 ::
  (MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
   MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8) ->
  (MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
   MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
   MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8804'__38 ->
   MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8804'__38) ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8771'__24
d_antimono'45''8804''45'distrib'45''8851'_2968 v0 v1
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinMaxOp.du_antimono'45''8804''45'distrib'45''8851'_3264
      (coe d_'8804''45'totalPreorder_524) (coe d_'8851''45'operator_2720)
      (coe d_'8852''45'operator_2722) (coe v0)
      (coe d_antimono'8658'cong_546 v0 v1) (coe v1)
-- Data.Rational.Unnormalised.Properties.antimono-≤-distrib-⊔
d_antimono'45''8804''45'distrib'45''8852'_2978 ::
  (MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
   MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8) ->
  (MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
   MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
   MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8804'__38 ->
   MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8804'__38) ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8771'__24
d_antimono'45''8804''45'distrib'45''8852'_2978 v0 v1
  = coe
      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinMaxOp.du_antimono'45''8804''45'distrib'45''8852'_3310
      (coe d_'8804''45'totalPreorder_524) (coe d_'8851''45'operator_2720)
      (coe d_'8852''45'operator_2722) (coe v0)
      (coe d_antimono'8658'cong_546 v0 v1) (coe v1)
-- Data.Rational.Unnormalised.Properties.neg-distrib-⊔-⊓
d_neg'45'distrib'45''8852''45''8851'_2986 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8771'__24
d_neg'45'distrib'45''8852''45''8851'_2986
  = coe
      d_antimono'45''8804''45'distrib'45''8852'_2978
      (coe MAlonzo.Code.Data.Rational.Unnormalised.Base.d_'45'__190)
      (coe d_neg'45'mono'45''8804'_1550)
-- Data.Rational.Unnormalised.Properties.neg-distrib-⊓-⊔
d_neg'45'distrib'45''8851''45''8852'_2992 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8771'__24
d_neg'45'distrib'45''8851''45''8852'_2992
  = coe
      d_antimono'45''8804''45'distrib'45''8851'_2968
      (coe MAlonzo.Code.Data.Rational.Unnormalised.Base.d_'45'__190)
      (coe d_neg'45'mono'45''8804'_1550)
-- Data.Rational.Unnormalised.Properties.*-distribˡ-⊓-nonNeg
d_'42''45'distrib'737''45''8851''45'nonNeg_3002 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Integer.Base.T_NonNegative_144 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8771'__24
d_'42''45'distrib'737''45''8851''45'nonNeg_3002 v0 ~v1
  = du_'42''45'distrib'737''45''8851''45'nonNeg_3002 v0
du_'42''45'distrib'737''45''8851''45'nonNeg_3002 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8771'__24
du_'42''45'distrib'737''45''8851''45'nonNeg_3002 v0
  = coe
      d_mono'45''8804''45'distrib'45''8851'_2958
      (coe
         MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'42'__202 (coe v0))
      (coe du_'42''45'mono'691''45''8804''45'nonNeg_2144 (coe v0))
-- Data.Rational.Unnormalised.Properties.*-distribʳ-⊓-nonNeg
d_'42''45'distrib'691''45''8851''45'nonNeg_3014 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Integer.Base.T_NonNegative_144 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8771'__24
d_'42''45'distrib'691''45''8851''45'nonNeg_3014 v0 ~v1
  = du_'42''45'distrib'691''45''8851''45'nonNeg_3014 v0
du_'42''45'distrib'691''45''8851''45'nonNeg_3014 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8771'__24
du_'42''45'distrib'691''45''8851''45'nonNeg_3014 v0
  = coe
      d_mono'45''8804''45'distrib'45''8851'_2958
      (coe
         (\ v1 ->
            MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'42'__202
              (coe v1) (coe v0)))
      (coe du_'42''45'mono'737''45''8804''45'nonNeg_2114 (coe v0))
-- Data.Rational.Unnormalised.Properties.*-distribˡ-⊔-nonNeg
d_'42''45'distrib'737''45''8852''45'nonNeg_3026 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Integer.Base.T_NonNegative_144 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8771'__24
d_'42''45'distrib'737''45''8852''45'nonNeg_3026 v0 ~v1
  = du_'42''45'distrib'737''45''8852''45'nonNeg_3026 v0
du_'42''45'distrib'737''45''8852''45'nonNeg_3026 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8771'__24
du_'42''45'distrib'737''45''8852''45'nonNeg_3026 v0
  = coe
      d_mono'45''8804''45'distrib'45''8852'_2948
      (coe
         MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'42'__202 (coe v0))
      (coe du_'42''45'mono'691''45''8804''45'nonNeg_2144 (coe v0))
-- Data.Rational.Unnormalised.Properties.*-distribʳ-⊔-nonNeg
d_'42''45'distrib'691''45''8852''45'nonNeg_3038 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Integer.Base.T_NonNegative_144 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8771'__24
d_'42''45'distrib'691''45''8852''45'nonNeg_3038 v0 ~v1
  = du_'42''45'distrib'691''45''8852''45'nonNeg_3038 v0
du_'42''45'distrib'691''45''8852''45'nonNeg_3038 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8771'__24
du_'42''45'distrib'691''45''8852''45'nonNeg_3038 v0
  = coe
      d_mono'45''8804''45'distrib'45''8852'_2948
      (coe
         (\ v1 ->
            MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'42'__202
              (coe v1) (coe v0)))
      (coe du_'42''45'mono'737''45''8804''45'nonNeg_2114 (coe v0))
-- Data.Rational.Unnormalised.Properties.*-distribˡ-⊔-nonPos
d_'42''45'distrib'737''45''8852''45'nonPos_3050 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Integer.Base.T_NonPositive_154 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8771'__24
d_'42''45'distrib'737''45''8852''45'nonPos_3050 v0 ~v1
  = du_'42''45'distrib'737''45''8852''45'nonPos_3050 v0
du_'42''45'distrib'737''45''8852''45'nonPos_3050 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8771'__24
du_'42''45'distrib'737''45''8852''45'nonPos_3050 v0
  = coe
      d_antimono'45''8804''45'distrib'45''8852'_2978
      (coe
         MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'42'__202 (coe v0))
      (coe du_'42''45'mono'691''45''8804''45'nonPos_2218 (coe v0))
-- Data.Rational.Unnormalised.Properties.*-distribʳ-⊔-nonPos
d_'42''45'distrib'691''45''8852''45'nonPos_3062 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Integer.Base.T_NonPositive_154 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8771'__24
d_'42''45'distrib'691''45''8852''45'nonPos_3062 v0 ~v1
  = du_'42''45'distrib'691''45''8852''45'nonPos_3062 v0
du_'42''45'distrib'691''45''8852''45'nonPos_3062 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8771'__24
du_'42''45'distrib'691''45''8852''45'nonPos_3062 v0
  = coe
      d_antimono'45''8804''45'distrib'45''8852'_2978
      (coe
         (\ v1 ->
            MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'42'__202
              (coe v1) (coe v0)))
      (coe du_'42''45'mono'737''45''8804''45'nonPos_2196 (coe v0))
-- Data.Rational.Unnormalised.Properties.*-distribˡ-⊓-nonPos
d_'42''45'distrib'737''45''8851''45'nonPos_3074 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Integer.Base.T_NonPositive_154 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8771'__24
d_'42''45'distrib'737''45''8851''45'nonPos_3074 v0 ~v1
  = du_'42''45'distrib'737''45''8851''45'nonPos_3074 v0
du_'42''45'distrib'737''45''8851''45'nonPos_3074 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8771'__24
du_'42''45'distrib'737''45''8851''45'nonPos_3074 v0
  = coe
      d_antimono'45''8804''45'distrib'45''8851'_2968
      (coe
         MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'42'__202 (coe v0))
      (coe du_'42''45'mono'691''45''8804''45'nonPos_2218 (coe v0))
-- Data.Rational.Unnormalised.Properties.*-distribʳ-⊓-nonPos
d_'42''45'distrib'691''45''8851''45'nonPos_3086 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Integer.Base.T_NonPositive_154 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8771'__24
d_'42''45'distrib'691''45''8851''45'nonPos_3086 v0 ~v1
  = du_'42''45'distrib'691''45''8851''45'nonPos_3086 v0
du_'42''45'distrib'691''45''8851''45'nonPos_3086 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8771'__24
du_'42''45'distrib'691''45''8851''45'nonPos_3086 v0
  = coe
      d_antimono'45''8804''45'distrib'45''8851'_2968
      (coe
         (\ v1 ->
            MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'42'__202
              (coe v1) (coe v0)))
      (coe du_'42''45'mono'737''45''8804''45'nonPos_2196 (coe v0))
-- Data.Rational.Unnormalised.Properties.⊓-mono-<
d_'8851''45'mono'45''60'_3090 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'60'__46 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'60'__46 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'60'__46
d_'8851''45'mono'45''60'_3090 v0 v1 v2 v3 v4 v5
  = let v6
          = coe
              MAlonzo.Code.Data.Sum.Base.du_'91'_'44'_'93'_52
              (coe
                 (\ v6 ->
                    coe
                      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                      (coe du_p'8804'q'8658'p'8851'q'8771'p_2662 (coe v1) (coe v3))))
              (coe
                 (\ v6 ->
                    coe
                      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                      (coe
                         d_p'8805'q'8658'p'8851'q'8771'q_2690 (coe v1) (coe v3) (coe v6))))
              (coe
                 MAlonzo.Code.Data.Sum.Base.du_'91'_'44'_'93'_52
                 (coe
                    (\ v6 ->
                       coe
                         MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                         (coe
                            MAlonzo.Code.Data.Rational.Unnormalised.Base.C_'42''8804''42'_44
                            v6)))
                 (coe
                    (\ v6 ->
                       coe
                         MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                         (coe
                            MAlonzo.Code.Data.Rational.Unnormalised.Base.C_'42''8804''42'_44
                            v6)))
                 (coe
                    MAlonzo.Code.Data.Integer.Properties.d_'8804''45'total_2776
                    (coe
                       MAlonzo.Code.Data.Integer.Base.d__'9667'__230
                       (coe
                          MAlonzo.Code.Data.Sign.Base.d__'42'__14
                          (coe
                             MAlonzo.Code.Data.Integer.Base.d_sign_24
                             (coe
                                MAlonzo.Code.Data.Rational.Unnormalised.Base.d_numerator_14
                                (coe v1)))
                          (coe
                             MAlonzo.Code.Data.Integer.Base.d_sign_24
                             (coe
                                MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                (coe v3))))
                       (coe
                          mulInt
                          (coe
                             MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18
                             (coe
                                MAlonzo.Code.Data.Rational.Unnormalised.Base.d_numerator_14
                                (coe v1)))
                          (coe
                             MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18
                             (coe
                                MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                (coe v3)))))
                    (coe
                       MAlonzo.Code.Data.Integer.Base.d__'42'__308
                       (coe
                          MAlonzo.Code.Data.Rational.Unnormalised.Base.d_numerator_14
                          (coe v3))
                       (coe
                          MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                          (coe v1))))) in
    coe
      (case coe v6 of
         MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v7
           -> coe
                d_'60''45'resp'691''45''8771'_734
                (coe
                   MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'8851'__254
                   (coe v0) (coe v2))
                (coe v1)
                (coe
                   MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'8851'__254
                   (coe v1) (coe v3))
                (coe du_'8771''45'sym_170 (coe v7))
                (coe
                   d_'8804''45''60''45'trans_610
                   (coe
                      MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'8851'__254
                      (coe v0) (coe v2))
                   (coe v0) (coe v1)
                   (coe
                      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8851'y'8804'x_2838
                      (coe d_'8804''45'totalPreorder_524) (coe d_'8851''45'operator_2720)
                      (coe v0) (coe v2))
                   (coe v4))
         MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v7
           -> coe
                d_'60''45'resp'691''45''8771'_734
                (coe
                   MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'8851'__254
                   (coe v0) (coe v2))
                (coe v3)
                (coe
                   MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'8851'__254
                   (coe v1) (coe v3))
                (coe du_'8771''45'sym_170 (coe v7))
                (coe
                   d_'8804''45''60''45'trans_610
                   (coe
                      MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'8851'__254
                      (coe v0) (coe v2))
                   (coe v2) (coe v3)
                   (coe
                      MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8851'y'8804'y_2864
                      (coe d_'8804''45'totalPreorder_524) (coe d_'8851''45'operator_2720)
                      (coe v0) (coe v2))
                   (coe v5))
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Data.Rational.Unnormalised.Properties.⊔-mono-<
d_'8852''45'mono'45''60'_3136 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'60'__46 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'60'__46 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'60'__46
d_'8852''45'mono'45''60'_3136 v0 v1 v2 v3 v4 v5
  = let v6
          = coe
              MAlonzo.Code.Data.Sum.Base.du_'91'_'44'_'93'_52
              (coe
                 (\ v6 ->
                    coe
                      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                      (coe
                         d_p'8805'q'8658'p'8852'q'8771'p_2632 (coe v0) (coe v2) (coe v6))))
              (coe
                 (\ v6 ->
                    coe
                      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                      (coe du_p'8804'q'8658'p'8852'q'8771'q_2604 (coe v0) (coe v2))))
              (coe
                 MAlonzo.Code.Data.Sum.Base.du_'91'_'44'_'93'_52
                 (coe
                    (\ v6 ->
                       coe
                         MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                         (coe
                            MAlonzo.Code.Data.Rational.Unnormalised.Base.C_'42''8804''42'_44
                            v6)))
                 (coe
                    (\ v6 ->
                       coe
                         MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                         (coe
                            MAlonzo.Code.Data.Rational.Unnormalised.Base.C_'42''8804''42'_44
                            v6)))
                 (coe
                    MAlonzo.Code.Data.Integer.Properties.d_'8804''45'total_2776
                    (coe
                       MAlonzo.Code.Data.Integer.Base.d__'9667'__230
                       (coe
                          MAlonzo.Code.Data.Sign.Base.d__'42'__14
                          (coe
                             MAlonzo.Code.Data.Integer.Base.d_sign_24
                             (coe
                                MAlonzo.Code.Data.Rational.Unnormalised.Base.d_numerator_14
                                (coe v2)))
                          (coe
                             MAlonzo.Code.Data.Integer.Base.d_sign_24
                             (coe
                                MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                (coe v0))))
                       (coe
                          mulInt
                          (coe
                             MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18
                             (coe
                                MAlonzo.Code.Data.Rational.Unnormalised.Base.d_numerator_14
                                (coe v2)))
                          (coe
                             MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18
                             (coe
                                MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                (coe v0)))))
                    (coe
                       MAlonzo.Code.Data.Integer.Base.d__'42'__308
                       (coe
                          MAlonzo.Code.Data.Rational.Unnormalised.Base.d_numerator_14
                          (coe v0))
                       (coe
                          MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                          (coe v2))))) in
    coe
      (case coe v6 of
         MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v7
           -> coe
                d_'60''45'resp'737''45''8771'_770
                (coe
                   MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'8852'__244
                   (coe v1) (coe v3))
                (coe v0)
                (coe
                   MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'8852'__244
                   (coe v0) (coe v2))
                (coe du_'8771''45'sym_170 (coe v7))
                (coe
                   d_'60''45''8804''45'trans_644 (coe v0) (coe v1)
                   (coe
                      MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'8852'__244
                      (coe v1) (coe v3))
                   (coe v4)
                   (let v8 = d_'8804''45'totalPreorder_524 in
                    coe
                      (let v9 = d_'8852''45'operator_2722 in
                       coe
                         (coe
                            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8851'y'8804'x_2838
                            (coe
                               MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_760
                               (coe v8))
                            (coe
                               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_182
                               (coe v9))
                            (coe v1) (coe v3)))))
         MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v7
           -> coe
                d_'60''45'resp'737''45''8771'_770
                (coe
                   MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'8852'__244
                   (coe v1) (coe v3))
                (coe v2)
                (coe
                   MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'8852'__244
                   (coe v0) (coe v2))
                (coe du_'8771''45'sym_170 (coe v7))
                (coe
                   d_'60''45''8804''45'trans_644 (coe v2) (coe v3)
                   (coe
                      MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'8852'__244
                      (coe v1) (coe v3))
                   (coe v5)
                   (let v8 = d_'8804''45'totalPreorder_524 in
                    coe
                      (let v9 = d_'8852''45'operator_2722 in
                       coe
                         (coe
                            MAlonzo.Code.Algebra.Construct.NaturalChoice.MinOp.du_x'8851'y'8804'y_2864
                            (coe
                               MAlonzo.Code.Relation.Binary.Construct.Flip.EqAndOrd.du_totalPreorder_760
                               (coe v8))
                            (coe
                               MAlonzo.Code.Algebra.Construct.NaturalChoice.Base.du_MaxOp'8658'MinOp_182
                               (coe v9))
                            (coe v1) (coe v3)))))
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Data.Rational.Unnormalised.Properties.pos⊓pos⇒pos
d_pos'8851'pos'8658'pos_3190 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Integer.Base.T_Positive_134 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Integer.Base.T_Positive_134 ->
  MAlonzo.Code.Data.Integer.Base.T_Positive_134
d_pos'8851'pos'8658'pos_3190 v0 ~v1 v2 ~v3
  = du_pos'8851'pos'8658'pos_3190 v0 v2
du_pos'8851'pos'8658'pos_3190 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Integer.Base.T_Positive_134
du_pos'8851'pos'8658'pos_3190 v0 v1
  = coe
      MAlonzo.Code.Data.Rational.Unnormalised.Base.d_positive_162
      (coe
         MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'8851'__254
         (coe v0) (coe v1))
      (coe
         d_'8851''45'mono'45''60'_3090
         (coe MAlonzo.Code.Data.Rational.Unnormalised.Base.d_0ℚ'7512'_108)
         (coe v0)
         (coe MAlonzo.Code.Data.Rational.Unnormalised.Base.d_0ℚ'7512'_108)
         (coe v1) (coe du_positive'8315''185'_926 (coe v0))
         (coe du_positive'8315''185'_926 (coe v1)))
-- Data.Rational.Unnormalised.Properties.pos⊔pos⇒pos
d_pos'8852'pos'8658'pos_3204 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Integer.Base.T_Positive_134 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Integer.Base.T_Positive_134 ->
  MAlonzo.Code.Data.Integer.Base.T_Positive_134
d_pos'8852'pos'8658'pos_3204 v0 ~v1 v2 ~v3
  = du_pos'8852'pos'8658'pos_3204 v0 v2
du_pos'8852'pos'8658'pos_3204 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Integer.Base.T_Positive_134
du_pos'8852'pos'8658'pos_3204 v0 v1
  = coe
      MAlonzo.Code.Data.Rational.Unnormalised.Base.d_positive_162
      (coe
         MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'8852'__244
         (coe v0) (coe v1))
      (coe
         d_'8852''45'mono'45''60'_3136
         (coe MAlonzo.Code.Data.Rational.Unnormalised.Base.d_0ℚ'7512'_108)
         (coe v0)
         (coe MAlonzo.Code.Data.Rational.Unnormalised.Base.d_0ℚ'7512'_108)
         (coe v1) (coe du_positive'8315''185'_926 (coe v0))
         (coe du_positive'8315''185'_926 (coe v1)))
-- Data.Rational.Unnormalised.Properties.∣-∣-cong
d_'8739''45''8739''45'cong_3210 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8771'__24 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8771'__24
d_'8739''45''8739''45'cong_3210 v0 v1 v2
  = case coe v0 of
      MAlonzo.Code.Data.Rational.Unnormalised.Base.C_mkℚ'7512'_22 v3 v4
        -> coe
             seq (coe v3)
             (coe
                seq (coe v1)
                (coe
                   seq (coe v2)
                   (coe
                      MAlonzo.Code.Data.Rational.Unnormalised.Base.C_'42''8801''42'_30)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Rational.Unnormalised.Properties.∣p∣≃0⇒p≃0
d_'8739'p'8739''8771'0'8658'p'8771'0_3238 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8771'__24 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8771'__24
d_'8739'p'8739''8771'0'8658'p'8771'0_3238 v0 v1
  = coe seq (coe v0) (coe v1)
-- Data.Rational.Unnormalised.Properties.0≤∣p∣
d_0'8804''8739'p'8739'_3252 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8804'__38
d_0'8804''8739'p'8739'_3252 v0
  = case coe v0 of
      MAlonzo.Code.Data.Rational.Unnormalised.Base.C_mkℚ'7512'_22 v1 v2
        -> coe
             seq (coe v1)
             (coe
                MAlonzo.Code.Data.Rational.Unnormalised.Base.C_'42''8804''42'_44
                (coe
                   MAlonzo.Code.Data.Integer.Base.C_'43''8804''43'_48
                   (coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Rational.Unnormalised.Properties.∣-p∣≡∣p∣
d_'8739''45'p'8739''8801''8739'p'8739'_3256 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8739''45'p'8739''8801''8739'p'8739'_3256 = erased
-- Data.Rational.Unnormalised.Properties.∣-p∣≃∣p∣
d_'8739''45'p'8739''8771''8739'p'8739'_3270 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8771'__24
d_'8739''45'p'8739''8771''8739'p'8739'_3270 ~v0
  = du_'8739''45'p'8739''8771''8739'p'8739'_3270
du_'8739''45'p'8739''8771''8739'p'8739'_3270 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8771'__24
du_'8739''45'p'8739''8771''8739'p'8739'_3270
  = coe du_'8771''45'reflexive_168
-- Data.Rational.Unnormalised.Properties.0≤p⇒∣p∣≡p
d_0'8804'p'8658''8739'p'8739''8801'p_3272 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8804'__38 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_0'8804'p'8658''8739'p'8739''8801'p_3272 = erased
-- Data.Rational.Unnormalised.Properties.0≤p⇒∣p∣≃p
d_0'8804'p'8658''8739'p'8739''8771'p_3286 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8804'__38 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8771'__24
d_0'8804'p'8658''8739'p'8739''8771'p_3286 ~v0 ~v1
  = du_0'8804'p'8658''8739'p'8739''8771'p_3286
du_0'8804'p'8658''8739'p'8739''8771'p_3286 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8771'__24
du_0'8804'p'8658''8739'p'8739''8771'p_3286
  = coe du_'8771''45'reflexive_168
-- Data.Rational.Unnormalised.Properties.∣p∣≡p⇒0≤p
d_'8739'p'8739''8801'p'8658'0'8804'p_3290 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8804'__38
d_'8739'p'8739''8801'p'8658'0'8804'p_3290 v0 ~v1
  = du_'8739'p'8739''8801'p'8658'0'8804'p_3290 v0
du_'8739'p'8739''8801'p'8658'0'8804'p_3290 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8804'__38
du_'8739'p'8739''8801'p'8658'0'8804'p_3290 v0
  = case coe v0 of
      MAlonzo.Code.Data.Rational.Unnormalised.Base.C_mkℚ'7512'_22 v1 v2
        -> coe
             MAlonzo.Code.Data.Rational.Unnormalised.Base.C_'42''8804''42'_44
             (coe
                MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
                (coe
                   MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_start_96
                   (coe
                      MAlonzo.Code.Data.Integer.Properties.d_'8804''45'isPreorder_2822)
                   (\ v3 v4 v5 ->
                      coe
                        MAlonzo.Code.Data.Integer.Properties.du_'60''8658''8804'_2868 v5))
                (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                   (coe
                      MAlonzo.Code.Data.Rational.Unnormalised.Base.d_numerator_14
                      (coe MAlonzo.Code.Data.Rational.Unnormalised.Base.d_0ℚ'7512'_108))
                   (coe
                      MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                      (coe v0)))
                (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                   (coe v1)
                   (coe
                      MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                      (coe MAlonzo.Code.Data.Rational.Unnormalised.Base.d_0ℚ'7512'_108)))
                (coe
                   MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_436
                   (\ v3 v4 v5 v6 v7 -> v7)
                   (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                      (coe MAlonzo.Code.Data.Integer.Base.d_0ℤ_12)
                      (coe addInt (coe (1 :: Integer)) (coe v2)))
                   MAlonzo.Code.Data.Integer.Base.d_0ℤ_12
                   (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                      (coe v1)
                      (coe
                         MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                         (coe MAlonzo.Code.Data.Rational.Unnormalised.Base.d_0ℚ'7512'_108)))
                   (coe
                      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8804'_308
                      (coe
                         MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8804''45'go_138
                         (coe
                            MAlonzo.Code.Data.Integer.Properties.d_'8804''45'isPreorder_2822)
                         (\ v3 v4 v5 v6 v7 ->
                            coe
                              MAlonzo.Code.Data.Integer.Properties.du_'8804''45''60''45'trans_2980
                              v6 v7))
                      MAlonzo.Code.Data.Integer.Base.d_0ℤ_12 v1
                      (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                         (coe v1)
                         (coe
                            MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                            (coe MAlonzo.Code.Data.Rational.Unnormalised.Base.d_0ℚ'7512'_108)))
                      (coe
                         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10216'_448
                         (\ v3 v4 v5 v6 v7 -> v7) v1
                         (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                            (coe v1) (coe MAlonzo.Code.Data.Integer.Base.d_1ℤ_16))
                         (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                            (coe v1)
                            (coe
                               MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                               (coe MAlonzo.Code.Data.Rational.Unnormalised.Base.d_0ℚ'7512'_108)))
                         (coe
                            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                            (coe
                               MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_stop_166
                               (coe
                                  MAlonzo.Code.Data.Integer.Properties.d_'8804''45'isPreorder_2822))
                            (coe
                               MAlonzo.Code.Data.Integer.Base.d__'42'__308 (coe v1)
                               (coe MAlonzo.Code.Data.Integer.Base.d_1ℤ_16)))
                         erased)
                      (coe
                         MAlonzo.Code.Data.Integer.Base.C_'43''8804''43'_48
                         (coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26)))
                   erased))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Rational.Unnormalised.Properties.∣p∣≡p∨∣p∣≡-p
d_'8739'p'8739''8801'p'8744''8739'p'8739''8801''45'p_3304 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_'8739'p'8739''8801'p'8744''8739'p'8739''8801''45'p_3304 v0
  = case coe v0 of
      MAlonzo.Code.Data.Rational.Unnormalised.Base.C_mkℚ'7512'_22 v1 v2
        -> case coe v1 of
             _ | coe geqInt (coe v1) (coe (0 :: Integer)) ->
                 coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 erased
             _ -> coe MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 erased
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Rational.Unnormalised.Properties.∣p∣≃p⇒0≤p
d_'8739'p'8739''8771'p'8658'0'8804'p_3314 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8771'__24 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8804'__38
d_'8739'p'8739''8771'p'8658'0'8804'p_3314 v0 v1
  = let v2
          = d_'8739'p'8739''8801'p'8744''8739'p'8739''8801''45'p_3304
              (coe v0) in
    coe
      (case coe v2 of
         MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v3
           -> coe du_'8739'p'8739''8801'p'8658'0'8804'p_3290 (coe v0)
         MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v3
           -> coe
                d_'8804''45'reflexive_432
                (coe
                   MAlonzo.Code.Data.Rational.Unnormalised.Base.C_mkℚ'7512'_22
                   (coe (0 :: Integer)) (coe (0 :: Integer)))
                (coe v0)
                (coe
                   du_'8771''45'sym_170
                   (coe
                      d_p'8771''45'p'8658'p'8771'0_1276 (coe v0)
                      (coe du_'8771''45'sym_170 (coe v1))))
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Data.Rational.Unnormalised.Properties.∣p+q∣≤∣p∣+∣q∣
d_'8739'p'43'q'8739''8804''8739'p'8739''43''8739'q'8739'_3344 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8804'__38
d_'8739'p'43'q'8739''8804''8739'p'8739''43''8739'q'8739'_3344 v0 v1
  = case coe v0 of
      MAlonzo.Code.Data.Rational.Unnormalised.Base.C_mkℚ'7512'_22 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Data.Rational.Unnormalised.Base.C_mkℚ'7512'_22 v4 v5
               -> coe
                    MAlonzo.Code.Data.Rational.Unnormalised.Base.C_'42''8804''42'_44
                    (coe
                       MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
                       (coe
                          MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_start_96
                          (coe
                             MAlonzo.Code.Data.Integer.Properties.d_'8804''45'isPreorder_2822)
                          (\ v6 v7 v8 ->
                             coe
                               MAlonzo.Code.Data.Integer.Properties.du_'60''8658''8804'_2868 v8))
                       (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                          (coe
                             MAlonzo.Code.Data.Rational.Unnormalised.Base.d_numerator_14
                             (coe
                                MAlonzo.Code.Data.Rational.Unnormalised.Base.d_'8739'_'8739'_260
                                (coe
                                   MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'43'__196
                                   (coe v0) (coe v1))))
                          (coe
                             MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                             (coe
                                MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'43'__196
                                (coe
                                   MAlonzo.Code.Data.Rational.Unnormalised.Base.d_'8739'_'8739'_260
                                   (coe v0))
                                (coe
                                   MAlonzo.Code.Data.Rational.Unnormalised.Base.d_'8739'_'8739'_260
                                   (coe v1)))))
                       (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                          (coe
                             MAlonzo.Code.Data.Rational.Unnormalised.Base.d_numerator_14
                             (coe
                                MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'43'__196
                                (coe
                                   MAlonzo.Code.Data.Rational.Unnormalised.Base.d_'8739'_'8739'_260
                                   (coe v0))
                                (coe
                                   MAlonzo.Code.Data.Rational.Unnormalised.Base.d_'8739'_'8739'_260
                                   (coe v1))))
                          (coe
                             MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                             (coe
                                MAlonzo.Code.Data.Rational.Unnormalised.Base.d_'8739'_'8739'_260
                                (coe
                                   MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'43'__196
                                   (coe v0) (coe v1)))))
                       (coe
                          MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_436
                          (\ v6 v7 v8 v9 v10 -> v10)
                          (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                             (coe
                                MAlonzo.Code.Data.Rational.Unnormalised.Base.d_numerator_14
                                (coe
                                   MAlonzo.Code.Data.Rational.Unnormalised.Base.du__'47'__102
                                   (coe
                                      MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18
                                      (coe
                                         MAlonzo.Code.Data.Integer.Base.d__'43'__276
                                         (coe du_'8613'p'8615'q_3354 (coe v2) (coe v4) (coe v5))
                                         (coe du_'8613'q'8615'p_3356 (coe v2) (coe v3) (coe v4))))
                                   (coe d_'8615'p'8615'q_3366 (coe v2) (coe v3) (coe v4) (coe v5))))
                             (coe d_'8615'p'8615'q_3366 (coe v2) (coe v3) (coe v4) (coe v5)))
                          (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                             (coe
                                MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18
                                (coe
                                   MAlonzo.Code.Data.Integer.Base.d__'43'__276
                                   (coe du_'8613'p'8615'q_3354 (coe v2) (coe v4) (coe v5))
                                   (coe du_'8613'q'8615'p_3356 (coe v2) (coe v3) (coe v4))))
                             (coe d_'8615'p'8615'q_3366 (coe v2) (coe v3) (coe v4) (coe v5)))
                          (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                             (coe
                                MAlonzo.Code.Data.Rational.Unnormalised.Base.d_numerator_14
                                (coe
                                   MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'43'__196
                                   (coe
                                      MAlonzo.Code.Data.Rational.Unnormalised.Base.d_'8739'_'8739'_260
                                      (coe v0))
                                   (coe
                                      MAlonzo.Code.Data.Rational.Unnormalised.Base.d_'8739'_'8739'_260
                                      (coe v1))))
                             (coe
                                MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                (coe
                                   MAlonzo.Code.Data.Rational.Unnormalised.Base.d_'8739'_'8739'_260
                                   (coe
                                      MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'43'__196
                                      (coe v0) (coe v1)))))
                          (coe
                             MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8804'_308
                             (coe
                                MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8804''45'go_138
                                (coe
                                   MAlonzo.Code.Data.Integer.Properties.d_'8804''45'isPreorder_2822)
                                (\ v6 v7 v8 v9 v10 ->
                                   coe
                                     MAlonzo.Code.Data.Integer.Properties.du_'8804''45''60''45'trans_2980
                                     v9 v10))
                             (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                (coe
                                   MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18
                                   (coe
                                      MAlonzo.Code.Data.Integer.Base.d__'43'__276
                                      (coe du_'8613'p'8615'q_3354 (coe v2) (coe v4) (coe v5))
                                      (coe du_'8613'q'8615'p_3356 (coe v2) (coe v3) (coe v4))))
                                (coe d_'8615'p'8615'q_3366 (coe v2) (coe v3) (coe v4) (coe v5)))
                             (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                (coe
                                   MAlonzo.Code.Data.Integer.Base.d__'43'__276
                                   (coe
                                      MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18
                                      (coe du_'8613'p'8615'q_3354 (coe v2) (coe v4) (coe v5)))
                                   (coe
                                      MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18
                                      (coe du_'8613'q'8615'p_3356 (coe v2) (coe v3) (coe v4))))
                                (coe d_'8615'p'8615'q_3366 (coe v2) (coe v3) (coe v4) (coe v5)))
                             (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                (coe
                                   MAlonzo.Code.Data.Rational.Unnormalised.Base.d_numerator_14
                                   (coe
                                      MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'43'__196
                                      (coe
                                         MAlonzo.Code.Data.Rational.Unnormalised.Base.d_'8739'_'8739'_260
                                         (coe v0))
                                      (coe
                                         MAlonzo.Code.Data.Rational.Unnormalised.Base.d_'8739'_'8739'_260
                                         (coe v1))))
                                (coe
                                   MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                   (coe
                                      MAlonzo.Code.Data.Rational.Unnormalised.Base.d_'8739'_'8739'_260
                                      (coe
                                         MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'43'__196
                                         (coe v0) (coe v1)))))
                             (coe
                                MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10216'_448
                                (\ v6 v7 v8 v9 v10 -> v10)
                                (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                   (coe
                                      MAlonzo.Code.Data.Integer.Base.d__'43'__276
                                      (coe
                                         MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18
                                         (coe du_'8613'p'8615'q_3354 (coe v2) (coe v4) (coe v5)))
                                      (coe
                                         MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18
                                         (coe du_'8613'q'8615'p_3356 (coe v2) (coe v3) (coe v4))))
                                   (coe d_'8615'p'8615'q_3366 (coe v2) (coe v3) (coe v4) (coe v5)))
                                (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                   (coe
                                      MAlonzo.Code.Data.Integer.Base.d__'43'__276
                                      (coe
                                         du_'8739''8613'p'8739''8615'q_3362 (coe v2) (coe v4)
                                         (coe v5))
                                      (coe
                                         du_'8739''8613'q'8739''8615'p_3364 (coe v2) (coe v3)
                                         (coe v4)))
                                   (coe d_'8615'p'8615'q_3366 (coe v2) (coe v3) (coe v4) (coe v5)))
                                (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                   (coe
                                      MAlonzo.Code.Data.Rational.Unnormalised.Base.d_numerator_14
                                      (coe
                                         MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'43'__196
                                         (coe
                                            MAlonzo.Code.Data.Rational.Unnormalised.Base.d_'8739'_'8739'_260
                                            (coe v0))
                                         (coe
                                            MAlonzo.Code.Data.Rational.Unnormalised.Base.d_'8739'_'8739'_260
                                            (coe v1))))
                                   (coe
                                      MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                      (coe
                                         MAlonzo.Code.Data.Rational.Unnormalised.Base.d_'8739'_'8739'_260
                                         (coe
                                            MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'43'__196
                                            (coe v0) (coe v1)))))
                                (coe
                                   MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_436
                                   (\ v6 v7 v8 v9 v10 -> v10)
                                   (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                      (coe
                                         MAlonzo.Code.Data.Integer.Base.d__'43'__276
                                         (coe
                                            d_'8613''8739'p'8739''8615'q_3358 (coe v2) (coe v3)
                                            (coe v4) (coe v5))
                                         (coe
                                            d_'8613''8739'q'8739''8615'p_3360 (coe v2) (coe v3)
                                            (coe v4) (coe v5)))
                                      (coe
                                         d_'8615'p'8615'q_3366 (coe v2) (coe v3) (coe v4) (coe v5)))
                                   (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                      (coe
                                         MAlonzo.Code.Data.Rational.Unnormalised.Base.d_numerator_14
                                         (coe
                                            MAlonzo.Code.Data.Rational.Unnormalised.Base.du__'47'__102
                                            (coe
                                               MAlonzo.Code.Data.Integer.Base.d__'43'__276
                                               (coe
                                                  d_'8613''8739'p'8739''8615'q_3358 (coe v2)
                                                  (coe v3) (coe v4) (coe v5))
                                               (coe
                                                  d_'8613''8739'q'8739''8615'p_3360 (coe v2)
                                                  (coe v3) (coe v4) (coe v5)))
                                            (coe
                                               d_'8615'p'8615'q_3366 (coe v2) (coe v3) (coe v4)
                                               (coe v5))))
                                      (coe
                                         d_'8615'p'8615'q_3366 (coe v2) (coe v3) (coe v4) (coe v5)))
                                   (MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                      (coe
                                         MAlonzo.Code.Data.Rational.Unnormalised.Base.d_numerator_14
                                         (coe
                                            MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'43'__196
                                            (coe
                                               MAlonzo.Code.Data.Rational.Unnormalised.Base.d_'8739'_'8739'_260
                                               (coe v0))
                                            (coe
                                               MAlonzo.Code.Data.Rational.Unnormalised.Base.d_'8739'_'8739'_260
                                               (coe v1))))
                                      (coe
                                         MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                         (coe
                                            MAlonzo.Code.Data.Rational.Unnormalised.Base.d_'8739'_'8739'_260
                                            (coe
                                               MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'43'__196
                                               (coe v0) (coe v1)))))
                                   (coe
                                      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
                                      (coe
                                         MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_stop_166
                                         (coe
                                            MAlonzo.Code.Data.Integer.Properties.d_'8804''45'isPreorder_2822))
                                      (coe
                                         MAlonzo.Code.Data.Integer.Base.d__'42'__308
                                         (coe
                                            MAlonzo.Code.Data.Rational.Unnormalised.Base.d_numerator_14
                                            (coe
                                               MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'43'__196
                                               (coe
                                                  MAlonzo.Code.Data.Rational.Unnormalised.Base.d_'8739'_'8739'_260
                                                  (coe v0))
                                               (coe
                                                  MAlonzo.Code.Data.Rational.Unnormalised.Base.d_'8739'_'8739'_260
                                                  (coe v1))))
                                         (coe
                                            MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
                                            (coe
                                               MAlonzo.Code.Data.Rational.Unnormalised.Base.d_'8739'_'8739'_260
                                               (coe
                                                  MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'43'__196
                                                  (coe v0) (coe v1))))))
                                   erased)
                                erased)
                             (coe
                                MAlonzo.Code.Data.Integer.Properties.du_'42''45'mono'691''45''8804''45'nonNeg_6034
                                (coe d_'8615'p'8615'q_3366 (coe v2) (coe v3) (coe v4) (coe v5))
                                (coe
                                   MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18
                                   (coe
                                      MAlonzo.Code.Data.Integer.Base.d__'43'__276
                                      (coe du_'8613'p'8615'q_3354 (coe v2) (coe v4) (coe v5))
                                      (coe du_'8613'q'8615'p_3356 (coe v2) (coe v3) (coe v4))))
                                (coe
                                   addInt
                                   (coe
                                      MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18
                                      (coe du_'8613'q'8615'p_3356 (coe v2) (coe v3) (coe v4)))
                                   (coe
                                      MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18
                                      (coe du_'8613'p'8615'q_3354 (coe v2) (coe v4) (coe v5))))
                                (coe
                                   MAlonzo.Code.Data.Integer.Base.C_'43''8804''43'_48
                                   (MAlonzo.Code.Data.Integer.Properties.d_'8739'i'43'j'8739''8804''8739'i'8739''43''8739'j'8739'_3884
                                      (coe du_'8613'p'8615'q_3354 (coe v2) (coe v4) (coe v5))
                                      (coe du_'8613'q'8615'p_3356 (coe v2) (coe v3) (coe v4))))))
                          erased))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Rational.Unnormalised.Properties._.↥p↧q
d_'8613'p'8615'q_3354 ::
  Integer -> Integer -> Integer -> Integer -> Integer
d_'8613'p'8615'q_3354 v0 ~v1 v2 v3
  = du_'8613'p'8615'q_3354 v0 v2 v3
du_'8613'p'8615'q_3354 :: Integer -> Integer -> Integer -> Integer
du_'8613'p'8615'q_3354 v0 v1 v2
  = coe
      MAlonzo.Code.Data.Integer.Base.d__'42'__308 (coe v0)
      (coe
         MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
         (coe
            MAlonzo.Code.Data.Rational.Unnormalised.Base.C_mkℚ'7512'_22
            (coe v1) (coe v2)))
-- Data.Rational.Unnormalised.Properties._.↥q↧p
d_'8613'q'8615'p_3356 ::
  Integer -> Integer -> Integer -> Integer -> Integer
d_'8613'q'8615'p_3356 v0 v1 v2 ~v3
  = du_'8613'q'8615'p_3356 v0 v1 v2
du_'8613'q'8615'p_3356 :: Integer -> Integer -> Integer -> Integer
du_'8613'q'8615'p_3356 v0 v1 v2
  = coe
      MAlonzo.Code.Data.Integer.Base.d__'42'__308 (coe v2)
      (coe
         MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
         (coe
            MAlonzo.Code.Data.Rational.Unnormalised.Base.C_mkℚ'7512'_22
            (coe v0) (coe v1)))
-- Data.Rational.Unnormalised.Properties._.↥∣p∣↧q
d_'8613''8739'p'8739''8615'q_3358 ::
  Integer -> Integer -> Integer -> Integer -> Integer
d_'8613''8739'p'8739''8615'q_3358 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Data.Integer.Base.d__'42'__308
      (coe
         MAlonzo.Code.Data.Rational.Unnormalised.Base.d_numerator_14
         (coe
            MAlonzo.Code.Data.Rational.Unnormalised.Base.d_'8739'_'8739'_260
            (coe
               MAlonzo.Code.Data.Rational.Unnormalised.Base.C_mkℚ'7512'_22
               (coe v0) (coe v1))))
      (coe
         MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
         (coe
            MAlonzo.Code.Data.Rational.Unnormalised.Base.C_mkℚ'7512'_22
            (coe v2) (coe v3)))
-- Data.Rational.Unnormalised.Properties._.↥∣q∣↧p
d_'8613''8739'q'8739''8615'p_3360 ::
  Integer -> Integer -> Integer -> Integer -> Integer
d_'8613''8739'q'8739''8615'p_3360 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Data.Integer.Base.d__'42'__308
      (coe
         MAlonzo.Code.Data.Rational.Unnormalised.Base.d_numerator_14
         (coe
            MAlonzo.Code.Data.Rational.Unnormalised.Base.d_'8739'_'8739'_260
            (coe
               MAlonzo.Code.Data.Rational.Unnormalised.Base.C_mkℚ'7512'_22
               (coe v2) (coe v3))))
      (coe
         MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
         (coe
            MAlonzo.Code.Data.Rational.Unnormalised.Base.C_mkℚ'7512'_22
            (coe v0) (coe v1)))
-- Data.Rational.Unnormalised.Properties._.∣↥p∣↧q
d_'8739''8613'p'8739''8615'q_3362 ::
  Integer -> Integer -> Integer -> Integer -> Integer
d_'8739''8613'p'8739''8615'q_3362 v0 ~v1 v2 v3
  = du_'8739''8613'p'8739''8615'q_3362 v0 v2 v3
du_'8739''8613'p'8739''8615'q_3362 ::
  Integer -> Integer -> Integer -> Integer
du_'8739''8613'p'8739''8615'q_3362 v0 v1 v2
  = coe
      MAlonzo.Code.Data.Integer.Base.d__'42'__308
      (coe MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18 (coe v0))
      (coe
         MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
         (coe
            MAlonzo.Code.Data.Rational.Unnormalised.Base.C_mkℚ'7512'_22
            (coe v1) (coe v2)))
-- Data.Rational.Unnormalised.Properties._.∣↥q∣↧p
d_'8739''8613'q'8739''8615'p_3364 ::
  Integer -> Integer -> Integer -> Integer -> Integer
d_'8739''8613'q'8739''8615'p_3364 v0 v1 v2 ~v3
  = du_'8739''8613'q'8739''8615'p_3364 v0 v1 v2
du_'8739''8613'q'8739''8615'p_3364 ::
  Integer -> Integer -> Integer -> Integer
du_'8739''8613'q'8739''8615'p_3364 v0 v1 v2
  = coe
      MAlonzo.Code.Data.Integer.Base.d__'42'__308
      (coe MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18 (coe v2))
      (coe
         MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominator_20
         (coe
            MAlonzo.Code.Data.Rational.Unnormalised.Base.C_mkℚ'7512'_22
            (coe v0) (coe v1)))
-- Data.Rational.Unnormalised.Properties._.↧p↧q
d_'8615'p'8615'q_3366 ::
  Integer -> Integer -> Integer -> Integer -> Integer
d_'8615'p'8615'q_3366 v0 v1 v2 v3
  = coe
      mulInt
      (coe
         MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominatorℕ_18
         (coe
            MAlonzo.Code.Data.Rational.Unnormalised.Base.C_mkℚ'7512'_22
            (coe v0) (coe v1)))
      (coe
         MAlonzo.Code.Data.Rational.Unnormalised.Base.d_denominatorℕ_18
         (coe
            MAlonzo.Code.Data.Rational.Unnormalised.Base.C_mkℚ'7512'_22
            (coe v2) (coe v3)))
-- Data.Rational.Unnormalised.Properties._.∣m∣n≡∣mn∣
d_'8739'm'8739'n'8801''8739'mn'8739'_3372 ::
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8739'm'8739'n'8801''8739'mn'8739'_3372 = erased
-- Data.Rational.Unnormalised.Properties._.∣↥p∣↧q≡∣↥p↧q∣
d_'8739''8613'p'8739''8615'q'8801''8739''8613'p'8615'q'8739'_3378 ::
  Integer ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8739''8613'p'8739''8615'q'8801''8739''8613'p'8615'q'8739'_3378
  = erased
-- Data.Rational.Unnormalised.Properties._.∣↥q∣↧p≡∣↥q↧p∣
d_'8739''8613'q'8739''8615'p'8801''8739''8613'q'8615'p'8739'_3380 ::
  Integer ->
  Integer ->
  Integer ->
  Integer -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8739''8613'q'8739''8615'p'8801''8739''8613'q'8615'p'8739'_3380
  = erased
-- Data.Rational.Unnormalised.Properties.∣p-q∣≤∣p∣+∣q∣
d_'8739'p'45'q'8739''8804''8739'p'8739''43''8739'q'8739'_3394 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8804'__38
d_'8739'p'45'q'8739''8804''8739'p'8739''43''8739'q'8739'_3394 v0 v1
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_begin__46
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_start_96
         (coe d_'8804''45'isPreorder_512)
         (\ v2 v3 v4 -> coe du_'60''8658''8804'_556 v4))
      (MAlonzo.Code.Data.Rational.Unnormalised.Base.d_'8739'_'8739'_260
         (coe
            MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'45'__208 (coe v0)
            (coe v1)))
      (MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'43'__196
         (coe
            MAlonzo.Code.Data.Rational.Unnormalised.Base.d_'8739'_'8739'_260
            (coe v0))
         (coe
            MAlonzo.Code.Data.Rational.Unnormalised.Base.d_'8739'_'8739'_260
            (coe v1)))
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8804'_308
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_'8804''45'go_138
            (coe d_'8804''45'isPreorder_512)
            (coe d_'8804''45''60''45'trans_610))
         (MAlonzo.Code.Data.Rational.Unnormalised.Base.d_'8739'_'8739'_260
            (coe
               MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'45'__208 (coe v0)
               (coe v1)))
         (MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'43'__196
            (coe
               MAlonzo.Code.Data.Rational.Unnormalised.Base.d_'8739'_'8739'_260
               (coe v0))
            (coe
               MAlonzo.Code.Data.Rational.Unnormalised.Base.d_'8739'_'8739'_260
               (coe
                  MAlonzo.Code.Data.Rational.Unnormalised.Base.d_'45'__190
                  (coe v1))))
         (MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'43'__196
            (coe
               MAlonzo.Code.Data.Rational.Unnormalised.Base.d_'8739'_'8739'_260
               (coe v0))
            (coe
               MAlonzo.Code.Data.Rational.Unnormalised.Base.d_'8739'_'8739'_260
               (coe v1)))
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8801''45''10217'_436
            (\ v2 v3 v4 v5 v6 -> v6)
            (MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'43'__196
               (coe
                  MAlonzo.Code.Data.Rational.Unnormalised.Base.d_'8739'_'8739'_260
                  (coe v0))
               (coe
                  MAlonzo.Code.Data.Rational.Unnormalised.Base.d_'8739'_'8739'_260
                  (coe
                     MAlonzo.Code.Data.Rational.Unnormalised.Base.d_'45'__190
                     (coe v1))))
            (MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'43'__196
               (coe
                  MAlonzo.Code.Data.Rational.Unnormalised.Base.d_'8739'_'8739'_260
                  (coe v0))
               (coe
                  MAlonzo.Code.Data.Rational.Unnormalised.Base.d_'8739'_'8739'_260
                  (coe v1)))
            (MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'43'__196
               (coe
                  MAlonzo.Code.Data.Rational.Unnormalised.Base.d_'8739'_'8739'_260
                  (coe v0))
               (coe
                  MAlonzo.Code.Data.Rational.Unnormalised.Base.d_'8739'_'8739'_260
                  (coe v1)))
            (coe
               MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
               (coe
                  MAlonzo.Code.Relation.Binary.Reasoning.Base.Triple.du_stop_166
                  (coe d_'8804''45'isPreorder_512))
               (coe
                  MAlonzo.Code.Data.Rational.Unnormalised.Base.d__'43'__196
                  (coe
                     MAlonzo.Code.Data.Rational.Unnormalised.Base.d_'8739'_'8739'_260
                     (coe v0))
                  (coe
                     MAlonzo.Code.Data.Rational.Unnormalised.Base.d_'8739'_'8739'_260
                     (coe v1))))
            erased)
         (d_'8739'p'43'q'8739''8804''8739'p'8739''43''8739'q'8739'_3344
            (coe v0)
            (coe
               MAlonzo.Code.Data.Rational.Unnormalised.Base.d_'45'__190
               (coe v1))))
-- Data.Rational.Unnormalised.Properties.∣p*q∣≡∣p∣*∣q∣
d_'8739'p'42'q'8739''8801''8739'p'8739''42''8739'q'8739'_3410 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8739'p'42'q'8739''8801''8739'p'8739''42''8739'q'8739'_3410
  = erased
-- Data.Rational.Unnormalised.Properties.∣p*q∣≃∣p∣*∣q∣
d_'8739'p'42'q'8739''8771''8739'p'8739''42''8739'q'8739'_3428 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8771'__24
d_'8739'p'42'q'8739''8771''8739'p'8739''42''8739'q'8739'_3428 ~v0
                                                              ~v1
  = du_'8739'p'42'q'8739''8771''8739'p'8739''42''8739'q'8739'_3428
du_'8739'p'42'q'8739''8771''8739'p'8739''42''8739'q'8739'_3428 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8771'__24
du_'8739'p'42'q'8739''8771''8739'p'8739''42''8739'q'8739'_3428
  = coe du_'8771''45'reflexive_168
-- Data.Rational.Unnormalised.Properties.∣∣p∣∣≡∣p∣
d_'8739''8739'p'8739''8739''8801''8739'p'8739'_3436 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8739''8739'p'8739''8739''8801''8739'p'8739'_3436 = erased
-- Data.Rational.Unnormalised.Properties.∣∣p∣∣≃∣p∣
d_'8739''8739'p'8739''8739''8771''8739'p'8739'_3442 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8771'__24
d_'8739''8739'p'8739''8739''8771''8739'p'8739'_3442 ~v0
  = du_'8739''8739'p'8739''8739''8771''8739'p'8739'_3442
du_'8739''8739'p'8739''8739''8771''8739'p'8739'_3442 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8771'__24
du_'8739''8739'p'8739''8739''8771''8739'p'8739'_3442
  = coe du_'8771''45'reflexive_168
-- Data.Rational.Unnormalised.Properties.∣-∣-nonNeg
d_'8739''45''8739''45'nonNeg_3448 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Integer.Base.T_NonNegative_144
d_'8739''45''8739''45'nonNeg_3448 v0
  = case coe v0 of
      MAlonzo.Code.Data.Rational.Unnormalised.Base.C_mkℚ'7512'_22 v1 v2
        -> coe
             seq (coe v1)
             (coe
                MAlonzo.Code.Data.Integer.Base.C_NonNegative'46'constructor_1457
                (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Rational.Unnormalised.Properties.neg-mono-<->
d_neg'45'mono'45''60''45''62'_3450 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'60'__46 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'60'__46
d_neg'45'mono'45''60''45''62'_3450 = coe d_neg'45'mono'45''60'_400
-- Data.Rational.Unnormalised.Properties.↥[p/q]≡p
d_'8613''91'p'47'q'93''8801'p_3452 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8613''91'p'47'q'93''8801'p_3452 = erased
-- Data.Rational.Unnormalised.Properties.↧[p/q]≡q
d_'8615''91'p'47'q'93''8801'q_3454 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T_NonZero_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8615''91'p'47'q'93''8801'q_3454 = erased
-- Data.Rational.Unnormalised.Properties.*-monoʳ-≤-pos
d_'42''45'mono'691''45''8804''45'pos_3460 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Integer.Base.T_Positive_134 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8804'__38 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8804'__38
d_'42''45'mono'691''45''8804''45'pos_3460 v0 ~v1 v2 v3
  = du_'42''45'mono'691''45''8804''45'pos_3460 v0 v2 v3
du_'42''45'mono'691''45''8804''45'pos_3460 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8804'__38 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8804'__38
du_'42''45'mono'691''45''8804''45'pos_3460 v0 v1 v2
  = case coe v0 of
      MAlonzo.Code.Data.Rational.Unnormalised.Base.C_mkℚ'7512'_22 v3 v4
        -> case coe v3 of
             0 -> coe (\ v5 -> MAlonzo.RTE.mazUnreachableError)
             _ | coe geqInt (coe v3) (coe (1 :: Integer)) ->
                 coe
                   du_'42''45'mono'691''45''8804''45'nonNeg_2144 (coe v0) (coe v1)
                   (coe v2)
             _ -> coe (\ v5 -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Rational.Unnormalised.Properties.*-monoˡ-≤-pos
d_'42''45'mono'737''45''8804''45'pos_3468 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Integer.Base.T_Positive_134 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8804'__38 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8804'__38
d_'42''45'mono'737''45''8804''45'pos_3468 v0 ~v1 v2 v3
  = du_'42''45'mono'737''45''8804''45'pos_3468 v0 v2 v3
du_'42''45'mono'737''45''8804''45'pos_3468 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8804'__38 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8804'__38
du_'42''45'mono'737''45''8804''45'pos_3468 v0 v1 v2
  = case coe v0 of
      MAlonzo.Code.Data.Rational.Unnormalised.Base.C_mkℚ'7512'_22 v3 v4
        -> case coe v3 of
             0 -> coe (\ v5 -> MAlonzo.RTE.mazUnreachableError)
             _ | coe geqInt (coe v3) (coe (1 :: Integer)) ->
                 coe
                   du_'42''45'mono'737''45''8804''45'nonNeg_2114 (coe v0) (coe v1)
                   (coe v2)
             _ -> coe (\ v5 -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Rational.Unnormalised.Properties.≤-steps
d_'8804''45'steps_3472 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Integer.Base.T_NonNegative_144 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8804'__38 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8804'__38
d_'8804''45'steps_3472 v0 v1 v2 v3 v4
  = coe du_p'8804'q'8658'p'8804'r'43'q_1356 v0 v1 v2 v4
-- Data.Rational.Unnormalised.Properties.*-monoˡ-≤-neg
d_'42''45'mono'737''45''8804''45'neg_3478 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Integer.Base.T_Negative_164 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8804'__38 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8804'__38
d_'42''45'mono'737''45''8804''45'neg_3478 v0 ~v1 v2 v3
  = du_'42''45'mono'737''45''8804''45'neg_3478 v0 v2 v3
du_'42''45'mono'737''45''8804''45'neg_3478 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8804'__38 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8804'__38
du_'42''45'mono'737''45''8804''45'neg_3478 v0 v1 v2
  = case coe v0 of
      MAlonzo.Code.Data.Rational.Unnormalised.Base.C_mkℚ'7512'_22 v3 v4
        -> case coe v3 of
             _ | coe geqInt (coe v3) (coe (0 :: Integer)) ->
                 coe (\ v5 -> MAlonzo.RTE.mazUnreachableError)
             _ -> coe
                    du_'42''45'mono'737''45''8804''45'nonPos_2196 (coe v0) (coe v1)
                    (coe v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Rational.Unnormalised.Properties.*-monoʳ-≤-neg
d_'42''45'mono'691''45''8804''45'neg_3486 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Integer.Base.T_Negative_164 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8804'__38 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8804'__38
d_'42''45'mono'691''45''8804''45'neg_3486 v0 ~v1 v2 v3
  = du_'42''45'mono'691''45''8804''45'neg_3486 v0 v2 v3
du_'42''45'mono'691''45''8804''45'neg_3486 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8804'__38 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'8804'__38
du_'42''45'mono'691''45''8804''45'neg_3486 v0 v1 v2
  = case coe v0 of
      MAlonzo.Code.Data.Rational.Unnormalised.Base.C_mkℚ'7512'_22 v3 v4
        -> case coe v3 of
             _ | coe geqInt (coe v3) (coe (0 :: Integer)) ->
                 coe (\ v5 -> MAlonzo.RTE.mazUnreachableError)
             _ -> coe
                    du_'42''45'mono'691''45''8804''45'nonPos_2218 (coe v0) (coe v1)
                    (coe v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Rational.Unnormalised.Properties.*-cancelˡ-<-pos
d_'42''45'cancel'737''45''60''45'pos_3496 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Integer.Base.T_Positive_134 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'60'__46 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'60'__46
d_'42''45'cancel'737''45''60''45'pos_3496 v0 ~v1 v2 v3
  = du_'42''45'cancel'737''45''60''45'pos_3496 v0 v2 v3
du_'42''45'cancel'737''45''60''45'pos_3496 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'60'__46 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'60'__46
du_'42''45'cancel'737''45''60''45'pos_3496 v0 v1 v2
  = case coe v0 of
      MAlonzo.Code.Data.Rational.Unnormalised.Base.C_mkℚ'7512'_22 v3 v4
        -> case coe v3 of
             0 -> coe (\ v5 -> MAlonzo.RTE.mazUnreachableError)
             _ | coe geqInt (coe v3) (coe (1 :: Integer)) ->
                 coe
                   du_'42''45'cancel'737''45''60''45'nonNeg_2328 (coe v1) (coe v2)
                   (coe v0)
             _ -> coe (\ v5 -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Rational.Unnormalised.Properties.*-cancelʳ-<-pos
d_'42''45'cancel'691''45''60''45'pos_3508 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Integer.Base.T_Positive_134 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'60'__46 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'60'__46
d_'42''45'cancel'691''45''60''45'pos_3508 v0 ~v1 v2 v3
  = du_'42''45'cancel'691''45''60''45'pos_3508 v0 v2 v3
du_'42''45'cancel'691''45''60''45'pos_3508 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'60'__46 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'60'__46
du_'42''45'cancel'691''45''60''45'pos_3508 v0 v1 v2
  = case coe v0 of
      MAlonzo.Code.Data.Rational.Unnormalised.Base.C_mkℚ'7512'_22 v3 v4
        -> case coe v3 of
             0 -> coe (\ v5 -> MAlonzo.RTE.mazUnreachableError)
             _ | coe geqInt (coe v3) (coe (1 :: Integer)) ->
                 coe
                   du_'42''45'cancel'691''45''60''45'nonNeg_2310 (coe v1) (coe v2)
                   (coe v0)
             _ -> coe (\ v5 -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Rational.Unnormalised.Properties.*-cancelˡ-<-neg
d_'42''45'cancel'737''45''60''45'neg_3520 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Integer.Base.T_Negative_164 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'60'__46 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'60'__46
d_'42''45'cancel'737''45''60''45'neg_3520 v0 ~v1 v2 v3
  = du_'42''45'cancel'737''45''60''45'neg_3520 v0 v2 v3
du_'42''45'cancel'737''45''60''45'neg_3520 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'60'__46 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'60'__46
du_'42''45'cancel'737''45''60''45'neg_3520 v0 v1 v2
  = case coe v0 of
      MAlonzo.Code.Data.Rational.Unnormalised.Base.C_mkℚ'7512'_22 v3 v4
        -> case coe v3 of
             _ | coe geqInt (coe v3) (coe (0 :: Integer)) ->
                 coe (\ v5 -> MAlonzo.RTE.mazUnreachableError)
             _ -> coe
                    du_'42''45'cancel'737''45''60''45'nonPos_2392 (coe v1) (coe v2)
                    (coe v0)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Rational.Unnormalised.Properties.*-cancelʳ-<-neg
d_'42''45'cancel'691''45''60''45'neg_3530 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Integer.Base.T_Negative_164 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'60'__46 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'60'__46
d_'42''45'cancel'691''45''60''45'neg_3530 v0 ~v1 v2 v3
  = du_'42''45'cancel'691''45''60''45'neg_3530 v0 v2 v3
du_'42''45'cancel'691''45''60''45'neg_3530 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'60'__46 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'60'__46
du_'42''45'cancel'691''45''60''45'neg_3530 v0 v1 v2
  = case coe v0 of
      MAlonzo.Code.Data.Rational.Unnormalised.Base.C_mkℚ'7512'_22 v3 v4
        -> case coe v3 of
             _ | coe geqInt (coe v3) (coe (0 :: Integer)) ->
                 coe (\ v5 -> MAlonzo.RTE.mazUnreachableError)
             _ -> coe
                    du_'42''45'cancel'691''45''60''45'nonPos_2412 (coe v1) (coe v2)
                    (coe v0)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Rational.Unnormalised.Properties.positive⇒nonNegative
d_positive'8658'nonNegative_3536 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Integer.Base.T_Positive_134 ->
  MAlonzo.Code.Data.Integer.Base.T_NonNegative_144
d_positive'8658'nonNegative_3536 v0 ~v1
  = du_positive'8658'nonNegative_3536 v0
du_positive'8658'nonNegative_3536 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Integer.Base.T_NonNegative_144
du_positive'8658'nonNegative_3536 v0
  = coe du_pos'8658'nonNeg_950 (coe v0)
-- Data.Rational.Unnormalised.Properties.negative⇒nonPositive
d_negative'8658'nonPositive_3544 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Integer.Base.T_Negative_164 ->
  MAlonzo.Code.Data.Integer.Base.T_NonPositive_154
d_negative'8658'nonPositive_3544 v0 ~v1
  = du_negative'8658'nonPositive_3544 v0
du_negative'8658'nonPositive_3544 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Integer.Base.T_NonPositive_154
du_negative'8658'nonPositive_3544 v0
  = coe du_neg'8658'nonPos_956 (coe v0)
-- Data.Rational.Unnormalised.Properties.negative<positive
d_negative'60'positive_3554 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Integer.Base.T_Negative_164 ->
  MAlonzo.Code.Data.Integer.Base.T_Positive_134 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'60'__46
d_negative'60'positive_3554 v0 v1 ~v2 ~v3
  = du_negative'60'positive_3554 v0 v1
du_negative'60'positive_3554 ::
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T_ℚ'7512'_8 ->
  MAlonzo.Code.Data.Rational.Unnormalised.Base.T__'60'__46
du_negative'60'positive_3554 v0 v1
  = coe du_neg'60'pos_964 (coe v0) (coe v1)
