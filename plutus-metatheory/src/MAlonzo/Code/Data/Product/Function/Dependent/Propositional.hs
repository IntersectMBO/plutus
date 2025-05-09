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

module MAlonzo.Code.Data.Product.Function.Dependent.Propositional where

import Data.Text qualified
import MAlonzo.Code.Agda.Builtin.Equality qualified
import MAlonzo.Code.Agda.Builtin.Sigma qualified
import MAlonzo.Code.Agda.Primitive qualified
import MAlonzo.Code.Data.Product.Base qualified
import MAlonzo.Code.Function.Base qualified
import MAlonzo.Code.Function.Bundles qualified
import MAlonzo.Code.Function.Properties.Inverse qualified
import MAlonzo.Code.Function.Properties.Inverse.HalfAdjointEquivalence qualified
import MAlonzo.Code.Function.Properties.RightInverse qualified
import MAlonzo.Code.Function.Related.Propositional qualified
import MAlonzo.Code.Relation.Binary.Reasoning.Syntax qualified
import MAlonzo.RTE (AgdaAny, add64, addInt, coe, eq64, eqInt, erased, geqInt, lt64, ltInt, mul64,
                    mulInt, quot64, quotInt, rem64, remInt, sub64, subInt, word64FromNat,
                    word64ToNat)
import MAlonzo.RTE qualified

-- Data.Product.Function.Dependent.Propositional._.Σ-⟶
d_Σ'45''10230'_36 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  MAlonzo.Code.Function.Bundles.T_Func_714 ->
  (AgdaAny -> MAlonzo.Code.Function.Bundles.T_Func_714) ->
  MAlonzo.Code.Function.Bundles.T_Func_714
d_Σ'45''10230'_36 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 v9
  = du_Σ'45''10230'_36 v8 v9
du_Σ'45''10230'_36 ::
  MAlonzo.Code.Function.Bundles.T_Func_714 ->
  (AgdaAny -> MAlonzo.Code.Function.Bundles.T_Func_714) ->
  MAlonzo.Code.Function.Bundles.T_Func_714
du_Σ'45''10230'_36 v0 v1
  = coe
      MAlonzo.Code.Function.Bundles.du_mk'10230'_2266
      (coe
         MAlonzo.Code.Data.Product.Base.du_map_128
         (coe MAlonzo.Code.Function.Bundles.d_to_720 (coe v0))
         (coe (\ v2 -> MAlonzo.Code.Function.Bundles.d_to_720 (coe v1 v2))))
-- Data.Product.Function.Dependent.Propositional._.Σ-⇔
d_Σ'45''8660'_50 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  MAlonzo.Code.Function.Bundles.T_Surjection_846 ->
  (AgdaAny -> MAlonzo.Code.Function.Bundles.T_Equivalence_1714) ->
  MAlonzo.Code.Function.Bundles.T_Equivalence_1714
d_Σ'45''8660'_50 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 v9
  = du_Σ'45''8660'_50 v8 v9
du_Σ'45''8660'_50 ::
  MAlonzo.Code.Function.Bundles.T_Surjection_846 ->
  (AgdaAny -> MAlonzo.Code.Function.Bundles.T_Equivalence_1714) ->
  MAlonzo.Code.Function.Bundles.T_Equivalence_1714
du_Σ'45''8660'_50 v0 v1
  = coe
      MAlonzo.Code.Function.Bundles.du_mk'8660'_2298
      (coe
         MAlonzo.Code.Data.Product.Base.du_map_128
         (coe MAlonzo.Code.Function.Bundles.d_to_854 (coe v0))
         (coe
            (\ v2 -> MAlonzo.Code.Function.Bundles.d_to_1724 (coe v1 v2))))
      (coe
         MAlonzo.Code.Data.Product.Base.du_map_128
         (coe MAlonzo.Code.Function.Bundles.du_to'8315'_920 (coe v0))
         (coe
            (\ v2 v3 ->
               coe
                 MAlonzo.Code.Function.Bundles.d_from_1726
                 (coe
                    v1
                    (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                       (coe MAlonzo.Code.Function.Bundles.d_surjective_858 v0 v2)))
                 v3)))
-- Data.Product.Function.Dependent.Propositional._.Σ-↣
d_Σ'45''8611'_66 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  MAlonzo.Code.Function.Bundles.T_Inverse_1960 ->
  (AgdaAny -> MAlonzo.Code.Function.Bundles.T_Injection_776) ->
  MAlonzo.Code.Function.Bundles.T_Injection_776
d_Σ'45''8611'_66 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 v9
  = du_Σ'45''8611'_66 v8 v9
du_Σ'45''8611'_66 ::
  MAlonzo.Code.Function.Bundles.T_Inverse_1960 ->
  (AgdaAny -> MAlonzo.Code.Function.Bundles.T_Injection_776) ->
  MAlonzo.Code.Function.Bundles.T_Injection_776
du_Σ'45''8611'_66 v0 v1
  = coe
      MAlonzo.Code.Function.Bundles.du_mk'8611'_2272
      (coe
         (\ v2 ->
            coe
              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
              (coe
                 MAlonzo.Code.Function.Properties.Inverse.HalfAdjointEquivalence.d_to_46
                 (coe du_I'8771'J_84 (coe v0))
                 (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v2)))
              (coe
                 MAlonzo.Code.Function.Bundles.d_to_784
                 (coe v1 (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v2)))
                 (MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v2)))))
      erased
-- Data.Product.Function.Dependent.Propositional._._.I≃J
d_I'8771'J_84 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  MAlonzo.Code.Function.Bundles.T_Inverse_1960 ->
  (AgdaAny -> MAlonzo.Code.Function.Bundles.T_Injection_776) ->
  MAlonzo.Code.Function.Properties.Inverse.HalfAdjointEquivalence.T__'8771'__24
d_I'8771'J_84 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 ~v9
  = du_I'8771'J_84 v8
du_I'8771'J_84 ::
  MAlonzo.Code.Function.Bundles.T_Inverse_1960 ->
  MAlonzo.Code.Function.Properties.Inverse.HalfAdjointEquivalence.T__'8771'__24
du_I'8771'J_84 v0
  = coe
      MAlonzo.Code.Function.Properties.Inverse.HalfAdjointEquivalence.du_'8596''8658''8771'_100
      (coe v0)
-- Data.Product.Function.Dependent.Propositional._._._.from
d_from_88 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  MAlonzo.Code.Function.Bundles.T_Inverse_1960 ->
  (AgdaAny -> MAlonzo.Code.Function.Bundles.T_Injection_776) ->
  AgdaAny -> AgdaAny
d_from_88 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 ~v9 = du_from_88 v8
du_from_88 ::
  MAlonzo.Code.Function.Bundles.T_Inverse_1960 -> AgdaAny -> AgdaAny
du_from_88 v0
  = coe
      MAlonzo.Code.Function.Properties.Inverse.HalfAdjointEquivalence.d_from_48
      (coe du_I'8771'J_84 (coe v0))
-- Data.Product.Function.Dependent.Propositional._._._.to
d_to_98 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  MAlonzo.Code.Function.Bundles.T_Inverse_1960 ->
  (AgdaAny -> MAlonzo.Code.Function.Bundles.T_Injection_776) ->
  AgdaAny -> AgdaAny
d_to_98 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 ~v9 = du_to_98 v8
du_to_98 ::
  MAlonzo.Code.Function.Bundles.T_Inverse_1960 -> AgdaAny -> AgdaAny
du_to_98 v0
  = coe
      MAlonzo.Code.Function.Properties.Inverse.HalfAdjointEquivalence.d_to_46
      (coe du_I'8771'J_84 (coe v0))
-- Data.Product.Function.Dependent.Propositional._._.subst-application′
d_subst'45'application'8242'_112 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  MAlonzo.Code.Function.Bundles.T_Inverse_1960 ->
  (AgdaAny -> MAlonzo.Code.Function.Bundles.T_Injection_776) ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_subst'45'application'8242'_112 = erased
-- Data.Product.Function.Dependent.Propositional._._._._.from
d_from_130 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  MAlonzo.Code.Function.Bundles.T_Inverse_1960 ->
  (AgdaAny -> MAlonzo.Code.Function.Bundles.T_Injection_776) ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> AgdaAny
d_from_130 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 ~v9 ~v10 ~v11 ~v12
           ~v13 ~v14
  = du_from_130 v8
du_from_130 ::
  MAlonzo.Code.Function.Bundles.T_Inverse_1960 -> AgdaAny -> AgdaAny
du_from_130 v0
  = coe
      MAlonzo.Code.Function.Properties.Inverse.HalfAdjointEquivalence.d_from_48
      (coe du_I'8771'J_84 (coe v0))
-- Data.Product.Function.Dependent.Propositional._._._._.to
d_to_140 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  MAlonzo.Code.Function.Bundles.T_Inverse_1960 ->
  (AgdaAny -> MAlonzo.Code.Function.Bundles.T_Injection_776) ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> AgdaAny
d_to_140 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 ~v9 ~v10 ~v11 ~v12 ~v13
         ~v14
  = du_to_140 v8
du_to_140 ::
  MAlonzo.Code.Function.Bundles.T_Inverse_1960 -> AgdaAny -> AgdaAny
du_to_140 v0
  = coe
      MAlonzo.Code.Function.Properties.Inverse.HalfAdjointEquivalence.d_to_46
      (coe du_I'8771'J_84 (coe v0))
-- Data.Product.Function.Dependent.Propositional._._._.g′
d_g'8242'_144 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  MAlonzo.Code.Function.Bundles.T_Inverse_1960 ->
  (AgdaAny -> MAlonzo.Code.Function.Bundles.T_Injection_776) ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_g'8242'_144 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 ~v9 ~v10 ~v11 ~v12
              v13 ~v14 v15 v16
  = du_g'8242'_144 v8 v13 v15 v16
du_g'8242'_144 ::
  MAlonzo.Code.Function.Bundles.T_Inverse_1960 ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny -> AgdaAny
du_g'8242'_144 v0 v1 v2 v3
  = coe
      v1
      (coe
         MAlonzo.Code.Function.Properties.Inverse.HalfAdjointEquivalence.d_from_48
         (coe du_I'8771'J_84 (coe v0)) v2)
      v3
-- Data.Product.Function.Dependent.Propositional._._._.g′-lemma
d_g'8242''45'lemma_152 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  MAlonzo.Code.Function.Bundles.T_Inverse_1960 ->
  (AgdaAny -> MAlonzo.Code.Function.Bundles.T_Injection_776) ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_g'8242''45'lemma_152 = erased
-- Data.Product.Function.Dependent.Propositional._._._._.lemma
d_lemma_168 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  MAlonzo.Code.Function.Bundles.T_Inverse_1960 ->
  (AgdaAny -> MAlonzo.Code.Function.Bundles.T_Injection_776) ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_lemma_168 = erased
-- Data.Product.Function.Dependent.Propositional._._.to′
d_to'8242'_172 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  MAlonzo.Code.Function.Bundles.T_Inverse_1960 ->
  (AgdaAny -> MAlonzo.Code.Function.Bundles.T_Injection_776) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_to'8242'_172 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 v9
  = du_to'8242'_172 v8 v9
du_to'8242'_172 ::
  MAlonzo.Code.Function.Bundles.T_Inverse_1960 ->
  (AgdaAny -> MAlonzo.Code.Function.Bundles.T_Injection_776) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_to'8242'_172 v0 v1
  = coe
      MAlonzo.Code.Data.Product.Base.du_map_128
      (coe
         MAlonzo.Code.Function.Properties.Inverse.HalfAdjointEquivalence.d_to_46
         (coe du_I'8771'J_84 (coe v0)))
      (coe (\ v2 -> MAlonzo.Code.Function.Bundles.d_to_784 (coe v1 v2)))
-- Data.Product.Function.Dependent.Propositional._._.to-injective
d_to'45'injective_174 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  MAlonzo.Code.Function.Bundles.T_Inverse_1960 ->
  (AgdaAny -> MAlonzo.Code.Function.Bundles.T_Injection_776) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_to'45'injective_174 = erased
-- Data.Product.Function.Dependent.Propositional._.Σ-↠
d_Σ'45''8608'_210 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  MAlonzo.Code.Function.Bundles.T_Surjection_846 ->
  (AgdaAny -> MAlonzo.Code.Function.Bundles.T_Surjection_846) ->
  MAlonzo.Code.Function.Bundles.T_Surjection_846
d_Σ'45''8608'_210 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 v9
  = du_Σ'45''8608'_210 v8 v9
du_Σ'45''8608'_210 ::
  MAlonzo.Code.Function.Bundles.T_Surjection_846 ->
  (AgdaAny -> MAlonzo.Code.Function.Bundles.T_Surjection_846) ->
  MAlonzo.Code.Function.Bundles.T_Surjection_846
du_Σ'45''8608'_210 v0 v1
  = coe
      MAlonzo.Code.Function.Bundles.du_mk'8608''8347'_2360
      (coe du_to'8242'_228 (coe v0) (coe v1))
      (coe du_strictlySurjective'8242'_236 (coe v0) (coe v1))
-- Data.Product.Function.Dependent.Propositional._._.to′
d_to'8242'_228 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  MAlonzo.Code.Function.Bundles.T_Surjection_846 ->
  (AgdaAny -> MAlonzo.Code.Function.Bundles.T_Surjection_846) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_to'8242'_228 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 v9
  = du_to'8242'_228 v8 v9
du_to'8242'_228 ::
  MAlonzo.Code.Function.Bundles.T_Surjection_846 ->
  (AgdaAny -> MAlonzo.Code.Function.Bundles.T_Surjection_846) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_to'8242'_228 v0 v1
  = coe
      MAlonzo.Code.Data.Product.Base.du_map_128
      (coe MAlonzo.Code.Function.Bundles.d_to_854 (coe v0))
      (coe (\ v2 -> MAlonzo.Code.Function.Bundles.d_to_854 (coe v1 v2)))
-- Data.Product.Function.Dependent.Propositional._._.backcast
d_backcast_232 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  MAlonzo.Code.Function.Bundles.T_Surjection_846 ->
  (AgdaAny -> MAlonzo.Code.Function.Bundles.T_Surjection_846) ->
  AgdaAny -> AgdaAny -> AgdaAny
d_backcast_232 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 v11
  = du_backcast_232 v11
du_backcast_232 :: AgdaAny -> AgdaAny
du_backcast_232 v0 = coe v0
-- Data.Product.Function.Dependent.Propositional._._.to⁻′
d_to'8315''8242'_234 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  MAlonzo.Code.Function.Bundles.T_Surjection_846 ->
  (AgdaAny -> MAlonzo.Code.Function.Bundles.T_Surjection_846) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_to'8315''8242'_234 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 v9
  = du_to'8315''8242'_234 v8 v9
du_to'8315''8242'_234 ::
  MAlonzo.Code.Function.Bundles.T_Surjection_846 ->
  (AgdaAny -> MAlonzo.Code.Function.Bundles.T_Surjection_846) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_to'8315''8242'_234 v0 v1
  = coe
      MAlonzo.Code.Data.Product.Base.du_map_128
      (coe MAlonzo.Code.Function.Bundles.du_to'8315'_920 (coe v0))
      (coe
         (\ v2 v3 ->
            coe
              MAlonzo.Code.Function.Bundles.du_to'8315'_920
              (coe
                 v1
                 (coe
                    MAlonzo.Code.Function.Bundles.du_to'8315'_920 (coe v0) (coe v2)))
              (coe v3)))
-- Data.Product.Function.Dependent.Propositional._._.strictlySurjective′
d_strictlySurjective'8242'_236 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  MAlonzo.Code.Function.Bundles.T_Surjection_846 ->
  (AgdaAny -> MAlonzo.Code.Function.Bundles.T_Surjection_846) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_strictlySurjective'8242'_236 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
                               v9 v10
  = du_strictlySurjective'8242'_236 v8 v9 v10
du_strictlySurjective'8242'_236 ::
  MAlonzo.Code.Function.Bundles.T_Surjection_846 ->
  (AgdaAny -> MAlonzo.Code.Function.Bundles.T_Surjection_846) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_strictlySurjective'8242'_236 v0 v1 v2
  = coe
      seq (coe v2)
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
         (coe du_to'8315''8242'_234 v0 v1 v2) erased)
-- Data.Product.Function.Dependent.Propositional._.Σ-↩
d_Σ'45''8617'_254 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  MAlonzo.Code.Function.Bundles.T_LeftInverse_1792 ->
  (AgdaAny -> MAlonzo.Code.Function.Bundles.T_LeftInverse_1792) ->
  MAlonzo.Code.Function.Bundles.T_LeftInverse_1792
d_Σ'45''8617'_254 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 v9
  = du_Σ'45''8617'_254 v8 v9
du_Σ'45''8617'_254 ::
  MAlonzo.Code.Function.Bundles.T_LeftInverse_1792 ->
  (AgdaAny -> MAlonzo.Code.Function.Bundles.T_LeftInverse_1792) ->
  MAlonzo.Code.Function.Bundles.T_LeftInverse_1792
du_Σ'45''8617'_254 v0 v1
  = coe
      MAlonzo.Code.Function.Bundles.du_mk'8617'_2308
      (coe du_to'8242'_272 (coe v0) (coe v1))
      (coe du_from'8242'_278 (coe v0) (coe v1)) erased
-- Data.Product.Function.Dependent.Propositional._._.to′
d_to'8242'_272 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  MAlonzo.Code.Function.Bundles.T_LeftInverse_1792 ->
  (AgdaAny -> MAlonzo.Code.Function.Bundles.T_LeftInverse_1792) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_to'8242'_272 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 v9
  = du_to'8242'_272 v8 v9
du_to'8242'_272 ::
  MAlonzo.Code.Function.Bundles.T_LeftInverse_1792 ->
  (AgdaAny -> MAlonzo.Code.Function.Bundles.T_LeftInverse_1792) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_to'8242'_272 v0 v1
  = coe
      MAlonzo.Code.Data.Product.Base.du_map_128
      (coe MAlonzo.Code.Function.Bundles.d_to_1804 (coe v0))
      (coe (\ v2 -> MAlonzo.Code.Function.Bundles.d_to_1804 (coe v1 v2)))
-- Data.Product.Function.Dependent.Propositional._._.backcast
d_backcast_276 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  MAlonzo.Code.Function.Bundles.T_LeftInverse_1792 ->
  (AgdaAny -> MAlonzo.Code.Function.Bundles.T_LeftInverse_1792) ->
  AgdaAny -> AgdaAny -> AgdaAny
d_backcast_276 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 v11
  = du_backcast_276 v11
du_backcast_276 :: AgdaAny -> AgdaAny
du_backcast_276 v0 = coe v0
-- Data.Product.Function.Dependent.Propositional._._.from′
d_from'8242'_278 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  MAlonzo.Code.Function.Bundles.T_LeftInverse_1792 ->
  (AgdaAny -> MAlonzo.Code.Function.Bundles.T_LeftInverse_1792) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_from'8242'_278 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 v9
  = du_from'8242'_278 v8 v9
du_from'8242'_278 ::
  MAlonzo.Code.Function.Bundles.T_LeftInverse_1792 ->
  (AgdaAny -> MAlonzo.Code.Function.Bundles.T_LeftInverse_1792) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_from'8242'_278 v0 v1
  = coe
      MAlonzo.Code.Data.Product.Base.du_map_128
      (coe MAlonzo.Code.Function.Bundles.d_from_1806 (coe v0))
      (coe
         (\ v2 v3 ->
            coe
              MAlonzo.Code.Function.Bundles.d_from_1806
              (coe v1 (coe MAlonzo.Code.Function.Bundles.d_from_1806 v0 v2)) v3))
-- Data.Product.Function.Dependent.Propositional._._.inv
d_inv_280 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  MAlonzo.Code.Function.Bundles.T_LeftInverse_1792 ->
  (AgdaAny -> MAlonzo.Code.Function.Bundles.T_LeftInverse_1792) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_inv_280 = erased
-- Data.Product.Function.Dependent.Propositional._.Σ-↔
d_Σ'45''8596'_298 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  MAlonzo.Code.Function.Bundles.T_Inverse_1960 ->
  (AgdaAny -> MAlonzo.Code.Function.Bundles.T_Inverse_1960) ->
  MAlonzo.Code.Function.Bundles.T_Inverse_1960
d_Σ'45''8596'_298 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 v9
  = du_Σ'45''8596'_298 v8 v9
du_Σ'45''8596'_298 ::
  MAlonzo.Code.Function.Bundles.T_Inverse_1960 ->
  (AgdaAny -> MAlonzo.Code.Function.Bundles.T_Inverse_1960) ->
  MAlonzo.Code.Function.Bundles.T_Inverse_1960
du_Σ'45''8596'_298 v0 v1
  = coe
      MAlonzo.Code.Function.Bundles.du_mk'8596''8347''8242'_2366
      (coe
         MAlonzo.Code.Function.Bundles.d_to_854
         (coe du_surjection'8242'_318 (coe v0) (coe v1)))
      (coe
         MAlonzo.Code.Function.Bundles.du_to'8315'_920
         (coe du_surjection'8242'_318 (coe v0) (coe v1)))
-- Data.Product.Function.Dependent.Propositional._._.I≃J
d_I'8771'J_316 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  MAlonzo.Code.Function.Bundles.T_Inverse_1960 ->
  (AgdaAny -> MAlonzo.Code.Function.Bundles.T_Inverse_1960) ->
  MAlonzo.Code.Function.Properties.Inverse.HalfAdjointEquivalence.T__'8771'__24
d_I'8771'J_316 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 ~v9
  = du_I'8771'J_316 v8
du_I'8771'J_316 ::
  MAlonzo.Code.Function.Bundles.T_Inverse_1960 ->
  MAlonzo.Code.Function.Properties.Inverse.HalfAdjointEquivalence.T__'8771'__24
du_I'8771'J_316 v0
  = coe
      MAlonzo.Code.Function.Properties.Inverse.HalfAdjointEquivalence.du_'8596''8658''8771'_100
      (coe v0)
-- Data.Product.Function.Dependent.Propositional._._.surjection′
d_surjection'8242'_318 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  MAlonzo.Code.Function.Bundles.T_Inverse_1960 ->
  (AgdaAny -> MAlonzo.Code.Function.Bundles.T_Inverse_1960) ->
  MAlonzo.Code.Function.Bundles.T_Surjection_846
d_surjection'8242'_318 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 v9
  = du_surjection'8242'_318 v8 v9
du_surjection'8242'_318 ::
  MAlonzo.Code.Function.Bundles.T_Inverse_1960 ->
  (AgdaAny -> MAlonzo.Code.Function.Bundles.T_Inverse_1960) ->
  MAlonzo.Code.Function.Bundles.T_Surjection_846
du_surjection'8242'_318 v0 v1
  = coe
      du_Σ'45''8608'_210
      (coe
         MAlonzo.Code.Function.Properties.Inverse.du_'8596''8658''8608'_644
         (coe
            MAlonzo.Code.Function.Properties.Inverse.HalfAdjointEquivalence.du_'8771''8658''8596'_78
            (coe du_I'8771'J_316 (coe v0))))
      (coe
         (\ v2 ->
            coe
              MAlonzo.Code.Function.Properties.Inverse.du_'8596''8658''8608'_644
              (coe v1 v2)))
-- Data.Product.Function.Dependent.Propositional._._.left-inverse-of
d_left'45'inverse'45'of_322 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  MAlonzo.Code.Function.Bundles.T_Inverse_1960 ->
  (AgdaAny -> MAlonzo.Code.Function.Bundles.T_Inverse_1960) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_left'45'inverse'45'of_322 = erased
-- Data.Product.Function.Dependent.Propositional._.swap-coercions
d_swap'45'coercions_346 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  MAlonzo.Code.Function.Related.Propositional.T_Kind_6 ->
  (AgdaAny -> ()) ->
  MAlonzo.Code.Function.Bundles.T_Inverse_1960 ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_swap'45'coercions_346 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 v8 v9 v10 v11
  = du_swap'45'coercions_346 v6 v7 v8 v9 v10 v11
du_swap'45'coercions_346 ::
  (AgdaAny -> ()) ->
  MAlonzo.Code.Function.Related.Propositional.T_Kind_6 ->
  (AgdaAny -> ()) ->
  MAlonzo.Code.Function.Bundles.T_Inverse_1960 ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du_swap'45'coercions_346 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8764'_300
      (\ v6 v7 v8 ->
         coe
           MAlonzo.Code.Function.Related.Propositional.du_K'45'trans_164
           (coe v1))
      (coe v0 (coe MAlonzo.Code.Function.Bundles.d_from_1974 v3 v5))
      (coe
         v2
         (coe
            MAlonzo.Code.Function.Bundles.d_to_1972 v3
            (coe MAlonzo.Code.Function.Bundles.d_from_1974 v3 v5)))
      (coe v2 v5)
      (coe
         MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du_step'45''8596''45''10217'_410
         (\ v6 v7 v8 ->
            coe
              MAlonzo.Code.Function.Base.du__'8728''8242'__216
              (coe
                 MAlonzo.Code.Function.Related.Propositional.du_K'45'trans_164
                 (coe v1))
              (coe
                 MAlonzo.Code.Function.Related.Propositional.du_'8596''8658'_82
                 (coe v1)))
         (coe
            v2
            (coe
               MAlonzo.Code.Function.Bundles.d_to_1972 v3
               (coe MAlonzo.Code.Function.Bundles.d_from_1974 v3 v5)))
         (coe v2 v5) (coe v2 v5)
         (coe
            MAlonzo.Code.Relation.Binary.Reasoning.Syntax.du__'8718'_492
            (\ v6 ->
               coe
                 MAlonzo.Code.Function.Related.Propositional.du_K'45'refl_160
                 (coe v1))
            (coe v2 v5))
         (coe
            MAlonzo.Code.Function.Related.Propositional.du_K'45'reflexive_162
            (coe MAlonzo.Code.Function.Related.Propositional.C_bijection_22)))
      (coe v4 (coe MAlonzo.Code.Function.Bundles.d_from_1974 v3 v5))
-- Data.Product.Function.Dependent.Propositional.cong
d_cong_368 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  MAlonzo.Code.Function.Related.Propositional.T_Kind_6 ->
  MAlonzo.Code.Function.Bundles.T_Inverse_1960 ->
  (AgdaAny -> AgdaAny) -> AgdaAny
d_cong_368 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 v9 v10
  = du_cong_368 v8 v9 v10
du_cong_368 ::
  MAlonzo.Code.Function.Related.Propositional.T_Kind_6 ->
  MAlonzo.Code.Function.Bundles.T_Inverse_1960 ->
  (AgdaAny -> AgdaAny) -> AgdaAny
du_cong_368 v0 v1 v2
  = case coe v0 of
      MAlonzo.Code.Function.Related.Propositional.C_implication_8
        -> coe
             du_Σ'45''10230'_36
             (coe
                MAlonzo.Code.Function.Properties.Inverse.du_'8596''8658''10230'_638
                v1)
             (coe v2)
      MAlonzo.Code.Function.Related.Propositional.C_reverseImplication_10
        -> coe
             du_Σ'45''10230'_36
             (coe
                MAlonzo.Code.Function.Properties.Inverse.du_'8596''8658''10229'_640
                v1)
             (coe
                du_swap'45'coercions_346 erased (coe v0) erased (coe v1) (coe v2))
      MAlonzo.Code.Function.Related.Propositional.C_equivalence_12
        -> coe
             du_Σ'45''8660'_50
             (coe
                MAlonzo.Code.Function.Properties.Inverse.du_'8596''8658''8608'_644
                v1)
             (coe v2)
      MAlonzo.Code.Function.Related.Propositional.C_injection_14
        -> coe du_Σ'45''8611'_66 (coe v1) (coe v2)
      MAlonzo.Code.Function.Related.Propositional.C_reverseInjection_16
        -> coe
             du_Σ'45''8611'_66
             (coe
                MAlonzo.Code.Function.Properties.Inverse.du_'8596''45'sym_38 v1)
             (coe
                du_swap'45'coercions_346 erased (coe v0) erased (coe v1) (coe v2))
      MAlonzo.Code.Function.Related.Propositional.C_leftInverse_18
        -> coe
             MAlonzo.Code.Function.Properties.RightInverse.du_'8617''8658''8618'_402
             (coe
                du_Σ'45''8617'_254
                (coe
                   MAlonzo.Code.Function.Properties.Inverse.du_'8596''8658''8617'_650
                   (coe
                      MAlonzo.Code.Function.Properties.Inverse.du_'8596''45'sym_38 v1))
                (coe
                   (\ v3 ->
                      coe
                        MAlonzo.Code.Function.Properties.RightInverse.du_'8618''8658''8617'_400
                        (coe
                           du_swap'45'coercions_346 erased (coe v0) erased (coe v1) (coe v2)
                           (coe v3)))))
      MAlonzo.Code.Function.Related.Propositional.C_surjection_20
        -> coe
             du_Σ'45''8608'_210
             (coe
                MAlonzo.Code.Function.Properties.Inverse.du_'8596''8658''8608'_644
                v1)
             (coe v2)
      MAlonzo.Code.Function.Related.Propositional.C_bijection_22
        -> coe du_Σ'45''8596'_298 (coe v1) (coe v2)
      _ -> MAlonzo.RTE.mazUnreachableError
