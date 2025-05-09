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

module MAlonzo.Code.Data.Sum.Function.Propositional where

import Data.Text qualified
import MAlonzo.Code.Agda.Primitive qualified
import MAlonzo.Code.Data.Sum.Function.Setoid qualified
import MAlonzo.Code.Data.Sum.Relation.Binary.Pointwise qualified
import MAlonzo.Code.Function.Bundles qualified
import MAlonzo.Code.Function.Construct.Composition qualified
import MAlonzo.Code.Function.Construct.Symmetry qualified
import MAlonzo.Code.Function.Properties.Inverse qualified
import MAlonzo.Code.Function.Related.Propositional qualified
import MAlonzo.Code.Relation.Binary.Bundles qualified
import MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties qualified
import MAlonzo.RTE (AgdaAny, add64, addInt, coe, eq64, eqInt, erased, geqInt, lt64, ltInt, mul64,
                    mulInt, quot64, quotInt, rem64, remInt, sub64, subInt, word64FromNat,
                    word64ToNat)
import MAlonzo.RTE qualified

-- Data.Sum.Function.Propositional.liftViaInverse
d_liftViaInverse_64 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (MAlonzo.Code.Agda.Primitive.T_Level_18 ->
   MAlonzo.Code.Agda.Primitive.T_Level_18 ->
   MAlonzo.Code.Agda.Primitive.T_Level_18 ->
   MAlonzo.Code.Agda.Primitive.T_Level_18 ->
   MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
   MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 -> ()) ->
  (MAlonzo.Code.Agda.Primitive.T_Level_18 ->
   MAlonzo.Code.Agda.Primitive.T_Level_18 ->
   MAlonzo.Code.Agda.Primitive.T_Level_18 ->
   MAlonzo.Code.Agda.Primitive.T_Level_18 ->
   MAlonzo.Code.Agda.Primitive.T_Level_18 ->
   MAlonzo.Code.Agda.Primitive.T_Level_18 ->
   MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
   MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
   MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
   AgdaAny -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Agda.Primitive.T_Level_18 ->
   MAlonzo.Code.Agda.Primitive.T_Level_18 ->
   MAlonzo.Code.Agda.Primitive.T_Level_18 ->
   MAlonzo.Code.Agda.Primitive.T_Level_18 ->
   MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
   MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
   MAlonzo.Code.Function.Bundles.T_Inverse_1960 -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny -> AgdaAny
d_liftViaInverse_64 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9 v10 v11
                    v12 v13
  = du_liftViaInverse_64 v9 v10 v11 v12 v13
du_liftViaInverse_64 ::
  (MAlonzo.Code.Agda.Primitive.T_Level_18 ->
   MAlonzo.Code.Agda.Primitive.T_Level_18 ->
   MAlonzo.Code.Agda.Primitive.T_Level_18 ->
   MAlonzo.Code.Agda.Primitive.T_Level_18 ->
   MAlonzo.Code.Agda.Primitive.T_Level_18 ->
   MAlonzo.Code.Agda.Primitive.T_Level_18 ->
   MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
   MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
   MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
   AgdaAny -> AgdaAny -> AgdaAny) ->
  (MAlonzo.Code.Agda.Primitive.T_Level_18 ->
   MAlonzo.Code.Agda.Primitive.T_Level_18 ->
   MAlonzo.Code.Agda.Primitive.T_Level_18 ->
   MAlonzo.Code.Agda.Primitive.T_Level_18 ->
   MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
   MAlonzo.Code.Relation.Binary.Bundles.T_Setoid_44 ->
   MAlonzo.Code.Function.Bundles.T_Inverse_1960 -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny -> AgdaAny
du_liftViaInverse_64 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Function.Properties.Inverse.du_transportVia_694
      (coe ()) (coe ())
      (coe
         MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties.du_setoid_402)
      (coe ()) (coe ())
      (coe
         MAlonzo.Code.Data.Sum.Relation.Binary.Pointwise.du__'8846''8347'__432
         (coe
            MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties.du_setoid_402)
         (coe
            MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties.du_setoid_402))
      (coe ()) (coe ())
      (coe
         MAlonzo.Code.Data.Sum.Relation.Binary.Pointwise.du__'8846''8347'__432
         (coe
            MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties.du_setoid_402)
         (coe
            MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties.du_setoid_402))
      (coe ()) (coe ())
      (coe
         MAlonzo.Code.Relation.Binary.PropositionalEquality.Properties.du_setoid_402)
      (coe v0) (coe v1)
      (coe
         MAlonzo.Code.Function.Construct.Symmetry.du_inverse_1052
         (coe
            MAlonzo.Code.Data.Sum.Relation.Binary.Pointwise.du_Pointwise'45''8801''8596''8801'_446))
      (coe v2 v3 v4)
      (coe
         MAlonzo.Code.Data.Sum.Relation.Binary.Pointwise.du_Pointwise'45''8801''8596''8801'_446)
-- Data.Sum.Function.Propositional._⊎-⟶_
d__'8846''45''10230'__76 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Function.Bundles.T_Func_714 ->
  MAlonzo.Code.Function.Bundles.T_Func_714 ->
  MAlonzo.Code.Function.Bundles.T_Func_714
d__'8846''45''10230'__76 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
  = du__'8846''45''10230'__76
du__'8846''45''10230'__76 ::
  MAlonzo.Code.Function.Bundles.T_Func_714 ->
  MAlonzo.Code.Function.Bundles.T_Func_714 ->
  MAlonzo.Code.Function.Bundles.T_Func_714
du__'8846''45''10230'__76
  = coe
      du_liftViaInverse_64
      (coe
         (\ v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 ->
            coe
              MAlonzo.Code.Function.Construct.Composition.du_function_1204 v9
              v10))
      (coe
         (\ v0 v1 v2 v3 v4 v5 v6 ->
            coe MAlonzo.Code.Function.Properties.Inverse.du_toFunction_44 v6))
      (coe
         MAlonzo.Code.Data.Sum.Function.Setoid.du__'8846''45'function__132)
-- Data.Sum.Function.Propositional._⊎-⇔_
d__'8846''45''8660'__78 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Function.Bundles.T_Equivalence_1714 ->
  MAlonzo.Code.Function.Bundles.T_Equivalence_1714 ->
  MAlonzo.Code.Function.Bundles.T_Equivalence_1714
d__'8846''45''8660'__78 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
  = du__'8846''45''8660'__78
du__'8846''45''8660'__78 ::
  MAlonzo.Code.Function.Bundles.T_Equivalence_1714 ->
  MAlonzo.Code.Function.Bundles.T_Equivalence_1714 ->
  MAlonzo.Code.Function.Bundles.T_Equivalence_1714
du__'8846''45''8660'__78
  = coe
      du_liftViaInverse_64
      (coe
         (\ v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 ->
            coe
              MAlonzo.Code.Function.Construct.Composition.du_equivalence_1764 v9
              v10))
      (coe
         (\ v0 v1 v2 v3 v4 v5 v6 ->
            coe
              MAlonzo.Code.Function.Properties.Inverse.du_Inverse'8658'Equivalence_552
              v6))
      (coe
         MAlonzo.Code.Data.Sum.Function.Setoid.du__'8846''45'equivalence__142)
-- Data.Sum.Function.Propositional._⊎-↣_
d__'8846''45''8611'__80 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Function.Bundles.T_Injection_776 ->
  MAlonzo.Code.Function.Bundles.T_Injection_776 ->
  MAlonzo.Code.Function.Bundles.T_Injection_776
d__'8846''45''8611'__80 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
  = du__'8846''45''8611'__80
du__'8846''45''8611'__80 ::
  MAlonzo.Code.Function.Bundles.T_Injection_776 ->
  MAlonzo.Code.Function.Bundles.T_Injection_776 ->
  MAlonzo.Code.Function.Bundles.T_Injection_776
du__'8846''45''8611'__80
  = coe
      du_liftViaInverse_64
      (coe
         (\ v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 ->
            coe
              MAlonzo.Code.Function.Construct.Composition.du_injection_1326 v9
              v10))
      (coe
         (\ v0 v1 v2 v3 v4 ->
            coe
              MAlonzo.Code.Function.Properties.Inverse.du_Inverse'8658'Injection_216
              (coe v4)))
      (coe
         MAlonzo.Code.Data.Sum.Function.Setoid.du__'8846''45'injection__152)
-- Data.Sum.Function.Propositional._⊎-↠_
d__'8846''45''8608'__82 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Function.Bundles.T_Surjection_846 ->
  MAlonzo.Code.Function.Bundles.T_Surjection_846 ->
  MAlonzo.Code.Function.Bundles.T_Surjection_846
d__'8846''45''8608'__82 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
  = du__'8846''45''8608'__82
du__'8846''45''8608'__82 ::
  MAlonzo.Code.Function.Bundles.T_Surjection_846 ->
  MAlonzo.Code.Function.Bundles.T_Surjection_846 ->
  MAlonzo.Code.Function.Bundles.T_Surjection_846
du__'8846''45''8608'__82
  = coe
      du_liftViaInverse_64
      (coe
         (\ v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 ->
            coe
              MAlonzo.Code.Function.Construct.Composition.du_surjection_1460 v9
              v10))
      (coe
         (\ v0 v1 v2 v3 v4 v5 v6 ->
            coe
              MAlonzo.Code.Function.Properties.Inverse.du_Inverse'8658'Surjection_328
              v6))
      (coe
         MAlonzo.Code.Data.Sum.Function.Setoid.du__'8846''45'surjection__162)
-- Data.Sum.Function.Propositional._⊎-↩_
d__'8846''45''8617'__84 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Function.Bundles.T_LeftInverse_1792 ->
  MAlonzo.Code.Function.Bundles.T_LeftInverse_1792 ->
  MAlonzo.Code.Function.Bundles.T_LeftInverse_1792
d__'8846''45''8617'__84 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
  = du__'8846''45''8617'__84
du__'8846''45''8617'__84 ::
  MAlonzo.Code.Function.Bundles.T_LeftInverse_1792 ->
  MAlonzo.Code.Function.Bundles.T_LeftInverse_1792 ->
  MAlonzo.Code.Function.Bundles.T_LeftInverse_1792
du__'8846''45''8617'__84
  = coe
      du_liftViaInverse_64
      (coe
         (\ v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 ->
            coe
              MAlonzo.Code.Function.Construct.Composition.du_leftInverse_1906 v9
              v10))
      (coe
         (\ v0 v1 v2 v3 v4 v5 v6 ->
            coe MAlonzo.Code.Function.Bundles.du_leftInverse_1986 v6))
      (coe
         MAlonzo.Code.Data.Sum.Function.Setoid.du__'8846''45'leftInverse__182)
-- Data.Sum.Function.Propositional._⊎-↪_
d__'8846''45''8618'__86 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Function.Bundles.T_RightInverse_1880 ->
  MAlonzo.Code.Function.Bundles.T_RightInverse_1880 ->
  MAlonzo.Code.Function.Bundles.T_RightInverse_1880
d__'8846''45''8618'__86 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
  = du__'8846''45''8618'__86
du__'8846''45''8618'__86 ::
  MAlonzo.Code.Function.Bundles.T_RightInverse_1880 ->
  MAlonzo.Code.Function.Bundles.T_RightInverse_1880 ->
  MAlonzo.Code.Function.Bundles.T_RightInverse_1880
du__'8846''45''8618'__86
  = coe
      du_liftViaInverse_64
      (coe
         (\ v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 ->
            coe
              MAlonzo.Code.Function.Construct.Composition.du_rightInverse_2064 v9
              v10))
      (coe
         (\ v0 v1 v2 v3 v4 v5 v6 ->
            coe MAlonzo.Code.Function.Bundles.du_rightInverse_1988 v6))
      (coe
         MAlonzo.Code.Data.Sum.Function.Setoid.du__'8846''45'rightInverse__198)
-- Data.Sum.Function.Propositional._⊎-⤖_
d__'8846''45''10518'__88 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Function.Bundles.T_Bijection_926 ->
  MAlonzo.Code.Function.Bundles.T_Bijection_926 ->
  MAlonzo.Code.Function.Bundles.T_Bijection_926
d__'8846''45''10518'__88 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
  = du__'8846''45''10518'__88
du__'8846''45''10518'__88 ::
  MAlonzo.Code.Function.Bundles.T_Bijection_926 ->
  MAlonzo.Code.Function.Bundles.T_Bijection_926 ->
  MAlonzo.Code.Function.Bundles.T_Bijection_926
du__'8846''45''10518'__88
  = coe
      du_liftViaInverse_64
      (coe
         (\ v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 ->
            coe
              MAlonzo.Code.Function.Construct.Composition.du_bijection_1606 v9
              v10))
      (coe
         (\ v0 v1 v2 v3 v4 ->
            coe
              MAlonzo.Code.Function.Properties.Inverse.du_Inverse'8658'Bijection_440
              (coe v4)))
      (coe
         MAlonzo.Code.Data.Sum.Function.Setoid.du__'8846''45'bijection__172)
-- Data.Sum.Function.Propositional._⊎-↔_
d__'8846''45''8596'__90 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Function.Bundles.T_Inverse_1960 ->
  MAlonzo.Code.Function.Bundles.T_Inverse_1960 ->
  MAlonzo.Code.Function.Bundles.T_Inverse_1960
d__'8846''45''8596'__90 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
  = du__'8846''45''8596'__90
du__'8846''45''8596'__90 ::
  MAlonzo.Code.Function.Bundles.T_Inverse_1960 ->
  MAlonzo.Code.Function.Bundles.T_Inverse_1960 ->
  MAlonzo.Code.Function.Bundles.T_Inverse_1960
du__'8846''45''8596'__90
  = coe
      du_liftViaInverse_64
      (coe
         (\ v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 ->
            coe
              MAlonzo.Code.Function.Construct.Composition.du_inverse_2210 v9
              v10))
      (coe (\ v0 v1 v2 v3 v4 v5 v6 -> v6))
      (coe
         MAlonzo.Code.Data.Sum.Function.Setoid.du__'8846''45'inverse__214)
-- Data.Sum.Function.Propositional._⊎-cong_
d__'8846''45'cong__94 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Function.Related.Propositional.T_Kind_6 ->
  AgdaAny -> AgdaAny -> AgdaAny
d__'8846''45'cong__94 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8
  = du__'8846''45'cong__94 v8
du__'8846''45'cong__94 ::
  MAlonzo.Code.Function.Related.Propositional.T_Kind_6 ->
  AgdaAny -> AgdaAny -> AgdaAny
du__'8846''45'cong__94 v0
  = case coe v0 of
      MAlonzo.Code.Function.Related.Propositional.C_implication_8
        -> coe du__'8846''45''10230'__76
      MAlonzo.Code.Function.Related.Propositional.C_reverseImplication_10
        -> coe du__'8846''45''10230'__76
      MAlonzo.Code.Function.Related.Propositional.C_equivalence_12
        -> coe du__'8846''45''8660'__78
      MAlonzo.Code.Function.Related.Propositional.C_injection_14
        -> coe du__'8846''45''8611'__80
      MAlonzo.Code.Function.Related.Propositional.C_reverseInjection_16
        -> coe du__'8846''45''8611'__80
      MAlonzo.Code.Function.Related.Propositional.C_leftInverse_18
        -> coe du__'8846''45''8618'__86
      MAlonzo.Code.Function.Related.Propositional.C_surjection_20
        -> coe du__'8846''45''8608'__82
      MAlonzo.Code.Function.Related.Propositional.C_bijection_22
        -> coe du__'8846''45''8596'__90
      _ -> MAlonzo.RTE.mazUnreachableError
