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

module MAlonzo.Code.Algebra.Consequences.Base where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Relation.Binary.Consequences

-- Algebra.Consequences.Base._._.Congruent₂
d_Congruent'8322'_24 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> ()) -> (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d_Congruent'8322'_24 = erased
-- Algebra.Consequences.Base._._.LeftCongruent
d_LeftCongruent_30 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> ()) -> (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d_LeftCongruent_30 = erased
-- Algebra.Consequences.Base._._.RightCongruent
d_RightCongruent_32 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> ()) -> (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d_RightCongruent_32 = erased
-- Algebra.Consequences.Base._.Congruence.∙-congˡ
d_'8729''45'cong'737'_42 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny ->
   AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'737'_42 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6 v7 v8 v9
  = du_'8729''45'cong'737'_42 v5 v6 v7 v8 v9
du_'8729''45'cong'737'_42 ::
  (AgdaAny ->
   AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'737'_42 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Relation.Binary.Consequences.du_mono'8322''8658'mono'737'_342
      (coe (\ v5 -> coe v1 v2)) (coe (\ v5 v6 -> coe v0 v2 v2)) (coe v2)
      (coe v3) (coe v4)
-- Algebra.Consequences.Base._.Congruence.∙-congʳ
d_'8729''45'cong'691'_46 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny ->
   AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_'8729''45'cong'691'_46 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6 v7 v8 v9
  = du_'8729''45'cong'691'_46 v5 v6 v7 v8 v9
du_'8729''45'cong'691'_46 ::
  (AgdaAny ->
   AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_'8729''45'cong'691'_46 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Relation.Binary.Consequences.du_mono'8322''8658'mono'691'_352
      (coe (\ v5 -> coe v1 v2))
      (coe (\ v5 v6 v7 v8 -> coe v0 v5 v6 v2 v2)) (coe v2) (coe v3)
      (coe v4)
-- Algebra.Consequences.Base._._.Idempotent
d_Idempotent_68 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> ()) -> (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d_Idempotent_68 = erased
-- Algebra.Consequences.Base._._.Selective
d_Selective_76 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> ()) -> (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d_Selective_76 = erased
-- Algebra.Consequences.Base._._.sel⇒idem
d_sel'8658'idem_80 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30) ->
  AgdaAny -> AgdaAny
d_sel'8658'idem_80 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6
  = du_sel'8658'idem_80 v5 v6
du_sel'8658'idem_80 ::
  (AgdaAny -> AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30) ->
  AgdaAny -> AgdaAny
du_sel'8658'idem_80 v0 v1
  = coe MAlonzo.Code.Data.Sum.Base.du_reduce_76 (coe v0 v1 v1)
-- Algebra.Consequences.Base._._.Involutive
d_Involutive_106 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> ()) -> (AgdaAny -> AgdaAny) -> ()
d_Involutive_106 = erased
-- Algebra.Consequences.Base._._.SelfInverse
d_SelfInverse_114 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> ()) -> (AgdaAny -> AgdaAny) -> ()
d_SelfInverse_114 = erased
-- Algebra.Consequences.Base._._.reflexive∧selfInverse⇒involutive
d_reflexive'8743'selfInverse'8658'involutive_116 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_reflexive'8743'selfInverse'8658'involutive_116 ~v0 ~v1 ~v2 v3 ~v4
                                                 v5 v6 v7
  = du_reflexive'8743'selfInverse'8658'involutive_116 v3 v5 v6 v7
du_reflexive'8743'selfInverse'8658'involutive_116 ::
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du_reflexive'8743'selfInverse'8658'involutive_116 v0 v1 v2 v3
  = coe v2 v3 (coe v0 v3) (coe v1 (coe v0 v3))
-- Algebra.Consequences.Base.reflexive+selfInverse⇒involutive
d_reflexive'43'selfInverse'8658'involutive_122 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_reflexive'43'selfInverse'8658'involutive_122 ~v0 ~v1
  = du_reflexive'43'selfInverse'8658'involutive_122
du_reflexive'43'selfInverse'8658'involutive_122 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du_reflexive'43'selfInverse'8658'involutive_122 v0 v1 v2 v3 v4 v5
  = coe du_reflexive'8743'selfInverse'8658'involutive_116 v1 v3 v4 v5
