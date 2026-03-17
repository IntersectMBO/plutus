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

module MAlonzo.Code.Class.Prelude where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Primitive

-- Class.Prelude._.3REL
d_3REL_58 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> () -> () -> MAlonzo.Code.Agda.Primitive.T_Level_18 -> ()
d_3REL_58 = erased
-- Class.Prelude._.Decidable³
d_Decidable'179'_76 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  () ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> AgdaAny -> ()) -> ()
d_Decidable'179'_76 = erased
-- Class.Prelude.Alg._._Absorbs_
d__Absorbs__126 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d__Absorbs__126 = erased
-- Class.Prelude.Alg._._DistributesOver_
d__DistributesOver__128 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d__DistributesOver__128 = erased
-- Class.Prelude.Alg._._DistributesOverʳ_
d__DistributesOver'691'__130 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d__DistributesOver'691'__130 = erased
-- Class.Prelude.Alg._._DistributesOverˡ_
d__DistributesOver'737'__132 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d__DistributesOver'737'__132 = erased
-- Class.Prelude.Alg._._IdempotentOn_
d__IdempotentOn__134 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny -> ()
d__IdempotentOn__134 = erased
-- Class.Prelude.Alg._._MiddleFourExchange_
d__MiddleFourExchange__136 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d__MiddleFourExchange__136 = erased
-- Class.Prelude.Alg._.Absorptive
d_Absorptive_138 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d_Absorptive_138 = erased
-- Class.Prelude.Alg._.AlmostCancellative
d_AlmostCancellative_140 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  AgdaAny -> (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d_AlmostCancellative_140 = erased
-- Class.Prelude.Alg._.AlmostLeftCancellative
d_AlmostLeftCancellative_142 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  AgdaAny -> (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d_AlmostLeftCancellative_142 = erased
-- Class.Prelude.Alg._.AlmostRightCancellative
d_AlmostRightCancellative_144 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  AgdaAny -> (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d_AlmostRightCancellative_144 = erased
-- Class.Prelude.Alg._.Alternative
d_Alternative_146 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) -> (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d_Alternative_146 = erased
-- Class.Prelude.Alg._.Associative
d_Associative_148 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) -> (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d_Associative_148 = erased
-- Class.Prelude.Alg._.Cancellative
d_Cancellative_150 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) -> (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d_Cancellative_150 = erased
-- Class.Prelude.Alg._.Commutative
d_Commutative_152 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) -> (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d_Commutative_152 = erased
-- Class.Prelude.Alg._.Congruent₁
d_Congruent'8321'_154 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) -> (AgdaAny -> AgdaAny) -> ()
d_Congruent'8321'_154 = erased
-- Class.Prelude.Alg._.Congruent₂
d_Congruent'8322'_156 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) -> (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d_Congruent'8322'_156 = erased
-- Class.Prelude.Alg._.Conical
d_Conical_158 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  AgdaAny -> (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d_Conical_158 = erased
-- Class.Prelude.Alg._.Flexible
d_Flexible_160 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) -> (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d_Flexible_160 = erased
-- Class.Prelude.Alg._.Idempotent
d_Idempotent_162 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) -> (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d_Idempotent_162 = erased
-- Class.Prelude.Alg._.IdempotentFun
d_IdempotentFun_164 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) -> (AgdaAny -> AgdaAny) -> ()
d_IdempotentFun_164 = erased
-- Class.Prelude.Alg._.Identical
d_Identical_166 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) -> (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d_Identical_166 = erased
-- Class.Prelude.Alg._.Identity
d_Identity_168 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  AgdaAny -> (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d_Identity_168 = erased
-- Class.Prelude.Alg._.Interchangable
d_Interchangable_170 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d_Interchangable_170 = erased
-- Class.Prelude.Alg._.Inverse
d_Inverse_172 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) -> (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d_Inverse_172 = erased
-- Class.Prelude.Alg._.Invertible
d_Invertible_174 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  AgdaAny -> (AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny -> ()
d_Invertible_174 = erased
-- Class.Prelude.Alg._.Involutive
d_Involutive_176 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) -> (AgdaAny -> AgdaAny) -> ()
d_Involutive_176 = erased
-- Class.Prelude.Alg._.LeftAlternative
d_LeftAlternative_178 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) -> (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d_LeftAlternative_178 = erased
-- Class.Prelude.Alg._.LeftBol
d_LeftBol_180 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) -> (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d_LeftBol_180 = erased
-- Class.Prelude.Alg._.LeftCancellative
d_LeftCancellative_182 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) -> (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d_LeftCancellative_182 = erased
-- Class.Prelude.Alg._.LeftCongruent
d_LeftCongruent_184 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) -> (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d_LeftCongruent_184 = erased
-- Class.Prelude.Alg._.LeftConical
d_LeftConical_186 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  AgdaAny -> (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d_LeftConical_186 = erased
-- Class.Prelude.Alg._.LeftDivides
d_LeftDivides_188 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d_LeftDivides_188 = erased
-- Class.Prelude.Alg._.LeftDividesʳ
d_LeftDivides'691'_190 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d_LeftDivides'691'_190 = erased
-- Class.Prelude.Alg._.LeftDividesˡ
d_LeftDivides'737'_192 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d_LeftDivides'737'_192 = erased
-- Class.Prelude.Alg._.LeftIdentity
d_LeftIdentity_194 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  AgdaAny -> (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d_LeftIdentity_194 = erased
-- Class.Prelude.Alg._.LeftInverse
d_LeftInverse_196 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) -> (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d_LeftInverse_196 = erased
-- Class.Prelude.Alg._.LeftInvertible
d_LeftInvertible_198 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  AgdaAny -> (AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny -> ()
d_LeftInvertible_198 = erased
-- Class.Prelude.Alg._.LeftSemimedial
d_LeftSemimedial_200 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) -> (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d_LeftSemimedial_200 = erased
-- Class.Prelude.Alg._.LeftZero
d_LeftZero_202 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  AgdaAny -> (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d_LeftZero_202 = erased
-- Class.Prelude.Alg._.Medial
d_Medial_204 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) -> (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d_Medial_204 = erased
-- Class.Prelude.Alg._.MiddleBol
d_MiddleBol_206 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d_MiddleBol_206 = erased
-- Class.Prelude.Alg._.RightAlternative
d_RightAlternative_208 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) -> (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d_RightAlternative_208 = erased
-- Class.Prelude.Alg._.RightBol
d_RightBol_210 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) -> (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d_RightBol_210 = erased
-- Class.Prelude.Alg._.RightCancellative
d_RightCancellative_212 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) -> (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d_RightCancellative_212 = erased
-- Class.Prelude.Alg._.RightCongruent
d_RightCongruent_214 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) -> (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d_RightCongruent_214 = erased
-- Class.Prelude.Alg._.RightConical
d_RightConical_216 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  AgdaAny -> (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d_RightConical_216 = erased
-- Class.Prelude.Alg._.RightDivides
d_RightDivides_218 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d_RightDivides_218 = erased
-- Class.Prelude.Alg._.RightDividesʳ
d_RightDivides'691'_220 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d_RightDivides'691'_220 = erased
-- Class.Prelude.Alg._.RightDividesˡ
d_RightDivides'737'_222 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d_RightDivides'737'_222 = erased
-- Class.Prelude.Alg._.RightIdentity
d_RightIdentity_224 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  AgdaAny -> (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d_RightIdentity_224 = erased
-- Class.Prelude.Alg._.RightInverse
d_RightInverse_226 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) -> (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d_RightInverse_226 = erased
-- Class.Prelude.Alg._.RightInvertible
d_RightInvertible_228 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  AgdaAny -> (AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny -> ()
d_RightInvertible_228 = erased
-- Class.Prelude.Alg._.RightSemimedial
d_RightSemimedial_230 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) -> (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d_RightSemimedial_230 = erased
-- Class.Prelude.Alg._.RightZero
d_RightZero_232 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  AgdaAny -> (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d_RightZero_232 = erased
-- Class.Prelude.Alg._.Selective
d_Selective_234 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) -> (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d_Selective_234 = erased
-- Class.Prelude.Alg._.SelfInverse
d_SelfInverse_236 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) -> (AgdaAny -> AgdaAny) -> ()
d_SelfInverse_236 = erased
-- Class.Prelude.Alg._.Semimedial
d_Semimedial_238 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) -> (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d_Semimedial_238 = erased
-- Class.Prelude.Alg._.StarDestructive
d_StarDestructive_240 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> (AgdaAny -> AgdaAny) -> ()
d_StarDestructive_240 = erased
-- Class.Prelude.Alg._.StarExpansive
d_StarExpansive_242 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  AgdaAny ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> (AgdaAny -> AgdaAny) -> ()
d_StarExpansive_242 = erased
-- Class.Prelude.Alg._.StarLeftDestructive
d_StarLeftDestructive_244 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> (AgdaAny -> AgdaAny) -> ()
d_StarLeftDestructive_244 = erased
-- Class.Prelude.Alg._.StarLeftExpansive
d_StarLeftExpansive_246 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  AgdaAny ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> (AgdaAny -> AgdaAny) -> ()
d_StarLeftExpansive_246 = erased
-- Class.Prelude.Alg._.StarRightDestructive
d_StarRightDestructive_248 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> (AgdaAny -> AgdaAny) -> ()
d_StarRightDestructive_248 = erased
-- Class.Prelude.Alg._.StarRightExpansive
d_StarRightExpansive_250 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  AgdaAny ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> (AgdaAny -> AgdaAny) -> ()
d_StarRightExpansive_250 = erased
-- Class.Prelude.Alg._.Zero
d_Zero_252 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  AgdaAny -> (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d_Zero_252 = erased
-- Class.Prelude.Alg≡._Absorbs_
d__Absorbs__260 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d__Absorbs__260 = erased
-- Class.Prelude.Alg≡._DistributesOver_
d__DistributesOver__262 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d__DistributesOver__262 = erased
-- Class.Prelude.Alg≡._DistributesOverʳ_
d__DistributesOver'691'__264 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d__DistributesOver'691'__264 = erased
-- Class.Prelude.Alg≡._DistributesOverˡ_
d__DistributesOver'737'__266 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d__DistributesOver'737'__266 = erased
-- Class.Prelude.Alg≡._IdempotentOn_
d__IdempotentOn__268 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> (AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny -> ()
d__IdempotentOn__268 = erased
-- Class.Prelude.Alg≡._MiddleFourExchange_
d__MiddleFourExchange__270 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d__MiddleFourExchange__270 = erased
-- Class.Prelude.Alg≡.Absorptive
d_Absorptive_272 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d_Absorptive_272 = erased
-- Class.Prelude.Alg≡.AlmostCancellative
d_AlmostCancellative_274 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> AgdaAny -> (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d_AlmostCancellative_274 = erased
-- Class.Prelude.Alg≡.AlmostLeftCancellative
d_AlmostLeftCancellative_276 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> AgdaAny -> (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d_AlmostLeftCancellative_276 = erased
-- Class.Prelude.Alg≡.AlmostRightCancellative
d_AlmostRightCancellative_278 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> AgdaAny -> (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d_AlmostRightCancellative_278 = erased
-- Class.Prelude.Alg≡.Alternative
d_Alternative_280 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d_Alternative_280 = erased
-- Class.Prelude.Alg≡.Associative
d_Associative_282 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d_Associative_282 = erased
-- Class.Prelude.Alg≡.Cancellative
d_Cancellative_284 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d_Cancellative_284 = erased
-- Class.Prelude.Alg≡.Commutative
d_Commutative_286 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d_Commutative_286 = erased
-- Class.Prelude.Alg≡.Congruent₁
d_Congruent'8321'_288 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> (AgdaAny -> AgdaAny) -> ()
d_Congruent'8321'_288 = erased
-- Class.Prelude.Alg≡.Congruent₂
d_Congruent'8322'_290 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d_Congruent'8322'_290 = erased
-- Class.Prelude.Alg≡.Conical
d_Conical_292 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> AgdaAny -> (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d_Conical_292 = erased
-- Class.Prelude.Alg≡.Flexible
d_Flexible_294 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d_Flexible_294 = erased
-- Class.Prelude.Alg≡.Idempotent
d_Idempotent_296 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d_Idempotent_296 = erased
-- Class.Prelude.Alg≡.IdempotentFun
d_IdempotentFun_298 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> (AgdaAny -> AgdaAny) -> ()
d_IdempotentFun_298 = erased
-- Class.Prelude.Alg≡.Identical
d_Identical_300 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d_Identical_300 = erased
-- Class.Prelude.Alg≡.Identity
d_Identity_302 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> AgdaAny -> (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d_Identity_302 = erased
-- Class.Prelude.Alg≡.Interchangable
d_Interchangable_304 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d_Interchangable_304 = erased
-- Class.Prelude.Alg≡.Inverse
d_Inverse_306 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) -> (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d_Inverse_306 = erased
-- Class.Prelude.Alg≡.Invertible
d_Invertible_308 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> AgdaAny -> (AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny -> ()
d_Invertible_308 = erased
-- Class.Prelude.Alg≡.Involutive
d_Involutive_310 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> (AgdaAny -> AgdaAny) -> ()
d_Involutive_310 = erased
-- Class.Prelude.Alg≡.LeftAlternative
d_LeftAlternative_312 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d_LeftAlternative_312 = erased
-- Class.Prelude.Alg≡.LeftBol
d_LeftBol_314 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d_LeftBol_314 = erased
-- Class.Prelude.Alg≡.LeftCancellative
d_LeftCancellative_316 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d_LeftCancellative_316 = erased
-- Class.Prelude.Alg≡.LeftCongruent
d_LeftCongruent_318 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d_LeftCongruent_318 = erased
-- Class.Prelude.Alg≡.LeftConical
d_LeftConical_320 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> AgdaAny -> (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d_LeftConical_320 = erased
-- Class.Prelude.Alg≡.LeftDivides
d_LeftDivides_322 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d_LeftDivides_322 = erased
-- Class.Prelude.Alg≡.LeftDividesʳ
d_LeftDivides'691'_324 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d_LeftDivides'691'_324 = erased
-- Class.Prelude.Alg≡.LeftDividesˡ
d_LeftDivides'737'_326 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d_LeftDivides'737'_326 = erased
-- Class.Prelude.Alg≡.LeftIdentity
d_LeftIdentity_328 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> AgdaAny -> (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d_LeftIdentity_328 = erased
-- Class.Prelude.Alg≡.LeftInverse
d_LeftInverse_330 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) -> (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d_LeftInverse_330 = erased
-- Class.Prelude.Alg≡.LeftInvertible
d_LeftInvertible_332 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> AgdaAny -> (AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny -> ()
d_LeftInvertible_332 = erased
-- Class.Prelude.Alg≡.LeftSemimedial
d_LeftSemimedial_334 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d_LeftSemimedial_334 = erased
-- Class.Prelude.Alg≡.LeftZero
d_LeftZero_336 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> AgdaAny -> (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d_LeftZero_336 = erased
-- Class.Prelude.Alg≡.Medial
d_Medial_338 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d_Medial_338 = erased
-- Class.Prelude.Alg≡.MiddleBol
d_MiddleBol_340 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d_MiddleBol_340 = erased
-- Class.Prelude.Alg≡.RightAlternative
d_RightAlternative_342 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d_RightAlternative_342 = erased
-- Class.Prelude.Alg≡.RightBol
d_RightBol_344 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d_RightBol_344 = erased
-- Class.Prelude.Alg≡.RightCancellative
d_RightCancellative_346 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d_RightCancellative_346 = erased
-- Class.Prelude.Alg≡.RightCongruent
d_RightCongruent_348 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d_RightCongruent_348 = erased
-- Class.Prelude.Alg≡.RightConical
d_RightConical_350 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> AgdaAny -> (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d_RightConical_350 = erased
-- Class.Prelude.Alg≡.RightDivides
d_RightDivides_352 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d_RightDivides_352 = erased
-- Class.Prelude.Alg≡.RightDividesʳ
d_RightDivides'691'_354 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d_RightDivides'691'_354 = erased
-- Class.Prelude.Alg≡.RightDividesˡ
d_RightDivides'737'_356 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d_RightDivides'737'_356 = erased
-- Class.Prelude.Alg≡.RightIdentity
d_RightIdentity_358 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> AgdaAny -> (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d_RightIdentity_358 = erased
-- Class.Prelude.Alg≡.RightInverse
d_RightInverse_360 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  AgdaAny ->
  (AgdaAny -> AgdaAny) -> (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d_RightInverse_360 = erased
-- Class.Prelude.Alg≡.RightInvertible
d_RightInvertible_362 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> AgdaAny -> (AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny -> ()
d_RightInvertible_362 = erased
-- Class.Prelude.Alg≡.RightSemimedial
d_RightSemimedial_364 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d_RightSemimedial_364 = erased
-- Class.Prelude.Alg≡.RightZero
d_RightZero_366 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> AgdaAny -> (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d_RightZero_366 = erased
-- Class.Prelude.Alg≡.Selective
d_Selective_368 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d_Selective_368 = erased
-- Class.Prelude.Alg≡.SelfInverse
d_SelfInverse_370 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> (AgdaAny -> AgdaAny) -> ()
d_SelfInverse_370 = erased
-- Class.Prelude.Alg≡.Semimedial
d_Semimedial_372 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d_Semimedial_372 = erased
-- Class.Prelude.Alg≡.StarDestructive
d_StarDestructive_374 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> (AgdaAny -> AgdaAny) -> ()
d_StarDestructive_374 = erased
-- Class.Prelude.Alg≡.StarExpansive
d_StarExpansive_376 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  AgdaAny ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> (AgdaAny -> AgdaAny) -> ()
d_StarExpansive_376 = erased
-- Class.Prelude.Alg≡.StarLeftDestructive
d_StarLeftDestructive_378 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> (AgdaAny -> AgdaAny) -> ()
d_StarLeftDestructive_378 = erased
-- Class.Prelude.Alg≡.StarLeftExpansive
d_StarLeftExpansive_380 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  AgdaAny ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> (AgdaAny -> AgdaAny) -> ()
d_StarLeftExpansive_380 = erased
-- Class.Prelude.Alg≡.StarRightDestructive
d_StarRightDestructive_382 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> (AgdaAny -> AgdaAny) -> ()
d_StarRightDestructive_382 = erased
-- Class.Prelude.Alg≡.StarRightExpansive
d_StarRightExpansive_384 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  AgdaAny ->
  (AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> (AgdaAny -> AgdaAny) -> ()
d_StarRightExpansive_384 = erased
-- Class.Prelude.Alg≡.Zero
d_Zero_386 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> AgdaAny -> (AgdaAny -> AgdaAny -> AgdaAny) -> ()
d_Zero_386 = erased
-- Class.Prelude.itω
d_itω_390 :: () -> AgdaAny -> AgdaAny
d_itω_390 ~v0 v1 = du_itω_390 v1
du_itω_390 :: AgdaAny -> AgdaAny
du_itω_390 v0 = coe v0
