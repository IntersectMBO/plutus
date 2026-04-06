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

module MAlonzo.Code.Function.Consequences where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Data.Product.Base

-- Function.Consequences.contraInjective
d_contraInjective_30 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  (AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_contraInjective_30 = erased
-- Function.Consequences.inverseˡ⇒surjective
d_inverse'737''8658'surjective_38 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inverse'737''8658'surjective_38 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
                                  v8 ~v9 v10 v11
  = du_inverse'737''8658'surjective_38 v8 v10 v11
du_inverse'737''8658'surjective_38 ::
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_inverse'737''8658'surjective_38 v0 v1 v2
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0 v2) (coe v1 v2)
-- Function.Consequences.inverseʳ⇒injective
d_inverse'691''8658'injective_50 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_inverse'691''8658'injective_50 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 ~v8
                                 v9 v10 v11 v12 v13 v14 v15 v16
  = du_inverse'691''8658'injective_50
      v7 v9 v10 v11 v12 v13 v14 v15 v16
du_inverse'691''8658'injective_50 ::
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_inverse'691''8658'injective_50 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = coe
      v4 v6 (coe v0 (coe v1 v6)) v7
      (coe
         v3 (coe v0 (coe v1 v6)) v6
         (coe v5 v6 (coe v1 v6) (coe v2 (coe v1 v6))))
      (coe v5 v7 (coe v1 v6) v8)
-- Function.Consequences.inverseᵇ⇒bijective
d_inverse'7495''8658'bijective_72 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_inverse'7495''8658'bijective_72 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 v8
                                  ~v9 v10 v11 v12 v13
  = du_inverse'7495''8658'bijective_72 v7 v8 v10 v11 v12 v13
du_inverse'7495''8658'bijective_72 ::
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_inverse'7495''8658'bijective_72 v0 v1 v2 v3 v4 v5
  = case coe v5 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
             (coe
                du_inverse'691''8658'injective_50 (coe v1) (coe v0) (coe v2)
                (coe v3) (coe v4) (coe v7))
             (coe du_inverse'737''8658'surjective_38 (coe v1) (coe v6))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Function.Consequences.surjective⇒strictlySurjective
d_surjective'8658'strictlySurjective_90 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_surjective'8658'strictlySurjective_90 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6
                                        ~v7 ~v8 v9 v10 v11
  = du_surjective'8658'strictlySurjective_90 v9 v10 v11
du_surjective'8658'strictlySurjective_90 ::
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_surjective'8658'strictlySurjective_90 v0 v1 v2
  = coe
      MAlonzo.Code.Data.Product.Base.du_map'8322'_150
      (\ v3 v4 -> coe v4 v3 (coe v0 v3)) (coe v1 v2)
-- Function.Consequences.strictlySurjective⇒surjective
d_strictlySurjective'8658'surjective_100 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_strictlySurjective'8658'surjective_100 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
                                         ~v6 ~v7 v8 v9 v10 v11 v12
  = du_strictlySurjective'8658'surjective_100 v8 v9 v10 v11 v12
du_strictlySurjective'8658'surjective_100 ::
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_strictlySurjective'8658'surjective_100 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Data.Product.Base.du_map'8322'_150
      (\ v5 v6 v7 v8 ->
         coe v1 (coe v0 v7) (coe v0 v5) v4 (coe v2 v7 v5 v8) v6)
      (coe v3 v4)
-- Function.Consequences.inverseˡ⇒strictlyInverseˡ
d_inverse'737''8658'strictlyInverse'737'_118 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_inverse'737''8658'strictlyInverse'737'_118 ~v0 ~v1 ~v2 ~v3 ~v4
                                             ~v5 ~v6 v7 ~v8 ~v9 v10 v11 v12
  = du_inverse'737''8658'strictlyInverse'737'_118 v7 v10 v11 v12
du_inverse'737''8658'strictlyInverse'737'_118 ::
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du_inverse'737''8658'strictlyInverse'737'_118 v0 v1 v2 v3
  = coe v2 v3 (coe v0 v3) (coe v1 (coe v0 v3))
-- Function.Consequences.strictlyInverseˡ⇒inverseˡ
d_strictlyInverse'737''8658'inverse'737'_126 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_strictlyInverse'737''8658'inverse'737'_126 ~v0 ~v1 ~v2 ~v3 ~v4
                                             ~v5 ~v6 ~v7 v8 v9 v10 v11 v12 v13 v14 v15
  = du_strictlyInverse'737''8658'inverse'737'_126
      v8 v9 v10 v11 v12 v13 v14 v15
du_strictlyInverse'737''8658'inverse'737'_126 ::
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_strictlyInverse'737''8658'inverse'737'_126 v0 v1 v2 v3 v4 v5 v6
                                              v7
  = coe
      v2 (coe v0 v6) (coe v0 (coe v1 v5)) v5 (coe v3 v6 (coe v1 v5) v7)
      (coe v4 v5)
-- Function.Consequences.inverseʳ⇒strictlyInverseʳ
d_inverse'691''8658'strictlyInverse'691'_142 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_inverse'691''8658'strictlyInverse'691'_142 ~v0 ~v1 ~v2 ~v3 ~v4
                                             ~v5 v6 ~v7 ~v8 ~v9 v10 v11 v12
  = du_inverse'691''8658'strictlyInverse'691'_142 v6 v10 v11 v12
du_inverse'691''8658'strictlyInverse'691'_142 ::
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du_inverse'691''8658'strictlyInverse'691'_142 v0 v1 v2 v3
  = coe v2 v3 (coe v0 v3) (coe v1 (coe v0 v3))
-- Function.Consequences.strictlyInverseʳ⇒inverseʳ
d_strictlyInverse'691''8658'inverse'691'_150 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
d_strictlyInverse'691''8658'inverse'691'_150 ~v0 ~v1 ~v2 ~v3 ~v4
                                             ~v5 ~v6 ~v7 v8 v9 v10 v11 v12 v13 v14 v15
  = du_strictlyInverse'691''8658'inverse'691'_150
      v8 v9 v10 v11 v12 v13 v14 v15
du_strictlyInverse'691''8658'inverse'691'_150 ::
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny
du_strictlyInverse'691''8658'inverse'691'_150 v0 v1 v2 v3 v4 v5 v6
                                              v7
  = coe
      v2 (coe v0 v6) (coe v0 (coe v1 v5)) v5 (coe v3 v6 (coe v1 v5) v7)
      (coe v4 v5)
