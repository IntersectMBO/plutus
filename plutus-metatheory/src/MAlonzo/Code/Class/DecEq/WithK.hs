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

module MAlonzo.Code.Class.DecEq.WithK where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.Unit
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Class.DecEq.Core
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core
import qualified MAlonzo.Code.Relation.Nullary.Reflects

-- Class.DecEq.WithK.≟-refl
d_'8799''45'refl_12 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Class.DecEq.Core.T_DecEq_10 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8799''45'refl_12 = erased
-- Class.DecEq.WithK.==-refl
d_'61''61''45'refl_24 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Class.DecEq.Core.T_DecEq_10 -> AgdaAny -> AgdaAny
d_'61''61''45'refl_24 ~v0 ~v1 ~v2 ~v3 = du_'61''61''45'refl_24
du_'61''61''45'refl_24 :: AgdaAny
du_'61''61''45'refl_24 = coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
-- Class.DecEq.WithK.≡ᵇ-refl
d_'8801''7495''45'refl_26 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Class.DecEq.Core.T_DecEq_10 -> AgdaAny -> AgdaAny
d_'8801''7495''45'refl_26 ~v0 ~v1 ~v2 = du_'8801''7495''45'refl_26
du_'8801''7495''45'refl_26 :: AgdaAny -> AgdaAny
du_'8801''7495''45'refl_26 v0 = coe du_'61''61''45'refl_24
-- Class.DecEq.WithK.DecEq-Σ
d_DecEq'45'Σ_34 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Class.DecEq.Core.T_DecEq_10 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> ()) ->
  (AgdaAny -> MAlonzo.Code.Class.DecEq.Core.T_DecEq_10) ->
  MAlonzo.Code.Class.DecEq.Core.T_DecEq_10
d_DecEq'45'Σ_34 ~v0 ~v1 v2 ~v3 ~v4 v5 = du_DecEq'45'Σ_34 v2 v5
du_DecEq'45'Σ_34 ::
  MAlonzo.Code.Class.DecEq.Core.T_DecEq_10 ->
  (AgdaAny -> MAlonzo.Code.Class.DecEq.Core.T_DecEq_10) ->
  MAlonzo.Code.Class.DecEq.Core.T_DecEq_10
du_DecEq'45'Σ_34 v0 v1
  = coe
      MAlonzo.Code.Class.DecEq.Core.C_DecEq'46'constructor_31
      (coe
         (\ v2 ->
            case coe v2 of
              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
                -> coe
                     (\ v5 ->
                        case coe v5 of
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
                            -> let v8
                                     = coe MAlonzo.Code.Class.DecEq.Core.d__'8799'__16 v0 v3 v6 in
                               coe
                                 (case coe v8 of
                                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v9 v10
                                      -> if coe v9
                                           then coe
                                                  seq (coe v10)
                                                  (let v11
                                                         = coe
                                                             MAlonzo.Code.Class.DecEq.Core.d__'8799'__16
                                                             (coe v1 v3) v4 v7 in
                                                   coe
                                                     (case coe v11 of
                                                        MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v12 v13
                                                          -> if coe v12
                                                               then coe
                                                                      seq (coe v13)
                                                                      (coe
                                                                         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                         (coe v12)
                                                                         (coe
                                                                            MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                                                                            erased))
                                                               else coe
                                                                      seq (coe v13)
                                                                      (coe
                                                                         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                                         (coe v12)
                                                                         (coe
                                                                            MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
                                                        _ -> MAlonzo.RTE.mazUnreachableError))
                                           else coe
                                                  seq (coe v10)
                                                  (coe
                                                     MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                     (coe v9)
                                                     (coe
                                                        MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
                                    _ -> MAlonzo.RTE.mazUnreachableError)
                          _ -> MAlonzo.RTE.mazUnreachableError)
              _ -> MAlonzo.RTE.mazUnreachableError))
