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

module MAlonzo.Code.Class.Setoid.Instances where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.Unit
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Class.Setoid.Core
import qualified MAlonzo.Code.Level
import qualified MAlonzo.Code.Relation.Binary.Structures

-- Class.Setoid.Instances.Setoid-Maybe
d_Setoid'45'Maybe_6 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Class.Setoid.Core.T_ISetoid_10 ->
  MAlonzo.Code.Class.Setoid.Core.T_ISetoid_10
d_Setoid'45'Maybe_6 ~v0 ~v1 v2 = du_Setoid'45'Maybe_6 v2
du_Setoid'45'Maybe_6 ::
  MAlonzo.Code.Class.Setoid.Core.T_ISetoid_10 ->
  MAlonzo.Code.Class.Setoid.Core.T_ISetoid_10
du_Setoid'45'Maybe_6 v0
  = coe
      MAlonzo.Code.Class.Setoid.Core.C_ISetoid'46'constructor_47
      (MAlonzo.Code.Class.Setoid.Core.d_relℓ_18 (coe v0))
-- Class.Setoid.Instances.SetoidLaws-Maybe
d_SetoidLaws'45'Maybe_16 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Class.Setoid.Core.T_ISetoid_10 ->
  MAlonzo.Code.Class.Setoid.Core.T_SetoidLaws_302 ->
  MAlonzo.Code.Class.Setoid.Core.T_SetoidLaws_302
d_SetoidLaws'45'Maybe_16 ~v0 ~v1 ~v2 v3
  = du_SetoidLaws'45'Maybe_16 v3
du_SetoidLaws'45'Maybe_16 ::
  MAlonzo.Code.Class.Setoid.Core.T_SetoidLaws_302 ->
  MAlonzo.Code.Class.Setoid.Core.T_SetoidLaws_302
du_SetoidLaws'45'Maybe_16 v0
  = coe
      MAlonzo.Code.Class.Setoid.Core.C_SetoidLaws'46'constructor_3537
      (coe
         MAlonzo.Code.Relation.Binary.Structures.C_IsEquivalence'46'constructor_745
         (coe
            (\ v1 ->
               case coe v1 of
                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
                   -> coe
                        MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                        (MAlonzo.Code.Class.Setoid.Core.d_isEquivalence_310 (coe v0)) v2
                 MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                   -> coe
                        MAlonzo.Code.Level.C_lift_20
                        (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                 _ -> MAlonzo.RTE.mazUnreachableError))
         (coe
            (\ v1 v2 ->
               case coe v1 of
                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
                   -> case coe v2 of
                        MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
                          -> coe
                               MAlonzo.Code.Relation.Binary.Structures.d_sym_36
                               (MAlonzo.Code.Class.Setoid.Core.d_isEquivalence_310 (coe v0)) v3 v4
                        MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe (\ v4 -> v4)
                        _ -> MAlonzo.RTE.mazUnreachableError
                 MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                   -> coe seq (coe v2) (coe (\ v3 -> v3))
                 _ -> MAlonzo.RTE.mazUnreachableError))
         (coe
            (\ v1 v2 v3 v4 v5 ->
               case coe v1 of
                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
                   -> case coe v2 of
                        MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v7
                          -> case coe v3 of
                               MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v8
                                 -> coe
                                      MAlonzo.Code.Relation.Binary.Structures.d_trans_38
                                      (MAlonzo.Code.Class.Setoid.Core.d_isEquivalence_310 (coe v0))
                                      v6 v7 v8 v4 v5
                               _ -> MAlonzo.RTE.mazUnreachableError
                        _ -> MAlonzo.RTE.mazUnreachableError
                 MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                   -> coe seq (coe v2) (coe seq (coe v3) (coe v4))
                 _ -> MAlonzo.RTE.mazUnreachableError)))
