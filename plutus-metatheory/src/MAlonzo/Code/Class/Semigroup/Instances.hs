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

module MAlonzo.Code.Class.Semigroup.Instances where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.Unit
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Class.Semigroup.Core
import qualified MAlonzo.Code.Class.Setoid.Core
import qualified MAlonzo.Code.Data.Integer.Base
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Data.List.NonEmpty.Base
import qualified MAlonzo.Code.Data.Nat.Binary.Base
import qualified MAlonzo.Code.Data.String.Base
import qualified MAlonzo.Code.Data.Vec.Base
import qualified MAlonzo.Code.Level
import qualified MAlonzo.Code.Relation.Binary.Structures

-- Class.Semigroup.Instances.Semigroup-List
d_Semigroup'45'List_6 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> MAlonzo.Code.Class.Semigroup.Core.T_Semigroup_10
d_Semigroup'45'List_6 ~v0 ~v1 = du_Semigroup'45'List_6
du_Semigroup'45'List_6 ::
  MAlonzo.Code.Class.Semigroup.Core.T_Semigroup_10
du_Semigroup'45'List_6
  = coe
      MAlonzo.Code.Class.Semigroup.Core.C_Semigroup'46'constructor_25
      (coe MAlonzo.Code.Data.List.Base.du__'43''43'__32)
-- Class.Semigroup.Instances.Semigroup-List⁺
d_Semigroup'45'List'8314'_8 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> MAlonzo.Code.Class.Semigroup.Core.T_Semigroup_10
d_Semigroup'45'List'8314'_8 ~v0 ~v1 = du_Semigroup'45'List'8314'_8
du_Semigroup'45'List'8314'_8 ::
  MAlonzo.Code.Class.Semigroup.Core.T_Semigroup_10
du_Semigroup'45'List'8314'_8
  = coe
      MAlonzo.Code.Class.Semigroup.Core.C_Semigroup'46'constructor_25
      (coe
         MAlonzo.Code.Data.List.NonEmpty.Base.du__'8314''43''43''8314'__178)
-- Class.Semigroup.Instances.Semigroup-∃Vec
d_Semigroup'45''8707'Vec_10 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> MAlonzo.Code.Class.Semigroup.Core.T_Semigroup_10
d_Semigroup'45''8707'Vec_10 ~v0 ~v1 = du_Semigroup'45''8707'Vec_10
du_Semigroup'45''8707'Vec_10 ::
  MAlonzo.Code.Class.Semigroup.Core.T_Semigroup_10
du_Semigroup'45''8707'Vec_10
  = coe
      MAlonzo.Code.Class.Semigroup.Core.C_Semigroup'46'constructor_25
      (coe
         (\ v0 ->
            case coe v0 of
              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v1 v2
                -> coe
                     (\ v3 ->
                        case coe v3 of
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
                            -> coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                 (coe addInt (coe v1) (coe v4))
                                 (coe
                                    MAlonzo.Code.Data.Vec.Base.du__'43''43'__188 (coe v2) (coe v5))
                          _ -> MAlonzo.RTE.mazUnreachableError)
              _ -> MAlonzo.RTE.mazUnreachableError))
-- Class.Semigroup.Instances.Semigroup-String
d_Semigroup'45'String_20 ::
  MAlonzo.Code.Class.Semigroup.Core.T_Semigroup_10
d_Semigroup'45'String_20
  = coe
      MAlonzo.Code.Class.Semigroup.Core.C_Semigroup'46'constructor_25
      (coe MAlonzo.Code.Data.String.Base.d__'43''43'__20)
-- Class.Semigroup.Instances._.Semigroup-Maybe
d_Semigroup'45'Maybe_34 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Class.Semigroup.Core.T_Semigroup_10 ->
  MAlonzo.Code.Class.Semigroup.Core.T_Semigroup_10
d_Semigroup'45'Maybe_34 ~v0 ~v1 v2 = du_Semigroup'45'Maybe_34 v2
du_Semigroup'45'Maybe_34 ::
  MAlonzo.Code.Class.Semigroup.Core.T_Semigroup_10 ->
  MAlonzo.Code.Class.Semigroup.Core.T_Semigroup_10
du_Semigroup'45'Maybe_34 v0
  = coe
      MAlonzo.Code.Class.Semigroup.Core.C_Semigroup'46'constructor_25
      (coe
         (\ v1 v2 ->
            case coe v1 of
              MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
                -> case coe v2 of
                     MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
                       -> coe
                            MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                            (coe MAlonzo.Code.Class.Semigroup.Core.d__'9671'__16 v0 v3 v4)
                     MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v1
                     _ -> MAlonzo.RTE.mazUnreachableError
              MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v2
              _ -> MAlonzo.RTE.mazUnreachableError))
-- Class.Semigroup.Instances._._.SemigroupLaws≡-Maybe
d_SemigroupLaws'8801''45'Maybe_52 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Class.Semigroup.Core.T_Semigroup_10 ->
  MAlonzo.Code.Class.Semigroup.Core.T_SemigroupLaws_40 ->
  MAlonzo.Code.Class.Semigroup.Core.T_SemigroupLaws_40
d_SemigroupLaws'8801''45'Maybe_52 ~v0 ~v1 ~v2 ~v3
  = du_SemigroupLaws'8801''45'Maybe_52
du_SemigroupLaws'8801''45'Maybe_52 ::
  MAlonzo.Code.Class.Semigroup.Core.T_SemigroupLaws_40
du_SemigroupLaws'8801''45'Maybe_52
  = coe
      MAlonzo.Code.Class.Semigroup.Core.C_SemigroupLaws'46'constructor_2433
      erased erased
-- Class.Semigroup.Instances._._.SemigroupLaws-Maybe
d_SemigroupLaws'45'Maybe_96 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Class.Semigroup.Core.T_Semigroup_10 ->
  MAlonzo.Code.Class.Setoid.Core.T_ISetoid_10 ->
  MAlonzo.Code.Class.Setoid.Core.T_SetoidLaws_302 ->
  MAlonzo.Code.Class.Semigroup.Core.T_SemigroupLaws_40 ->
  MAlonzo.Code.Class.Semigroup.Core.T_SemigroupLaws_40
d_SemigroupLaws'45'Maybe_96 ~v0 ~v1 v2 ~v3 v4 v5
  = du_SemigroupLaws'45'Maybe_96 v2 v4 v5
du_SemigroupLaws'45'Maybe_96 ::
  MAlonzo.Code.Class.Semigroup.Core.T_Semigroup_10 ->
  MAlonzo.Code.Class.Setoid.Core.T_SetoidLaws_302 ->
  MAlonzo.Code.Class.Semigroup.Core.T_SemigroupLaws_40 ->
  MAlonzo.Code.Class.Semigroup.Core.T_SemigroupLaws_40
du_SemigroupLaws'45'Maybe_96 v0 v1 v2
  = coe
      MAlonzo.Code.Class.Semigroup.Core.C_SemigroupLaws'46'constructor_2433
      (coe
         (\ v3 v4 ->
            case coe v3 of
              MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v5
                -> case coe v4 of
                     MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
                       -> coe
                            MAlonzo.Code.Class.Semigroup.Core.d_'9671''45'comm_310 v2 v5 v6
                     MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                       -> coe
                            MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                            (MAlonzo.Code.Class.Setoid.Core.d_isEquivalence_310 (coe v1)) v5
                     _ -> MAlonzo.RTE.mazUnreachableError
              MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                -> case coe v4 of
                     MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v5
                       -> coe
                            MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                            (MAlonzo.Code.Class.Setoid.Core.d_isEquivalence_310 (coe v1)) v5
                     MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                       -> coe
                            MAlonzo.Code.Level.C_lift_20
                            (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                     _ -> MAlonzo.RTE.mazUnreachableError
              _ -> MAlonzo.RTE.mazUnreachableError))
      (coe
         (\ v3 v4 v5 ->
            case coe v3 of
              MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
                -> case coe v4 of
                     MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v7
                       -> case coe v5 of
                            MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v8
                              -> coe
                                   MAlonzo.Code.Class.Semigroup.Core.d_'9671''45'assoc'691'_312 v2
                                   v6 v7 v8
                            MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                              -> coe
                                   MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                                   (MAlonzo.Code.Class.Setoid.Core.d_isEquivalence_310 (coe v1))
                                   (coe MAlonzo.Code.Class.Semigroup.Core.d__'9671'__16 v0 v6 v7)
                            _ -> MAlonzo.RTE.mazUnreachableError
                     MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                       -> case coe v5 of
                            MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v7
                              -> let v8
                                       = coe
                                           MAlonzo.Code.Class.Semigroup.Core.d__'9671'__16 v0 v6
                                           v7 in
                                 coe
                                   (coe
                                      MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                                      (MAlonzo.Code.Class.Setoid.Core.d_isEquivalence_310 (coe v1))
                                      v8)
                            MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                              -> coe
                                   MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                                   (MAlonzo.Code.Class.Setoid.Core.d_isEquivalence_310 (coe v1)) v6
                            _ -> MAlonzo.RTE.mazUnreachableError
                     _ -> MAlonzo.RTE.mazUnreachableError
              MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                -> case coe v4 of
                     MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
                       -> case coe v5 of
                            MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v7
                              -> let v8
                                       = coe
                                           MAlonzo.Code.Class.Semigroup.Core.d__'9671'__16 v0 v6
                                           v7 in
                                 coe
                                   (coe
                                      MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                                      (MAlonzo.Code.Class.Setoid.Core.d_isEquivalence_310 (coe v1))
                                      v8)
                            MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                              -> coe
                                   MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                                   (MAlonzo.Code.Class.Setoid.Core.d_isEquivalence_310 (coe v1)) v6
                            _ -> MAlonzo.RTE.mazUnreachableError
                     MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                       -> case coe v5 of
                            MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
                              -> coe
                                   MAlonzo.Code.Relation.Binary.Structures.d_refl_34
                                   (MAlonzo.Code.Class.Setoid.Core.d_isEquivalence_310 (coe v1)) v6
                            MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                              -> coe
                                   MAlonzo.Code.Level.C_lift_20
                                   (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                            _ -> MAlonzo.RTE.mazUnreachableError
                     _ -> MAlonzo.RTE.mazUnreachableError
              _ -> MAlonzo.RTE.mazUnreachableError))
-- Class.Semigroup.Instances._.Semigroup-×
d_Semigroup'45''215'_142 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Class.Semigroup.Core.T_Semigroup_10 ->
  MAlonzo.Code.Class.Semigroup.Core.T_Semigroup_10 ->
  MAlonzo.Code.Class.Semigroup.Core.T_Semigroup_10
d_Semigroup'45''215'_142 ~v0 ~v1 ~v2 ~v3 v4 v5
  = du_Semigroup'45''215'_142 v4 v5
du_Semigroup'45''215'_142 ::
  MAlonzo.Code.Class.Semigroup.Core.T_Semigroup_10 ->
  MAlonzo.Code.Class.Semigroup.Core.T_Semigroup_10 ->
  MAlonzo.Code.Class.Semigroup.Core.T_Semigroup_10
du_Semigroup'45''215'_142 v0 v1
  = coe
      MAlonzo.Code.Class.Semigroup.Core.C_Semigroup'46'constructor_25
      (coe
         (\ v2 ->
            case coe v2 of
              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
                -> coe
                     (\ v5 ->
                        case coe v5 of
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
                            -> coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                 (coe MAlonzo.Code.Class.Semigroup.Core.d__'9671'__16 v0 v3 v6)
                                 (coe MAlonzo.Code.Class.Semigroup.Core.d__'9671'__16 v1 v4 v7)
                          _ -> MAlonzo.RTE.mazUnreachableError)
              _ -> MAlonzo.RTE.mazUnreachableError))
-- Class.Semigroup.Instances._.SemigroupLaws-×
d_SemigroupLaws'45''215'_152 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Class.Semigroup.Core.T_Semigroup_10 ->
  MAlonzo.Code.Class.Semigroup.Core.T_Semigroup_10 ->
  MAlonzo.Code.Class.Semigroup.Core.T_SemigroupLaws_40 ->
  MAlonzo.Code.Class.Semigroup.Core.T_SemigroupLaws_40 ->
  MAlonzo.Code.Class.Semigroup.Core.T_SemigroupLaws_40
d_SemigroupLaws'45''215'_152 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7
  = du_SemigroupLaws'45''215'_152
du_SemigroupLaws'45''215'_152 ::
  MAlonzo.Code.Class.Semigroup.Core.T_SemigroupLaws_40
du_SemigroupLaws'45''215'_152
  = coe
      MAlonzo.Code.Class.Semigroup.Core.C_SemigroupLaws'46'constructor_2433
      erased erased
-- Class.Semigroup.Instances._._.p
d_p_158 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Class.Semigroup.Core.T_Semigroup_10 ->
  MAlonzo.Code.Class.Semigroup.Core.T_Semigroup_10 ->
  MAlonzo.Code.Class.Semigroup.Core.T_SemigroupLaws_40 ->
  MAlonzo.Code.Class.Semigroup.Core.T_SemigroupLaws_40 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_p_158 = erased
-- Class.Semigroup.Instances._._.q
d_q_180 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Class.Semigroup.Core.T_Semigroup_10 ->
  MAlonzo.Code.Class.Semigroup.Core.T_Semigroup_10 ->
  MAlonzo.Code.Class.Semigroup.Core.T_SemigroupLaws_40 ->
  MAlonzo.Code.Class.Semigroup.Core.T_SemigroupLaws_40 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_q_180 = erased
-- Class.Semigroup.Instances._.Semigroup-ℕ-+
d_Semigroup'45'ℕ'45''43'_202 ::
  MAlonzo.Code.Class.Semigroup.Core.T_Semigroup_10
d_Semigroup'45'ℕ'45''43'_202
  = coe
      MAlonzo.Code.Class.Semigroup.Core.C_Semigroup'46'constructor_25
      (coe addInt)
-- Class.Semigroup.Instances._.SemigroupLaws-ℕ-+
d_SemigroupLaws'45'ℕ'45''43'_206 ::
  MAlonzo.Code.Class.Semigroup.Core.T_SemigroupLaws_40
d_SemigroupLaws'45'ℕ'45''43'_206
  = coe
      MAlonzo.Code.Class.Semigroup.Core.C_SemigroupLaws'46'constructor_2433
      erased erased
-- Class.Semigroup.Instances._.Semigroup-ℕ-*
d_Semigroup'45'ℕ'45''42'_214 ::
  MAlonzo.Code.Class.Semigroup.Core.T_Semigroup_10
d_Semigroup'45'ℕ'45''42'_214
  = coe
      MAlonzo.Code.Class.Semigroup.Core.C_Semigroup'46'constructor_25
      (coe mulInt)
-- Class.Semigroup.Instances._.SemigroupLaws-ℕ-*
d_SemigroupLaws'45'ℕ'45''42'_218 ::
  MAlonzo.Code.Class.Semigroup.Core.T_SemigroupLaws_40
d_SemigroupLaws'45'ℕ'45''42'_218
  = coe
      MAlonzo.Code.Class.Semigroup.Core.C_SemigroupLaws'46'constructor_2433
      erased erased
-- Class.Semigroup.Instances._.Semigroup-ℕᵇ-+
d_Semigroup'45'ℕ'7495''45''43'_230 ::
  MAlonzo.Code.Class.Semigroup.Core.T_Semigroup_10
d_Semigroup'45'ℕ'7495''45''43'_230
  = coe
      MAlonzo.Code.Class.Semigroup.Core.C_Semigroup'46'constructor_25
      (coe MAlonzo.Code.Data.Nat.Binary.Base.d__'43'__110)
-- Class.Semigroup.Instances._.SemigroupLaws-ℕᵇ-+
d_SemigroupLaws'45'ℕ'7495''45''43'_234 ::
  MAlonzo.Code.Class.Semigroup.Core.T_SemigroupLaws_40
d_SemigroupLaws'45'ℕ'7495''45''43'_234
  = coe
      MAlonzo.Code.Class.Semigroup.Core.C_SemigroupLaws'46'constructor_2433
      erased erased
-- Class.Semigroup.Instances._.Semigroup-ℤ-+
d_Semigroup'45'ℤ'45''43'_246 ::
  MAlonzo.Code.Class.Semigroup.Core.T_Semigroup_10
d_Semigroup'45'ℤ'45''43'_246
  = coe
      MAlonzo.Code.Class.Semigroup.Core.C_Semigroup'46'constructor_25
      (coe MAlonzo.Code.Data.Integer.Base.d__'43'__276)
-- Class.Semigroup.Instances._.SemigroupLaws-ℤ-+
d_SemigroupLaws'45'ℤ'45''43'_250 ::
  MAlonzo.Code.Class.Semigroup.Core.T_SemigroupLaws_40
d_SemigroupLaws'45'ℤ'45''43'_250
  = coe
      MAlonzo.Code.Class.Semigroup.Core.C_SemigroupLaws'46'constructor_2433
      erased erased
-- Class.Semigroup.Instances._.Semigroup-ℤ-*
d_Semigroup'45'ℤ'45''42'_258 ::
  MAlonzo.Code.Class.Semigroup.Core.T_Semigroup_10
d_Semigroup'45'ℤ'45''42'_258
  = coe
      MAlonzo.Code.Class.Semigroup.Core.C_Semigroup'46'constructor_25
      (coe MAlonzo.Code.Data.Integer.Base.d__'42'__308)
-- Class.Semigroup.Instances._.SemigroupLaws-ℤ-*
d_SemigroupLaws'45'ℤ'45''42'_262 ::
  MAlonzo.Code.Class.Semigroup.Core.T_SemigroupLaws_40
d_SemigroupLaws'45'ℤ'45''42'_262
  = coe
      MAlonzo.Code.Class.Semigroup.Core.C_SemigroupLaws'46'constructor_2433
      erased erased
