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

module MAlonzo.Code.Class.Monoid.Instances where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Class.Monoid.Core
import qualified MAlonzo.Code.Class.Semigroup.Core
import qualified MAlonzo.Code.Class.Setoid.Core
import qualified MAlonzo.Code.Data.Integer.Base
import qualified MAlonzo.Code.Data.Nat.Binary.Base
import qualified MAlonzo.Code.Data.Vec.Base

-- Class.Monoid.Instances.Monoid-List
d_Monoid'45'List_6 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> MAlonzo.Code.Class.Monoid.Core.T_Monoid_12
d_Monoid'45'List_6 ~v0 ~v1 = du_Monoid'45'List_6
du_Monoid'45'List_6 :: MAlonzo.Code.Class.Monoid.Core.T_Monoid_12
du_Monoid'45'List_6
  = coe
      MAlonzo.Code.Class.Monoid.Core.C_Monoid'46'constructor_37
      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
-- Class.Monoid.Instances.MonoidLaws-List
d_MonoidLaws'45'List_8 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> MAlonzo.Code.Class.Monoid.Core.T_MonoidLaws_40
d_MonoidLaws'45'List_8 ~v0 ~v1 = du_MonoidLaws'45'List_8
du_MonoidLaws'45'List_8 ::
  MAlonzo.Code.Class.Monoid.Core.T_MonoidLaws_40
du_MonoidLaws'45'List_8
  = coe
      MAlonzo.Code.Class.Monoid.Core.C_MonoidLaws'46'constructor_2449
      (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased)
-- Class.Monoid.Instances.Monoid-Vec
d_Monoid'45'Vec_14 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> MAlonzo.Code.Class.Monoid.Core.T_Monoid_12
d_Monoid'45'Vec_14 ~v0 ~v1 = du_Monoid'45'Vec_14
du_Monoid'45'Vec_14 :: MAlonzo.Code.Class.Monoid.Core.T_Monoid_12
du_Monoid'45'Vec_14
  = coe
      MAlonzo.Code.Class.Monoid.Core.C_Monoid'46'constructor_37
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe (0 :: Integer))
         (coe MAlonzo.Code.Data.Vec.Base.C_'91''93'_32))
-- Class.Monoid.Instances.Monoid-String
d_Monoid'45'String_16 :: MAlonzo.Code.Class.Monoid.Core.T_Monoid_12
d_Monoid'45'String_16
  = coe
      MAlonzo.Code.Class.Monoid.Core.C_Monoid'46'constructor_37
      (coe ("" :: Data.Text.Text))
-- Class.Monoid.Instances._.Monoid-Maybe
d_Monoid'45'Maybe_28 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Class.Semigroup.Core.T_Semigroup_10 ->
  MAlonzo.Code.Class.Monoid.Core.T_Monoid_12 ->
  MAlonzo.Code.Class.Monoid.Core.T_Monoid_12
d_Monoid'45'Maybe_28 ~v0 ~v1 ~v2 ~v3 = du_Monoid'45'Maybe_28
du_Monoid'45'Maybe_28 :: MAlonzo.Code.Class.Monoid.Core.T_Monoid_12
du_Monoid'45'Maybe_28
  = coe
      MAlonzo.Code.Class.Monoid.Core.C_Monoid'46'constructor_37
      (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18)
-- Class.Monoid.Instances._.MonoidLaws-Maybe
d_MonoidLaws'45'Maybe_30 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Class.Semigroup.Core.T_Semigroup_10 ->
  MAlonzo.Code.Class.Monoid.Core.T_Monoid_12 ->
  MAlonzo.Code.Class.Monoid.Core.T_MonoidLaws_40 ->
  MAlonzo.Code.Class.Monoid.Core.T_MonoidLaws_40
d_MonoidLaws'45'Maybe_30 ~v0 ~v1 ~v2 ~v3 ~v4
  = du_MonoidLaws'45'Maybe_30
du_MonoidLaws'45'Maybe_30 ::
  MAlonzo.Code.Class.Monoid.Core.T_MonoidLaws_40
du_MonoidLaws'45'Maybe_30
  = coe
      MAlonzo.Code.Class.Monoid.Core.C_MonoidLaws'46'constructor_2449
      (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased)
-- Class.Monoid.Instances._._.p
d_p_36 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Class.Semigroup.Core.T_Semigroup_10 ->
  MAlonzo.Code.Class.Monoid.Core.T_Monoid_12 ->
  MAlonzo.Code.Class.Monoid.Core.T_MonoidLaws_40 ->
  Maybe AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_p_36 = erased
-- Class.Monoid.Instances._._.q
d_q_40 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Class.Semigroup.Core.T_Semigroup_10 ->
  MAlonzo.Code.Class.Monoid.Core.T_Monoid_12 ->
  MAlonzo.Code.Class.Monoid.Core.T_MonoidLaws_40 ->
  Maybe AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_q_40 = erased
-- Class.Monoid.Instances._.Monoid-×
d_Monoid'45''215'_56 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Class.Semigroup.Core.T_Semigroup_10 ->
  MAlonzo.Code.Class.Semigroup.Core.T_Semigroup_10 ->
  MAlonzo.Code.Class.Monoid.Core.T_Monoid_12 ->
  MAlonzo.Code.Class.Monoid.Core.T_Monoid_12 ->
  MAlonzo.Code.Class.Monoid.Core.T_Monoid_12
d_Monoid'45''215'_56 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7
  = du_Monoid'45''215'_56 v6 v7
du_Monoid'45''215'_56 ::
  MAlonzo.Code.Class.Monoid.Core.T_Monoid_12 ->
  MAlonzo.Code.Class.Monoid.Core.T_Monoid_12 ->
  MAlonzo.Code.Class.Monoid.Core.T_Monoid_12
du_Monoid'45''215'_56 v0 v1
  = coe
      MAlonzo.Code.Class.Monoid.Core.C_Monoid'46'constructor_37
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
         (coe MAlonzo.Code.Class.Monoid.Core.d_ε_20 (coe v0))
         (coe MAlonzo.Code.Class.Monoid.Core.d_ε_20 (coe v1)))
-- Class.Monoid.Instances._.MonoidLaws-×
d_MonoidLaws'45''215'_62 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Class.Semigroup.Core.T_Semigroup_10 ->
  MAlonzo.Code.Class.Semigroup.Core.T_Semigroup_10 ->
  MAlonzo.Code.Class.Monoid.Core.T_Monoid_12 ->
  MAlonzo.Code.Class.Monoid.Core.T_Monoid_12 ->
  MAlonzo.Code.Class.Monoid.Core.T_MonoidLaws_40 ->
  MAlonzo.Code.Class.Monoid.Core.T_MonoidLaws_40 ->
  MAlonzo.Code.Class.Monoid.Core.T_MonoidLaws_40
d_MonoidLaws'45''215'_62 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9
  = du_MonoidLaws'45''215'_62
du_MonoidLaws'45''215'_62 ::
  MAlonzo.Code.Class.Monoid.Core.T_MonoidLaws_40
du_MonoidLaws'45''215'_62
  = coe
      MAlonzo.Code.Class.Monoid.Core.C_MonoidLaws'46'constructor_2449
      (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased)
-- Class.Monoid.Instances._._.p
d_p_68 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Class.Semigroup.Core.T_Semigroup_10 ->
  MAlonzo.Code.Class.Semigroup.Core.T_Semigroup_10 ->
  MAlonzo.Code.Class.Monoid.Core.T_Monoid_12 ->
  MAlonzo.Code.Class.Monoid.Core.T_Monoid_12 ->
  MAlonzo.Code.Class.Monoid.Core.T_MonoidLaws_40 ->
  MAlonzo.Code.Class.Monoid.Core.T_MonoidLaws_40 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_p_68 = erased
-- Class.Monoid.Instances._._.q
d_q_82 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Class.Semigroup.Core.T_Semigroup_10 ->
  MAlonzo.Code.Class.Semigroup.Core.T_Semigroup_10 ->
  MAlonzo.Code.Class.Monoid.Core.T_Monoid_12 ->
  MAlonzo.Code.Class.Monoid.Core.T_Monoid_12 ->
  MAlonzo.Code.Class.Monoid.Core.T_MonoidLaws_40 ->
  MAlonzo.Code.Class.Monoid.Core.T_MonoidLaws_40 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_q_82 = erased
-- Class.Monoid.Instances._._.Monoid-ℕ-+
d_Monoid'45'ℕ'45''43'_106 ::
  MAlonzo.Code.Class.Monoid.Core.T_Monoid_12
d_Monoid'45'ℕ'45''43'_106
  = coe
      MAlonzo.Code.Class.Monoid.Core.C_Monoid'46'constructor_37
      (coe (0 :: Integer))
-- Class.Monoid.Instances._._.MonoidLaws-ℕ-+
d_MonoidLaws'45'ℕ'45''43'_112 ::
  MAlonzo.Code.Class.Monoid.Core.T_MonoidLaws_40
d_MonoidLaws'45'ℕ'45''43'_112
  = coe
      MAlonzo.Code.Class.Monoid.Core.C_MonoidLaws'46'constructor_2449
      (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased)
-- Class.Monoid.Instances._._.Monoid-ℕ-*
d_Monoid'45'ℕ'45''42'_120 ::
  MAlonzo.Code.Class.Monoid.Core.T_Monoid_12
d_Monoid'45'ℕ'45''42'_120
  = coe
      MAlonzo.Code.Class.Monoid.Core.C_Monoid'46'constructor_37
      (coe (1 :: Integer))
-- Class.Monoid.Instances._._.MonoidLaws-ℕ-*
d_MonoidLaws'45'ℕ'45''42'_126 ::
  MAlonzo.Code.Class.Monoid.Core.T_MonoidLaws_40
d_MonoidLaws'45'ℕ'45''42'_126
  = coe
      MAlonzo.Code.Class.Monoid.Core.C_MonoidLaws'46'constructor_2449
      (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased)
-- Class.Monoid.Instances._.Monoid-ℕᵇ-+
d_Monoid'45'ℕ'7495''45''43'_134 ::
  MAlonzo.Code.Class.Monoid.Core.T_Monoid_12
d_Monoid'45'ℕ'7495''45''43'_134
  = coe
      MAlonzo.Code.Class.Monoid.Core.C_Monoid'46'constructor_37
      (coe MAlonzo.Code.Data.Nat.Binary.Base.C_zero_10)
-- Class.Monoid.Instances._.MonoidLaws-ℕᵇ-+
d_MonoidLaws'45'ℕ'7495''45''43'_140 ::
  MAlonzo.Code.Class.Monoid.Core.T_MonoidLaws_40
d_MonoidLaws'45'ℕ'7495''45''43'_140
  = coe
      MAlonzo.Code.Class.Monoid.Core.C_MonoidLaws'46'constructor_2449
      (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased)
-- Class.Monoid.Instances._._.Monoid-ℤ-+
d_Monoid'45'ℤ'45''43'_152 ::
  MAlonzo.Code.Class.Monoid.Core.T_Monoid_12
d_Monoid'45'ℤ'45''43'_152
  = coe
      MAlonzo.Code.Class.Monoid.Core.C_Monoid'46'constructor_37
      (coe MAlonzo.Code.Data.Integer.Base.d_0ℤ_12)
-- Class.Monoid.Instances._._.MonoidLaws-ℤ-+
d_MonoidLaws'45'ℤ'45''43'_158 ::
  MAlonzo.Code.Class.Monoid.Core.T_MonoidLaws_40
d_MonoidLaws'45'ℤ'45''43'_158
  = coe
      MAlonzo.Code.Class.Monoid.Core.C_MonoidLaws'46'constructor_2449
      (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased)
-- Class.Monoid.Instances._._.Monoid-ℤ-*
d_Monoid'45'ℤ'45''42'_166 ::
  MAlonzo.Code.Class.Monoid.Core.T_Monoid_12
d_Monoid'45'ℤ'45''42'_166
  = coe
      MAlonzo.Code.Class.Monoid.Core.C_Monoid'46'constructor_37
      (coe MAlonzo.Code.Data.Integer.Base.d_1ℤ_16)
-- Class.Monoid.Instances._._.MonoidLaws-ℤ-*
d_MonoidLaws'45'ℤ'45''42'_172 ::
  MAlonzo.Code.Class.Monoid.Core.T_MonoidLaws_40
d_MonoidLaws'45'ℤ'45''42'_172
  = coe
      MAlonzo.Code.Class.Monoid.Core.C_MonoidLaws'46'constructor_2449
      (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased)
-- Class.Monoid.Instances._.just-◇ˡ
d_just'45''9671''737'_192 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Class.Semigroup.Core.T_Semigroup_10 ->
  MAlonzo.Code.Class.Monoid.Core.T_Monoid_12 ->
  MAlonzo.Code.Class.Setoid.Core.T_ISetoid_10 ->
  MAlonzo.Code.Class.Monoid.Core.T_MonoidLaws_40 ->
  AgdaAny ->
  Maybe AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_just'45''9671''737'_192 = erased
-- Class.Monoid.Instances._.just-◇ʳ
d_just'45''9671''691'_198 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Class.Semigroup.Core.T_Semigroup_10 ->
  MAlonzo.Code.Class.Monoid.Core.T_Monoid_12 ->
  MAlonzo.Code.Class.Setoid.Core.T_ISetoid_10 ->
  MAlonzo.Code.Class.Monoid.Core.T_MonoidLaws_40 ->
  AgdaAny ->
  Maybe AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_just'45''9671''691'_198 = erased
