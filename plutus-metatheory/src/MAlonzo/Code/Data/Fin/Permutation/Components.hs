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

module MAlonzo.Code.Data.Fin.Permutation.Components where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Data.Fin.Base
import qualified MAlonzo.Code.Data.Fin.Properties
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core

-- Data.Fin.Permutation.Components.transpose
d_transpose_10 ::
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10
d_transpose_10 ~v0 v1 v2 v3 = du_transpose_10 v1 v2 v3
du_transpose_10 ::
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10
du_transpose_10 v0 v1 v2
  = let v3
          = MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
              (coe
                 MAlonzo.Code.Data.Fin.Properties.du__'8799'__50 (coe v2)
                 (coe v0)) in
    coe
      (if coe v3
         then coe v1
         else (let v4
                     = MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
                         (coe
                            MAlonzo.Code.Data.Fin.Properties.du__'8799'__50 (coe v2)
                            (coe v1)) in
               coe (if coe v4 then coe v0 else coe v2)))
-- Data.Fin.Permutation.Components.transpose-inverse
d_transpose'45'inverse_58 ::
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_transpose'45'inverse_58 = erased
-- Data.Fin.Permutation.Components.reverse
d_reverse_130 ::
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10
d_reverse_130 = coe MAlonzo.Code.Data.Fin.Base.d_opposite_384
-- Data.Fin.Permutation.Components.reverse-prop
d_reverse'45'prop_132 ::
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reverse'45'prop_132 = erased
-- Data.Fin.Permutation.Components.reverse-involutive
d_reverse'45'involutive_134 ::
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reverse'45'involutive_134 = erased
-- Data.Fin.Permutation.Components.reverse-suc
d_reverse'45'suc_140 ::
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_reverse'45'suc_140 = erased
