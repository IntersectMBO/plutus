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

module MAlonzo.Code.Reflection.AST.Meta where

import Data.Text qualified
import MAlonzo.Code.Agda.Builtin.Reflection qualified
import MAlonzo.Code.Data.Nat.Properties qualified
import MAlonzo.Code.Relation.Binary.Construct.On qualified
import MAlonzo.Code.Relation.Nullary.Decidable.Core qualified
import MAlonzo.RTE (AgdaAny, add64, addInt, coe, eq64, eqInt, erased, geqInt, lt64, ltInt, mul64,
                    mulInt, quot64, quotInt, rem64, remInt, sub64, subInt, word64FromNat,
                    word64ToNat)
import MAlonzo.RTE qualified

-- Reflection.AST.Meta._≈_
d__'8776'__6 :: AgdaAny -> AgdaAny -> ()
d__'8776'__6 = erased
-- Reflection.AST.Meta._≈?_
d__'8776''63'__8 ::
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8776''63'__8
  = coe
      MAlonzo.Code.Relation.Binary.Construct.On.du_decidable_102
      (coe MAlonzo.Code.Agda.Builtin.Reflection.d_primMetaToNat_46)
      (coe MAlonzo.Code.Data.Nat.Properties.d__'8799'__2688)
-- Reflection.AST.Meta._≟_
d__'8799'__10 ::
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8799'__10 v0 v1
  = coe
      MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_168
      erased erased (coe d__'8776''63'__8 v0 v1)
