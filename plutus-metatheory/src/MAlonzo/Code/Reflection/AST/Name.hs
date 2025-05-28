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

module MAlonzo.Code.Reflection.AST.Name where

import Data.Text qualified
import MAlonzo.Code.Agda.Builtin.Reflection qualified
import MAlonzo.Code.Data.Product.Properties qualified
import MAlonzo.Code.Data.Word64.Properties qualified
import MAlonzo.Code.Relation.Binary.Construct.On qualified
import MAlonzo.Code.Relation.Nullary.Decidable.Core qualified
import MAlonzo.RTE (AgdaAny, add64, addInt, coe, eq64, eqInt, erased, geqInt, lt64, ltInt, mul64,
                    mulInt, quot64, quotInt, rem64, remInt, sub64, subInt, word64FromNat,
                    word64ToNat)
import MAlonzo.RTE qualified

-- Reflection.AST.Name.Names
d_Names_6 :: ()
d_Names_6 = erased
-- Reflection.AST.Name._≈_
d__'8776'__8 :: AgdaAny -> AgdaAny -> ()
d__'8776'__8 = erased
-- Reflection.AST.Name._≈?_
d__'8776''63'__10 ::
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8776''63'__10
  = coe
      MAlonzo.Code.Relation.Binary.Construct.On.du_decidable_102
      (coe MAlonzo.Code.Agda.Builtin.Reflection.d_primQNameToWord64s_36)
      (coe
         MAlonzo.Code.Data.Product.Properties.du_'8801''45'dec_78
         (coe MAlonzo.Code.Data.Word64.Properties.d__'8799'__52)
         (coe (\ v0 -> MAlonzo.Code.Data.Word64.Properties.d__'8799'__52)))
-- Reflection.AST.Name._≟_
d__'8799'__12 ::
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8799'__12 v0 v1
  = coe
      MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_168
      erased erased (coe d__'8776''63'__10 v0 v1)
