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

module MAlonzo.Code.Type.BetaNormal.Equality where

import Data.Text qualified
import MAlonzo.Code.Agda.Builtin.Equality qualified
import MAlonzo.Code.Data.Vec.Base qualified
import MAlonzo.Code.Type qualified
import MAlonzo.Code.Type.BetaNormal qualified
import MAlonzo.Code.Utils qualified
import MAlonzo.RTE (AgdaAny, add64, addInt, coe, eq64, eqInt, erased, geqInt, lt64, ltInt, mul64,
                    mulInt, quot64, quotInt, rem64, remInt, sub64, subInt, word64FromNat,
                    word64ToNat)
import MAlonzo.RTE qualified

-- Type.BetaNormal.Equality.renNf-cong
d_renNf'45'cong_18 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  (MAlonzo.Code.Utils.T_Kind_636 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 ->
   MAlonzo.Code.Type.T__'8715''8902'__14) ->
  (MAlonzo.Code.Utils.T_Kind_636 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 ->
   MAlonzo.Code.Type.T__'8715''8902'__14) ->
  (MAlonzo.Code.Utils.T_Kind_636 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Utils.T_Kind_636 ->
  MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_renNf'45'cong_18 = erased
-- Type.BetaNormal.Equality.renNe-cong
d_renNe'45'cong_32 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  (MAlonzo.Code.Utils.T_Kind_636 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 ->
   MAlonzo.Code.Type.T__'8715''8902'__14) ->
  (MAlonzo.Code.Utils.T_Kind_636 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 ->
   MAlonzo.Code.Type.T__'8715''8902'__14) ->
  (MAlonzo.Code.Utils.T_Kind_636 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Utils.T_Kind_636 ->
  MAlonzo.Code.Type.BetaNormal.T__'8866'Ne'8902'__6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_renNe'45'cong_32 = erased
-- Type.BetaNormal.Equality.renNf-cong-List
d_renNf'45'cong'45'List_46 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  (MAlonzo.Code.Utils.T_Kind_636 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 ->
   MAlonzo.Code.Type.T__'8715''8902'__14) ->
  (MAlonzo.Code.Utils.T_Kind_636 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 ->
   MAlonzo.Code.Type.T__'8715''8902'__14) ->
  (MAlonzo.Code.Utils.T_Kind_636 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  [MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_renNf'45'cong'45'List_46 = erased
-- Type.BetaNormal.Equality.renNf-cong-VecList
d_renNf'45'cong'45'VecList_62 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  (MAlonzo.Code.Utils.T_Kind_636 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 ->
   MAlonzo.Code.Type.T__'8715''8902'__14) ->
  (MAlonzo.Code.Utils.T_Kind_636 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 ->
   MAlonzo.Code.Type.T__'8715''8902'__14) ->
  (MAlonzo.Code.Utils.T_Kind_636 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  Integer ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_renNf'45'cong'45'VecList_62 = erased
-- Type.BetaNormal.Equality.renNf-id
d_renNf'45'id_128 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Utils.T_Kind_636 ->
  MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_renNf'45'id_128 = erased
-- Type.BetaNormal.Equality.renNe-id
d_renNe'45'id_132 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Utils.T_Kind_636 ->
  MAlonzo.Code.Type.BetaNormal.T__'8866'Ne'8902'__6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_renNe'45'id_132 = erased
-- Type.BetaNormal.Equality.renNe-id-List
d_renNe'45'id'45'List_136 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Utils.T_Kind_636 ->
  [MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_renNe'45'id'45'List_136 = erased
-- Type.BetaNormal.Equality.renNe-id-VecList
d_renNe'45'id'45'VecList_142 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Utils.T_Kind_636 ->
  Integer ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_renNe'45'id'45'VecList_142 = erased
-- Type.BetaNormal.Equality.renNf-comp
d_renNf'45'comp_186 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  (MAlonzo.Code.Utils.T_Kind_636 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 ->
   MAlonzo.Code.Type.T__'8715''8902'__14) ->
  (MAlonzo.Code.Utils.T_Kind_636 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 ->
   MAlonzo.Code.Type.T__'8715''8902'__14) ->
  MAlonzo.Code.Utils.T_Kind_636 ->
  MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_renNf'45'comp_186 = erased
-- Type.BetaNormal.Equality.renNe-comp
d_renNe'45'comp_196 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  (MAlonzo.Code.Utils.T_Kind_636 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 ->
   MAlonzo.Code.Type.T__'8715''8902'__14) ->
  (MAlonzo.Code.Utils.T_Kind_636 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 ->
   MAlonzo.Code.Type.T__'8715''8902'__14) ->
  MAlonzo.Code.Utils.T_Kind_636 ->
  MAlonzo.Code.Type.BetaNormal.T__'8866'Ne'8902'__6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_renNe'45'comp_196 = erased
-- Type.BetaNormal.Equality.renNf-comp-List
d_renNf'45'comp'45'List_204 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  (MAlonzo.Code.Utils.T_Kind_636 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 ->
   MAlonzo.Code.Type.T__'8715''8902'__14) ->
  (MAlonzo.Code.Utils.T_Kind_636 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 ->
   MAlonzo.Code.Type.T__'8715''8902'__14) ->
  [MAlonzo.Code.Type.BetaNormal.T__'8866'Nf'8902'__4] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_renNf'45'comp'45'List_204 = erased
-- Type.BetaNormal.Equality.renNf-comp-VecList
d_renNf'45'comp'45'VecList_214 ::
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  MAlonzo.Code.Type.T_Ctx'8902'_2 ->
  Integer ->
  (MAlonzo.Code.Utils.T_Kind_636 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 ->
   MAlonzo.Code.Type.T__'8715''8902'__14) ->
  (MAlonzo.Code.Utils.T_Kind_636 ->
   MAlonzo.Code.Type.T__'8715''8902'__14 ->
   MAlonzo.Code.Type.T__'8715''8902'__14) ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_renNf'45'comp'45'VecList_214 = erased
