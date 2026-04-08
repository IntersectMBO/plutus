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

module MAlonzo.Code.Relation.Binary.Construct.Add.Extrema.Strict where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Function.Base
import qualified MAlonzo.Code.Relation.Binary.Construct.Add.Infimum.NonStrict
import qualified MAlonzo.Code.Relation.Binary.Construct.Add.Infimum.Strict
import qualified MAlonzo.Code.Relation.Binary.Construct.Add.Point.Equality
import qualified MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.NonStrict
import qualified MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict
import qualified MAlonzo.Code.Relation.Binary.Definitions
import qualified MAlonzo.Code.Relation.Binary.Structures
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core

-- Relation.Binary.Construct.Add.Extrema.Strict.Inf._<₋_
d__'60''8331'__22 a0 a1 a2 a3 a4 a5 = ()
-- Relation.Binary.Construct.Add.Extrema.Strict.Sup._<⁺_
d__'60''8314'__88 a0 a1 a2 a3 a4 a5 = ()
-- Relation.Binary.Construct.Add.Extrema.Strict.[<]-injective
d_'91''60''93''45'injective_164 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.T__'60''8314'__20 ->
  AgdaAny
d_'91''60''93''45'injective_164 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_'91''60''93''45'injective_164
du_'91''60''93''45'injective_164 ::
  MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.T__'60''8314'__20 ->
  AgdaAny
du_'91''60''93''45'injective_164
  = coe
      MAlonzo.Code.Function.Base.du__'8728''8242'__216
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Add.Infimum.Strict.du_'91''60''93''45'injective_36)
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.du_'91''60''93''45'injective_36)
-- Relation.Binary.Construct.Add.Extrema.Strict.<±-asym
d_'60''177''45'asym_166 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  Maybe (Maybe AgdaAny) ->
  Maybe (Maybe AgdaAny) ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.T__'60''8314'__20 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.T__'60''8314'__20 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'60''177''45'asym_166 = erased
-- Relation.Binary.Construct.Add.Extrema.Strict.<±-trans
d_'60''177''45'trans_168 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  Maybe (Maybe AgdaAny) ->
  Maybe (Maybe AgdaAny) ->
  Maybe (Maybe AgdaAny) ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.T__'60''8314'__20 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.T__'60''8314'__20 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.T__'60''8314'__20
d_'60''177''45'trans_168 ~v0 ~v1 ~v2 ~v3
  = du_'60''177''45'trans_168
du_'60''177''45'trans_168 ::
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  Maybe (Maybe AgdaAny) ->
  Maybe (Maybe AgdaAny) ->
  Maybe (Maybe AgdaAny) ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.T__'60''8314'__20 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.T__'60''8314'__20 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.T__'60''8314'__20
du_'60''177''45'trans_168
  = coe
      MAlonzo.Code.Function.Base.du__'8728''8242'__216
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.du_'60''8314''45'trans_48)
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Add.Infimum.Strict.du_'60''8331''45'trans_48)
-- Relation.Binary.Construct.Add.Extrema.Strict.<±-dec
d_'60''177''45'dec_170 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  Maybe (Maybe AgdaAny) ->
  Maybe (Maybe AgdaAny) ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_'60''177''45'dec_170 ~v0 ~v1 ~v2 ~v3 = du_'60''177''45'dec_170
du_'60''177''45'dec_170 ::
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  Maybe (Maybe AgdaAny) ->
  Maybe (Maybe AgdaAny) ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du_'60''177''45'dec_170
  = coe
      MAlonzo.Code.Function.Base.du__'8728''8242'__216
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.du_'60''8314''45'dec_62)
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Add.Infimum.Strict.du_'60''8331''45'dec_62)
-- Relation.Binary.Construct.Add.Extrema.Strict.<±-irrelevant
d_'60''177''45'irrelevant_172 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  Maybe (Maybe AgdaAny) ->
  Maybe (Maybe AgdaAny) ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.T__'60''8314'__20 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.T__'60''8314'__20 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'60''177''45'irrelevant_172 = erased
-- Relation.Binary.Construct.Add.Extrema.Strict._._._≤⁺_
d__'8804''8314'__184 a0 a1 a2 a3 a4 a5 a6 a7 = ()
-- Relation.Binary.Construct.Add.Extrema.Strict._.<±-transʳ
d_'60''177''45'trans'691'_238 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  Maybe (Maybe AgdaAny) ->
  Maybe (Maybe AgdaAny) ->
  Maybe (Maybe AgdaAny) ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.NonStrict.T__'8804''8314'__20 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.T__'60''8314'__20 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.T__'60''8314'__20
d_'60''177''45'trans'691'_238 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_'60''177''45'trans'691'_238
du_'60''177''45'trans'691'_238 ::
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  Maybe (Maybe AgdaAny) ->
  Maybe (Maybe AgdaAny) ->
  Maybe (Maybe AgdaAny) ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.NonStrict.T__'8804''8314'__20 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.T__'60''8314'__20 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.T__'60''8314'__20
du_'60''177''45'trans'691'_238
  = coe
      MAlonzo.Code.Function.Base.du__'8728''8242'__216
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.du_'60''8314''45'trans'691'_154)
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Add.Infimum.Strict.du_'60''8331''45'trans'691'_154)
-- Relation.Binary.Construct.Add.Extrema.Strict._.<±-transˡ
d_'60''177''45'trans'737'_240 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  Maybe (Maybe AgdaAny) ->
  Maybe (Maybe AgdaAny) ->
  Maybe (Maybe AgdaAny) ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.T__'60''8314'__20 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.NonStrict.T__'8804''8314'__20 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.T__'60''8314'__20
d_'60''177''45'trans'737'_240 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_'60''177''45'trans'737'_240
du_'60''177''45'trans'737'_240 ::
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  Maybe (Maybe AgdaAny) ->
  Maybe (Maybe AgdaAny) ->
  Maybe (Maybe AgdaAny) ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.T__'60''8314'__20 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.NonStrict.T__'8804''8314'__20 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.T__'60''8314'__20
du_'60''177''45'trans'737'_240
  = coe
      MAlonzo.Code.Function.Base.du__'8728''8242'__216
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.du_'60''8314''45'trans'737'_168)
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Add.Infimum.Strict.du_'60''8331''45'trans'737'_170)
-- Relation.Binary.Construct.Add.Extrema.Strict.<±-cmp-≡
d_'60''177''45'cmp'45''8801'_242 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny ->
   AgdaAny -> MAlonzo.Code.Relation.Binary.Definitions.T_Tri_158) ->
  Maybe (Maybe AgdaAny) ->
  Maybe (Maybe AgdaAny) ->
  MAlonzo.Code.Relation.Binary.Definitions.T_Tri_158
d_'60''177''45'cmp'45''8801'_242 ~v0 ~v1 ~v2 ~v3
  = du_'60''177''45'cmp'45''8801'_242
du_'60''177''45'cmp'45''8801'_242 ::
  (AgdaAny ->
   AgdaAny -> MAlonzo.Code.Relation.Binary.Definitions.T_Tri_158) ->
  Maybe (Maybe AgdaAny) ->
  Maybe (Maybe AgdaAny) ->
  MAlonzo.Code.Relation.Binary.Definitions.T_Tri_158
du_'60''177''45'cmp'45''8801'_242
  = coe
      MAlonzo.Code.Function.Base.du__'8728''8242'__216
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.du_'60''8314''45'cmp'45''8801'_184)
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Add.Infimum.Strict.du_'60''8331''45'cmp'45''8801'_208)
-- Relation.Binary.Construct.Add.Extrema.Strict.<±-irrefl-≡
d_'60''177''45'irrefl'45''8801'_244 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  Maybe (Maybe AgdaAny) ->
  Maybe (Maybe AgdaAny) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.T__'60''8314'__20 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'60''177''45'irrefl'45''8801'_244 = erased
-- Relation.Binary.Construct.Add.Extrema.Strict.<±-respˡ-≡
d_'60''177''45'resp'737''45''8801'_246 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  Maybe (Maybe AgdaAny) ->
  Maybe (Maybe AgdaAny) ->
  Maybe (Maybe AgdaAny) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.T__'60''8314'__20 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.T__'60''8314'__20
d_'60''177''45'resp'737''45''8801'_246 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6
                                       ~v7 v8
  = du_'60''177''45'resp'737''45''8801'_246 v8
du_'60''177''45'resp'737''45''8801'_246 ::
  MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.T__'60''8314'__20 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.T__'60''8314'__20
du_'60''177''45'resp'737''45''8801'_246 v0 = coe v0
-- Relation.Binary.Construct.Add.Extrema.Strict.<±-respʳ-≡
d_'60''177''45'resp'691''45''8801'_248 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  Maybe (Maybe AgdaAny) ->
  Maybe (Maybe AgdaAny) ->
  Maybe (Maybe AgdaAny) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.T__'60''8314'__20 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.T__'60''8314'__20
d_'60''177''45'resp'691''45''8801'_248 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6
                                       ~v7 v8
  = du_'60''177''45'resp'691''45''8801'_248 v8
du_'60''177''45'resp'691''45''8801'_248 ::
  MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.T__'60''8314'__20 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.T__'60''8314'__20
du_'60''177''45'resp'691''45''8801'_248 v0 = coe v0
-- Relation.Binary.Construct.Add.Extrema.Strict.<±-resp-≡
d_'60''177''45'resp'45''8801'_250 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'60''177''45'resp'45''8801'_250 ~v0 ~v1 ~v2 ~v3
  = du_'60''177''45'resp'45''8801'_250
du_'60''177''45'resp'45''8801'_250 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'60''177''45'resp'45''8801'_250
  = coe
      MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.du_'60''8314''45'resp'45''8801'_254
-- Relation.Binary.Construct.Add.Extrema.Strict._._._≈∙_
d__'8776''8729'__262 a0 a1 a2 a3 a4 a5 a6 a7 = ()
-- Relation.Binary.Construct.Add.Extrema.Strict._.<±-cmp
d_'60''177''45'cmp_288 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny ->
   AgdaAny -> MAlonzo.Code.Relation.Binary.Definitions.T_Tri_158) ->
  Maybe (Maybe AgdaAny) ->
  Maybe (Maybe AgdaAny) ->
  MAlonzo.Code.Relation.Binary.Definitions.T_Tri_158
d_'60''177''45'cmp_288 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_'60''177''45'cmp_288
du_'60''177''45'cmp_288 ::
  (AgdaAny ->
   AgdaAny -> MAlonzo.Code.Relation.Binary.Definitions.T_Tri_158) ->
  Maybe (Maybe AgdaAny) ->
  Maybe (Maybe AgdaAny) ->
  MAlonzo.Code.Relation.Binary.Definitions.T_Tri_158
du_'60''177''45'cmp_288
  = coe
      MAlonzo.Code.Function.Base.du__'8728''8242'__216
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.du_'60''8314''45'cmp_284)
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Add.Infimum.Strict.du_'60''8331''45'cmp_312)
-- Relation.Binary.Construct.Add.Extrema.Strict._.<±-irrefl
d_'60''177''45'irrefl_290 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny ->
   AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  Maybe (Maybe AgdaAny) ->
  Maybe (Maybe AgdaAny) ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Point.Equality.T__'8776''8729'__20 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.T__'60''8314'__20 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_'60''177''45'irrefl_290 = erased
-- Relation.Binary.Construct.Add.Extrema.Strict._.<±-respˡ-≈±
d_'60''177''45'resp'737''45''8776''177'_292 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  Maybe (Maybe AgdaAny) ->
  Maybe (Maybe AgdaAny) ->
  Maybe (Maybe AgdaAny) ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Point.Equality.T__'8776''8729'__20 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.T__'60''8314'__20 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.T__'60''8314'__20
d_'60''177''45'resp'737''45''8776''177'_292 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_'60''177''45'resp'737''45''8776''177'_292
du_'60''177''45'resp'737''45''8776''177'_292 ::
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  Maybe (Maybe AgdaAny) ->
  Maybe (Maybe AgdaAny) ->
  Maybe (Maybe AgdaAny) ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Point.Equality.T__'8776''8729'__20 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.T__'60''8314'__20 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.T__'60''8314'__20
du_'60''177''45'resp'737''45''8776''177'_292
  = coe
      MAlonzo.Code.Function.Base.du__'8728''8242'__216
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.du_'60''8314''45'resp'737''45''8776''8314'_350)
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Add.Infimum.Strict.du_'60''8331''45'resp'737''45''8776''8331'_378)
-- Relation.Binary.Construct.Add.Extrema.Strict._.<±-respʳ-≈±
d_'60''177''45'resp'691''45''8776''177'_294 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  Maybe (Maybe AgdaAny) ->
  Maybe (Maybe AgdaAny) ->
  Maybe (Maybe AgdaAny) ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Point.Equality.T__'8776''8729'__20 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.T__'60''8314'__20 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.T__'60''8314'__20
d_'60''177''45'resp'691''45''8776''177'_294 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_'60''177''45'resp'691''45''8776''177'_294
du_'60''177''45'resp'691''45''8776''177'_294 ::
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  Maybe (Maybe AgdaAny) ->
  Maybe (Maybe AgdaAny) ->
  Maybe (Maybe AgdaAny) ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Point.Equality.T__'8776''8729'__20 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.T__'60''8314'__20 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.T__'60''8314'__20
du_'60''177''45'resp'691''45''8776''177'_294
  = coe
      MAlonzo.Code.Function.Base.du__'8728''8242'__216
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.du_'60''8314''45'resp'691''45''8776''8314'_368)
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Add.Infimum.Strict.du_'60''8331''45'resp'691''45''8776''8331'_390)
-- Relation.Binary.Construct.Add.Extrema.Strict._.<±-resp-≈±
d_'60''177''45'resp'45''8776''177'_296 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'60''177''45'resp'45''8776''177'_296 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_'60''177''45'resp'45''8776''177'_296
du_'60''177''45'resp'45''8776''177'_296 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'60''177''45'resp'45''8776''177'_296
  = coe
      MAlonzo.Code.Function.Base.du__'8728''8242'__216
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.du_'60''8314''45'resp'45''8776''8314'_380)
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Add.Infimum.Strict.du_'60''8331''45'resp'45''8776''8331'_408)
-- Relation.Binary.Construct.Add.Extrema.Strict.<±-isStrictPartialOrder-≡
d_'60''177''45'isStrictPartialOrder'45''8801'_298 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsStrictPartialOrder_370 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsStrictPartialOrder_370
d_'60''177''45'isStrictPartialOrder'45''8801'_298 ~v0 ~v1 ~v2 ~v3
  = du_'60''177''45'isStrictPartialOrder'45''8801'_298
du_'60''177''45'isStrictPartialOrder'45''8801'_298 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsStrictPartialOrder_370 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsStrictPartialOrder_370
du_'60''177''45'isStrictPartialOrder'45''8801'_298
  = coe
      MAlonzo.Code.Function.Base.du__'8728''8242'__216
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.du_'60''8314''45'isStrictPartialOrder'45''8801'_382)
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Add.Infimum.Strict.du_'60''8331''45'isStrictPartialOrder'45''8801'_410)
-- Relation.Binary.Construct.Add.Extrema.Strict.<±-isDecStrictPartialOrder-≡
d_'60''177''45'isDecStrictPartialOrder'45''8801'_300 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecStrictPartialOrder_418 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecStrictPartialOrder_418
d_'60''177''45'isDecStrictPartialOrder'45''8801'_300 ~v0 ~v1 ~v2
                                                     ~v3
  = du_'60''177''45'isDecStrictPartialOrder'45''8801'_300
du_'60''177''45'isDecStrictPartialOrder'45''8801'_300 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecStrictPartialOrder_418 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecStrictPartialOrder_418
du_'60''177''45'isDecStrictPartialOrder'45''8801'_300
  = coe
      MAlonzo.Code.Function.Base.du__'8728''8242'__216
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.du_'60''8314''45'isDecStrictPartialOrder'45''8801'_418)
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Add.Infimum.Strict.du_'60''8331''45'isDecStrictPartialOrder'45''8801'_446)
-- Relation.Binary.Construct.Add.Extrema.Strict.<±-isStrictTotalOrder-≡
d_'60''177''45'isStrictTotalOrder'45''8801'_302 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsStrictTotalOrder_624 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsStrictTotalOrder_624
d_'60''177''45'isStrictTotalOrder'45''8801'_302 ~v0 ~v1 ~v2 ~v3
  = du_'60''177''45'isStrictTotalOrder'45''8801'_302
du_'60''177''45'isStrictTotalOrder'45''8801'_302 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsStrictTotalOrder_624 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsStrictTotalOrder_624
du_'60''177''45'isStrictTotalOrder'45''8801'_302
  = coe
      MAlonzo.Code.Function.Base.du__'8728''8242'__216
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.du_'60''8314''45'isStrictTotalOrder'45''8801'_466)
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Add.Infimum.Strict.du_'60''8331''45'isStrictTotalOrder'45''8801'_494)
-- Relation.Binary.Construct.Add.Extrema.Strict._._._≈∙_
d__'8776''8729'__314 a0 a1 a2 a3 a4 a5 a6 a7 = ()
-- Relation.Binary.Construct.Add.Extrema.Strict._.<±-isStrictPartialOrder
d_'60''177''45'isStrictPartialOrder_340 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsStrictPartialOrder_370 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsStrictPartialOrder_370
d_'60''177''45'isStrictPartialOrder_340 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_'60''177''45'isStrictPartialOrder_340
du_'60''177''45'isStrictPartialOrder_340 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsStrictPartialOrder_370 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsStrictPartialOrder_370
du_'60''177''45'isStrictPartialOrder_340
  = coe
      MAlonzo.Code.Function.Base.du__'8728''8242'__216
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.du_'60''8314''45'isStrictPartialOrder_548)
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Add.Infimum.Strict.du_'60''8331''45'isStrictPartialOrder_580)
-- Relation.Binary.Construct.Add.Extrema.Strict._.<±-isDecStrictPartialOrder
d_'60''177''45'isDecStrictPartialOrder_342 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecStrictPartialOrder_418 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecStrictPartialOrder_418
d_'60''177''45'isDecStrictPartialOrder_342 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_'60''177''45'isDecStrictPartialOrder_342
du_'60''177''45'isDecStrictPartialOrder_342 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecStrictPartialOrder_418 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecStrictPartialOrder_418
du_'60''177''45'isDecStrictPartialOrder_342
  = coe
      MAlonzo.Code.Function.Base.du__'8728''8242'__216
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.du_'60''8314''45'isDecStrictPartialOrder_584)
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Add.Infimum.Strict.du_'60''8331''45'isDecStrictPartialOrder_616)
-- Relation.Binary.Construct.Add.Extrema.Strict._.<±-isStrictTotalOrder
d_'60''177''45'isStrictTotalOrder_344 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsStrictTotalOrder_624 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsStrictTotalOrder_624
d_'60''177''45'isStrictTotalOrder_344 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_'60''177''45'isStrictTotalOrder_344
du_'60''177''45'isStrictTotalOrder_344 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsStrictTotalOrder_624 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsStrictTotalOrder_624
du_'60''177''45'isStrictTotalOrder_344
  = coe
      MAlonzo.Code.Function.Base.du__'8728''8242'__216
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.du_'60''8314''45'isStrictTotalOrder_632)
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Add.Infimum.Strict.du_'60''8331''45'isStrictTotalOrder_664)
