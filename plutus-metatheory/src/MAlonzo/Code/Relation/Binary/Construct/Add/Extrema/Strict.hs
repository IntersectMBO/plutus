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

module MAlonzo.Code.Relation.Binary.Construct.Add.Extrema.Strict where

import Data.Text qualified
import MAlonzo.Code.Agda.Builtin.Equality qualified
import MAlonzo.Code.Agda.Builtin.Sigma qualified
import MAlonzo.Code.Agda.Primitive qualified
import MAlonzo.Code.Data.Irrelevant qualified
import MAlonzo.Code.Function.Base qualified
import MAlonzo.Code.Relation.Binary.Construct.Add.Infimum.NonStrict qualified
import MAlonzo.Code.Relation.Binary.Construct.Add.Infimum.Strict qualified
import MAlonzo.Code.Relation.Binary.Construct.Add.Point.Equality qualified
import MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.NonStrict qualified
import MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict qualified
import MAlonzo.Code.Relation.Binary.Definitions qualified
import MAlonzo.Code.Relation.Binary.Structures qualified
import MAlonzo.Code.Relation.Nullary.Decidable.Core qualified
import MAlonzo.RTE (AgdaAny, add64, addInt, coe, eq64, eqInt, erased, geqInt, lt64, ltInt, mul64,
                    mulInt, quot64, quotInt, rem64, remInt, sub64, subInt, word64FromNat,
                    word64ToNat)
import MAlonzo.RTE qualified

-- Relation.Binary.Construct.Add.Extrema.Strict.Inf._<₋_
d__'60''8331'__22 a0 a1 a2 a3 a4 a5 = ()
-- Relation.Binary.Construct.Add.Extrema.Strict.Sup._<⁺_
d__'60''8314'__82 a0 a1 a2 a3 a4 a5 = ()
-- Relation.Binary.Construct.Add.Extrema.Strict.[<]-injective
d_'91''60''93''45'injective_158 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.T__'60''8314'__20 ->
  AgdaAny
d_'91''60''93''45'injective_158 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_'91''60''93''45'injective_158
du_'91''60''93''45'injective_158 ::
  MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.T__'60''8314'__20 ->
  AgdaAny
du_'91''60''93''45'injective_158
  = coe
      MAlonzo.Code.Function.Base.du__'8728''8242'__216
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Add.Infimum.Strict.du_'91''60''93''45'injective_36)
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.du_'91''60''93''45'injective_36)
-- Relation.Binary.Construct.Add.Extrema.Strict.<±-asym
d_'60''177''45'asym_160 ::
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
d_'60''177''45'asym_160 = erased
-- Relation.Binary.Construct.Add.Extrema.Strict.<±-trans
d_'60''177''45'trans_162 ::
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
d_'60''177''45'trans_162 ~v0 ~v1 ~v2 ~v3
  = du_'60''177''45'trans_162
du_'60''177''45'trans_162 ::
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  Maybe (Maybe AgdaAny) ->
  Maybe (Maybe AgdaAny) ->
  Maybe (Maybe AgdaAny) ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.T__'60''8314'__20 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.T__'60''8314'__20 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.T__'60''8314'__20
du_'60''177''45'trans_162
  = coe
      MAlonzo.Code.Function.Base.du__'8728''8242'__216
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.du_'60''8314''45'trans_48)
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Add.Infimum.Strict.du_'60''8331''45'trans_48)
-- Relation.Binary.Construct.Add.Extrema.Strict.<±-dec
d_'60''177''45'dec_164 ::
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
d_'60''177''45'dec_164 ~v0 ~v1 ~v2 ~v3 = du_'60''177''45'dec_164
du_'60''177''45'dec_164 ::
  (AgdaAny ->
   AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  Maybe (Maybe AgdaAny) ->
  Maybe (Maybe AgdaAny) ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du_'60''177''45'dec_164
  = coe
      MAlonzo.Code.Function.Base.du__'8728''8242'__216
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.du_'60''8314''45'dec_62)
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Add.Infimum.Strict.du_'60''8331''45'dec_62)
-- Relation.Binary.Construct.Add.Extrema.Strict.<±-irrelevant
d_'60''177''45'irrelevant_166 ::
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
d_'60''177''45'irrelevant_166 = erased
-- Relation.Binary.Construct.Add.Extrema.Strict._._._≤⁺_
d__'8804''8314'__178 a0 a1 a2 a3 a4 a5 a6 a7 = ()
-- Relation.Binary.Construct.Add.Extrema.Strict._.<±-transʳ
d_'60''177''45'trans'691'_232 ::
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
d_'60''177''45'trans'691'_232 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_'60''177''45'trans'691'_232
du_'60''177''45'trans'691'_232 ::
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  Maybe (Maybe AgdaAny) ->
  Maybe (Maybe AgdaAny) ->
  Maybe (Maybe AgdaAny) ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.NonStrict.T__'8804''8314'__20 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.T__'60''8314'__20 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.T__'60''8314'__20
du_'60''177''45'trans'691'_232
  = coe
      MAlonzo.Code.Function.Base.du__'8728''8242'__216
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.du_'60''8314''45'trans'691'_154)
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Add.Infimum.Strict.du_'60''8331''45'trans'691'_154)
-- Relation.Binary.Construct.Add.Extrema.Strict._.<±-transˡ
d_'60''177''45'trans'737'_234 ::
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
d_'60''177''45'trans'737'_234 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_'60''177''45'trans'737'_234
du_'60''177''45'trans'737'_234 ::
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  Maybe (Maybe AgdaAny) ->
  Maybe (Maybe AgdaAny) ->
  Maybe (Maybe AgdaAny) ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.T__'60''8314'__20 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.NonStrict.T__'8804''8314'__20 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.T__'60''8314'__20
du_'60''177''45'trans'737'_234
  = coe
      MAlonzo.Code.Function.Base.du__'8728''8242'__216
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.du_'60''8314''45'trans'737'_168)
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Add.Infimum.Strict.du_'60''8331''45'trans'737'_172)
-- Relation.Binary.Construct.Add.Extrema.Strict.<±-cmp-≡
d_'60''177''45'cmp'45''8801'_236 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny ->
   AgdaAny -> MAlonzo.Code.Relation.Binary.Definitions.T_Tri_158) ->
  Maybe (Maybe AgdaAny) ->
  Maybe (Maybe AgdaAny) ->
  MAlonzo.Code.Relation.Binary.Definitions.T_Tri_158
d_'60''177''45'cmp'45''8801'_236 ~v0 ~v1 ~v2 ~v3
  = du_'60''177''45'cmp'45''8801'_236
du_'60''177''45'cmp'45''8801'_236 ::
  (AgdaAny ->
   AgdaAny -> MAlonzo.Code.Relation.Binary.Definitions.T_Tri_158) ->
  Maybe (Maybe AgdaAny) ->
  Maybe (Maybe AgdaAny) ->
  MAlonzo.Code.Relation.Binary.Definitions.T_Tri_158
du_'60''177''45'cmp'45''8801'_236
  = coe
      MAlonzo.Code.Function.Base.du__'8728''8242'__216
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.du_'60''8314''45'cmp'45''8801'_184)
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Add.Infimum.Strict.du_'60''8331''45'cmp'45''8801'_186)
-- Relation.Binary.Construct.Add.Extrema.Strict.<±-irrefl-≡
d_'60''177''45'irrefl'45''8801'_238 ::
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
d_'60''177''45'irrefl'45''8801'_238 = erased
-- Relation.Binary.Construct.Add.Extrema.Strict.<±-respˡ-≡
d_'60''177''45'resp'737''45''8801'_240 ::
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
d_'60''177''45'resp'737''45''8801'_240 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6
                                       ~v7 v8
  = du_'60''177''45'resp'737''45''8801'_240 v8
du_'60''177''45'resp'737''45''8801'_240 ::
  MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.T__'60''8314'__20 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.T__'60''8314'__20
du_'60''177''45'resp'737''45''8801'_240 v0 = coe v0
-- Relation.Binary.Construct.Add.Extrema.Strict.<±-respʳ-≡
d_'60''177''45'resp'691''45''8801'_242 ::
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
d_'60''177''45'resp'691''45''8801'_242 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6
                                       ~v7 v8
  = du_'60''177''45'resp'691''45''8801'_242 v8
du_'60''177''45'resp'691''45''8801'_242 ::
  MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.T__'60''8314'__20 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.T__'60''8314'__20
du_'60''177''45'resp'691''45''8801'_242 v0 = coe v0
-- Relation.Binary.Construct.Add.Extrema.Strict.<±-resp-≡
d_'60''177''45'resp'45''8801'_244 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'60''177''45'resp'45''8801'_244 ~v0 ~v1 ~v2 ~v3
  = du_'60''177''45'resp'45''8801'_244
du_'60''177''45'resp'45''8801'_244 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'60''177''45'resp'45''8801'_244
  = coe
      MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.du_'60''8314''45'resp'45''8801'_254
-- Relation.Binary.Construct.Add.Extrema.Strict._._._≈∙_
d__'8776''8729'__256 a0 a1 a2 a3 a4 a5 a6 a7 = ()
-- Relation.Binary.Construct.Add.Extrema.Strict._.<±-cmp
d_'60''177''45'cmp_282 ::
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
d_'60''177''45'cmp_282 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_'60''177''45'cmp_282
du_'60''177''45'cmp_282 ::
  (AgdaAny ->
   AgdaAny -> MAlonzo.Code.Relation.Binary.Definitions.T_Tri_158) ->
  Maybe (Maybe AgdaAny) ->
  Maybe (Maybe AgdaAny) ->
  MAlonzo.Code.Relation.Binary.Definitions.T_Tri_158
du_'60''177''45'cmp_282
  = coe
      MAlonzo.Code.Function.Base.du__'8728''8242'__216
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.du_'60''8314''45'cmp_296)
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Add.Infimum.Strict.du_'60''8331''45'cmp_298)
-- Relation.Binary.Construct.Add.Extrema.Strict._.<±-irrefl
d_'60''177''45'irrefl_284 ::
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
d_'60''177''45'irrefl_284 = erased
-- Relation.Binary.Construct.Add.Extrema.Strict._.<±-respˡ-≈±
d_'60''177''45'resp'737''45''8776''177'_286 ::
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
d_'60''177''45'resp'737''45''8776''177'_286 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_'60''177''45'resp'737''45''8776''177'_286
du_'60''177''45'resp'737''45''8776''177'_286 ::
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  Maybe (Maybe AgdaAny) ->
  Maybe (Maybe AgdaAny) ->
  Maybe (Maybe AgdaAny) ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Point.Equality.T__'8776''8729'__20 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.T__'60''8314'__20 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.T__'60''8314'__20
du_'60''177''45'resp'737''45''8776''177'_286
  = coe
      MAlonzo.Code.Function.Base.du__'8728''8242'__216
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.du_'60''8314''45'resp'737''45''8776''8314'_362)
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Add.Infimum.Strict.du_'60''8331''45'resp'737''45''8776''8331'_364)
-- Relation.Binary.Construct.Add.Extrema.Strict._.<±-respʳ-≈±
d_'60''177''45'resp'691''45''8776''177'_288 ::
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
d_'60''177''45'resp'691''45''8776''177'_288 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_'60''177''45'resp'691''45''8776''177'_288
du_'60''177''45'resp'691''45''8776''177'_288 ::
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  Maybe (Maybe AgdaAny) ->
  Maybe (Maybe AgdaAny) ->
  Maybe (Maybe AgdaAny) ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Point.Equality.T__'8776''8729'__20 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.T__'60''8314'__20 ->
  MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.T__'60''8314'__20
du_'60''177''45'resp'691''45''8776''177'_288
  = coe
      MAlonzo.Code.Function.Base.du__'8728''8242'__216
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.du_'60''8314''45'resp'691''45''8776''8314'_380)
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Add.Infimum.Strict.du_'60''8331''45'resp'691''45''8776''8331'_376)
-- Relation.Binary.Construct.Add.Extrema.Strict._.<±-resp-≈±
d_'60''177''45'resp'45''8776''177'_290 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'60''177''45'resp'45''8776''177'_290 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_'60''177''45'resp'45''8776''177'_290
du_'60''177''45'resp'45''8776''177'_290 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'60''177''45'resp'45''8776''177'_290
  = coe
      MAlonzo.Code.Function.Base.du__'8728''8242'__216
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.du_'60''8314''45'resp'45''8776''8314'_392)
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Add.Infimum.Strict.du_'60''8331''45'resp'45''8776''8331'_394)
-- Relation.Binary.Construct.Add.Extrema.Strict.<±-isStrictPartialOrder-≡
d_'60''177''45'isStrictPartialOrder'45''8801'_292 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsStrictPartialOrder_290 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsStrictPartialOrder_290
d_'60''177''45'isStrictPartialOrder'45''8801'_292 ~v0 ~v1 ~v2 ~v3
  = du_'60''177''45'isStrictPartialOrder'45''8801'_292
du_'60''177''45'isStrictPartialOrder'45''8801'_292 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsStrictPartialOrder_290 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsStrictPartialOrder_290
du_'60''177''45'isStrictPartialOrder'45''8801'_292
  = coe
      MAlonzo.Code.Function.Base.du__'8728''8242'__216
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.du_'60''8314''45'isStrictPartialOrder'45''8801'_394)
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Add.Infimum.Strict.du_'60''8331''45'isStrictPartialOrder'45''8801'_396)
-- Relation.Binary.Construct.Add.Extrema.Strict.<±-isDecStrictPartialOrder-≡
d_'60''177''45'isDecStrictPartialOrder'45''8801'_294 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecStrictPartialOrder_336 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecStrictPartialOrder_336
d_'60''177''45'isDecStrictPartialOrder'45''8801'_294 ~v0 ~v1 ~v2
                                                     ~v3
  = du_'60''177''45'isDecStrictPartialOrder'45''8801'_294
du_'60''177''45'isDecStrictPartialOrder'45''8801'_294 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecStrictPartialOrder_336 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecStrictPartialOrder_336
du_'60''177''45'isDecStrictPartialOrder'45''8801'_294
  = coe
      MAlonzo.Code.Function.Base.du__'8728''8242'__216
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.du_'60''8314''45'isDecStrictPartialOrder'45''8801'_430)
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Add.Infimum.Strict.du_'60''8331''45'isDecStrictPartialOrder'45''8801'_432)
-- Relation.Binary.Construct.Add.Extrema.Strict.<±-isStrictTotalOrder-≡
d_'60''177''45'isStrictTotalOrder'45''8801'_296 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsStrictTotalOrder_534 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsStrictTotalOrder_534
d_'60''177''45'isStrictTotalOrder'45''8801'_296 ~v0 ~v1 ~v2 ~v3
  = du_'60''177''45'isStrictTotalOrder'45''8801'_296
du_'60''177''45'isStrictTotalOrder'45''8801'_296 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsStrictTotalOrder_534 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsStrictTotalOrder_534
du_'60''177''45'isStrictTotalOrder'45''8801'_296
  = coe
      MAlonzo.Code.Function.Base.du__'8728''8242'__216
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.du_'60''8314''45'isStrictTotalOrder'45''8801'_478)
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Add.Infimum.Strict.du_'60''8331''45'isStrictTotalOrder'45''8801'_480)
-- Relation.Binary.Construct.Add.Extrema.Strict._._._≈∙_
d__'8776''8729'__308 a0 a1 a2 a3 a4 a5 a6 a7 = ()
-- Relation.Binary.Construct.Add.Extrema.Strict._.<±-isStrictPartialOrder
d_'60''177''45'isStrictPartialOrder_334 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsStrictPartialOrder_290 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsStrictPartialOrder_290
d_'60''177''45'isStrictPartialOrder_334 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_'60''177''45'isStrictPartialOrder_334
du_'60''177''45'isStrictPartialOrder_334 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsStrictPartialOrder_290 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsStrictPartialOrder_290
du_'60''177''45'isStrictPartialOrder_334
  = coe
      MAlonzo.Code.Function.Base.du__'8728''8242'__216
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.du_'60''8314''45'isStrictPartialOrder_572)
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Add.Infimum.Strict.du_'60''8331''45'isStrictPartialOrder_574)
-- Relation.Binary.Construct.Add.Extrema.Strict._.<±-isDecStrictPartialOrder
d_'60''177''45'isDecStrictPartialOrder_336 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecStrictPartialOrder_336 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecStrictPartialOrder_336
d_'60''177''45'isDecStrictPartialOrder_336 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_'60''177''45'isDecStrictPartialOrder_336
du_'60''177''45'isDecStrictPartialOrder_336 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecStrictPartialOrder_336 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsDecStrictPartialOrder_336
du_'60''177''45'isDecStrictPartialOrder_336
  = coe
      MAlonzo.Code.Function.Base.du__'8728''8242'__216
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.du_'60''8314''45'isDecStrictPartialOrder_608)
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Add.Infimum.Strict.du_'60''8331''45'isDecStrictPartialOrder_610)
-- Relation.Binary.Construct.Add.Extrema.Strict._.<±-isStrictTotalOrder
d_'60''177''45'isStrictTotalOrder_338 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsStrictTotalOrder_534 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsStrictTotalOrder_534
d_'60''177''45'isStrictTotalOrder_338 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_'60''177''45'isStrictTotalOrder_338
du_'60''177''45'isStrictTotalOrder_338 ::
  MAlonzo.Code.Relation.Binary.Structures.T_IsStrictTotalOrder_534 ->
  MAlonzo.Code.Relation.Binary.Structures.T_IsStrictTotalOrder_534
du_'60''177''45'isStrictTotalOrder_338
  = coe
      MAlonzo.Code.Function.Base.du__'8728''8242'__216
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Add.Supremum.Strict.du_'60''8314''45'isStrictTotalOrder_656)
      (coe
         MAlonzo.Code.Relation.Binary.Construct.Add.Infimum.Strict.du_'60''8331''45'isStrictTotalOrder_658)
