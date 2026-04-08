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

module MAlonzo.Code.Data.Vec.Base where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Data.Bool.Base
import qualified MAlonzo.Code.Data.Fin.Base
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Data.Product.Base
import qualified MAlonzo.Code.Data.These.Base
import qualified MAlonzo.Code.Function.Base
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core

-- Data.Vec.Base.Vec
d_Vec_28 a0 a1 a2 = ()
data T_Vec_28 = C_'91''93'_32 | C__'8759'__38 AgdaAny T_Vec_28
-- Data.Vec.Base._[_]=_
d__'91'_'93''61'__44 a0 a1 a2 a3 a4 a5 = ()
data T__'91'_'93''61'__44
  = C_here_52 | C_there_64 T__'91'_'93''61'__44
-- Data.Vec.Base.length
d_length_66 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> Integer -> T_Vec_28 -> Integer
d_length_66 ~v0 ~v1 v2 ~v3 = du_length_66 v2
du_length_66 :: Integer -> Integer
du_length_66 v0 = coe v0
-- Data.Vec.Base.head
d_head_70 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> Integer -> T_Vec_28 -> AgdaAny
d_head_70 ~v0 ~v1 ~v2 v3 = du_head_70 v3
du_head_70 :: T_Vec_28 -> AgdaAny
du_head_70 v0
  = case coe v0 of
      C__'8759'__38 v2 v3 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Vec.Base.tail
d_tail_76 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> Integer -> T_Vec_28 -> T_Vec_28
d_tail_76 ~v0 ~v1 ~v2 v3 = du_tail_76 v3
du_tail_76 :: T_Vec_28 -> T_Vec_28
du_tail_76 v0
  = case coe v0 of
      C__'8759'__38 v2 v3 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Vec.Base.lookup
d_lookup_82 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  Integer ->
  T_Vec_28 -> MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> AgdaAny
d_lookup_82 ~v0 ~v1 ~v2 v3 v4 = du_lookup_82 v3 v4
du_lookup_82 ::
  T_Vec_28 -> MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> AgdaAny
du_lookup_82 v0 v1
  = case coe v0 of
      C__'8759'__38 v3 v4
        -> case coe v1 of
             MAlonzo.Code.Data.Fin.Base.C_zero_12 -> coe v3
             MAlonzo.Code.Data.Fin.Base.C_suc_16 v6
               -> coe du_lookup_82 (coe v4) (coe v6)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Vec.Base.iterate
d_iterate_96 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> (AgdaAny -> AgdaAny) -> AgdaAny -> Integer -> T_Vec_28
d_iterate_96 ~v0 ~v1 v2 v3 v4 = du_iterate_96 v2 v3 v4
du_iterate_96 ::
  (AgdaAny -> AgdaAny) -> AgdaAny -> Integer -> T_Vec_28
du_iterate_96 v0 v1 v2
  = case coe v2 of
      0 -> coe C_'91''93'_32
      _ -> let v3 = subInt (coe v2) (coe (1 :: Integer)) in
           coe
             (coe
                C__'8759'__38 v1 (coe du_iterate_96 (coe v0) (coe v0 v1) (coe v3)))
-- Data.Vec.Base.insertAt
d_insertAt_108 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  Integer ->
  T_Vec_28 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> AgdaAny -> T_Vec_28
d_insertAt_108 ~v0 ~v1 ~v2 v3 v4 v5 = du_insertAt_108 v3 v4 v5
du_insertAt_108 ::
  T_Vec_28 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> AgdaAny -> T_Vec_28
du_insertAt_108 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Data.Fin.Base.C_zero_12 -> coe C__'8759'__38 v2 v0
      MAlonzo.Code.Data.Fin.Base.C_suc_16 v4
        -> case coe v0 of
             C__'8759'__38 v6 v7
               -> coe
                    C__'8759'__38 v6 (coe du_insertAt_108 (coe v7) (coe v4) (coe v2))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Vec.Base.removeAt
d_removeAt_122 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  Integer ->
  T_Vec_28 -> MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> T_Vec_28
d_removeAt_122 ~v0 ~v1 ~v2 v3 v4 = du_removeAt_122 v3 v4
du_removeAt_122 ::
  T_Vec_28 -> MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> T_Vec_28
du_removeAt_122 v0 v1
  = case coe v0 of
      C__'8759'__38 v3 v4
        -> case coe v1 of
             MAlonzo.Code.Data.Fin.Base.C_zero_12 -> coe v4
             MAlonzo.Code.Data.Fin.Base.C_suc_16 v6
               -> case coe v4 of
                    C__'8759'__38 v8 v9
                      -> coe
                           C__'8759'__38 v3
                           (coe du_removeAt_122 (coe C__'8759'__38 v8 v9) (coe v6))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Vec.Base.updateAt
d_updateAt_134 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  Integer ->
  T_Vec_28 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  (AgdaAny -> AgdaAny) -> T_Vec_28
d_updateAt_134 ~v0 ~v1 ~v2 v3 v4 v5 = du_updateAt_134 v3 v4 v5
du_updateAt_134 ::
  T_Vec_28 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  (AgdaAny -> AgdaAny) -> T_Vec_28
du_updateAt_134 v0 v1 v2
  = case coe v0 of
      C__'8759'__38 v4 v5
        -> case coe v1 of
             MAlonzo.Code.Data.Fin.Base.C_zero_12
               -> coe C__'8759'__38 (coe v2 v4) v5
             MAlonzo.Code.Data.Fin.Base.C_suc_16 v7
               -> coe
                    C__'8759'__38 v4 (coe du_updateAt_134 (coe v5) (coe v7) (coe v2))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Vec.Base._[_]%=_
d__'91'_'93''37''61'__150 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  Integer ->
  T_Vec_28 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  (AgdaAny -> AgdaAny) -> T_Vec_28
d__'91'_'93''37''61'__150 ~v0 ~v1 ~v2 v3 v4 v5
  = du__'91'_'93''37''61'__150 v3 v4 v5
du__'91'_'93''37''61'__150 ::
  T_Vec_28 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  (AgdaAny -> AgdaAny) -> T_Vec_28
du__'91'_'93''37''61'__150 v0 v1 v2
  = coe du_updateAt_134 (coe v0) (coe v1) (coe v2)
-- Data.Vec.Base._[_]≔_
d__'91'_'93''8788'__158 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  Integer ->
  T_Vec_28 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> AgdaAny -> T_Vec_28
d__'91'_'93''8788'__158 ~v0 ~v1 ~v2 v3 v4 v5
  = du__'91'_'93''8788'__158 v3 v4 v5
du__'91'_'93''8788'__158 ::
  T_Vec_28 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> AgdaAny -> T_Vec_28
du__'91'_'93''8788'__158 v0 v1 v2
  = coe
      du__'91'_'93''37''61'__150 (coe v0) (coe v1) (coe (\ v3 -> v2))
-- Data.Vec.Base.cast
d_cast_168 ::
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T_Vec_28 -> T_Vec_28
d_cast_168 ~v0 v1 ~v2 ~v3 ~v4 v5 = du_cast_168 v1 v5
du_cast_168 :: Integer -> T_Vec_28 -> T_Vec_28
du_cast_168 v0 v1
  = case coe v0 of
      0 -> coe seq (coe v1) (coe C_'91''93'_32)
      _ -> let v2 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (case coe v1 of
                C__'8759'__38 v4 v5
                  -> coe C__'8759'__38 v4 (coe du_cast_168 (coe v2) (coe v5))
                _ -> MAlonzo.RTE.mazUnreachableError)
-- Data.Vec.Base.map
d_map_178 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> Integer -> (AgdaAny -> AgdaAny) -> T_Vec_28 -> T_Vec_28
d_map_178 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6 = du_map_178 v5 v6
du_map_178 :: (AgdaAny -> AgdaAny) -> T_Vec_28 -> T_Vec_28
du_map_178 v0 v1
  = case coe v1 of
      C_'91''93'_32 -> coe v1
      C__'8759'__38 v3 v4
        -> coe C__'8759'__38 (coe v0 v3) (coe du_map_178 (coe v0) (coe v4))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Vec.Base._++_
d__'43''43'__188 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> Integer -> Integer -> T_Vec_28 -> T_Vec_28 -> T_Vec_28
d__'43''43'__188 ~v0 ~v1 ~v2 ~v3 v4 v5 = du__'43''43'__188 v4 v5
du__'43''43'__188 :: T_Vec_28 -> T_Vec_28 -> T_Vec_28
du__'43''43'__188 v0 v1
  = case coe v0 of
      C_'91''93'_32 -> coe v1
      C__'8759'__38 v3 v4
        -> coe C__'8759'__38 v3 (coe du__'43''43'__188 (coe v4) (coe v1))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Vec.Base.concat
d_concat_198 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> Integer -> Integer -> T_Vec_28 -> T_Vec_28
d_concat_198 ~v0 ~v1 ~v2 ~v3 v4 = du_concat_198 v4
du_concat_198 :: T_Vec_28 -> T_Vec_28
du_concat_198 v0
  = case coe v0 of
      C_'91''93'_32 -> coe v0
      C__'8759'__38 v2 v3
        -> coe du__'43''43'__188 (coe v2) (coe du_concat_198 (coe v3))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Vec.Base.alignWith
d_alignWith_204 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  Integer ->
  Integer ->
  (MAlonzo.Code.Data.These.Base.T_These_38 -> AgdaAny) ->
  T_Vec_28 -> T_Vec_28 -> T_Vec_28
d_alignWith_204 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 v9 v10
  = du_alignWith_204 v8 v9 v10
du_alignWith_204 ::
  (MAlonzo.Code.Data.These.Base.T_These_38 -> AgdaAny) ->
  T_Vec_28 -> T_Vec_28 -> T_Vec_28
du_alignWith_204 v0 v1 v2
  = case coe v1 of
      C_'91''93'_32
        -> coe
             du_map_178
             (coe
                MAlonzo.Code.Function.Base.du__'8728''8242'__216 (coe v0)
                (coe MAlonzo.Code.Data.These.Base.C_that_50))
             (coe v2)
      C__'8759'__38 v4 v5
        -> case coe v2 of
             C_'91''93'_32
               -> coe
                    du_map_178
                    (coe
                       MAlonzo.Code.Function.Base.du__'8728''8242'__216 (coe v0)
                       (coe MAlonzo.Code.Data.These.Base.C_this_48))
                    (coe C__'8759'__38 v4 v5)
             C__'8759'__38 v7 v8
               -> coe
                    C__'8759'__38
                    (coe
                       v0 (coe MAlonzo.Code.Data.These.Base.C_these_52 (coe v4) (coe v7)))
                    (coe du_alignWith_204 (coe v0) (coe v5) (coe v8))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Vec.Base.restrictWith
d_restrictWith_224 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  Integer ->
  Integer ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> T_Vec_28 -> T_Vec_28 -> T_Vec_28
d_restrictWith_224 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 v9 v10
  = du_restrictWith_224 v8 v9 v10
du_restrictWith_224 ::
  (AgdaAny -> AgdaAny -> AgdaAny) -> T_Vec_28 -> T_Vec_28 -> T_Vec_28
du_restrictWith_224 v0 v1 v2
  = case coe v1 of
      C_'91''93'_32 -> coe v1
      C__'8759'__38 v4 v5
        -> case coe v2 of
             C_'91''93'_32 -> coe v2
             C__'8759'__38 v7 v8
               -> coe
                    C__'8759'__38 (coe v0 v4 v7)
                    (coe du_restrictWith_224 (coe v0) (coe v5) (coe v8))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Vec.Base.zipWith
d_zipWith_242 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  Integer ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> T_Vec_28 -> T_Vec_28 -> T_Vec_28
d_zipWith_242 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 v8 v9
  = du_zipWith_242 v7 v8 v9
du_zipWith_242 ::
  (AgdaAny -> AgdaAny -> AgdaAny) -> T_Vec_28 -> T_Vec_28 -> T_Vec_28
du_zipWith_242 v0 v1 v2
  = case coe v1 of
      C_'91''93'_32 -> coe seq (coe v2) (coe v1)
      C__'8759'__38 v4 v5
        -> case coe v2 of
             C__'8759'__38 v7 v8
               -> coe
                    C__'8759'__38 (coe v0 v4 v7)
                    (coe du_zipWith_242 (coe v0) (coe v5) (coe v8))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Vec.Base.unzipWith
d_unzipWith_256 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  Integer ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  T_Vec_28 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_unzipWith_256 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 v8
  = du_unzipWith_256 v7 v8
du_unzipWith_256 ::
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  T_Vec_28 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_unzipWith_256 v0 v1
  = case coe v1 of
      C_'91''93'_32
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1) (coe v1)
      C__'8759'__38 v3 v4
        -> coe
             MAlonzo.Code.Data.Product.Base.du_zip_198 (coe C__'8759'__38)
             (coe (\ v5 v6 -> coe C__'8759'__38)) (coe v0 v3)
             (coe du_unzipWith_256 (coe v0) (coe v4))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Vec.Base.align
d_align_266 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  Integer ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> Integer -> T_Vec_28 -> T_Vec_28 -> T_Vec_28
d_align_266 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 = du_align_266
du_align_266 :: T_Vec_28 -> T_Vec_28 -> T_Vec_28
du_align_266 = coe du_alignWith_204 (coe (\ v0 -> v0))
-- Data.Vec.Base.restrict
d_restrict_268 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  Integer ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> Integer -> T_Vec_28 -> T_Vec_28 -> T_Vec_28
d_restrict_268 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 = du_restrict_268
du_restrict_268 :: T_Vec_28 -> T_Vec_28 -> T_Vec_28
du_restrict_268
  = coe
      du_restrictWith_224
      (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32)
-- Data.Vec.Base.zip
d_zip_270 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  Integer ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> T_Vec_28 -> T_Vec_28 -> T_Vec_28
d_zip_270 ~v0 ~v1 ~v2 ~v3 ~v4 = du_zip_270
du_zip_270 :: T_Vec_28 -> T_Vec_28 -> T_Vec_28
du_zip_270
  = coe
      du_zipWith_242 (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32)
-- Data.Vec.Base.unzip
d_unzip_272 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> Integer -> T_Vec_28 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_unzip_272 ~v0 ~v1 ~v2 ~v3 ~v4 = du_unzip_272
du_unzip_272 :: T_Vec_28 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_unzip_272 = coe du_unzipWith_256 (coe (\ v0 -> v0))
-- Data.Vec.Base._⋎_
d__'8910'__274 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> Integer -> Integer -> T_Vec_28 -> T_Vec_28 -> T_Vec_28
d__'8910'__274 ~v0 ~v1 ~v2 ~v3 v4 v5 = du__'8910'__274 v4 v5
du__'8910'__274 :: T_Vec_28 -> T_Vec_28 -> T_Vec_28
du__'8910'__274 v0 v1
  = case coe v0 of
      C_'91''93'_32 -> coe v1
      C__'8759'__38 v3 v4
        -> coe C__'8759'__38 v3 (coe du__'8910'__274 (coe v1) (coe v4))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Vec.Base._⊛_
d__'8859'__284 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> Integer -> T_Vec_28 -> T_Vec_28 -> T_Vec_28
d__'8859'__284 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6 = du__'8859'__284 v5 v6
du__'8859'__284 :: T_Vec_28 -> T_Vec_28 -> T_Vec_28
du__'8859'__284 v0 v1
  = case coe v0 of
      C_'91''93'_32 -> coe seq (coe v1) (coe v0)
      C__'8759'__38 v3 v4
        -> case coe v1 of
             C__'8759'__38 v6 v7
               -> coe
                    C__'8759'__38 (coe v3 v6) (coe du__'8859'__284 (coe v4) (coe v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Vec.Base.CartesianBind._>>=_
d__'62''62''61'__296 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  Integer ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> Integer -> T_Vec_28 -> (AgdaAny -> T_Vec_28) -> T_Vec_28
d__'62''62''61'__296 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7
  = du__'62''62''61'__296 v6 v7
du__'62''62''61'__296 ::
  T_Vec_28 -> (AgdaAny -> T_Vec_28) -> T_Vec_28
du__'62''62''61'__296 v0 v1
  = coe du_concat_198 (coe du_map_178 (coe v1) (coe v0))
-- Data.Vec.Base._⊛*_
d__'8859''42'__302 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> Integer -> Integer -> T_Vec_28 -> T_Vec_28 -> T_Vec_28
d__'8859''42'__302 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7
  = du__'8859''42'__302 v6 v7
du__'8859''42'__302 :: T_Vec_28 -> T_Vec_28 -> T_Vec_28
du__'8859''42'__302 v0 v1
  = coe
      du__'62''62''61'__296 (coe v0)
      (coe (\ v2 -> coe du_map_178 (coe v2) (coe v1)))
-- Data.Vec.Base.allPairs
d_allPairs_310 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  Integer ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> Integer -> T_Vec_28 -> T_Vec_28 -> T_Vec_28
d_allPairs_310 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7
  = du_allPairs_310 v6 v7
du_allPairs_310 :: T_Vec_28 -> T_Vec_28 -> T_Vec_28
du_allPairs_310 v0 v1
  = coe
      du__'8859''42'__302
      (coe
         du_map_178 (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32)
         (coe v0))
      (coe v1)
-- Data.Vec.Base.diagonal
d_diagonal_316 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> Integer -> T_Vec_28 -> T_Vec_28
d_diagonal_316 ~v0 ~v1 ~v2 v3 = du_diagonal_316 v3
du_diagonal_316 :: T_Vec_28 -> T_Vec_28
du_diagonal_316 v0
  = case coe v0 of
      C_'91''93'_32 -> coe v0
      C__'8759'__38 v2 v3
        -> coe
             C__'8759'__38 (coe du_head_70 (coe v2))
             (coe du_diagonal_316 (coe du_map_178 (coe du_tail_76) (coe v3)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Vec.Base.DiagonalBind._>>=_
d__'62''62''61'__324 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  Integer ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> T_Vec_28 -> (AgdaAny -> T_Vec_28) -> T_Vec_28
d__'62''62''61'__324 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6
  = du__'62''62''61'__324 v5 v6
du__'62''62''61'__324 ::
  T_Vec_28 -> (AgdaAny -> T_Vec_28) -> T_Vec_28
du__'62''62''61'__324 v0 v1
  = coe du_diagonal_316 (coe du_map_178 (coe v1) (coe v0))
-- Data.Vec.Base._.FoldrOp
d_FoldrOp_342 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> (Integer -> ()) -> ()
d_FoldrOp_342 = erased
-- Data.Vec.Base._.FoldlOp
d_FoldlOp_346 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> (Integer -> ()) -> ()
d_FoldlOp_346 = erased
-- Data.Vec.Base.foldr
d_foldr_352 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  Integer ->
  (Integer -> ()) ->
  (Integer -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> T_Vec_28 -> AgdaAny
d_foldr_352 ~v0 ~v1 ~v2 v3 ~v4 v5 v6 v7 = du_foldr_352 v3 v5 v6 v7
du_foldr_352 ::
  Integer ->
  (Integer -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> T_Vec_28 -> AgdaAny
du_foldr_352 v0 v1 v2 v3
  = case coe v3 of
      C_'91''93'_32 -> coe v2
      C__'8759'__38 v5 v6
        -> let v7 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (coe
                v1 v7 v5 (coe du_foldr_352 (coe v7) (coe v1) (coe v2) (coe v6)))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Vec.Base.foldl
d_foldl_372 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  Integer ->
  (Integer -> ()) ->
  (Integer -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> T_Vec_28 -> AgdaAny
d_foldl_372 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6 v7 = du_foldl_372 v5 v6 v7
du_foldl_372 ::
  (Integer -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny -> T_Vec_28 -> AgdaAny
du_foldl_372 v0 v1 v2
  = case coe v2 of
      C_'91''93'_32 -> coe v1
      C__'8759'__38 v4 v5
        -> coe
             du_foldl_372
             (coe (\ v6 -> coe v0 (addInt (coe (1 :: Integer)) (coe v6))))
             (coe v0 (0 :: Integer) v1 v4) (coe v5)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Vec.Base.foldr′
d_foldr'8242'_390 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  Integer ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny -> T_Vec_28 -> AgdaAny
d_foldr'8242'_390 ~v0 ~v1 ~v2 ~v3 v4 v5 = du_foldr'8242'_390 v4 v5
du_foldr'8242'_390 ::
  Integer ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny -> T_Vec_28 -> AgdaAny
du_foldr'8242'_390 v0 v1
  = coe du_foldr_352 (coe v0) (coe (\ v2 -> v1))
-- Data.Vec.Base.foldl′
d_foldl'8242'_394 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  Integer ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny -> T_Vec_28 -> AgdaAny
d_foldl'8242'_394 ~v0 ~v1 ~v2 ~v3 ~v4 v5 = du_foldl'8242'_394 v5
du_foldl'8242'_394 ::
  (AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny -> T_Vec_28 -> AgdaAny
du_foldl'8242'_394 v0 = coe du_foldl_372 (coe (\ v1 -> v0))
-- Data.Vec.Base.foldr₁
d_foldr'8321'_398 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  Integer -> (AgdaAny -> AgdaAny -> AgdaAny) -> T_Vec_28 -> AgdaAny
d_foldr'8321'_398 ~v0 ~v1 ~v2 v3 v4 = du_foldr'8321'_398 v3 v4
du_foldr'8321'_398 ::
  (AgdaAny -> AgdaAny -> AgdaAny) -> T_Vec_28 -> AgdaAny
du_foldr'8321'_398 v0 v1
  = case coe v1 of
      C__'8759'__38 v3 v4
        -> case coe v4 of
             C_'91''93'_32 -> coe v3
             C__'8759'__38 v6 v7
               -> coe
                    v0 v3 (coe du_foldr'8321'_398 (coe v0) (coe C__'8759'__38 v6 v7))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Vec.Base.foldl₁
d_foldl'8321'_412 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  Integer -> (AgdaAny -> AgdaAny -> AgdaAny) -> T_Vec_28 -> AgdaAny
d_foldl'8321'_412 ~v0 ~v1 ~v2 v3 v4 = du_foldl'8321'_412 v3 v4
du_foldl'8321'_412 ::
  (AgdaAny -> AgdaAny -> AgdaAny) -> T_Vec_28 -> AgdaAny
du_foldl'8321'_412 v0 v1
  = case coe v1 of
      C__'8759'__38 v3 v4
        -> coe du_foldl_372 (coe (\ v5 -> v0)) (coe v3) (coe v4)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Vec.Base.sum
d_sum_420 :: Integer -> T_Vec_28 -> Integer
d_sum_420 v0
  = coe
      du_foldr_352 (coe v0) (coe (\ v1 -> addInt)) (coe (0 :: Integer))
-- Data.Vec.Base.count
d_count_424 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  Integer ->
  (AgdaAny -> ()) ->
  (AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  T_Vec_28 -> Integer
d_count_424 ~v0 ~v1 ~v2 ~v3 ~v4 v5 v6 = du_count_424 v5 v6
du_count_424 ::
  (AgdaAny ->
   MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20) ->
  T_Vec_28 -> Integer
du_count_424 v0 v1
  = case coe v1 of
      C_'91''93'_32 -> coe (0 :: Integer)
      C__'8759'__38 v3 v4
        -> coe
             MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
             (MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
                (coe v0 v3))
             (\ v5 -> addInt (coe (1 :: Integer)) (coe v5)) (\ v5 -> v5)
             (coe du_count_424 (coe v0) (coe v4))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Vec.Base.countᵇ
d_count'7495'_434 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> Integer -> (AgdaAny -> Bool) -> T_Vec_28 -> Integer
d_count'7495'_434 ~v0 ~v1 ~v2 v3 = du_count'7495'_434 v3
du_count'7495'_434 :: (AgdaAny -> Bool) -> T_Vec_28 -> Integer
du_count'7495'_434 v0
  = coe
      du_count_424
      (coe
         (\ v1 ->
            MAlonzo.Code.Relation.Nullary.Decidable.Core.d_T'63'_72
              (coe v0 v1)))
-- Data.Vec.Base.[_]
d_'91'_'93'_438 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 -> () -> AgdaAny -> T_Vec_28
d_'91'_'93'_438 ~v0 ~v1 v2 = du_'91'_'93'_438 v2
du_'91'_'93'_438 :: AgdaAny -> T_Vec_28
du_'91'_'93'_438 v0 = coe C__'8759'__38 v0 (coe C_'91''93'_32)
-- Data.Vec.Base.replicate
d_replicate_444 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> Integer -> AgdaAny -> T_Vec_28
d_replicate_444 ~v0 ~v1 v2 v3 = du_replicate_444 v2 v3
du_replicate_444 :: Integer -> AgdaAny -> T_Vec_28
du_replicate_444 v0 v1
  = case coe v0 of
      0 -> coe C_'91''93'_32
      _ -> let v2 = subInt (coe v0) (coe (1 :: Integer)) in
           coe (coe C__'8759'__38 v1 (coe du_replicate_444 (coe v2) (coe v1)))
-- Data.Vec.Base.tabulate
d_tabulate_452 ::
  Integer ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> (MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> AgdaAny) -> T_Vec_28
d_tabulate_452 v0 ~v1 ~v2 v3 = du_tabulate_452 v0 v3
du_tabulate_452 ::
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> AgdaAny) -> T_Vec_28
du_tabulate_452 v0 v1
  = case coe v0 of
      0 -> coe C_'91''93'_32
      _ -> let v2 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (coe
                C__'8759'__38 (coe v1 (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))
                (coe
                   du_tabulate_452 (coe v2)
                   (coe
                      (\ v3 -> coe v1 (coe MAlonzo.Code.Data.Fin.Base.C_suc_16 v3)))))
-- Data.Vec.Base.allFin
d_allFin_462 :: Integer -> T_Vec_28
d_allFin_462 v0 = coe du_tabulate_452 (coe v0) (coe (\ v1 -> v1))
-- Data.Vec.Base.splitAt
d_splitAt_474 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  Integer ->
  Integer -> T_Vec_28 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_splitAt_474 ~v0 ~v1 v2 ~v3 v4 = du_splitAt_474 v2 v4
du_splitAt_474 ::
  Integer -> T_Vec_28 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_splitAt_474 v0 v1
  = case coe v0 of
      0 -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe C_'91''93'_32)
             (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1) erased)
      _ -> let v2 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (case coe v1 of
                C__'8759'__38 v4 v5
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                       (coe
                          C__'8759'__38 v4
                          (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                             (coe du_splitAt_474 (coe v2) (coe v5))))
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                (coe du_splitAt_474 (coe v2) (coe v5))))
                          erased)
                _ -> MAlonzo.RTE.mazUnreachableError)
-- Data.Vec.Base.take
d_take_496 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> Integer -> Integer -> T_Vec_28 -> T_Vec_28
d_take_496 ~v0 ~v1 v2 ~v3 v4 = du_take_496 v2 v4
du_take_496 :: Integer -> T_Vec_28 -> T_Vec_28
du_take_496 v0 v1
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
      (coe du_splitAt_474 (coe v0) (coe v1))
-- Data.Vec.Base.drop
d_drop_506 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> Integer -> Integer -> T_Vec_28 -> T_Vec_28
d_drop_506 ~v0 ~v1 v2 ~v3 v4 = du_drop_506 v2 v4
du_drop_506 :: Integer -> T_Vec_28 -> T_Vec_28
du_drop_506 v0 v1
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
         (coe du_splitAt_474 (coe v0) (coe v1)))
-- Data.Vec.Base.group
d_group_520 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  Integer ->
  Integer -> T_Vec_28 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_group_520 ~v0 ~v1 v2 v3 v4 = du_group_520 v2 v3 v4
du_group_520 ::
  Integer ->
  Integer -> T_Vec_28 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_group_520 v0 v1 v2
  = case coe v0 of
      0 -> coe
             seq (coe v2)
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe C_'91''93'_32)
                erased)
      _ -> let v3 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                (coe
                   C__'8759'__38
                   (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                      (coe du_splitAt_474 (coe v1) (coe v2)))
                   (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                      (coe
                         du_group_520 (coe v3) (coe v1)
                         (coe
                            MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                            (coe
                               MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                               (coe du_splitAt_474 (coe v1) (coe v2)))))))
                erased)
-- Data.Vec.Base.split
d_split_542 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> Integer -> T_Vec_28 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_split_542 ~v0 ~v1 ~v2 v3 = du_split_542 v3
du_split_542 :: T_Vec_28 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_split_542 v0
  = case coe v0 of
      C_'91''93'_32
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0) (coe v0)
      C__'8759'__38 v2 v3
        -> case coe v3 of
             C_'91''93'_32
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe C__'8759'__38 v2 v3) (coe v3)
             C__'8759'__38 v5 v6
               -> coe
                    MAlonzo.Code.Data.Product.Base.du_map_128
                    (coe C__'8759'__38 (coe v2))
                    (coe (\ v7 -> coe C__'8759'__38 (coe v5)))
                    (coe du_split_542 (coe v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Vec.Base.uncons
d_uncons_556 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> Integer -> T_Vec_28 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_uncons_556 ~v0 ~v1 ~v2 v3 = du_uncons_556 v3
du_uncons_556 :: T_Vec_28 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_uncons_556 v0
  = case coe v0 of
      C__'8759'__38 v2 v3
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Vec.Base.truncate
d_truncate_566 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> T_Vec_28 -> T_Vec_28
d_truncate_566 ~v0 ~v1 v2 ~v3 v4 v5 = du_truncate_566 v2 v4 v5
du_truncate_566 ::
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 -> T_Vec_28 -> T_Vec_28
du_truncate_566 v0 v1 v2
  = case coe v0 of
      0 -> coe C_'91''93'_32
      _ -> let v3 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (case coe v1 of
                MAlonzo.Code.Data.Nat.Base.C_s'8804's_34 v6
                  -> case coe v2 of
                       C__'8759'__38 v8 v9
                         -> coe
                              C__'8759'__38 v8 (coe du_truncate_566 (coe v3) (coe v6) (coe v9))
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> MAlonzo.RTE.mazUnreachableError)
-- Data.Vec.Base.padRight
d_padRight_578 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  Integer ->
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  AgdaAny -> T_Vec_28 -> T_Vec_28
d_padRight_578 ~v0 ~v1 ~v2 v3 v4 v5 v6
  = du_padRight_578 v3 v4 v5 v6
du_padRight_578 ::
  Integer ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22 ->
  AgdaAny -> T_Vec_28 -> T_Vec_28
du_padRight_578 v0 v1 v2 v3
  = case coe v1 of
      MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26
        -> coe du_replicate_444 (coe v0) (coe v2)
      MAlonzo.Code.Data.Nat.Base.C_s'8804's_34 v6
        -> let v7 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (case coe v3 of
                C__'8759'__38 v9 v10
                  -> coe
                       C__'8759'__38 v9
                       (coe du_padRight_578 (coe v7) (coe v6) (coe v2) (coe v10))
                _ -> MAlonzo.RTE.mazUnreachableError)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Vec.Base.toList
d_toList_592 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> Integer -> T_Vec_28 -> [AgdaAny]
d_toList_592 ~v0 ~v1 ~v2 v3 = du_toList_592 v3
du_toList_592 :: T_Vec_28 -> [AgdaAny]
du_toList_592 v0
  = case coe v0 of
      C_'91''93'_32 -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      C__'8759'__38 v2 v3
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v2)
             (coe du_toList_592 (coe v3))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Vec.Base.fromList
d_fromList_600 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> [AgdaAny] -> T_Vec_28
d_fromList_600 ~v0 ~v1 v2 = du_fromList_600 v2
du_fromList_600 :: [AgdaAny] -> T_Vec_28
du_fromList_600 v0
  = case coe v0 of
      [] -> coe C_'91''93'_32
      (:) v1 v2 -> coe C__'8759'__38 v1 (coe du_fromList_600 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Vec.Base._∷ʳ_
d__'8759''691'__606 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> Integer -> T_Vec_28 -> AgdaAny -> T_Vec_28
d__'8759''691'__606 ~v0 ~v1 ~v2 v3 v4 = du__'8759''691'__606 v3 v4
du__'8759''691'__606 :: T_Vec_28 -> AgdaAny -> T_Vec_28
du__'8759''691'__606 v0 v1
  = case coe v0 of
      C_'91''93'_32 -> coe du_'91'_'93'_438 (coe v1)
      C__'8759'__38 v3 v4
        -> coe
             C__'8759'__38 v3 (coe du__'8759''691'__606 (coe v4) (coe v1))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Vec.Base.reverse
d_reverse_616 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> Integer -> T_Vec_28 -> T_Vec_28
d_reverse_616 ~v0 ~v1 ~v2 = du_reverse_616
du_reverse_616 :: T_Vec_28 -> T_Vec_28
du_reverse_616
  = coe
      du_foldl_372 (coe (\ v0 v1 v2 -> coe C__'8759'__38 v2 v1))
      (coe C_'91''93'_32)
-- Data.Vec.Base._ʳ++_
d__'691''43''43'__622 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> Integer -> Integer -> T_Vec_28 -> T_Vec_28 -> T_Vec_28
d__'691''43''43'__622 ~v0 ~v1 ~v2 ~v3 v4 v5
  = du__'691''43''43'__622 v4 v5
du__'691''43''43'__622 :: T_Vec_28 -> T_Vec_28 -> T_Vec_28
du__'691''43''43'__622 v0 v1
  = coe
      du_foldl_372 (coe (\ v2 v3 v4 -> coe C__'8759'__38 v4 v3)) (coe v1)
      (coe v0)
-- Data.Vec.Base.initLast
d_initLast_640 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> Integer -> T_Vec_28 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_initLast_640 ~v0 ~v1 v2 v3 = du_initLast_640 v2 v3
du_initLast_640 ::
  Integer -> T_Vec_28 -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_initLast_640 v0 v1
  = case coe v0 of
      0 -> case coe v1 of
             C__'8759'__38 v3 v4
               -> coe
                    seq (coe v4)
                    (coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe C_'91''93'_32)
                       (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v3) erased))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> let v2 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (case coe v1 of
                C__'8759'__38 v4 v5
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                       (coe
                          C__'8759'__38 v4
                          (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                             (coe du_initLast_640 (coe v2) (coe v5))))
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                (coe du_initLast_640 (coe v2) (coe v5))))
                          erased)
                _ -> MAlonzo.RTE.mazUnreachableError)
-- Data.Vec.Base.init
d_init_658 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> Integer -> T_Vec_28 -> T_Vec_28
d_init_658 ~v0 ~v1 v2 v3 = du_init_658 v2 v3
du_init_658 :: Integer -> T_Vec_28 -> T_Vec_28
du_init_658 v0 v1
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
      (coe du_initLast_640 (coe v0) (coe v1))
-- Data.Vec.Base.last
d_last_662 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> Integer -> T_Vec_28 -> AgdaAny
d_last_662 ~v0 ~v1 v2 v3 = du_last_662 v2 v3
du_last_662 :: Integer -> T_Vec_28 -> AgdaAny
du_last_662 v0 v1
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
         (coe du_initLast_640 (coe v0) (coe v1)))
-- Data.Vec.Base.transpose
d_transpose_666 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> Integer -> Integer -> T_Vec_28 -> T_Vec_28
d_transpose_666 ~v0 ~v1 v2 ~v3 v4 = du_transpose_666 v2 v4
du_transpose_666 :: Integer -> T_Vec_28 -> T_Vec_28
du_transpose_666 v0 v1
  = case coe v1 of
      C_'91''93'_32 -> coe du_replicate_444 (coe v0) (coe v1)
      C__'8759'__38 v3 v4
        -> coe
             du__'8859'__284
             (coe
                du__'8859'__284 (coe du_replicate_444 (coe v0) (coe C__'8759'__38))
                (coe v3))
             (coe du_transpose_666 (coe v0) (coe v4))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Vec.Base.remove
d_remove_676 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  Integer ->
  T_Vec_28 -> MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> T_Vec_28
d_remove_676 v0 v1 v2 v3 v4 = coe du_removeAt_122 v3 v4
-- Data.Vec.Base.insert
d_insert_678 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  Integer ->
  T_Vec_28 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> AgdaAny -> T_Vec_28
d_insert_678 v0 v1 v2 v3 v4 v5 = coe du_insertAt_108 v3 v4 v5
