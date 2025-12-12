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
{-# LANGUAGE ViewPatterns #-}

module MAlonzo.Code.Utils where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Bool
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Int
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.Unit
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Data.Maybe.Base
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core
import qualified MAlonzo.Code.Relation.Nullary.Reflects

import Raw
import qualified Data.ByteString as BS
import qualified Data.Vector.Strict as Strict
import PlutusCore.Data as D
import qualified Data.Vector.Strict as SV
import qualified PlutusCore.Crypto.BLS12_381.G1 as G1
import qualified PlutusCore.Crypto.BLS12_381.G2 as G2
import qualified PlutusCore.Crypto.BLS12_381.Pairing as Pairing
type Pair a b = (a , b)
pattern ArrayDATA :: [D.Data] -> D.Data
pattern ArrayDATA xs <- D.Array (SV.toList -> xs) where
  ArrayDATA xs = D.Array (SV.fromList xs)
-- Utils.Either
d_Either_6 a0 a1 = ()
type T_Either_6 a0 a1 = Either a0 a1
pattern C_inj'8321'_12 a0 = Left a0
pattern C_inj'8322'_14 a0 = Right a0
check_inj'8321'_12 :: forall xA. forall xB. xA -> T_Either_6 xA xB
check_inj'8321'_12 = Left
check_inj'8322'_14 :: forall xA. forall xB. xB -> T_Either_6 xA xB
check_inj'8322'_14 = Right
cover_Either_6 :: Either a1 a2 -> ()
cover_Either_6 x
  = case x of
      Left _ -> ()
      Right _ -> ()
-- Utils.either
d_either_22 ::
  () ->
  () ->
  () ->
  T_Either_6 AgdaAny AgdaAny ->
  (AgdaAny -> AgdaAny) -> (AgdaAny -> AgdaAny) -> AgdaAny
d_either_22 ~v0 ~v1 ~v2 v3 v4 v5 = du_either_22 v3 v4 v5
du_either_22 ::
  T_Either_6 AgdaAny AgdaAny ->
  (AgdaAny -> AgdaAny) -> (AgdaAny -> AgdaAny) -> AgdaAny
du_either_22 v0 v1 v2
  = case coe v0 of
      C_inj'8321'_12 v3 -> coe v1 v3
      C_inj'8322'_14 v3 -> coe v2 v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Utils.eitherBind
d_eitherBind_42 ::
  () ->
  () ->
  () ->
  T_Either_6 AgdaAny AgdaAny ->
  (AgdaAny -> T_Either_6 AgdaAny AgdaAny) ->
  T_Either_6 AgdaAny AgdaAny
d_eitherBind_42 ~v0 ~v1 ~v2 v3 v4 = du_eitherBind_42 v3 v4
du_eitherBind_42 ::
  T_Either_6 AgdaAny AgdaAny ->
  (AgdaAny -> T_Either_6 AgdaAny AgdaAny) ->
  T_Either_6 AgdaAny AgdaAny
du_eitherBind_42 v0 v1
  = case coe v0 of
      C_inj'8321'_12 v2 -> coe v0
      C_inj'8322'_14 v2 -> coe v1 v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Utils.decIf
d_decIf_56 ::
  () ->
  () ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_decIf_56 ~v0 ~v1 v2 v3 v4 = du_decIf_56 v2 v3 v4
du_decIf_56 ::
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  AgdaAny -> AgdaAny -> AgdaAny
du_decIf_56 v0 v1 v2
  = case coe v0 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v3 v4
        -> if coe v3
             then coe seq (coe v4) (coe v1)
             else coe seq (coe v4) (coe v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Utils.cong₃
d_cong'8323'_92 ::
  () ->
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny -> AgdaAny -> AgdaAny) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_cong'8323'_92 = erased
-- Utils.≡-subst-removable
d_'8801''45'subst'45'removable_114 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> ()) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8801''45'subst'45'removable_114 = erased
-- Utils._∔_≣_
d__'8724'_'8803'__120 a0 a1 a2 = ()
data T__'8724'_'8803'__120
  = C_start_124 | C_bubble_132 T__'8724'_'8803'__120
-- Utils.unique∔
d_unique'8724'_144 ::
  Integer ->
  Integer ->
  Integer ->
  T__'8724'_'8803'__120 ->
  T__'8724'_'8803'__120 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_unique'8724'_144 = erased
-- Utils.+2∔
d_'43'2'8724'_156 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T__'8724'_'8803'__120
d_'43'2'8724'_156 v0 ~v1 ~v2 ~v3 = du_'43'2'8724'_156 v0
du_'43'2'8724'_156 :: Integer -> T__'8724'_'8803'__120
du_'43'2'8724'_156 v0
  = case coe v0 of
      0 -> coe C_start_124
      _ -> let v1 = subInt (coe v0) (coe (1 :: Integer)) in
           coe (coe C_bubble_132 (coe du_'43'2'8724'_156 (coe v1)))
-- Utils.∔2+
d_'8724'2'43'_174 ::
  Integer ->
  Integer ->
  Integer ->
  T__'8724'_'8803'__120 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8724'2'43'_174 = erased
-- Utils.alldone
d_alldone_180 :: Integer -> T__'8724'_'8803'__120
d_alldone_180 v0 = coe du_'43'2'8724'_156 (coe v0)
-- Utils.Monad
d_Monad_186 a0 = ()
data T_Monad_186
  = C_Monad'46'constructor_12257 (() -> AgdaAny -> AgdaAny)
                                 (() -> () -> AgdaAny -> (AgdaAny -> AgdaAny) -> AgdaAny)
-- Utils.Monad.return
d_return_202 :: T_Monad_186 -> () -> AgdaAny -> AgdaAny
d_return_202 v0
  = case coe v0 of
      C_Monad'46'constructor_12257 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Utils.Monad._>>=_
d__'62''62''61'__208 ::
  T_Monad_186 ->
  () -> () -> AgdaAny -> (AgdaAny -> AgdaAny) -> AgdaAny
d__'62''62''61'__208 v0
  = case coe v0 of
      C_Monad'46'constructor_12257 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Utils.Monad._>>_
d__'62''62'__214 ::
  (() -> ()) ->
  T_Monad_186 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d__'62''62'__214 ~v0 v1 ~v2 ~v3 v4 v5 = du__'62''62'__214 v1 v4 v5
du__'62''62'__214 :: T_Monad_186 -> AgdaAny -> AgdaAny -> AgdaAny
du__'62''62'__214 v0 v1 v2
  = coe d__'62''62''61'__208 v0 erased erased v1 (\ v3 -> v2)
-- Utils.Monad.fmap
d_fmap_224 ::
  (() -> ()) ->
  T_Monad_186 ->
  () -> () -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_fmap_224 ~v0 v1 ~v2 ~v3 v4 v5 = du_fmap_224 v1 v4 v5
du_fmap_224 ::
  T_Monad_186 -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du_fmap_224 v0 v1 v2
  = coe
      d__'62''62''61'__208 v0 erased erased v2
      (\ v3 -> coe d_return_202 v0 erased (coe v1 v3))
-- Utils._._>>_
d__'62''62'__232 ::
  (() -> ()) ->
  T_Monad_186 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d__'62''62'__232 ~v0 v1 = du__'62''62'__232 v1
du__'62''62'__232 ::
  T_Monad_186 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
du__'62''62'__232 v0 v1 v2 v3 v4
  = coe du__'62''62'__214 (coe v0) v3 v4
-- Utils._._>>=_
d__'62''62''61'__234 ::
  T_Monad_186 ->
  () -> () -> AgdaAny -> (AgdaAny -> AgdaAny) -> AgdaAny
d__'62''62''61'__234 v0 = coe d__'62''62''61'__208 (coe v0)
-- Utils._.fmap
d_fmap_236 ::
  (() -> ()) ->
  T_Monad_186 ->
  () -> () -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_fmap_236 ~v0 v1 = du_fmap_236 v1
du_fmap_236 ::
  T_Monad_186 ->
  () -> () -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du_fmap_236 v0 v1 v2 v3 v4 = coe du_fmap_224 (coe v0) v3 v4
-- Utils._.return
d_return_238 :: T_Monad_186 -> () -> AgdaAny -> AgdaAny
d_return_238 v0 = coe d_return_202 (coe v0)
-- Utils.MaybeMonad
d_MaybeMonad_240 :: T_Monad_186
d_MaybeMonad_240
  = coe
      C_Monad'46'constructor_12257
      (coe (\ v0 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16))
      (coe
         (\ v0 v1 v2 v3 ->
            coe MAlonzo.Code.Data.Maybe.Base.du__'62''62''61'__72 v2 v3))
-- Utils.sumBind
d_sumBind_248 ::
  () ->
  () ->
  () ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  (AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30) ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_sumBind_248 ~v0 ~v1 ~v2 v3 v4 = du_sumBind_248 v3 v4
du_sumBind_248 ::
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  (AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30) ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_sumBind_248 v0 v1
  = case coe v0 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v2 -> coe v1 v2
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v2 -> coe v0
      _ -> MAlonzo.RTE.mazUnreachableError
-- Utils.SumMonad
d_SumMonad_262 :: () -> T_Monad_186
d_SumMonad_262 ~v0 = du_SumMonad_262
du_SumMonad_262 :: T_Monad_186
du_SumMonad_262
  = coe
      C_Monad'46'constructor_12257
      (coe (\ v0 -> coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38))
      (coe (\ v0 v1 -> coe du_sumBind_248))
-- Utils.EitherMonad
d_EitherMonad_268 :: () -> T_Monad_186
d_EitherMonad_268 ~v0 = du_EitherMonad_268
du_EitherMonad_268 :: T_Monad_186
du_EitherMonad_268
  = coe
      C_Monad'46'constructor_12257 (coe (\ v0 -> coe C_inj'8322'_14))
      (coe (\ v0 v1 -> coe du_eitherBind_42))
-- Utils.EitherP
d_EitherP_274 :: () -> T_Monad_186
d_EitherP_274 ~v0 = du_EitherP_274
du_EitherP_274 :: T_Monad_186
du_EitherP_274
  = coe
      C_Monad'46'constructor_12257 (coe (\ v0 -> coe C_inj'8322'_14))
      (coe (\ v0 v1 -> coe du_eitherBind_42))
-- Utils.withE
d_withE_282 ::
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  T_Either_6 AgdaAny AgdaAny -> T_Either_6 AgdaAny AgdaAny
d_withE_282 ~v0 ~v1 ~v2 v3 v4 = du_withE_282 v3 v4
du_withE_282 ::
  (AgdaAny -> AgdaAny) ->
  T_Either_6 AgdaAny AgdaAny -> T_Either_6 AgdaAny AgdaAny
du_withE_282 v0 v1
  = case coe v1 of
      C_inj'8321'_12 v2 -> coe C_inj'8321'_12 (coe v0 v2)
      C_inj'8322'_14 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Utils.dec2Either
d_dec2Either_294 ::
  () ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  T_Either_6
    (AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) AgdaAny
d_dec2Either_294 ~v0 v1 = du_dec2Either_294 v1
du_dec2Either_294 ::
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  T_Either_6
    (AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) AgdaAny
du_dec2Either_294 v0
  = case coe v0 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v1 v2
        -> if coe v1
             then case coe v2 of
                    MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v3
                      -> coe C_inj'8322'_14 (coe v3)
                    _ -> MAlonzo.RTE.mazUnreachableError
             else coe seq (coe v2) (coe C_inj'8321'_12 erased)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Utils.Writer
d_Writer_304 a0 a1 = ()
data T_Writer_304 = C__'44'__318 AgdaAny AgdaAny
-- Utils.Writer.wrvalue
d_wrvalue_314 :: T_Writer_304 -> AgdaAny
d_wrvalue_314 v0
  = case coe v0 of
      C__'44'__318 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Utils.Writer.accum
d_accum_316 :: T_Writer_304 -> AgdaAny
d_accum_316 v0
  = case coe v0 of
      C__'44'__318 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Utils.WriterMonad.WriterMonad
d_WriterMonad_328 ::
  () -> AgdaAny -> (AgdaAny -> AgdaAny -> AgdaAny) -> T_Monad_186
d_WriterMonad_328 ~v0 v1 v2 = du_WriterMonad_328 v1 v2
du_WriterMonad_328 ::
  AgdaAny -> (AgdaAny -> AgdaAny -> AgdaAny) -> T_Monad_186
du_WriterMonad_328 v0 v1
  = coe
      C_Monad'46'constructor_12257
      (coe (\ v2 v3 -> coe C__'44'__318 (coe v3) (coe v0)))
      (coe
         (\ v2 v3 v4 ->
            case coe v4 of
              C__'44'__318 v5 v6
                -> coe
                     (\ v7 ->
                        coe
                          C__'44'__318 (coe d_wrvalue_314 (coe v7 v5))
                          (coe v1 v6 (d_accum_316 (coe v7 v5))))
              _ -> MAlonzo.RTE.mazUnreachableError))
-- Utils.WriterMonad.tell
d_tell_344 ::
  () ->
  AgdaAny ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny -> T_Writer_304
d_tell_344 ~v0 ~v1 ~v2 v3 = du_tell_344 v3
du_tell_344 :: AgdaAny -> T_Writer_304
du_tell_344 v0
  = coe
      C__'44'__318 (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8) (coe v0)
-- Utils.RuntimeError
d_RuntimeError_348 = ()
type T_RuntimeError_348 = RuntimeError
pattern C_gasError_350 = GasError
pattern C_userError_352 = UserError
pattern C_runtimeTypeError_354 = RuntimeTypeError
check_gasError_350 :: T_RuntimeError_348
check_gasError_350 = GasError
check_userError_352 :: T_RuntimeError_348
check_userError_352 = UserError
check_runtimeTypeError_354 :: T_RuntimeError_348
check_runtimeTypeError_354 = RuntimeTypeError
cover_RuntimeError_348 :: RuntimeError -> ()
cover_RuntimeError_348 x
  = case x of
      GasError -> ()
      UserError -> ()
      RuntimeTypeError -> ()
-- Utils.ByteString
type T_ByteString_356 = BS.ByteString
d_ByteString_356
  = error
      "MAlonzo Runtime Error: postulate evaluated: Utils.ByteString"
-- Utils.mkByteString
d_mkByteString_358
  = error
      "MAlonzo Runtime Error: postulate evaluated: Utils.mkByteString"
-- Utils.eqByteString
d_eqByteString_360 :: T_ByteString_356 -> T_ByteString_356 -> Bool
d_eqByteString_360 = (==)
-- Utils._×_
d__'215'__366 a0 a1 = ()
type T__'215'__366 a0 a1 = Pair a0 a1
pattern C__'44'__380 a0 a1 = (,) a0 a1
check__'44'__380 ::
  forall xA. forall xB. xA -> xB -> T__'215'__366 xA xB
check__'44'__380 = (,)
cover__'215'__366 :: Pair a1 a2 -> ()
cover__'215'__366 x
  = case x of
      (,) _ _ -> ()
-- Utils._×_.proj₁
d_proj'8321'_376 :: T__'215'__366 AgdaAny AgdaAny -> AgdaAny
d_proj'8321'_376 v0
  = case coe v0 of
      C__'44'__380 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Utils._×_.proj₂
d_proj'8322'_378 :: T__'215'__366 AgdaAny AgdaAny -> AgdaAny
d_proj'8322'_378 v0
  = case coe v0 of
      C__'44'__380 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Utils.List
d_List_384 a0 = ()
type T_List_384 a0 = [] a0
pattern C_'91''93'_388 = []
pattern C__'8759'__390 a0 a1 = (:) a0 a1
check_'91''93'_388 :: forall xA. T_List_384 xA
check_'91''93'_388 = []
check__'8759'__390 ::
  forall xA. xA -> T_List_384 xA -> T_List_384 xA
check__'8759'__390 = (:)
cover_List_384 :: [] a1 -> ()
cover_List_384 x
  = case x of
      [] -> ()
      (:) _ _ -> ()
-- Utils.length
d_length_394 :: () -> T_List_384 AgdaAny -> Integer
d_length_394 ~v0 v1 = du_length_394 v1
du_length_394 :: T_List_384 AgdaAny -> Integer
du_length_394 v0
  = case coe v0 of
      C_'91''93'_388 -> coe (0 :: Integer)
      C__'8759'__390 v1 v2
        -> coe addInt (coe (1 :: Integer)) (coe du_length_394 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Utils.map
d_map_404 ::
  () ->
  () ->
  (AgdaAny -> AgdaAny) -> T_List_384 AgdaAny -> T_List_384 AgdaAny
d_map_404 ~v0 ~v1 v2 v3 = du_map_404 v2 v3
du_map_404 ::
  (AgdaAny -> AgdaAny) -> T_List_384 AgdaAny -> T_List_384 AgdaAny
du_map_404 v0 v1
  = case coe v1 of
      C_'91''93'_388 -> coe v1
      C__'8759'__390 v2 v3
        -> coe
             C__'8759'__390 (coe v0 v2) (coe du_map_404 (coe v0) (coe v3))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Utils.toList
d_toList_416 :: () -> T_List_384 AgdaAny -> [AgdaAny]
d_toList_416 ~v0 v1 = du_toList_416 v1
du_toList_416 :: T_List_384 AgdaAny -> [AgdaAny]
du_toList_416 v0
  = case coe v0 of
      C_'91''93'_388 -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      C__'8759'__390 v1 v2
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v1)
             (coe du_toList_416 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Utils.fromList
d_fromList_424 :: () -> [AgdaAny] -> T_List_384 AgdaAny
d_fromList_424 ~v0 v1 = du_fromList_424 v1
du_fromList_424 :: [AgdaAny] -> T_List_384 AgdaAny
du_fromList_424 v0
  = case coe v0 of
      [] -> coe C_'91''93'_388
      (:) v1 v2
        -> coe C__'8759'__390 (coe v1) (coe du_fromList_424 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Utils.dropLIST
d_dropLIST_432 ::
  () -> Integer -> T_List_384 AgdaAny -> T_List_384 AgdaAny
d_dropLIST_432 ~v0 v1 v2 = du_dropLIST_432 v1 v2
du_dropLIST_432 ::
  Integer -> T_List_384 AgdaAny -> T_List_384 AgdaAny
du_dropLIST_432 v0 v1
  = case coe v0 of
      _ | coe geqInt (coe v0) (coe (0 :: Integer)) ->
          coe du_drop_444 (coe v0) (coe v1)
      _ -> coe v1
-- Utils._.drop
d_drop_444 ::
  () ->
  Integer ->
  T_List_384 AgdaAny ->
  () -> Integer -> T_List_384 AgdaAny -> T_List_384 AgdaAny
d_drop_444 ~v0 ~v1 ~v2 ~v3 v4 v5 = du_drop_444 v4 v5
du_drop_444 :: Integer -> T_List_384 AgdaAny -> T_List_384 AgdaAny
du_drop_444 v0 v1
  = case coe v0 of
      0 -> coe v1
      _ -> let v2 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (case coe v1 of
                C_'91''93'_388 -> coe v1
                C__'8759'__390 v3 v4 -> coe du_drop_444 (coe v2) (coe v4)
                _ -> MAlonzo.RTE.mazUnreachableError)
-- Utils.map-cong
d_map'45'cong_468 ::
  () ->
  () ->
  [AgdaAny] ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_map'45'cong_468 = erased
-- Utils.Array
type T_Array_478 a0 = Strict.Vector a0
d_Array_478
  = error "MAlonzo Runtime Error: postulate evaluated: Utils.Array"
-- Utils.HSlengthOfArray
d_HSlengthOfArray_482 :: forall xA. () -> T_Array_478 xA -> Integer
d_HSlengthOfArray_482 = \() -> \as -> toInteger (Strict.length as)
-- Utils.HSlistToArray
d_HSlistToArray_486 ::
  forall xA. () -> T_List_384 xA -> T_Array_478 xA
d_HSlistToArray_486 = \() -> Strict.fromList
-- Utils.HSindexArray
d_HSindexArray_488 ::
  forall xA. () -> T_Array_478 xA -> Integer -> xA
d_HSindexArray_488
  = \() -> \as -> \i -> as Strict.! (fromInteger i)
-- Utils.mkArray
d_mkArray_492
  = error "MAlonzo Runtime Error: postulate evaluated: Utils.mkArray"
-- Utils.DATA
d_DATA_494 = ()
type T_DATA_494 = Data
pattern C_ConstrDATA_496 a0 a1 = D.Constr a0 a1
pattern C_MapDATA_498 a0 = D.Map a0
pattern C_ListDATA_500 a0 = D.List a0
pattern C_ArrayDATA_502 a0 = ArrayDATA a0
pattern C_iDATA_504 a0 = D.I a0
pattern C_bDATA_506 a0 = D.B a0
check_ConstrDATA_496 ::
  Integer -> T_List_384 T_DATA_494 -> T_DATA_494
check_ConstrDATA_496 = D.Constr
check_MapDATA_498 ::
  T_List_384 (T__'215'__366 T_DATA_494 T_DATA_494) -> T_DATA_494
check_MapDATA_498 = D.Map
check_ListDATA_500 :: T_List_384 T_DATA_494 -> T_DATA_494
check_ListDATA_500 = D.List
check_ArrayDATA_502 :: T_List_384 T_DATA_494 -> T_DATA_494
check_ArrayDATA_502 = ArrayDATA
check_iDATA_504 :: Integer -> T_DATA_494
check_iDATA_504 = D.I
check_bDATA_506 :: T_ByteString_356 -> T_DATA_494
check_bDATA_506 = D.B
cover_DATA_494 :: Data -> ()
cover_DATA_494 x
  = case x of
      D.Constr _ _ -> ()
      D.Map _ -> ()
      D.List _ -> ()
      ArrayDATA _ -> ()
      D.I _ -> ()
      D.B _ -> ()
-- Utils.eqDATA
d_eqDATA_508 :: T_DATA_494 -> T_DATA_494 -> Bool
d_eqDATA_508 = (==)
-- Utils.Bls12-381-G1-Element
type T_Bls12'45'381'45'G1'45'Element_690 = G1.Element
d_Bls12'45'381'45'G1'45'Element_690
  = error
      "MAlonzo Runtime Error: postulate evaluated: Utils.Bls12-381-G1-Element"
-- Utils.eqBls12-381-G1-Element
d_eqBls12'45'381'45'G1'45'Element_692 ::
  T_Bls12'45'381'45'G1'45'Element_690 ->
  T_Bls12'45'381'45'G1'45'Element_690 -> Bool
d_eqBls12'45'381'45'G1'45'Element_692 = (==)
-- Utils.Bls12-381-G2-Element
type T_Bls12'45'381'45'G2'45'Element_694 = G2.Element
d_Bls12'45'381'45'G2'45'Element_694
  = error
      "MAlonzo Runtime Error: postulate evaluated: Utils.Bls12-381-G2-Element"
-- Utils.eqBls12-381-G2-Element
d_eqBls12'45'381'45'G2'45'Element_696 ::
  T_Bls12'45'381'45'G2'45'Element_694 ->
  T_Bls12'45'381'45'G2'45'Element_694 -> Bool
d_eqBls12'45'381'45'G2'45'Element_696 = (==)
-- Utils.Bls12-381-MlResult
type T_Bls12'45'381'45'MlResult_698 = Pairing.MlResult
d_Bls12'45'381'45'MlResult_698
  = error
      "MAlonzo Runtime Error: postulate evaluated: Utils.Bls12-381-MlResult"
-- Utils.eqBls12-381-MlResult
d_eqBls12'45'381'45'MlResult_700 ::
  T_Bls12'45'381'45'MlResult_698 ->
  T_Bls12'45'381'45'MlResult_698 -> Bool
d_eqBls12'45'381'45'MlResult_700 = (==)
-- Utils.Kind
d_Kind_702 = ()
type T_Kind_702 = KIND
pattern C_'42'_704 = Star
pattern C_'9839'_706 = Sharp
pattern C__'8658'__708 a0 a1 = Arrow a0 a1
check_'42'_704 :: T_Kind_702
check_'42'_704 = Star
check_'9839'_706 :: T_Kind_702
check_'9839'_706 = Sharp
check__'8658'__708 :: T_Kind_702 -> T_Kind_702 -> T_Kind_702
check__'8658'__708 = Arrow
cover_Kind_702 :: KIND -> ()
cover_Kind_702 x
  = case x of
      Star -> ()
      Sharp -> ()
      Arrow _ _ -> ()
