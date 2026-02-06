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
import qualified MAlonzo.Code.Data.Fin.Base
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Data.Maybe.Base
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Data.Nat.Properties
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core
import qualified MAlonzo.Code.Relation.Nullary.Reflects

import Raw
import qualified Data.ByteString as BS
import qualified Data.Vector.Strict as Strict
import PlutusCore.Data as D
import qualified PlutusCore.Crypto.BLS12_381.G1 as G1
import qualified PlutusCore.Crypto.BLS12_381.G2 as G2
import qualified PlutusCore.Crypto.BLS12_381.Pairing as Pairing
type Pair a b = (a , b)
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
-- Utils.maybeToEither
d_maybeToEither_74 ::
  () -> () -> AgdaAny -> Maybe AgdaAny -> T_Either_6 AgdaAny AgdaAny
d_maybeToEither_74 ~v0 ~v1 v2 = du_maybeToEither_74 v2
du_maybeToEither_74 ::
  AgdaAny -> Maybe AgdaAny -> T_Either_6 AgdaAny AgdaAny
du_maybeToEither_74 v0
  = coe
      MAlonzo.Code.Data.Maybe.Base.du_maybe_32 (coe C_inj'8322'_14)
      (coe C_inj'8321'_12 (coe v0))
-- Utils.try
d_try_82 ::
  () -> () -> Maybe AgdaAny -> AgdaAny -> T_Either_6 AgdaAny AgdaAny
d_try_82 ~v0 ~v1 v2 v3 = du_try_82 v2 v3
du_try_82 :: Maybe AgdaAny -> AgdaAny -> T_Either_6 AgdaAny AgdaAny
du_try_82 v0 v1
  = coe
      MAlonzo.Code.Data.Maybe.Base.du_maybe_32 (coe C_inj'8322'_14)
      (coe C_inj'8321'_12 (coe v1)) (coe v0)
-- Utils.eitherToMaybe
d_eitherToMaybe_92 ::
  () -> () -> T_Either_6 AgdaAny AgdaAny -> Maybe AgdaAny
d_eitherToMaybe_92 ~v0 ~v1 v2 = du_eitherToMaybe_92 v2
du_eitherToMaybe_92 :: T_Either_6 AgdaAny AgdaAny -> Maybe AgdaAny
du_eitherToMaybe_92 v0
  = case coe v0 of
      C_inj'8321'_12 v1
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      C_inj'8322'_14 v1
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Utils.natToFin
d_natToFin_98 ::
  Integer -> Integer -> Maybe MAlonzo.Code.Data.Fin.Base.T_Fin_10
d_natToFin_98 v0 v1
  = let v2
          = coe
              MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_168
              (\ v2 ->
                 coe
                   MAlonzo.Code.Data.Nat.Properties.du_'8804''7495''8658''8804'_2746
                   (coe addInt (coe (1 :: Integer)) (coe v1)))
              (coe
                 MAlonzo.Code.Data.Nat.Properties.du_'8804''8658''8804''7495'_2758)
              (coe
                 MAlonzo.Code.Relation.Nullary.Decidable.Core.d_T'63'_66
                 (coe
                    MAlonzo.Code.Data.Nat.Base.d__'8804''7495'__14
                    (coe addInt (coe (1 :: Integer)) (coe v1)) (coe v0))) in
    coe
      (case coe v2 of
         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v3 v4
           -> if coe v3
                then coe
                       seq (coe v4)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                          (coe MAlonzo.Code.Data.Fin.Base.du_fromℕ'60'_52 (coe v1)))
                else coe
                       seq (coe v4) (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Utils.cong₃
d_cong'8323'_140 ::
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
d_cong'8323'_140 = erased
-- Utils.≡-subst-removable
d_'8801''45'subst'45'removable_162 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> ()) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8801''45'subst'45'removable_162 = erased
-- Utils._∔_≣_
d__'8724'_'8803'__168 a0 a1 a2 = ()
data T__'8724'_'8803'__168
  = C_start_172 | C_bubble_180 T__'8724'_'8803'__168
-- Utils.unique∔
d_unique'8724'_192 ::
  Integer ->
  Integer ->
  Integer ->
  T__'8724'_'8803'__168 ->
  T__'8724'_'8803'__168 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_unique'8724'_192 = erased
-- Utils.+2∔
d_'43'2'8724'_204 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T__'8724'_'8803'__168
d_'43'2'8724'_204 v0 ~v1 ~v2 ~v3 = du_'43'2'8724'_204 v0
du_'43'2'8724'_204 :: Integer -> T__'8724'_'8803'__168
du_'43'2'8724'_204 v0
  = case coe v0 of
      0 -> coe C_start_172
      _ -> let v1 = subInt (coe v0) (coe (1 :: Integer)) in
           coe (coe C_bubble_180 (coe du_'43'2'8724'_204 (coe v1)))
-- Utils.∔2+
d_'8724'2'43'_222 ::
  Integer ->
  Integer ->
  Integer ->
  T__'8724'_'8803'__168 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8724'2'43'_222 = erased
-- Utils.alldone
d_alldone_228 :: Integer -> T__'8724'_'8803'__168
d_alldone_228 v0 = coe du_'43'2'8724'_204 (coe v0)
-- Utils.Monad
d_Monad_234 a0 = ()
data T_Monad_234
  = C_Monad'46'constructor_14319 (() -> AgdaAny -> AgdaAny)
                                 (() -> () -> AgdaAny -> (AgdaAny -> AgdaAny) -> AgdaAny)
-- Utils.Monad.return
d_return_250 :: T_Monad_234 -> () -> AgdaAny -> AgdaAny
d_return_250 v0
  = case coe v0 of
      C_Monad'46'constructor_14319 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Utils.Monad._>>=_
d__'62''62''61'__256 ::
  T_Monad_234 ->
  () -> () -> AgdaAny -> (AgdaAny -> AgdaAny) -> AgdaAny
d__'62''62''61'__256 v0
  = case coe v0 of
      C_Monad'46'constructor_14319 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Utils.Monad._>>_
d__'62''62'__262 ::
  (() -> ()) ->
  T_Monad_234 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d__'62''62'__262 ~v0 v1 ~v2 ~v3 v4 v5 = du__'62''62'__262 v1 v4 v5
du__'62''62'__262 :: T_Monad_234 -> AgdaAny -> AgdaAny -> AgdaAny
du__'62''62'__262 v0 v1 v2
  = coe d__'62''62''61'__256 v0 erased erased v1 (\ v3 -> v2)
-- Utils.Monad.fmap
d_fmap_272 ::
  (() -> ()) ->
  T_Monad_234 ->
  () -> () -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_fmap_272 ~v0 v1 ~v2 ~v3 v4 v5 = du_fmap_272 v1 v4 v5
du_fmap_272 ::
  T_Monad_234 -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du_fmap_272 v0 v1 v2
  = coe
      d__'62''62''61'__256 v0 erased erased v2
      (\ v3 -> coe d_return_250 v0 erased (coe v1 v3))
-- Utils._._>>_
d__'62''62'__280 ::
  (() -> ()) ->
  T_Monad_234 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d__'62''62'__280 ~v0 v1 = du__'62''62'__280 v1
du__'62''62'__280 ::
  T_Monad_234 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
du__'62''62'__280 v0 v1 v2 v3 v4
  = coe du__'62''62'__262 (coe v0) v3 v4
-- Utils._._>>=_
d__'62''62''61'__282 ::
  T_Monad_234 ->
  () -> () -> AgdaAny -> (AgdaAny -> AgdaAny) -> AgdaAny
d__'62''62''61'__282 v0 = coe d__'62''62''61'__256 (coe v0)
-- Utils._.fmap
d_fmap_284 ::
  (() -> ()) ->
  T_Monad_234 ->
  () -> () -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_fmap_284 ~v0 v1 = du_fmap_284 v1
du_fmap_284 ::
  T_Monad_234 ->
  () -> () -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du_fmap_284 v0 v1 v2 v3 v4 = coe du_fmap_272 (coe v0) v3 v4
-- Utils._.return
d_return_286 :: T_Monad_234 -> () -> AgdaAny -> AgdaAny
d_return_286 v0 = coe d_return_250 (coe v0)
-- Utils.MaybeMonad
d_MaybeMonad_288 :: T_Monad_234
d_MaybeMonad_288
  = coe
      C_Monad'46'constructor_14319
      (coe (\ v0 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16))
      (coe
         (\ v0 v1 v2 v3 ->
            coe MAlonzo.Code.Data.Maybe.Base.du__'62''62''61'__72 v2 v3))
-- Utils.sumBind
d_sumBind_296 ::
  () ->
  () ->
  () ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  (AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30) ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_sumBind_296 ~v0 ~v1 ~v2 v3 v4 = du_sumBind_296 v3 v4
du_sumBind_296 ::
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  (AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30) ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_sumBind_296 v0 v1
  = case coe v0 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v2 -> coe v1 v2
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v2 -> coe v0
      _ -> MAlonzo.RTE.mazUnreachableError
-- Utils.SumMonad
d_SumMonad_310 :: () -> T_Monad_234
d_SumMonad_310 ~v0 = du_SumMonad_310
du_SumMonad_310 :: T_Monad_234
du_SumMonad_310
  = coe
      C_Monad'46'constructor_14319
      (coe (\ v0 -> coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38))
      (coe (\ v0 v1 -> coe du_sumBind_296))
-- Utils.EitherMonad
d_EitherMonad_316 :: () -> T_Monad_234
d_EitherMonad_316 ~v0 = du_EitherMonad_316
du_EitherMonad_316 :: T_Monad_234
du_EitherMonad_316
  = coe
      C_Monad'46'constructor_14319 (coe (\ v0 -> coe C_inj'8322'_14))
      (coe (\ v0 v1 -> coe du_eitherBind_42))
-- Utils.EitherP
d_EitherP_322 :: () -> T_Monad_234
d_EitherP_322 ~v0 = du_EitherP_322
du_EitherP_322 :: T_Monad_234
du_EitherP_322
  = coe
      C_Monad'46'constructor_14319 (coe (\ v0 -> coe C_inj'8322'_14))
      (coe (\ v0 v1 -> coe du_eitherBind_42))
-- Utils.withE
d_withE_330 ::
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  T_Either_6 AgdaAny AgdaAny -> T_Either_6 AgdaAny AgdaAny
d_withE_330 ~v0 ~v1 ~v2 v3 v4 = du_withE_330 v3 v4
du_withE_330 ::
  (AgdaAny -> AgdaAny) ->
  T_Either_6 AgdaAny AgdaAny -> T_Either_6 AgdaAny AgdaAny
du_withE_330 v0 v1
  = case coe v1 of
      C_inj'8321'_12 v2 -> coe C_inj'8321'_12 (coe v0 v2)
      C_inj'8322'_14 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Utils.dec2Either
d_dec2Either_342 ::
  () ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  T_Either_6
    (AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) AgdaAny
d_dec2Either_342 ~v0 v1 = du_dec2Either_342 v1
du_dec2Either_342 ::
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  T_Either_6
    (AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) AgdaAny
du_dec2Either_342 v0
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
d_Writer_352 a0 a1 = ()
data T_Writer_352 = C__'44'__366 AgdaAny AgdaAny
-- Utils.Writer.wrvalue
d_wrvalue_362 :: T_Writer_352 -> AgdaAny
d_wrvalue_362 v0
  = case coe v0 of
      C__'44'__366 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Utils.Writer.accum
d_accum_364 :: T_Writer_352 -> AgdaAny
d_accum_364 v0
  = case coe v0 of
      C__'44'__366 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Utils.WriterMonad.WriterMonad
d_WriterMonad_376 ::
  () -> AgdaAny -> (AgdaAny -> AgdaAny -> AgdaAny) -> T_Monad_234
d_WriterMonad_376 ~v0 v1 v2 = du_WriterMonad_376 v1 v2
du_WriterMonad_376 ::
  AgdaAny -> (AgdaAny -> AgdaAny -> AgdaAny) -> T_Monad_234
du_WriterMonad_376 v0 v1
  = coe
      C_Monad'46'constructor_14319
      (coe (\ v2 v3 -> coe C__'44'__366 (coe v3) (coe v0)))
      (coe
         (\ v2 v3 v4 ->
            case coe v4 of
              C__'44'__366 v5 v6
                -> coe
                     (\ v7 ->
                        coe
                          C__'44'__366 (coe d_wrvalue_362 (coe v7 v5))
                          (coe v1 v6 (d_accum_364 (coe v7 v5))))
              _ -> MAlonzo.RTE.mazUnreachableError))
-- Utils.WriterMonad.tell
d_tell_392 ::
  () ->
  AgdaAny ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny -> T_Writer_352
d_tell_392 ~v0 ~v1 ~v2 v3 = du_tell_392 v3
du_tell_392 :: AgdaAny -> T_Writer_352
du_tell_392 v0
  = coe
      C__'44'__366 (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8) (coe v0)
-- Utils.RuntimeError
d_RuntimeError_396 = ()
type T_RuntimeError_396 = RuntimeError
pattern C_gasError_398 = GasError
pattern C_userError_400 = UserError
pattern C_runtimeTypeError_402 = RuntimeTypeError
check_gasError_398 :: T_RuntimeError_396
check_gasError_398 = GasError
check_userError_400 :: T_RuntimeError_396
check_userError_400 = UserError
check_runtimeTypeError_402 :: T_RuntimeError_396
check_runtimeTypeError_402 = RuntimeTypeError
cover_RuntimeError_396 :: RuntimeError -> ()
cover_RuntimeError_396 x
  = case x of
      GasError -> ()
      UserError -> ()
      RuntimeTypeError -> ()
-- Utils.ByteString
type T_ByteString_404 = BS.ByteString
d_ByteString_404
  = error
      "MAlonzo Runtime Error: postulate evaluated: Utils.ByteString"
-- Utils.mkByteString
d_mkByteString_406
  = error
      "MAlonzo Runtime Error: postulate evaluated: Utils.mkByteString"
-- Utils.eqByteString
d_eqByteString_408 :: T_ByteString_404 -> T_ByteString_404 -> Bool
d_eqByteString_408 = (==)
-- Utils._×_
d__'215'__414 a0 a1 = ()
type T__'215'__414 a0 a1 = Pair a0 a1
pattern C__'44'__428 a0 a1 = (,) a0 a1
check__'44'__428 ::
  forall xA. forall xB. xA -> xB -> T__'215'__414 xA xB
check__'44'__428 = (,)
cover__'215'__414 :: Pair a1 a2 -> ()
cover__'215'__414 x
  = case x of
      (,) _ _ -> ()
-- Utils._×_.proj₁
d_proj'8321'_424 :: T__'215'__414 AgdaAny AgdaAny -> AgdaAny
d_proj'8321'_424 v0
  = case coe v0 of
      C__'44'__428 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Utils._×_.proj₂
d_proj'8322'_426 :: T__'215'__414 AgdaAny AgdaAny -> AgdaAny
d_proj'8322'_426 v0
  = case coe v0 of
      C__'44'__428 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Utils.List
d_List_432 a0 = ()
type T_List_432 a0 = [] a0
pattern C_'91''93'_436 = []
pattern C__'8759'__438 a0 a1 = (:) a0 a1
check_'91''93'_436 :: forall xA. T_List_432 xA
check_'91''93'_436 = []
check__'8759'__438 ::
  forall xA. xA -> T_List_432 xA -> T_List_432 xA
check__'8759'__438 = (:)
cover_List_432 :: [] a1 -> ()
cover_List_432 x
  = case x of
      [] -> ()
      (:) _ _ -> ()
-- Utils.All
d_All_446 a0 a1 a2 a3 = ()
data T_All_446 = C_'91''93'_454 | C__'8759'__464 AgdaAny T_All_446
-- Utils.length
d_length_468 :: () -> T_List_432 AgdaAny -> Integer
d_length_468 ~v0 v1 = du_length_468 v1
du_length_468 :: T_List_432 AgdaAny -> Integer
du_length_468 v0
  = case coe v0 of
      C_'91''93'_436 -> coe (0 :: Integer)
      C__'8759'__438 v1 v2
        -> coe addInt (coe (1 :: Integer)) (coe du_length_468 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Utils.map
d_map_478 ::
  () ->
  () ->
  (AgdaAny -> AgdaAny) -> T_List_432 AgdaAny -> T_List_432 AgdaAny
d_map_478 ~v0 ~v1 v2 v3 = du_map_478 v2 v3
du_map_478 ::
  (AgdaAny -> AgdaAny) -> T_List_432 AgdaAny -> T_List_432 AgdaAny
du_map_478 v0 v1
  = case coe v1 of
      C_'91''93'_436 -> coe v1
      C__'8759'__438 v2 v3
        -> coe
             C__'8759'__438 (coe v0 v2) (coe du_map_478 (coe v0) (coe v3))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Utils.toList
d_toList_490 :: () -> T_List_432 AgdaAny -> [AgdaAny]
d_toList_490 ~v0 v1 = du_toList_490 v1
du_toList_490 :: T_List_432 AgdaAny -> [AgdaAny]
du_toList_490 v0
  = case coe v0 of
      C_'91''93'_436 -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      C__'8759'__438 v1 v2
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v1)
             (coe du_toList_490 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Utils.fromList
d_fromList_498 :: () -> [AgdaAny] -> T_List_432 AgdaAny
d_fromList_498 ~v0 v1 = du_fromList_498 v1
du_fromList_498 :: [AgdaAny] -> T_List_432 AgdaAny
du_fromList_498 v0
  = case coe v0 of
      [] -> coe C_'91''93'_436
      (:) v1 v2
        -> coe C__'8759'__438 (coe v1) (coe du_fromList_498 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Utils.dropLIST
d_dropLIST_506 ::
  () -> Integer -> T_List_432 AgdaAny -> T_List_432 AgdaAny
d_dropLIST_506 ~v0 v1 v2 = du_dropLIST_506 v1 v2
du_dropLIST_506 ::
  Integer -> T_List_432 AgdaAny -> T_List_432 AgdaAny
du_dropLIST_506 v0 v1
  = case coe v0 of
      _ | coe geqInt (coe v0) (coe (0 :: Integer)) ->
          coe du_drop_518 (coe v0) (coe v1)
      _ -> coe v1
-- Utils._.drop
d_drop_518 ::
  () ->
  Integer ->
  T_List_432 AgdaAny ->
  () -> Integer -> T_List_432 AgdaAny -> T_List_432 AgdaAny
d_drop_518 ~v0 ~v1 ~v2 ~v3 v4 v5 = du_drop_518 v4 v5
du_drop_518 :: Integer -> T_List_432 AgdaAny -> T_List_432 AgdaAny
du_drop_518 v0 v1
  = case coe v0 of
      0 -> coe v1
      _ -> let v2 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (case coe v1 of
                C_'91''93'_436 -> coe v1
                C__'8759'__438 v3 v4 -> coe du_drop_518 (coe v2) (coe v4)
                _ -> MAlonzo.RTE.mazUnreachableError)
-- Utils.map-cong
d_map'45'cong_542 ::
  () ->
  () ->
  [AgdaAny] ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_map'45'cong_542 = erased
-- Utils.sequence
d_sequence_558 ::
  () -> (() -> ()) -> T_Monad_234 -> T_List_432 AgdaAny -> AgdaAny
d_sequence_558 ~v0 ~v1 v2 v3 = du_sequence_558 v2 v3
du_sequence_558 :: T_Monad_234 -> T_List_432 AgdaAny -> AgdaAny
du_sequence_558 v0 v1
  = case coe v1 of
      C_'91''93'_436 -> coe d_return_250 v0 erased v1
      C__'8759'__438 v2 v3
        -> coe
             d__'62''62''61'__256 v0 erased erased v2
             (\ v4 ->
                coe
                  d__'62''62''61'__256 v0 erased erased
                  (coe du_sequence_558 (coe v0) (coe v3))
                  (\ v5 ->
                     coe d_return_250 v0 erased (coe C__'8759'__438 (coe v4) (coe v5))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Utils.mapM
d_mapM_576 ::
  () ->
  () ->
  (() -> ()) ->
  T_Monad_234 ->
  (AgdaAny -> AgdaAny) -> T_List_432 AgdaAny -> AgdaAny
d_mapM_576 ~v0 ~v1 ~v2 v3 v4 v5 = du_mapM_576 v3 v4 v5
du_mapM_576 ::
  T_Monad_234 ->
  (AgdaAny -> AgdaAny) -> T_List_432 AgdaAny -> AgdaAny
du_mapM_576 v0 v1 v2
  = coe du_sequence_558 (coe v0) (coe du_map_478 (coe v1) (coe v2))
-- Utils.Array
type T_Array_580 a0 = Strict.Vector a0
d_Array_580
  = error "MAlonzo Runtime Error: postulate evaluated: Utils.Array"
-- Utils.HSlengthOfArray
d_HSlengthOfArray_584 :: forall xA. () -> T_Array_580 xA -> Integer
d_HSlengthOfArray_584 = \() -> \as -> toInteger (Strict.length as)
-- Utils.HSlistToArray
d_HSlistToArray_588 ::
  forall xA. () -> T_List_432 xA -> T_Array_580 xA
d_HSlistToArray_588 = \() -> Strict.fromList
-- Utils.HSindexArray
d_HSindexArray_590 ::
  forall xA. () -> T_Array_580 xA -> Integer -> xA
d_HSindexArray_590
  = \() -> \as -> \i -> as Strict.! (fromInteger i)
-- Utils.mkArray
d_mkArray_594
  = error "MAlonzo Runtime Error: postulate evaluated: Utils.mkArray"
-- Utils.DATA
d_DATA_596 = ()
type T_DATA_596 = Data
pattern C_ConstrDATA_598 a0 a1 = D.Constr a0 a1
pattern C_MapDATA_600 a0 = D.Map a0
pattern C_ListDATA_602 a0 = D.List a0
pattern C_iDATA_604 a0 = D.I a0
pattern C_bDATA_606 a0 = D.B a0
check_ConstrDATA_598 ::
  Integer -> T_List_432 T_DATA_596 -> T_DATA_596
check_ConstrDATA_598 = D.Constr
check_MapDATA_600 ::
  T_List_432 (T__'215'__414 T_DATA_596 T_DATA_596) -> T_DATA_596
check_MapDATA_600 = D.Map
check_ListDATA_602 :: T_List_432 T_DATA_596 -> T_DATA_596
check_ListDATA_602 = D.List
check_iDATA_604 :: Integer -> T_DATA_596
check_iDATA_604 = D.I
check_bDATA_606 :: T_ByteString_404 -> T_DATA_596
check_bDATA_606 = D.B
cover_DATA_596 :: Data -> ()
cover_DATA_596 x
  = case x of
      D.Constr _ _ -> ()
      D.Map _ -> ()
      D.List _ -> ()
      D.I _ -> ()
      D.B _ -> ()
-- Utils.eqDATA
d_eqDATA_608 :: T_DATA_596 -> T_DATA_596 -> Bool
d_eqDATA_608 = (==)
-- Utils.Bls12-381-G1-Element
type T_Bls12'45'381'45'G1'45'Element_742 = G1.Element
d_Bls12'45'381'45'G1'45'Element_742
  = error
      "MAlonzo Runtime Error: postulate evaluated: Utils.Bls12-381-G1-Element"
-- Utils.eqBls12-381-G1-Element
d_eqBls12'45'381'45'G1'45'Element_744 ::
  T_Bls12'45'381'45'G1'45'Element_742 ->
  T_Bls12'45'381'45'G1'45'Element_742 -> Bool
d_eqBls12'45'381'45'G1'45'Element_744 = (==)
-- Utils.Bls12-381-G2-Element
type T_Bls12'45'381'45'G2'45'Element_746 = G2.Element
d_Bls12'45'381'45'G2'45'Element_746
  = error
      "MAlonzo Runtime Error: postulate evaluated: Utils.Bls12-381-G2-Element"
-- Utils.eqBls12-381-G2-Element
d_eqBls12'45'381'45'G2'45'Element_748 ::
  T_Bls12'45'381'45'G2'45'Element_746 ->
  T_Bls12'45'381'45'G2'45'Element_746 -> Bool
d_eqBls12'45'381'45'G2'45'Element_748 = (==)
-- Utils.Bls12-381-MlResult
type T_Bls12'45'381'45'MlResult_750 = Pairing.MlResult
d_Bls12'45'381'45'MlResult_750
  = error
      "MAlonzo Runtime Error: postulate evaluated: Utils.Bls12-381-MlResult"
-- Utils.eqBls12-381-MlResult
d_eqBls12'45'381'45'MlResult_752 ::
  T_Bls12'45'381'45'MlResult_750 ->
  T_Bls12'45'381'45'MlResult_750 -> Bool
d_eqBls12'45'381'45'MlResult_752 = (==)
-- Utils.Kind
d_Kind_754 = ()
type T_Kind_754 = KIND
pattern C_'42'_756 = Star
pattern C_'9839'_758 = Sharp
pattern C__'8658'__760 a0 a1 = Arrow a0 a1
check_'42'_756 :: T_Kind_754
check_'42'_756 = Star
check_'9839'_758 :: T_Kind_754
check_'9839'_758 = Sharp
check__'8658'__760 :: T_Kind_754 -> T_Kind_754 -> T_Kind_754
check__'8658'__760 = Arrow
cover_Kind_754 :: KIND -> ()
cover_Kind_754 x
  = case x of
      Star -> ()
      Sharp -> ()
      Arrow _ _ -> ()
