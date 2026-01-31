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
-- Utils.natToFin
d_natToFin_80 ::
  Integer -> Integer -> Maybe MAlonzo.Code.Data.Fin.Base.T_Fin_10
d_natToFin_80 v0 v1
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
d_cong'8323'_122 ::
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
d_cong'8323'_122 = erased
-- Utils.≡-subst-removable
d_'8801''45'subst'45'removable_144 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> ()) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8801''45'subst'45'removable_144 = erased
-- Utils._∔_≣_
d__'8724'_'8803'__150 a0 a1 a2 = ()
data T__'8724'_'8803'__150
  = C_start_154 | C_bubble_162 T__'8724'_'8803'__150
-- Utils.unique∔
d_unique'8724'_174 ::
  Integer ->
  Integer ->
  Integer ->
  T__'8724'_'8803'__150 ->
  T__'8724'_'8803'__150 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_unique'8724'_174 = erased
-- Utils.+2∔
d_'43'2'8724'_186 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T__'8724'_'8803'__150
d_'43'2'8724'_186 v0 ~v1 ~v2 ~v3 = du_'43'2'8724'_186 v0
du_'43'2'8724'_186 :: Integer -> T__'8724'_'8803'__150
du_'43'2'8724'_186 v0
  = case coe v0 of
      0 -> coe C_start_154
      _ -> let v1 = subInt (coe v0) (coe (1 :: Integer)) in
           coe (coe C_bubble_162 (coe du_'43'2'8724'_186 (coe v1)))
-- Utils.∔2+
d_'8724'2'43'_204 ::
  Integer ->
  Integer ->
  Integer ->
  T__'8724'_'8803'__150 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8724'2'43'_204 = erased
-- Utils.alldone
d_alldone_210 :: Integer -> T__'8724'_'8803'__150
d_alldone_210 v0 = coe du_'43'2'8724'_186 (coe v0)
-- Utils.Monad
d_Monad_216 a0 = ()
data T_Monad_216
  = C_Monad'46'constructor_13569 (() -> AgdaAny -> AgdaAny)
                                 (() -> () -> AgdaAny -> (AgdaAny -> AgdaAny) -> AgdaAny)
-- Utils.Monad.return
d_return_232 :: T_Monad_216 -> () -> AgdaAny -> AgdaAny
d_return_232 v0
  = case coe v0 of
      C_Monad'46'constructor_13569 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Utils.Monad._>>=_
d__'62''62''61'__238 ::
  T_Monad_216 ->
  () -> () -> AgdaAny -> (AgdaAny -> AgdaAny) -> AgdaAny
d__'62''62''61'__238 v0
  = case coe v0 of
      C_Monad'46'constructor_13569 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Utils.Monad._>>_
d__'62''62'__244 ::
  (() -> ()) ->
  T_Monad_216 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d__'62''62'__244 ~v0 v1 ~v2 ~v3 v4 v5 = du__'62''62'__244 v1 v4 v5
du__'62''62'__244 :: T_Monad_216 -> AgdaAny -> AgdaAny -> AgdaAny
du__'62''62'__244 v0 v1 v2
  = coe d__'62''62''61'__238 v0 erased erased v1 (\ v3 -> v2)
-- Utils.Monad.fmap
d_fmap_254 ::
  (() -> ()) ->
  T_Monad_216 ->
  () -> () -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_fmap_254 ~v0 v1 ~v2 ~v3 v4 v5 = du_fmap_254 v1 v4 v5
du_fmap_254 ::
  T_Monad_216 -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du_fmap_254 v0 v1 v2
  = coe
      d__'62''62''61'__238 v0 erased erased v2
      (\ v3 -> coe d_return_232 v0 erased (coe v1 v3))
-- Utils._._>>_
d__'62''62'__262 ::
  (() -> ()) ->
  T_Monad_216 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d__'62''62'__262 ~v0 v1 = du__'62''62'__262 v1
du__'62''62'__262 ::
  T_Monad_216 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
du__'62''62'__262 v0 v1 v2 v3 v4
  = coe du__'62''62'__244 (coe v0) v3 v4
-- Utils._._>>=_
d__'62''62''61'__264 ::
  T_Monad_216 ->
  () -> () -> AgdaAny -> (AgdaAny -> AgdaAny) -> AgdaAny
d__'62''62''61'__264 v0 = coe d__'62''62''61'__238 (coe v0)
-- Utils._.fmap
d_fmap_266 ::
  (() -> ()) ->
  T_Monad_216 ->
  () -> () -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_fmap_266 ~v0 v1 = du_fmap_266 v1
du_fmap_266 ::
  T_Monad_216 ->
  () -> () -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du_fmap_266 v0 v1 v2 v3 v4 = coe du_fmap_254 (coe v0) v3 v4
-- Utils._.return
d_return_268 :: T_Monad_216 -> () -> AgdaAny -> AgdaAny
d_return_268 v0 = coe d_return_232 (coe v0)
-- Utils.MaybeMonad
d_MaybeMonad_270 :: T_Monad_216
d_MaybeMonad_270
  = coe
      C_Monad'46'constructor_13569
      (coe (\ v0 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16))
      (coe
         (\ v0 v1 v2 v3 ->
            coe MAlonzo.Code.Data.Maybe.Base.du__'62''62''61'__72 v2 v3))
-- Utils.sumBind
d_sumBind_278 ::
  () ->
  () ->
  () ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  (AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30) ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_sumBind_278 ~v0 ~v1 ~v2 v3 v4 = du_sumBind_278 v3 v4
du_sumBind_278 ::
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  (AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30) ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_sumBind_278 v0 v1
  = case coe v0 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v2 -> coe v1 v2
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v2 -> coe v0
      _ -> MAlonzo.RTE.mazUnreachableError
-- Utils.SumMonad
d_SumMonad_292 :: () -> T_Monad_216
d_SumMonad_292 ~v0 = du_SumMonad_292
du_SumMonad_292 :: T_Monad_216
du_SumMonad_292
  = coe
      C_Monad'46'constructor_13569
      (coe (\ v0 -> coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38))
      (coe (\ v0 v1 -> coe du_sumBind_278))
-- Utils.EitherMonad
d_EitherMonad_298 :: () -> T_Monad_216
d_EitherMonad_298 ~v0 = du_EitherMonad_298
du_EitherMonad_298 :: T_Monad_216
du_EitherMonad_298
  = coe
      C_Monad'46'constructor_13569 (coe (\ v0 -> coe C_inj'8322'_14))
      (coe (\ v0 v1 -> coe du_eitherBind_42))
-- Utils.EitherP
d_EitherP_304 :: () -> T_Monad_216
d_EitherP_304 ~v0 = du_EitherP_304
du_EitherP_304 :: T_Monad_216
du_EitherP_304
  = coe
      C_Monad'46'constructor_13569 (coe (\ v0 -> coe C_inj'8322'_14))
      (coe (\ v0 v1 -> coe du_eitherBind_42))
-- Utils.withE
d_withE_312 ::
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  T_Either_6 AgdaAny AgdaAny -> T_Either_6 AgdaAny AgdaAny
d_withE_312 ~v0 ~v1 ~v2 v3 v4 = du_withE_312 v3 v4
du_withE_312 ::
  (AgdaAny -> AgdaAny) ->
  T_Either_6 AgdaAny AgdaAny -> T_Either_6 AgdaAny AgdaAny
du_withE_312 v0 v1
  = case coe v1 of
      C_inj'8321'_12 v2 -> coe C_inj'8321'_12 (coe v0 v2)
      C_inj'8322'_14 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Utils.dec2Either
d_dec2Either_324 ::
  () ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  T_Either_6
    (AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) AgdaAny
d_dec2Either_324 ~v0 v1 = du_dec2Either_324 v1
du_dec2Either_324 ::
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  T_Either_6
    (AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) AgdaAny
du_dec2Either_324 v0
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
d_Writer_334 a0 a1 = ()
data T_Writer_334 = C__'44'__348 AgdaAny AgdaAny
-- Utils.Writer.wrvalue
d_wrvalue_344 :: T_Writer_334 -> AgdaAny
d_wrvalue_344 v0
  = case coe v0 of
      C__'44'__348 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Utils.Writer.accum
d_accum_346 :: T_Writer_334 -> AgdaAny
d_accum_346 v0
  = case coe v0 of
      C__'44'__348 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Utils.WriterMonad.WriterMonad
d_WriterMonad_358 ::
  () -> AgdaAny -> (AgdaAny -> AgdaAny -> AgdaAny) -> T_Monad_216
d_WriterMonad_358 ~v0 v1 v2 = du_WriterMonad_358 v1 v2
du_WriterMonad_358 ::
  AgdaAny -> (AgdaAny -> AgdaAny -> AgdaAny) -> T_Monad_216
du_WriterMonad_358 v0 v1
  = coe
      C_Monad'46'constructor_13569
      (coe (\ v2 v3 -> coe C__'44'__348 (coe v3) (coe v0)))
      (coe
         (\ v2 v3 v4 ->
            case coe v4 of
              C__'44'__348 v5 v6
                -> coe
                     (\ v7 ->
                        coe
                          C__'44'__348 (coe d_wrvalue_344 (coe v7 v5))
                          (coe v1 v6 (d_accum_346 (coe v7 v5))))
              _ -> MAlonzo.RTE.mazUnreachableError))
-- Utils.WriterMonad.tell
d_tell_374 ::
  () ->
  AgdaAny ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny -> T_Writer_334
d_tell_374 ~v0 ~v1 ~v2 v3 = du_tell_374 v3
du_tell_374 :: AgdaAny -> T_Writer_334
du_tell_374 v0
  = coe
      C__'44'__348 (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8) (coe v0)
-- Utils.RuntimeError
d_RuntimeError_378 = ()
type T_RuntimeError_378 = RuntimeError
pattern C_gasError_380 = GasError
pattern C_userError_382 = UserError
pattern C_runtimeTypeError_384 = RuntimeTypeError
check_gasError_380 :: T_RuntimeError_378
check_gasError_380 = GasError
check_userError_382 :: T_RuntimeError_378
check_userError_382 = UserError
check_runtimeTypeError_384 :: T_RuntimeError_378
check_runtimeTypeError_384 = RuntimeTypeError
cover_RuntimeError_378 :: RuntimeError -> ()
cover_RuntimeError_378 x
  = case x of
      GasError -> ()
      UserError -> ()
      RuntimeTypeError -> ()
-- Utils.ByteString
type T_ByteString_386 = BS.ByteString
d_ByteString_386
  = error
      "MAlonzo Runtime Error: postulate evaluated: Utils.ByteString"
-- Utils.mkByteString
d_mkByteString_388
  = error
      "MAlonzo Runtime Error: postulate evaluated: Utils.mkByteString"
-- Utils.eqByteString
d_eqByteString_390 :: T_ByteString_386 -> T_ByteString_386 -> Bool
d_eqByteString_390 = (==)
-- Utils._×_
d__'215'__396 a0 a1 = ()
type T__'215'__396 a0 a1 = Pair a0 a1
pattern C__'44'__410 a0 a1 = (,) a0 a1
check__'44'__410 ::
  forall xA. forall xB. xA -> xB -> T__'215'__396 xA xB
check__'44'__410 = (,)
cover__'215'__396 :: Pair a1 a2 -> ()
cover__'215'__396 x
  = case x of
      (,) _ _ -> ()
-- Utils._×_.proj₁
d_proj'8321'_406 :: T__'215'__396 AgdaAny AgdaAny -> AgdaAny
d_proj'8321'_406 v0
  = case coe v0 of
      C__'44'__410 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Utils._×_.proj₂
d_proj'8322'_408 :: T__'215'__396 AgdaAny AgdaAny -> AgdaAny
d_proj'8322'_408 v0
  = case coe v0 of
      C__'44'__410 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Utils.List
d_List_414 a0 = ()
type T_List_414 a0 = [] a0
pattern C_'91''93'_418 = []
pattern C__'8759'__420 a0 a1 = (:) a0 a1
check_'91''93'_418 :: forall xA. T_List_414 xA
check_'91''93'_418 = []
check__'8759'__420 ::
  forall xA. xA -> T_List_414 xA -> T_List_414 xA
check__'8759'__420 = (:)
cover_List_414 :: [] a1 -> ()
cover_List_414 x
  = case x of
      [] -> ()
      (:) _ _ -> ()
-- Utils.length
d_length_424 :: () -> T_List_414 AgdaAny -> Integer
d_length_424 ~v0 v1 = du_length_424 v1
du_length_424 :: T_List_414 AgdaAny -> Integer
du_length_424 v0
  = case coe v0 of
      C_'91''93'_418 -> coe (0 :: Integer)
      C__'8759'__420 v1 v2
        -> coe addInt (coe (1 :: Integer)) (coe du_length_424 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Utils.map
d_map_434 ::
  () ->
  () ->
  (AgdaAny -> AgdaAny) -> T_List_414 AgdaAny -> T_List_414 AgdaAny
d_map_434 ~v0 ~v1 v2 v3 = du_map_434 v2 v3
du_map_434 ::
  (AgdaAny -> AgdaAny) -> T_List_414 AgdaAny -> T_List_414 AgdaAny
du_map_434 v0 v1
  = case coe v1 of
      C_'91''93'_418 -> coe v1
      C__'8759'__420 v2 v3
        -> coe
             C__'8759'__420 (coe v0 v2) (coe du_map_434 (coe v0) (coe v3))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Utils.toList
d_toList_446 :: () -> T_List_414 AgdaAny -> [AgdaAny]
d_toList_446 ~v0 v1 = du_toList_446 v1
du_toList_446 :: T_List_414 AgdaAny -> [AgdaAny]
du_toList_446 v0
  = case coe v0 of
      C_'91''93'_418 -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      C__'8759'__420 v1 v2
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v1)
             (coe du_toList_446 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Utils.fromList
d_fromList_454 :: () -> [AgdaAny] -> T_List_414 AgdaAny
d_fromList_454 ~v0 v1 = du_fromList_454 v1
du_fromList_454 :: [AgdaAny] -> T_List_414 AgdaAny
du_fromList_454 v0
  = case coe v0 of
      [] -> coe C_'91''93'_418
      (:) v1 v2
        -> coe C__'8759'__420 (coe v1) (coe du_fromList_454 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Utils.dropLIST
d_dropLIST_462 ::
  () -> Integer -> T_List_414 AgdaAny -> T_List_414 AgdaAny
d_dropLIST_462 ~v0 v1 v2 = du_dropLIST_462 v1 v2
du_dropLIST_462 ::
  Integer -> T_List_414 AgdaAny -> T_List_414 AgdaAny
du_dropLIST_462 v0 v1
  = case coe v0 of
      _ | coe geqInt (coe v0) (coe (0 :: Integer)) ->
          coe du_drop_474 (coe v0) (coe v1)
      _ -> coe v1
-- Utils._.drop
d_drop_474 ::
  () ->
  Integer ->
  T_List_414 AgdaAny ->
  () -> Integer -> T_List_414 AgdaAny -> T_List_414 AgdaAny
d_drop_474 ~v0 ~v1 ~v2 ~v3 v4 v5 = du_drop_474 v4 v5
du_drop_474 :: Integer -> T_List_414 AgdaAny -> T_List_414 AgdaAny
du_drop_474 v0 v1
  = case coe v0 of
      0 -> coe v1
      _ -> let v2 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (case coe v1 of
                C_'91''93'_418 -> coe v1
                C__'8759'__420 v3 v4 -> coe du_drop_474 (coe v2) (coe v4)
                _ -> MAlonzo.RTE.mazUnreachableError)
-- Utils.map-cong
d_map'45'cong_498 ::
  () ->
  () ->
  [AgdaAny] ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_map'45'cong_498 = erased
-- Utils.Array
type T_Array_508 a0 = Strict.Vector a0
d_Array_508
  = error "MAlonzo Runtime Error: postulate evaluated: Utils.Array"
-- Utils.HSlengthOfArray
d_HSlengthOfArray_512 :: forall xA. () -> T_Array_508 xA -> Integer
d_HSlengthOfArray_512 = \() -> \as -> toInteger (Strict.length as)
-- Utils.HSlistToArray
d_HSlistToArray_516 ::
  forall xA. () -> T_List_414 xA -> T_Array_508 xA
d_HSlistToArray_516 = \() -> Strict.fromList
-- Utils.HSindexArray
d_HSindexArray_518 ::
  forall xA. () -> T_Array_508 xA -> Integer -> xA
d_HSindexArray_518
  = \() -> \as -> \i -> as Strict.! (fromInteger i)
-- Utils.mkArray
d_mkArray_522
  = error "MAlonzo Runtime Error: postulate evaluated: Utils.mkArray"
-- Utils.DATA
d_DATA_524 = ()
type T_DATA_524 = Data
pattern C_ConstrDATA_526 a0 a1 = D.Constr a0 a1
pattern C_MapDATA_528 a0 = D.Map a0
pattern C_ListDATA_530 a0 = D.List a0
pattern C_iDATA_532 a0 = D.I a0
pattern C_bDATA_534 a0 = D.B a0
check_ConstrDATA_526 ::
  Integer -> T_List_414 T_DATA_524 -> T_DATA_524
check_ConstrDATA_526 = D.Constr
check_MapDATA_528 ::
  T_List_414 (T__'215'__396 T_DATA_524 T_DATA_524) -> T_DATA_524
check_MapDATA_528 = D.Map
check_ListDATA_530 :: T_List_414 T_DATA_524 -> T_DATA_524
check_ListDATA_530 = D.List
check_iDATA_532 :: Integer -> T_DATA_524
check_iDATA_532 = D.I
check_bDATA_534 :: T_ByteString_386 -> T_DATA_524
check_bDATA_534 = D.B
cover_DATA_524 :: Data -> ()
cover_DATA_524 x
  = case x of
      D.Constr _ _ -> ()
      D.Map _ -> ()
      D.List _ -> ()
      D.I _ -> ()
      D.B _ -> ()
-- Utils.eqDATA
d_eqDATA_536 :: T_DATA_524 -> T_DATA_524 -> Bool
d_eqDATA_536 = (==)
-- Utils.Bls12-381-G1-Element
type T_Bls12'45'381'45'G1'45'Element_670 = G1.Element
d_Bls12'45'381'45'G1'45'Element_670
  = error
      "MAlonzo Runtime Error: postulate evaluated: Utils.Bls12-381-G1-Element"
-- Utils.eqBls12-381-G1-Element
d_eqBls12'45'381'45'G1'45'Element_672 ::
  T_Bls12'45'381'45'G1'45'Element_670 ->
  T_Bls12'45'381'45'G1'45'Element_670 -> Bool
d_eqBls12'45'381'45'G1'45'Element_672 = (==)
-- Utils.Bls12-381-G2-Element
type T_Bls12'45'381'45'G2'45'Element_674 = G2.Element
d_Bls12'45'381'45'G2'45'Element_674
  = error
      "MAlonzo Runtime Error: postulate evaluated: Utils.Bls12-381-G2-Element"
-- Utils.eqBls12-381-G2-Element
d_eqBls12'45'381'45'G2'45'Element_676 ::
  T_Bls12'45'381'45'G2'45'Element_674 ->
  T_Bls12'45'381'45'G2'45'Element_674 -> Bool
d_eqBls12'45'381'45'G2'45'Element_676 = (==)
-- Utils.Bls12-381-MlResult
type T_Bls12'45'381'45'MlResult_678 = Pairing.MlResult
d_Bls12'45'381'45'MlResult_678
  = error
      "MAlonzo Runtime Error: postulate evaluated: Utils.Bls12-381-MlResult"
-- Utils.eqBls12-381-MlResult
d_eqBls12'45'381'45'MlResult_680 ::
  T_Bls12'45'381'45'MlResult_678 ->
  T_Bls12'45'381'45'MlResult_678 -> Bool
d_eqBls12'45'381'45'MlResult_680 = (==)
-- Utils.Kind
d_Kind_682 = ()
type T_Kind_682 = KIND
pattern C_'42'_684 = Star
pattern C_'9839'_686 = Sharp
pattern C__'8658'__688 a0 a1 = Arrow a0 a1
check_'42'_684 :: T_Kind_682
check_'42'_684 = Star
check_'9839'_686 :: T_Kind_682
check_'9839'_686 = Sharp
check__'8658'__688 :: T_Kind_682 -> T_Kind_682 -> T_Kind_682
check__'8658'__688 = Arrow
cover_Kind_682 :: KIND -> ()
cover_Kind_682 x
  = case x of
      Star -> ()
      Sharp -> ()
      Arrow _ _ -> ()
-- Utils.M.f
d_f_670 :: () -> AgdaAny -> AgdaAny
d_f_670 ~v0 v1 = du_f_670 v1
du_f_670 :: AgdaAny -> AgdaAny
du_f_670 v0 = coe v0
-- Utils.MNat.f
d_f_676 :: Integer -> Integer
d_f_676 v0 = coe v0
-- Utils.testM
d_testM_680 :: () -> AgdaAny -> AgdaAny
d_testM_680 ~v0 v1 = du_testM_680 v1
du_testM_680 :: AgdaAny -> AgdaAny
du_testM_680 v0 = coe v0
-- Utils.ByteString'
d_ByteString''_682 = ()
data T_ByteString''_682
  = C_mkBS_708 AgdaAny (AgdaAny -> AgdaAny -> AgdaAny)
               (T_List_384 AgdaAny -> AgdaAny) (AgdaAny -> T_List_384 AgdaAny)
-- Utils.ByteString'.W8
d_W8_696 :: T_ByteString''_682 -> ()
d_W8_696 = erased
-- Utils.ByteString'.BS
d_BS_698 :: T_ByteString''_682 -> ()
d_BS_698 = erased
-- Utils.ByteString'.empty
d_empty_700 :: T_ByteString''_682 -> AgdaAny
d_empty_700 v0
  = case coe v0 of
      C_mkBS_708 v3 v4 v5 v6 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Utils.ByteString'.cons
d_cons_702 :: T_ByteString''_682 -> AgdaAny -> AgdaAny -> AgdaAny
d_cons_702 v0
  = case coe v0 of
      C_mkBS_708 v3 v4 v5 v6 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Utils.ByteString'.pack
d_pack_704 :: T_ByteString''_682 -> T_List_384 AgdaAny -> AgdaAny
d_pack_704 v0
  = case coe v0 of
      C_mkBS_708 v3 v4 v5 v6 -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Utils.ByteString'.unpack
d_unpack_706 :: T_ByteString''_682 -> AgdaAny -> T_List_384 AgdaAny
d_unpack_706 v0
  = case coe v0 of
      C_mkBS_708 v3 v4 v5 v6 -> coe v6
      _ -> MAlonzo.RTE.mazUnreachableError
-- Utils.b
d_b_710 :: T_ByteString''_682
d_b_710
  = coe
      C_mkBS_708 (coe C_'91''93'_388) (coe C__'8759'__390) (\ v0 -> v0)
      (\ v0 -> v0)
-- Utils.AST1._.BS
d_BS_722 :: T_ByteString''_682 -> ()
d_BS_722 = erased
-- Utils.AST1._.W8
d_W8_724 :: T_ByteString''_682 -> ()
d_W8_724 = erased
-- Utils.AST1._.cons
d_cons_726 :: T_ByteString''_682 -> AgdaAny -> AgdaAny -> AgdaAny
d_cons_726 v0 = coe d_cons_702 (coe v0)
-- Utils.AST1._.empty
d_empty_728 :: T_ByteString''_682 -> AgdaAny
d_empty_728 v0 = coe d_empty_700 (coe v0)
-- Utils.AST1._.pack
d_pack_730 :: T_ByteString''_682 -> T_List_384 AgdaAny -> AgdaAny
d_pack_730 v0 = coe d_pack_704 (coe v0)
-- Utils.AST1._.unpack
d_unpack_732 :: T_ByteString''_682 -> AgdaAny -> T_List_384 AgdaAny
d_unpack_732 v0 = coe d_unpack_706 (coe v0)
-- Utils.AST1.x
d_x_734 :: T_ByteString''_682 -> AgdaAny
d_x_734 v0 = coe d_empty_700 (coe v0)
