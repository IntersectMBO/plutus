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
-- Utils.is-inj₁
d_is'45'inj'8321'_40 ::
  () -> () -> T_Either_6 AgdaAny AgdaAny -> Bool
d_is'45'inj'8321'_40 ~v0 ~v1 v2 = du_is'45'inj'8321'_40 v2
du_is'45'inj'8321'_40 :: T_Either_6 AgdaAny AgdaAny -> Bool
du_is'45'inj'8321'_40 v0
  = case coe v0 of
      C_inj'8321'_12 v1 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      C_inj'8322'_14 v1 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      _ -> MAlonzo.RTE.mazUnreachableError
-- Utils.is-inj₂
d_is'45'inj'8322'_46 ::
  () -> () -> T_Either_6 AgdaAny AgdaAny -> Bool
d_is'45'inj'8322'_46 ~v0 ~v1 v2 = du_is'45'inj'8322'_46 v2
du_is'45'inj'8322'_46 :: T_Either_6 AgdaAny AgdaAny -> Bool
du_is'45'inj'8322'_46 v0
  = case coe v0 of
      C_inj'8321'_12 v1 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      C_inj'8322'_14 v1 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      _ -> MAlonzo.RTE.mazUnreachableError
-- Utils.eitherBind
d_eitherBind_54 ::
  () ->
  () ->
  () ->
  T_Either_6 AgdaAny AgdaAny ->
  (AgdaAny -> T_Either_6 AgdaAny AgdaAny) ->
  T_Either_6 AgdaAny AgdaAny
d_eitherBind_54 ~v0 ~v1 ~v2 v3 v4 = du_eitherBind_54 v3 v4
du_eitherBind_54 ::
  T_Either_6 AgdaAny AgdaAny ->
  (AgdaAny -> T_Either_6 AgdaAny AgdaAny) ->
  T_Either_6 AgdaAny AgdaAny
du_eitherBind_54 v0 v1
  = case coe v0 of
      C_inj'8321'_12 v2 -> coe v0
      C_inj'8322'_14 v2 -> coe v1 v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Utils.decIf
d_decIf_68 ::
  () ->
  () ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  AgdaAny -> AgdaAny -> AgdaAny
d_decIf_68 ~v0 ~v1 v2 v3 v4 = du_decIf_68 v2 v3 v4
du_decIf_68 ::
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  AgdaAny -> AgdaAny -> AgdaAny
du_decIf_68 v0 v1 v2
  = case coe v0 of
      MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v3 v4
        -> if coe v3
             then coe seq (coe v4) (coe v1)
             else coe seq (coe v4) (coe v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Utils.maybeToEither
d_maybeToEither_86 ::
  () -> () -> AgdaAny -> Maybe AgdaAny -> T_Either_6 AgdaAny AgdaAny
d_maybeToEither_86 ~v0 ~v1 v2 = du_maybeToEither_86 v2
du_maybeToEither_86 ::
  AgdaAny -> Maybe AgdaAny -> T_Either_6 AgdaAny AgdaAny
du_maybeToEither_86 v0
  = coe
      MAlonzo.Code.Data.Maybe.Base.du_maybe_32 (coe C_inj'8322'_14)
      (coe C_inj'8321'_12 (coe v0))
-- Utils.try
d_try_94 ::
  () -> () -> Maybe AgdaAny -> AgdaAny -> T_Either_6 AgdaAny AgdaAny
d_try_94 ~v0 ~v1 v2 v3 = du_try_94 v2 v3
du_try_94 :: Maybe AgdaAny -> AgdaAny -> T_Either_6 AgdaAny AgdaAny
du_try_94 v0 v1
  = coe
      MAlonzo.Code.Data.Maybe.Base.du_maybe_32 (coe C_inj'8322'_14)
      (coe C_inj'8321'_12 (coe v1)) (coe v0)
-- Utils.eitherToMaybe
d_eitherToMaybe_104 ::
  () -> () -> T_Either_6 AgdaAny AgdaAny -> Maybe AgdaAny
d_eitherToMaybe_104 ~v0 ~v1 v2 = du_eitherToMaybe_104 v2
du_eitherToMaybe_104 :: T_Either_6 AgdaAny AgdaAny -> Maybe AgdaAny
du_eitherToMaybe_104 v0
  = case coe v0 of
      C_inj'8321'_12 v1
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      C_inj'8322'_14 v1
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Utils.natToFin
d_natToFin_110 ::
  Integer -> Integer -> Maybe MAlonzo.Code.Data.Fin.Base.T_Fin_10
d_natToFin_110 v0 v1
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
d_cong'8323'_152 ::
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
d_cong'8323'_152 = erased
-- Utils.≡-subst-removable
d_'8801''45'subst'45'removable_174 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> ()) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8801''45'subst'45'removable_174 = erased
-- Utils._∔_≣_
d__'8724'_'8803'__180 a0 a1 a2 = ()
data T__'8724'_'8803'__180
  = C_start_184 | C_bubble_192 T__'8724'_'8803'__180
-- Utils.unique∔
d_unique'8724'_204 ::
  Integer ->
  Integer ->
  Integer ->
  T__'8724'_'8803'__180 ->
  T__'8724'_'8803'__180 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_unique'8724'_204 = erased
-- Utils.+2∔
d_'43'2'8724'_216 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T__'8724'_'8803'__180
d_'43'2'8724'_216 v0 ~v1 ~v2 ~v3 = du_'43'2'8724'_216 v0
du_'43'2'8724'_216 :: Integer -> T__'8724'_'8803'__180
du_'43'2'8724'_216 v0
  = case coe v0 of
      0 -> coe C_start_184
      _ -> let v1 = subInt (coe v0) (coe (1 :: Integer)) in
           coe (coe C_bubble_192 (coe du_'43'2'8724'_216 (coe v1)))
-- Utils.∔2+
d_'8724'2'43'_234 ::
  Integer ->
  Integer ->
  Integer ->
  T__'8724'_'8803'__180 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8724'2'43'_234 = erased
-- Utils.alldone
d_alldone_240 :: Integer -> T__'8724'_'8803'__180
d_alldone_240 v0 = coe du_'43'2'8724'_216 (coe v0)
-- Utils.Monad
d_Monad_246 a0 = ()
data T_Monad_246
  = C_Monad'46'constructor_14947 (() -> AgdaAny -> AgdaAny)
                                 (() -> () -> AgdaAny -> (AgdaAny -> AgdaAny) -> AgdaAny)
-- Utils.Monad.return
d_return_262 :: T_Monad_246 -> () -> AgdaAny -> AgdaAny
d_return_262 v0
  = case coe v0 of
      C_Monad'46'constructor_14947 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Utils.Monad._>>=_
d__'62''62''61'__268 ::
  T_Monad_246 ->
  () -> () -> AgdaAny -> (AgdaAny -> AgdaAny) -> AgdaAny
d__'62''62''61'__268 v0
  = case coe v0 of
      C_Monad'46'constructor_14947 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Utils.Monad._>>_
d__'62''62'__274 ::
  (() -> ()) ->
  T_Monad_246 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d__'62''62'__274 ~v0 v1 ~v2 ~v3 v4 v5 = du__'62''62'__274 v1 v4 v5
du__'62''62'__274 :: T_Monad_246 -> AgdaAny -> AgdaAny -> AgdaAny
du__'62''62'__274 v0 v1 v2
  = coe d__'62''62''61'__268 v0 erased erased v1 (\ v3 -> v2)
-- Utils.Monad.fmap
d_fmap_284 ::
  (() -> ()) ->
  T_Monad_246 ->
  () -> () -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_fmap_284 ~v0 v1 ~v2 ~v3 v4 v5 = du_fmap_284 v1 v4 v5
du_fmap_284 ::
  T_Monad_246 -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du_fmap_284 v0 v1 v2
  = coe
      d__'62''62''61'__268 v0 erased erased v2
      (\ v3 -> coe d_return_262 v0 erased (coe v1 v3))
-- Utils._._>>_
d__'62''62'__292 ::
  (() -> ()) ->
  T_Monad_246 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d__'62''62'__292 ~v0 v1 = du__'62''62'__292 v1
du__'62''62'__292 ::
  T_Monad_246 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
du__'62''62'__292 v0 v1 v2 v3 v4
  = coe du__'62''62'__274 (coe v0) v3 v4
-- Utils._._>>=_
d__'62''62''61'__294 ::
  T_Monad_246 ->
  () -> () -> AgdaAny -> (AgdaAny -> AgdaAny) -> AgdaAny
d__'62''62''61'__294 v0 = coe d__'62''62''61'__268 (coe v0)
-- Utils._.fmap
d_fmap_296 ::
  (() -> ()) ->
  T_Monad_246 ->
  () -> () -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_fmap_296 ~v0 v1 = du_fmap_296 v1
du_fmap_296 ::
  T_Monad_246 ->
  () -> () -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du_fmap_296 v0 v1 v2 v3 v4 = coe du_fmap_284 (coe v0) v3 v4
-- Utils._.return
d_return_298 :: T_Monad_246 -> () -> AgdaAny -> AgdaAny
d_return_298 v0 = coe d_return_262 (coe v0)
-- Utils.MaybeMonad
d_MaybeMonad_300 :: T_Monad_246
d_MaybeMonad_300
  = coe
      C_Monad'46'constructor_14947
      (coe (\ v0 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16))
      (coe
         (\ v0 v1 v2 v3 ->
            coe MAlonzo.Code.Data.Maybe.Base.du__'62''62''61'__72 v2 v3))
-- Utils.sumBind
d_sumBind_308 ::
  () ->
  () ->
  () ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  (AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30) ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_sumBind_308 ~v0 ~v1 ~v2 v3 v4 = du_sumBind_308 v3 v4
du_sumBind_308 ::
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  (AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30) ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_sumBind_308 v0 v1
  = case coe v0 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v2 -> coe v1 v2
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v2 -> coe v0
      _ -> MAlonzo.RTE.mazUnreachableError
-- Utils.SumMonad
d_SumMonad_322 :: () -> T_Monad_246
d_SumMonad_322 ~v0 = du_SumMonad_322
du_SumMonad_322 :: T_Monad_246
du_SumMonad_322
  = coe
      C_Monad'46'constructor_14947
      (coe (\ v0 -> coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38))
      (coe (\ v0 v1 -> coe du_sumBind_308))
-- Utils.EitherMonad
d_EitherMonad_328 :: () -> T_Monad_246
d_EitherMonad_328 ~v0 = du_EitherMonad_328
du_EitherMonad_328 :: T_Monad_246
du_EitherMonad_328
  = coe
      C_Monad'46'constructor_14947 (coe (\ v0 -> coe C_inj'8322'_14))
      (coe (\ v0 v1 -> coe du_eitherBind_54))
-- Utils.EitherP
d_EitherP_334 :: () -> T_Monad_246
d_EitherP_334 ~v0 = du_EitherP_334
du_EitherP_334 :: T_Monad_246
du_EitherP_334
  = coe
      C_Monad'46'constructor_14947 (coe (\ v0 -> coe C_inj'8322'_14))
      (coe (\ v0 v1 -> coe du_eitherBind_54))
-- Utils.withE
d_withE_342 ::
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  T_Either_6 AgdaAny AgdaAny -> T_Either_6 AgdaAny AgdaAny
d_withE_342 ~v0 ~v1 ~v2 v3 v4 = du_withE_342 v3 v4
du_withE_342 ::
  (AgdaAny -> AgdaAny) ->
  T_Either_6 AgdaAny AgdaAny -> T_Either_6 AgdaAny AgdaAny
du_withE_342 v0 v1
  = case coe v1 of
      C_inj'8321'_12 v2 -> coe C_inj'8321'_12 (coe v0 v2)
      C_inj'8322'_14 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Utils.dec2Either
d_dec2Either_354 ::
  () ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  T_Either_6
    (AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) AgdaAny
d_dec2Either_354 ~v0 v1 = du_dec2Either_354 v1
du_dec2Either_354 ::
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  T_Either_6
    (AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) AgdaAny
du_dec2Either_354 v0
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
d_Writer_364 a0 a1 = ()
data T_Writer_364 = C__'44'__378 AgdaAny AgdaAny
-- Utils.Writer.wrvalue
d_wrvalue_374 :: T_Writer_364 -> AgdaAny
d_wrvalue_374 v0
  = case coe v0 of
      C__'44'__378 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Utils.Writer.accum
d_accum_376 :: T_Writer_364 -> AgdaAny
d_accum_376 v0
  = case coe v0 of
      C__'44'__378 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Utils.WriterMonad.WriterMonad
d_WriterMonad_388 ::
  () -> AgdaAny -> (AgdaAny -> AgdaAny -> AgdaAny) -> T_Monad_246
d_WriterMonad_388 ~v0 v1 v2 = du_WriterMonad_388 v1 v2
du_WriterMonad_388 ::
  AgdaAny -> (AgdaAny -> AgdaAny -> AgdaAny) -> T_Monad_246
du_WriterMonad_388 v0 v1
  = coe
      C_Monad'46'constructor_14947
      (coe (\ v2 v3 -> coe C__'44'__378 (coe v3) (coe v0)))
      (coe
         (\ v2 v3 v4 ->
            case coe v4 of
              C__'44'__378 v5 v6
                -> coe
                     (\ v7 ->
                        coe
                          C__'44'__378 (coe d_wrvalue_374 (coe v7 v5))
                          (coe v1 v6 (d_accum_376 (coe v7 v5))))
              _ -> MAlonzo.RTE.mazUnreachableError))
-- Utils.WriterMonad.tell
d_tell_404 ::
  () ->
  AgdaAny ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny -> T_Writer_364
d_tell_404 ~v0 ~v1 ~v2 v3 = du_tell_404 v3
du_tell_404 :: AgdaAny -> T_Writer_364
du_tell_404 v0
  = coe
      C__'44'__378 (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8) (coe v0)
-- Utils.RuntimeError
d_RuntimeError_408 = ()
type T_RuntimeError_408 = RuntimeError
pattern C_gasError_410 = GasError
pattern C_userError_412 = UserError
pattern C_runtimeTypeError_414 = RuntimeTypeError
check_gasError_410 :: T_RuntimeError_408
check_gasError_410 = GasError
check_userError_412 :: T_RuntimeError_408
check_userError_412 = UserError
check_runtimeTypeError_414 :: T_RuntimeError_408
check_runtimeTypeError_414 = RuntimeTypeError
cover_RuntimeError_408 :: RuntimeError -> ()
cover_RuntimeError_408 x
  = case x of
      GasError -> ()
      UserError -> ()
      RuntimeTypeError -> ()
-- Utils.ByteString
type T_ByteString_416 = BS.ByteString
d_ByteString_416
  = error
      "MAlonzo Runtime Error: postulate evaluated: Utils.ByteString"
-- Utils.mkByteString
d_mkByteString_418
  = error
      "MAlonzo Runtime Error: postulate evaluated: Utils.mkByteString"
-- Utils.eqByteString
d_eqByteString_420 :: T_ByteString_416 -> T_ByteString_416 -> Bool
d_eqByteString_420 = (==)
-- Utils._×_
d__'215'__426 a0 a1 = ()
type T__'215'__426 a0 a1 = Pair a0 a1
pattern C__'44'__440 a0 a1 = (,) a0 a1
check__'44'__440 ::
  forall xA. forall xB. xA -> xB -> T__'215'__426 xA xB
check__'44'__440 = (,)
cover__'215'__426 :: Pair a1 a2 -> ()
cover__'215'__426 x
  = case x of
      (,) _ _ -> ()
-- Utils._×_.proj₁
d_proj'8321'_436 :: T__'215'__426 AgdaAny AgdaAny -> AgdaAny
d_proj'8321'_436 v0
  = case coe v0 of
      C__'44'__440 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Utils._×_.proj₂
d_proj'8322'_438 :: T__'215'__426 AgdaAny AgdaAny -> AgdaAny
d_proj'8322'_438 v0
  = case coe v0 of
      C__'44'__440 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Utils.List
d_List_444 a0 = ()
type T_List_444 a0 = [] a0
pattern C_'91''93'_448 = []
pattern C__'8759'__450 a0 a1 = (:) a0 a1
check_'91''93'_448 :: forall xA. T_List_444 xA
check_'91''93'_448 = []
check__'8759'__450 ::
  forall xA. xA -> T_List_444 xA -> T_List_444 xA
check__'8759'__450 = (:)
cover_List_444 :: [] a1 -> ()
cover_List_444 x
  = case x of
      [] -> ()
      (:) _ _ -> ()
-- Utils.All
d_All_458 a0 a1 a2 a3 = ()
data T_All_458 = C_'91''93'_466 | C__'8759'__476 AgdaAny T_All_458
-- Utils.length
d_length_480 :: () -> T_List_444 AgdaAny -> Integer
d_length_480 ~v0 v1 = du_length_480 v1
du_length_480 :: T_List_444 AgdaAny -> Integer
du_length_480 v0
  = case coe v0 of
      C_'91''93'_448 -> coe (0 :: Integer)
      C__'8759'__450 v1 v2
        -> coe addInt (coe (1 :: Integer)) (coe du_length_480 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Utils.map
d_map_490 ::
  () ->
  () ->
  (AgdaAny -> AgdaAny) -> T_List_444 AgdaAny -> T_List_444 AgdaAny
d_map_490 ~v0 ~v1 v2 v3 = du_map_490 v2 v3
du_map_490 ::
  (AgdaAny -> AgdaAny) -> T_List_444 AgdaAny -> T_List_444 AgdaAny
du_map_490 v0 v1
  = case coe v1 of
      C_'91''93'_448 -> coe v1
      C__'8759'__450 v2 v3
        -> coe
             C__'8759'__450 (coe v0 v2) (coe du_map_490 (coe v0) (coe v3))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Utils.toList
d_toList_502 :: () -> T_List_444 AgdaAny -> [AgdaAny]
d_toList_502 ~v0 v1 = du_toList_502 v1
du_toList_502 :: T_List_444 AgdaAny -> [AgdaAny]
du_toList_502 v0
  = case coe v0 of
      C_'91''93'_448 -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      C__'8759'__450 v1 v2
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v1)
             (coe du_toList_502 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Utils.fromList
d_fromList_510 :: () -> [AgdaAny] -> T_List_444 AgdaAny
d_fromList_510 ~v0 v1 = du_fromList_510 v1
du_fromList_510 :: [AgdaAny] -> T_List_444 AgdaAny
du_fromList_510 v0
  = case coe v0 of
      [] -> coe C_'91''93'_448
      (:) v1 v2
        -> coe C__'8759'__450 (coe v1) (coe du_fromList_510 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Utils.dropLIST
d_dropLIST_518 ::
  () -> Integer -> T_List_444 AgdaAny -> T_List_444 AgdaAny
d_dropLIST_518 ~v0 v1 v2 = du_dropLIST_518 v1 v2
du_dropLIST_518 ::
  Integer -> T_List_444 AgdaAny -> T_List_444 AgdaAny
du_dropLIST_518 v0 v1
  = case coe v0 of
      _ | coe geqInt (coe v0) (coe (0 :: Integer)) ->
          coe du_drop_530 (coe v0) (coe v1)
      _ -> coe v1
-- Utils._.drop
d_drop_530 ::
  () ->
  Integer ->
  T_List_444 AgdaAny ->
  () -> Integer -> T_List_444 AgdaAny -> T_List_444 AgdaAny
d_drop_530 ~v0 ~v1 ~v2 ~v3 v4 v5 = du_drop_530 v4 v5
du_drop_530 :: Integer -> T_List_444 AgdaAny -> T_List_444 AgdaAny
du_drop_530 v0 v1
  = case coe v0 of
      0 -> coe v1
      _ -> let v2 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (case coe v1 of
                C_'91''93'_448 -> coe v1
                C__'8759'__450 v3 v4 -> coe du_drop_530 (coe v2) (coe v4)
                _ -> MAlonzo.RTE.mazUnreachableError)
-- Utils.map-cong
d_map'45'cong_554 ::
  () ->
  () ->
  [AgdaAny] ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_map'45'cong_554 = erased
-- Utils.sequence
d_sequence_570 ::
  () -> (() -> ()) -> T_Monad_246 -> T_List_444 AgdaAny -> AgdaAny
d_sequence_570 ~v0 ~v1 v2 v3 = du_sequence_570 v2 v3
du_sequence_570 :: T_Monad_246 -> T_List_444 AgdaAny -> AgdaAny
du_sequence_570 v0 v1
  = case coe v1 of
      C_'91''93'_448 -> coe d_return_262 v0 erased v1
      C__'8759'__450 v2 v3
        -> coe
             d__'62''62''61'__268 v0 erased erased v2
             (\ v4 ->
                coe
                  d__'62''62''61'__268 v0 erased erased
                  (coe du_sequence_570 (coe v0) (coe v3))
                  (\ v5 ->
                     coe d_return_262 v0 erased (coe C__'8759'__450 (coe v4) (coe v5))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Utils.mapM
d_mapM_588 ::
  () ->
  () ->
  (() -> ()) ->
  T_Monad_246 ->
  (AgdaAny -> AgdaAny) -> T_List_444 AgdaAny -> AgdaAny
d_mapM_588 ~v0 ~v1 ~v2 v3 v4 v5 = du_mapM_588 v3 v4 v5
du_mapM_588 ::
  T_Monad_246 ->
  (AgdaAny -> AgdaAny) -> T_List_444 AgdaAny -> AgdaAny
du_mapM_588 v0 v1 v2
  = coe du_sequence_570 (coe v0) (coe du_map_490 (coe v1) (coe v2))
-- Utils.Array
type T_Array_592 a0 = Strict.Vector a0
d_Array_592
  = error "MAlonzo Runtime Error: postulate evaluated: Utils.Array"
-- Utils.HSlengthOfArray
d_HSlengthOfArray_596 :: forall xA. () -> T_Array_592 xA -> Integer
d_HSlengthOfArray_596 = \() -> \as -> toInteger (Strict.length as)
-- Utils.HSlistToArray
d_HSlistToArray_600 ::
  forall xA. () -> T_List_444 xA -> T_Array_592 xA
d_HSlistToArray_600 = \() -> Strict.fromList
-- Utils.HSindexArray
d_HSindexArray_602 ::
  forall xA. () -> T_Array_592 xA -> Integer -> xA
d_HSindexArray_602
  = \() -> \as -> \i -> as Strict.! (fromInteger i)
-- Utils.mkArray
d_mkArray_606
  = error "MAlonzo Runtime Error: postulate evaluated: Utils.mkArray"
-- Utils.DATA
d_DATA_608 = ()
type T_DATA_608 = Data
pattern C_ConstrDATA_610 a0 a1 = D.Constr a0 a1
pattern C_MapDATA_612 a0 = D.Map a0
pattern C_ListDATA_614 a0 = D.List a0
pattern C_iDATA_616 a0 = D.I a0
pattern C_bDATA_618 a0 = D.B a0
check_ConstrDATA_610 ::
  Integer -> T_List_444 T_DATA_608 -> T_DATA_608
check_ConstrDATA_610 = D.Constr
check_MapDATA_612 ::
  T_List_444 (T__'215'__426 T_DATA_608 T_DATA_608) -> T_DATA_608
check_MapDATA_612 = D.Map
check_ListDATA_614 :: T_List_444 T_DATA_608 -> T_DATA_608
check_ListDATA_614 = D.List
check_iDATA_616 :: Integer -> T_DATA_608
check_iDATA_616 = D.I
check_bDATA_618 :: T_ByteString_416 -> T_DATA_608
check_bDATA_618 = D.B
cover_DATA_608 :: Data -> ()
cover_DATA_608 x
  = case x of
      D.Constr _ _ -> ()
      D.Map _ -> ()
      D.List _ -> ()
      D.I _ -> ()
      D.B _ -> ()
-- Utils.eqDATA
d_eqDATA_620 :: T_DATA_608 -> T_DATA_608 -> Bool
d_eqDATA_620 = (==)
-- Utils.Bls12-381-G1-Element
type T_Bls12'45'381'45'G1'45'Element_754 = G1.Element
d_Bls12'45'381'45'G1'45'Element_754
  = error
      "MAlonzo Runtime Error: postulate evaluated: Utils.Bls12-381-G1-Element"
-- Utils.eqBls12-381-G1-Element
d_eqBls12'45'381'45'G1'45'Element_756 ::
  T_Bls12'45'381'45'G1'45'Element_754 ->
  T_Bls12'45'381'45'G1'45'Element_754 -> Bool
d_eqBls12'45'381'45'G1'45'Element_756 = (==)
-- Utils.Bls12-381-G2-Element
type T_Bls12'45'381'45'G2'45'Element_758 = G2.Element
d_Bls12'45'381'45'G2'45'Element_758
  = error
      "MAlonzo Runtime Error: postulate evaluated: Utils.Bls12-381-G2-Element"
-- Utils.eqBls12-381-G2-Element
d_eqBls12'45'381'45'G2'45'Element_760 ::
  T_Bls12'45'381'45'G2'45'Element_758 ->
  T_Bls12'45'381'45'G2'45'Element_758 -> Bool
d_eqBls12'45'381'45'G2'45'Element_760 = (==)
-- Utils.Bls12-381-MlResult
type T_Bls12'45'381'45'MlResult_762 = Pairing.MlResult
d_Bls12'45'381'45'MlResult_762
  = error
      "MAlonzo Runtime Error: postulate evaluated: Utils.Bls12-381-MlResult"
-- Utils.eqBls12-381-MlResult
d_eqBls12'45'381'45'MlResult_764 ::
  T_Bls12'45'381'45'MlResult_762 ->
  T_Bls12'45'381'45'MlResult_762 -> Bool
d_eqBls12'45'381'45'MlResult_764 = (==)
-- Utils.Kind
d_Kind_766 = ()
type T_Kind_766 = KIND
pattern C_'42'_768 = Star
pattern C_'9839'_770 = Sharp
pattern C__'8658'__772 a0 a1 = Arrow a0 a1
check_'42'_768 :: T_Kind_766
check_'42'_768 = Star
check_'9839'_770 :: T_Kind_766
check_'9839'_770 = Sharp
check__'8658'__772 :: T_Kind_766 -> T_Kind_766 -> T_Kind_766
check__'8658'__772 = Arrow
cover_Kind_766 :: KIND -> ()
cover_Kind_766 x
  = case x of
      Star -> ()
      Sharp -> ()
      Arrow _ _ -> ()
