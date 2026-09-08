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
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Agda.Builtin.Unit
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Data.Fin.Base
import qualified MAlonzo.Code.Data.Integer.Properties
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
import qualified PlutusCore.Value as V
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
-- Utils._<|>_
d__'60''124''62'__84 ::
  () -> Maybe AgdaAny -> Maybe AgdaAny -> Maybe AgdaAny
d__'60''124''62'__84 ~v0 v1 v2 = du__'60''124''62'__84 v1 v2
du__'60''124''62'__84 ::
  Maybe AgdaAny -> Maybe AgdaAny -> Maybe AgdaAny
du__'60''124''62'__84 v0 v1
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2 -> coe v0
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Utils.maybeToEither
d_maybeToEither_94 ::
  () -> () -> AgdaAny -> Maybe AgdaAny -> T_Either_6 AgdaAny AgdaAny
d_maybeToEither_94 ~v0 ~v1 v2 = du_maybeToEither_94 v2
du_maybeToEither_94 ::
  AgdaAny -> Maybe AgdaAny -> T_Either_6 AgdaAny AgdaAny
du_maybeToEither_94 v0
  = coe
      MAlonzo.Code.Data.Maybe.Base.du_maybe_32 (coe C_inj'8322'_14)
      (coe C_inj'8321'_12 (coe v0))
-- Utils.try
d_try_102 ::
  () -> () -> Maybe AgdaAny -> AgdaAny -> T_Either_6 AgdaAny AgdaAny
d_try_102 ~v0 ~v1 v2 v3 = du_try_102 v2 v3
du_try_102 ::
  Maybe AgdaAny -> AgdaAny -> T_Either_6 AgdaAny AgdaAny
du_try_102 v0 v1
  = coe
      MAlonzo.Code.Data.Maybe.Base.du_maybe_32 (coe C_inj'8322'_14)
      (coe C_inj'8321'_12 (coe v1)) (coe v0)
-- Utils.eitherToMaybe
d_eitherToMaybe_112 ::
  () -> () -> T_Either_6 AgdaAny AgdaAny -> Maybe AgdaAny
d_eitherToMaybe_112 ~v0 ~v1 v2 = du_eitherToMaybe_112 v2
du_eitherToMaybe_112 :: T_Either_6 AgdaAny AgdaAny -> Maybe AgdaAny
du_eitherToMaybe_112 v0
  = case coe v0 of
      C_inj'8321'_12 v1
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      C_inj'8322'_14 v1
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Utils.natToFin
d_natToFin_118 ::
  Integer -> Integer -> Maybe MAlonzo.Code.Data.Fin.Base.T_Fin_10
d_natToFin_118 v0 v1
  = let v2
          = coe
              MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
              (\ v2 ->
                 coe
                   MAlonzo.Code.Data.Nat.Properties.du_'8804''7495''8658''8804'_2854
                   (coe addInt (coe (1 :: Integer)) (coe v1)))
              (coe
                 MAlonzo.Code.Data.Nat.Properties.du_'8804''8658''8804''7495'_2866)
              (coe
                 MAlonzo.Code.Relation.Nullary.Decidable.Core.d_T'63'_72
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
d_cong'8323'_160 ::
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
d_cong'8323'_160 = erased
-- Utils.≡-subst-removable
d_'8801''45'subst'45'removable_182 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> ()) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8801''45'subst'45'removable_182 = erased
-- Utils._∔_≣_
d__'8724'_'8803'__188 a0 a1 a2 = ()
data T__'8724'_'8803'__188
  = C_start_192 | C_bubble_200 T__'8724'_'8803'__188
-- Utils.unique∔
d_unique'8724'_212 ::
  Integer ->
  Integer ->
  Integer ->
  T__'8724'_'8803'__188 ->
  T__'8724'_'8803'__188 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_unique'8724'_212 = erased
-- Utils.+2∔
d_'43'2'8724'_224 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T__'8724'_'8803'__188
d_'43'2'8724'_224 v0 ~v1 ~v2 ~v3 = du_'43'2'8724'_224 v0
du_'43'2'8724'_224 :: Integer -> T__'8724'_'8803'__188
du_'43'2'8724'_224 v0
  = case coe v0 of
      0 -> coe C_start_192
      _ -> let v1 = subInt (coe v0) (coe (1 :: Integer)) in
           coe (coe C_bubble_200 (coe du_'43'2'8724'_224 (coe v1)))
-- Utils.∔2+
d_'8724'2'43'_242 ::
  Integer ->
  Integer ->
  Integer ->
  T__'8724'_'8803'__188 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8724'2'43'_242 = erased
-- Utils.alldone
d_alldone_248 :: Integer -> T__'8724'_'8803'__188
d_alldone_248 v0 = coe du_'43'2'8724'_224 (coe v0)
-- Utils.Monad
d_Monad_254 a0 = ()
data T_Monad_254
  = C_constructor_298 (() -> AgdaAny -> AgdaAny)
                      (() -> () -> AgdaAny -> (AgdaAny -> AgdaAny) -> AgdaAny)
-- Utils.Monad.return
d_return_270 :: T_Monad_254 -> () -> AgdaAny -> AgdaAny
d_return_270 v0
  = case coe v0 of
      C_constructor_298 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Utils.Monad._>>=_
d__'62''62''61'__276 ::
  T_Monad_254 ->
  () -> () -> AgdaAny -> (AgdaAny -> AgdaAny) -> AgdaAny
d__'62''62''61'__276 v0
  = case coe v0 of
      C_constructor_298 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Utils.Monad._>>_
d__'62''62'__282 ::
  (() -> ()) ->
  T_Monad_254 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d__'62''62'__282 ~v0 v1 ~v2 ~v3 v4 v5 = du__'62''62'__282 v1 v4 v5
du__'62''62'__282 :: T_Monad_254 -> AgdaAny -> AgdaAny -> AgdaAny
du__'62''62'__282 v0 v1 v2
  = coe d__'62''62''61'__276 v0 erased erased v1 (\ v3 -> v2)
-- Utils.Monad.fmap
d_fmap_292 ::
  (() -> ()) ->
  T_Monad_254 ->
  () -> () -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_fmap_292 ~v0 v1 ~v2 ~v3 v4 v5 = du_fmap_292 v1 v4 v5
du_fmap_292 ::
  T_Monad_254 -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du_fmap_292 v0 v1 v2
  = coe
      d__'62''62''61'__276 v0 erased erased v2
      (\ v3 -> coe d_return_270 v0 erased (coe v1 v3))
-- Utils._._>>_
d__'62''62'__302 ::
  (() -> ()) ->
  T_Monad_254 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d__'62''62'__302 ~v0 v1 = du__'62''62'__302 v1
du__'62''62'__302 ::
  T_Monad_254 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
du__'62''62'__302 v0 v1 v2 v3 v4
  = coe du__'62''62'__282 (coe v0) v3 v4
-- Utils._._>>=_
d__'62''62''61'__304 ::
  T_Monad_254 ->
  () -> () -> AgdaAny -> (AgdaAny -> AgdaAny) -> AgdaAny
d__'62''62''61'__304 v0 = coe d__'62''62''61'__276 (coe v0)
-- Utils._.fmap
d_fmap_306 ::
  (() -> ()) ->
  T_Monad_254 ->
  () -> () -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_fmap_306 ~v0 v1 = du_fmap_306 v1
du_fmap_306 ::
  T_Monad_254 ->
  () -> () -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du_fmap_306 v0 v1 v2 v3 v4 = coe du_fmap_292 (coe v0) v3 v4
-- Utils._.return
d_return_308 :: T_Monad_254 -> () -> AgdaAny -> AgdaAny
d_return_308 v0 = coe d_return_270 (coe v0)
-- Utils.MaybeMonad
d_MaybeMonad_310 :: T_Monad_254
d_MaybeMonad_310
  = coe
      C_constructor_298
      (coe (\ v0 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16))
      (coe
         (\ v0 v1 v2 v3 ->
            coe MAlonzo.Code.Data.Maybe.Base.du__'62''62''61'__72 v2 v3))
-- Utils.sumBind
d_sumBind_318 ::
  () ->
  () ->
  () ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  (AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30) ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_sumBind_318 ~v0 ~v1 ~v2 v3 v4 = du_sumBind_318 v3 v4
du_sumBind_318 ::
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  (AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30) ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_sumBind_318 v0 v1
  = case coe v0 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v2 -> coe v1 v2
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v2 -> coe v0
      _ -> MAlonzo.RTE.mazUnreachableError
-- Utils.SumMonad
d_SumMonad_332 :: () -> T_Monad_254
d_SumMonad_332 ~v0 = du_SumMonad_332
du_SumMonad_332 :: T_Monad_254
du_SumMonad_332
  = coe
      C_constructor_298
      (coe (\ v0 -> coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38))
      (coe (\ v0 v1 -> coe du_sumBind_318))
-- Utils.EitherMonad
d_EitherMonad_338 :: () -> T_Monad_254
d_EitherMonad_338 ~v0 = du_EitherMonad_338
du_EitherMonad_338 :: T_Monad_254
du_EitherMonad_338
  = coe
      C_constructor_298 (coe (\ v0 -> coe C_inj'8322'_14))
      (coe (\ v0 v1 -> coe du_eitherBind_54))
-- Utils.EitherP
d_EitherP_344 :: () -> T_Monad_254
d_EitherP_344 ~v0 = du_EitherP_344
du_EitherP_344 :: T_Monad_254
du_EitherP_344
  = coe
      C_constructor_298 (coe (\ v0 -> coe C_inj'8322'_14))
      (coe (\ v0 v1 -> coe du_eitherBind_54))
-- Utils.withE
d_withE_352 ::
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  T_Either_6 AgdaAny AgdaAny -> T_Either_6 AgdaAny AgdaAny
d_withE_352 ~v0 ~v1 ~v2 v3 v4 = du_withE_352 v3 v4
du_withE_352 ::
  (AgdaAny -> AgdaAny) ->
  T_Either_6 AgdaAny AgdaAny -> T_Either_6 AgdaAny AgdaAny
du_withE_352 v0 v1
  = case coe v1 of
      C_inj'8321'_12 v2 -> coe C_inj'8321'_12 (coe v0 v2)
      C_inj'8322'_14 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Utils.dec2Either
d_dec2Either_364 ::
  () ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  T_Either_6
    (AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) AgdaAny
d_dec2Either_364 ~v0 v1 = du_dec2Either_364 v1
du_dec2Either_364 ::
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  T_Either_6
    (AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) AgdaAny
du_dec2Either_364 v0
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
d_Writer_374 a0 a1 = ()
data T_Writer_374 = C__'44'__388 AgdaAny AgdaAny
-- Utils.Writer.wrvalue
d_wrvalue_384 :: T_Writer_374 -> AgdaAny
d_wrvalue_384 v0
  = case coe v0 of
      C__'44'__388 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Utils.Writer.accum
d_accum_386 :: T_Writer_374 -> AgdaAny
d_accum_386 v0
  = case coe v0 of
      C__'44'__388 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Utils.WriterMonad.WriterMonad
d_WriterMonad_398 ::
  () -> AgdaAny -> (AgdaAny -> AgdaAny -> AgdaAny) -> T_Monad_254
d_WriterMonad_398 ~v0 v1 v2 = du_WriterMonad_398 v1 v2
du_WriterMonad_398 ::
  AgdaAny -> (AgdaAny -> AgdaAny -> AgdaAny) -> T_Monad_254
du_WriterMonad_398 v0 v1
  = coe
      C_constructor_298
      (coe (\ v2 v3 -> coe C__'44'__388 (coe v3) (coe v0)))
      (coe
         (\ v2 v3 v4 ->
            case coe v4 of
              C__'44'__388 v5 v6
                -> coe
                     (\ v7 ->
                        coe
                          C__'44'__388 (coe d_wrvalue_384 (coe v7 v5))
                          (coe v1 v6 (d_accum_386 (coe v7 v5))))
              _ -> MAlonzo.RTE.mazUnreachableError))
-- Utils.WriterMonad.tell
d_tell_414 ::
  () ->
  AgdaAny ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny -> T_Writer_374
d_tell_414 ~v0 ~v1 ~v2 v3 = du_tell_414 v3
du_tell_414 :: AgdaAny -> T_Writer_374
du_tell_414 v0
  = coe
      C__'44'__388 (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8) (coe v0)
-- Utils.RuntimeError
d_RuntimeError_418 = ()
type T_RuntimeError_418 = RuntimeError
pattern C_gasError_420 = GasError
pattern C_userError_422 = UserError
pattern C_runtimeTypeError_424 = RuntimeTypeError
check_gasError_420 :: T_RuntimeError_418
check_gasError_420 = GasError
check_userError_422 :: T_RuntimeError_418
check_userError_422 = UserError
check_runtimeTypeError_424 :: T_RuntimeError_418
check_runtimeTypeError_424 = RuntimeTypeError
cover_RuntimeError_418 :: RuntimeError -> ()
cover_RuntimeError_418 x
  = case x of
      GasError -> ()
      UserError -> ()
      RuntimeTypeError -> ()
-- Utils.ByteString
type T_ByteString_426 = BS.ByteString
d_ByteString_426
  = error
      "MAlonzo Runtime Error: postulate evaluated: Utils.ByteString"
-- Utils.mkByteString
d_mkByteString_428
  = error
      "MAlonzo Runtime Error: postulate evaluated: Utils.mkByteString"
-- Utils.true≢false
d_true'8802'false_430 ::
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_true'8802'false_430 = erased
-- Utils.decEqFromBool
d_decEqFromBool_444 ::
  () ->
  (AgdaAny -> AgdaAny -> Bool) ->
  (AgdaAny ->
   AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_decEqFromBool_444 ~v0 v1 ~v2 v3 v4
  = du_decEqFromBool_444 v1 v3 v4
du_decEqFromBool_444 ::
  (AgdaAny -> AgdaAny -> Bool) ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
du_decEqFromBool_444 v0 v1 v2
  = let v3 = coe v0 v1 v2 in
    coe
      (if coe v3
         then coe
                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                (coe v3)
                (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 erased)
         else coe
                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                (coe v3)
                (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26))
-- Utils.eqByteStringᵇ
d_eqByteString'7495'_490 ::
  T_ByteString_426 -> T_ByteString_426 -> Bool
d_eqByteString'7495'_490 = (==)
-- Utils.eqByteString?
d_eqByteString'63'_496 ::
  T_ByteString_426 ->
  T_ByteString_426 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_eqByteString'63'_496
  = coe du_decEqFromBool_444 (coe d_eqByteString'7495'_490)
-- Utils._×_
d__'215'__508 a0 a1 = ()
type T__'215'__508 a0 a1 = Pair a0 a1
pattern C__'44'__522 a0 a1 = (,) a0 a1
check__'44'__522 ::
  forall xA. forall xB. xA -> xB -> T__'215'__508 xA xB
check__'44'__522 = (,)
cover__'215'__508 :: Pair a1 a2 -> ()
cover__'215'__508 x
  = case x of
      (,) _ _ -> ()
-- Utils._×_.proj₁
d_proj'8321'_518 :: T__'215'__508 AgdaAny AgdaAny -> AgdaAny
d_proj'8321'_518 v0
  = case coe v0 of
      C__'44'__522 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Utils._×_.proj₂
d_proj'8322'_520 :: T__'215'__508 AgdaAny AgdaAny -> AgdaAny
d_proj'8322'_520 v0
  = case coe v0 of
      C__'44'__522 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Utils.List
d_List_526 a0 = ()
type T_List_526 a0 = [] a0
pattern C_'91''93'_530 = []
pattern C__'8759'__532 a0 a1 = (:) a0 a1
check_'91''93'_530 :: forall xA. T_List_526 xA
check_'91''93'_530 = []
check__'8759'__532 ::
  forall xA. xA -> T_List_526 xA -> T_List_526 xA
check__'8759'__532 = (:)
cover_List_526 :: [] a1 -> ()
cover_List_526 x
  = case x of
      [] -> ()
      (:) _ _ -> ()
-- Utils.All
d_All_540 a0 a1 a2 a3 = ()
data T_All_540 = C_'91''93'_548 | C__'8759'__558 AgdaAny T_All_540
-- Utils.length
d_length_562 :: () -> T_List_526 AgdaAny -> Integer
d_length_562 ~v0 v1 = du_length_562 v1
du_length_562 :: T_List_526 AgdaAny -> Integer
du_length_562 v0
  = case coe v0 of
      C_'91''93'_530 -> coe (0 :: Integer)
      C__'8759'__532 v1 v2
        -> coe addInt (coe (1 :: Integer)) (coe du_length_562 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Utils.map
d_map_572 ::
  () ->
  () ->
  (AgdaAny -> AgdaAny) -> T_List_526 AgdaAny -> T_List_526 AgdaAny
d_map_572 ~v0 ~v1 v2 v3 = du_map_572 v2 v3
du_map_572 ::
  (AgdaAny -> AgdaAny) -> T_List_526 AgdaAny -> T_List_526 AgdaAny
du_map_572 v0 v1
  = case coe v1 of
      C_'91''93'_530 -> coe v1
      C__'8759'__532 v2 v3
        -> coe
             C__'8759'__532 (coe v0 v2) (coe du_map_572 (coe v0) (coe v3))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Utils.toList
d_toList_584 :: () -> T_List_526 AgdaAny -> [AgdaAny]
d_toList_584 ~v0 v1 = du_toList_584 v1
du_toList_584 :: T_List_526 AgdaAny -> [AgdaAny]
du_toList_584 v0
  = case coe v0 of
      C_'91''93'_530 -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      C__'8759'__532 v1 v2
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v1)
             (coe du_toList_584 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Utils.fromList
d_fromList_592 :: () -> [AgdaAny] -> T_List_526 AgdaAny
d_fromList_592 ~v0 v1 = du_fromList_592 v1
du_fromList_592 :: [AgdaAny] -> T_List_526 AgdaAny
du_fromList_592 v0
  = case coe v0 of
      [] -> coe C_'91''93'_530
      (:) v1 v2
        -> coe C__'8759'__532 (coe v1) (coe du_fromList_592 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Utils.dropLIST
d_dropLIST_600 ::
  () -> Integer -> T_List_526 AgdaAny -> T_List_526 AgdaAny
d_dropLIST_600 ~v0 v1 v2 = du_dropLIST_600 v1 v2
du_dropLIST_600 ::
  Integer -> T_List_526 AgdaAny -> T_List_526 AgdaAny
du_dropLIST_600 v0 v1
  = case coe v0 of
      _ | coe geqInt (coe v0) (coe (0 :: Integer)) ->
          coe du_drop_612 (coe v0) (coe v1)
      _ -> coe v1
-- Utils._.drop
d_drop_612 ::
  () ->
  Integer ->
  T_List_526 AgdaAny ->
  () -> Integer -> T_List_526 AgdaAny -> T_List_526 AgdaAny
d_drop_612 ~v0 ~v1 ~v2 ~v3 v4 v5 = du_drop_612 v4 v5
du_drop_612 :: Integer -> T_List_526 AgdaAny -> T_List_526 AgdaAny
du_drop_612 v0 v1
  = case coe v0 of
      0 -> coe v1
      _ -> let v2 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (case coe v1 of
                C_'91''93'_530 -> coe v1
                C__'8759'__532 v3 v4 -> coe du_drop_612 (coe v2) (coe v4)
                _ -> MAlonzo.RTE.mazUnreachableError)
-- Utils.map-cong
d_map'45'cong_636 ::
  () ->
  () ->
  [AgdaAny] ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_map'45'cong_636 = erased
-- Utils.sequence
d_sequence_652 ::
  () -> (() -> ()) -> T_Monad_254 -> T_List_526 AgdaAny -> AgdaAny
d_sequence_652 ~v0 ~v1 v2 v3 = du_sequence_652 v2 v3
du_sequence_652 :: T_Monad_254 -> T_List_526 AgdaAny -> AgdaAny
du_sequence_652 v0 v1
  = case coe v1 of
      C_'91''93'_530 -> coe d_return_270 v0 erased v1
      C__'8759'__532 v2 v3
        -> coe
             d__'62''62''61'__276 v0 erased erased v2
             (\ v4 ->
                coe
                  d__'62''62''61'__276 v0 erased erased
                  (coe du_sequence_652 (coe v0) (coe v3))
                  (\ v5 ->
                     coe d_return_270 v0 erased (coe C__'8759'__532 (coe v4) (coe v5))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Utils.mapM
d_mapM_670 ::
  () ->
  () ->
  (() -> ()) ->
  T_Monad_254 ->
  (AgdaAny -> AgdaAny) -> T_List_526 AgdaAny -> AgdaAny
d_mapM_670 ~v0 ~v1 ~v2 v3 v4 v5 = du_mapM_670 v3 v4 v5
du_mapM_670 ::
  T_Monad_254 ->
  (AgdaAny -> AgdaAny) -> T_List_526 AgdaAny -> AgdaAny
du_mapM_670 v0 v1 v2
  = coe du_sequence_652 (coe v0) (coe du_map_572 (coe v1) (coe v2))
-- Utils.Array
type T_Array_674 a0 = Strict.Vector a0
d_Array_674
  = error "MAlonzo Runtime Error: postulate evaluated: Utils.Array"
-- Utils.HSlengthOfArray
d_HSlengthOfArray_678 :: forall xA. () -> T_Array_674 xA -> Integer
d_HSlengthOfArray_678 = \() -> \as -> toInteger (Strict.length as)
-- Utils.HSlistToArray
d_HSlistToArray_682 ::
  forall xA. () -> T_List_526 xA -> T_Array_674 xA
d_HSlistToArray_682 = \() -> Strict.fromList
-- Utils.HSindexArray
d_HSindexArray_684 ::
  forall xA. () -> T_Array_674 xA -> Integer -> xA
d_HSindexArray_684
  = \() -> \as -> \i -> as Strict.! (fromInteger i)
-- Utils.HSarrayToList
d_HSarrayToList_686 ::
  forall xA. () -> T_Array_674 xA -> T_List_526 xA
d_HSarrayToList_686 = \() -> Strict.toList
-- Utils.HSarrayToList-injective
d_HSarrayToList'45'injective_692
  = error
      "MAlonzo Runtime Error: postulate evaluated: Utils.HSarrayToList-injective"
-- Utils.mkArray
d_mkArray_696
  = error "MAlonzo Runtime Error: postulate evaluated: Utils.mkArray"
-- Utils.DATA
d_DATA_698 = ()
type T_DATA_698 = Data
pattern C_ConstrDATA_700 a0 a1 = D.Constr a0 a1
pattern C_MapDATA_702 a0 = D.Map a0
pattern C_ListDATA_704 a0 = D.List a0
pattern C_iDATA_706 a0 = D.I a0
pattern C_bDATA_708 a0 = D.B a0
check_ConstrDATA_700 ::
  Integer -> T_List_526 T_DATA_698 -> T_DATA_698
check_ConstrDATA_700 = D.Constr
check_MapDATA_702 ::
  T_List_526 (T__'215'__508 T_DATA_698 T_DATA_698) -> T_DATA_698
check_MapDATA_702 = D.Map
check_ListDATA_704 :: T_List_526 T_DATA_698 -> T_DATA_698
check_ListDATA_704 = D.List
check_iDATA_706 :: Integer -> T_DATA_698
check_iDATA_706 = D.I
check_bDATA_708 :: T_ByteString_426 -> T_DATA_698
check_bDATA_708 = D.B
cover_DATA_698 :: Data -> ()
cover_DATA_698 x
  = case x of
      D.Constr _ _ -> ()
      D.Map _ -> ()
      D.List _ -> ()
      D.I _ -> ()
      D.B _ -> ()
-- Utils.eqDATA?
d_eqDATA'63'_714 ::
  T_DATA_698 ->
  T_DATA_698 -> MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_eqDATA'63'_714 v0 v1
  = case coe v0 of
      C_ConstrDATA_700 v2 v3
        -> case coe v1 of
             C_ConstrDATA_700 v4 v5
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                    erased
                    (coe
                       (\ v6 ->
                          coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased))
                    (coe
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.du__'215''45'dec__84
                       (coe
                          MAlonzo.Code.Data.Integer.Properties.d__'8799'__2800 (coe v2)
                          (coe v4))
                       (coe d_eqListDATA'63'_720 (coe v3) (coe v5)))
             C_MapDATA_702 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             C_ListDATA_704 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             C_iDATA_706 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             C_bDATA_708 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             _ -> MAlonzo.RTE.mazUnreachableError
      C_MapDATA_702 v2
        -> case coe v1 of
             C_ConstrDATA_700 v3 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             C_MapDATA_702 v3
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                    erased erased (coe d_eqListPairDATA'63'_732 (coe v2) (coe v3))
             C_ListDATA_704 v3
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             C_iDATA_706 v3
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             C_bDATA_708 v3
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             _ -> MAlonzo.RTE.mazUnreachableError
      C_ListDATA_704 v2
        -> case coe v1 of
             C_ConstrDATA_700 v3 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             C_MapDATA_702 v3
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             C_ListDATA_704 v3
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                    erased erased (coe d_eqListDATA'63'_720 (coe v2) (coe v3))
             C_iDATA_706 v3
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             C_bDATA_708 v3
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             _ -> MAlonzo.RTE.mazUnreachableError
      C_iDATA_706 v2
        -> case coe v1 of
             C_ConstrDATA_700 v3 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             C_MapDATA_702 v3
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             C_ListDATA_704 v3
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             C_iDATA_706 v3
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                    erased erased
                    (coe
                       MAlonzo.Code.Data.Integer.Properties.d__'8799'__2800 (coe v2)
                       (coe v3))
             C_bDATA_708 v3
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             _ -> MAlonzo.RTE.mazUnreachableError
      C_bDATA_708 v2
        -> case coe v1 of
             C_ConstrDATA_700 v3 v4
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             C_MapDATA_702 v3
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             C_ListDATA_704 v3
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             C_iDATA_706 v3
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             C_bDATA_708 v3
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                    erased erased (coe d_eqByteString'63'_496 v2 v3)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Utils.eqListDATA?
d_eqListDATA'63'_720 ::
  T_List_526 T_DATA_698 ->
  T_List_526 T_DATA_698 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_eqListDATA'63'_720 v0 v1
  = case coe v0 of
      C_'91''93'_530
        -> case coe v1 of
             C_'91''93'_530
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 erased)
             C__'8759'__532 v2 v3
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             _ -> MAlonzo.RTE.mazUnreachableError
      C__'8759'__532 v2 v3
        -> case coe v1 of
             C_'91''93'_530
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             C__'8759'__532 v4 v5
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                    erased
                    (coe
                       (\ v6 ->
                          coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased))
                    (coe
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.du__'215''45'dec__84
                       (coe d_eqDATA'63'_714 (coe v2) (coe v4))
                       (coe d_eqListDATA'63'_720 (coe v3) (coe v5)))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Utils.eqPairDATA?
d_eqPairDATA'63'_726 ::
  T__'215'__508 T_DATA_698 T_DATA_698 ->
  T__'215'__508 T_DATA_698 T_DATA_698 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_eqPairDATA'63'_726 v0 v1
  = case coe v0 of
      C__'44'__522 v2 v3
        -> case coe v1 of
             C__'44'__522 v4 v5
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                    erased
                    (coe
                       (\ v6 ->
                          coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased))
                    (coe
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.du__'215''45'dec__84
                       (coe d_eqDATA'63'_714 (coe v2) (coe v4))
                       (coe d_eqDATA'63'_714 (coe v3) (coe v5)))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Utils.eqListPairDATA?
d_eqListPairDATA'63'_732 ::
  T_List_526 (T__'215'__508 T_DATA_698 T_DATA_698) ->
  T_List_526 (T__'215'__508 T_DATA_698 T_DATA_698) ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_eqListPairDATA'63'_732 v0 v1
  = case coe v0 of
      C_'91''93'_530
        -> case coe v1 of
             C_'91''93'_530
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 erased)
             C__'8759'__532 v2 v3
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             _ -> MAlonzo.RTE.mazUnreachableError
      C__'8759'__532 v2 v3
        -> case coe v1 of
             C_'91''93'_530
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                    (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
                    (coe MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)
             C__'8759'__532 v4 v5
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                    erased
                    (coe
                       (\ v6 ->
                          coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased))
                    (coe
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.du__'215''45'dec__84
                       (coe d_eqPairDATA'63'_726 (coe v2) (coe v4))
                       (coe d_eqListPairDATA'63'_732 (coe v3) (coe v5)))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Utils.eqDATA
d_eqDATA_822 :: T_DATA_698 -> T_DATA_698 -> Bool
d_eqDATA_822 = (==)
-- Utils.Bls12-381-G1-Element
type T_Bls12'45'381'45'G1'45'Element_828 = G1.Element
d_Bls12'45'381'45'G1'45'Element_828
  = error
      "MAlonzo Runtime Error: postulate evaluated: Utils.Bls12-381-G1-Element"
-- Utils.eqBls12-381-G1-Elementᵇ
d_eqBls12'45'381'45'G1'45'Element'7495'_830 ::
  T_Bls12'45'381'45'G1'45'Element_828 ->
  T_Bls12'45'381'45'G1'45'Element_828 -> Bool
d_eqBls12'45'381'45'G1'45'Element'7495'_830 = (==)
-- Utils.eqBls12-381-G1-Element?
d_eqBls12'45'381'45'G1'45'Element'63'_836 ::
  T_Bls12'45'381'45'G1'45'Element_828 ->
  T_Bls12'45'381'45'G1'45'Element_828 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_eqBls12'45'381'45'G1'45'Element'63'_836
  = coe
      du_decEqFromBool_444
      (coe d_eqBls12'45'381'45'G1'45'Element'7495'_830)
-- Utils.Bls12-381-G2-Element
type T_Bls12'45'381'45'G2'45'Element_842 = G2.Element
d_Bls12'45'381'45'G2'45'Element_842
  = error
      "MAlonzo Runtime Error: postulate evaluated: Utils.Bls12-381-G2-Element"
-- Utils.eqBls12-381-G2-Elementᵇ
d_eqBls12'45'381'45'G2'45'Element'7495'_844 ::
  T_Bls12'45'381'45'G2'45'Element_842 ->
  T_Bls12'45'381'45'G2'45'Element_842 -> Bool
d_eqBls12'45'381'45'G2'45'Element'7495'_844 = (==)
-- Utils.eqBls12-381-G2-Element?
d_eqBls12'45'381'45'G2'45'Element'63'_850 ::
  T_Bls12'45'381'45'G2'45'Element_842 ->
  T_Bls12'45'381'45'G2'45'Element_842 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_eqBls12'45'381'45'G2'45'Element'63'_850
  = coe
      du_decEqFromBool_444
      (coe d_eqBls12'45'381'45'G2'45'Element'7495'_844)
-- Utils.Bls12-381-MlResult
type T_Bls12'45'381'45'MlResult_856 = Pairing.MlResult
d_Bls12'45'381'45'MlResult_856
  = error
      "MAlonzo Runtime Error: postulate evaluated: Utils.Bls12-381-MlResult"
-- Utils.eqBls12-381-MlResultᵇ
d_eqBls12'45'381'45'MlResult'7495'_858 ::
  T_Bls12'45'381'45'MlResult_856 ->
  T_Bls12'45'381'45'MlResult_856 -> Bool
d_eqBls12'45'381'45'MlResult'7495'_858 = (==)
-- Utils.eqBls12-381-MlResult?
d_eqBls12'45'381'45'MlResult'63'_864 ::
  T_Bls12'45'381'45'MlResult_856 ->
  T_Bls12'45'381'45'MlResult_856 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_eqBls12'45'381'45'MlResult'63'_864
  = coe
      du_decEqFromBool_444 (coe d_eqBls12'45'381'45'MlResult'7495'_858)
-- Utils.Value
type T_Value_870 = V.Value
d_Value_870
  = error "MAlonzo Runtime Error: postulate evaluated: Utils.Value"
-- Utils.eqValueᵇ
d_eqValue'7495'_872 :: T_Value_870 -> T_Value_870 -> Bool
d_eqValue'7495'_872 = (==)
-- Utils.eqValue?
d_eqValue'63'_878 ::
  T_Value_870 ->
  T_Value_870 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d_eqValue'63'_878
  = coe du_decEqFromBool_444 (coe d_eqValue'7495'_872)
-- Utils.valueFromList
d_valueFromList_884
  = error
      "MAlonzo Runtime Error: postulate evaluated: Utils.valueFromList"
-- Utils.Kind
d_Kind_886 = ()
type T_Kind_886 = KIND
pattern C_'42'_888 = Star
pattern C_'9839'_890 = Sharp
pattern C__'8658'__892 a0 a1 = Arrow a0 a1
check_'42'_888 :: T_Kind_886
check_'42'_888 = Star
check_'9839'_890 :: T_Kind_886
check_'9839'_890 = Sharp
check__'8658'__892 :: T_Kind_886 -> T_Kind_886 -> T_Kind_886
check__'8658'__892 = Arrow
cover_Kind_886 :: KIND -> ()
cover_Kind_886 x
  = case x of
      Star -> ()
      Sharp -> ()
      Arrow _ _ -> ()
-- Utils.TRACE
d_TRACE_902 ::
  () ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 -> AgdaAny -> AgdaAny
d_TRACE_902 ~v0 ~v1 v2 = du_TRACE_902 v2
du_TRACE_902 :: AgdaAny -> AgdaAny
du_TRACE_902 v0 = coe v0
