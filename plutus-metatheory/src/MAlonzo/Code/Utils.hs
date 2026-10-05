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
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Agda.Builtin.Unit
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Data.Bool.Base
import qualified MAlonzo.Code.Data.Bool.ListAction
import qualified MAlonzo.Code.Data.Bool.Properties
import qualified MAlonzo.Code.Data.Fin.Base
import qualified MAlonzo.Code.Data.Integer.Base
import qualified MAlonzo.Code.Data.Integer.Properties
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Data.Maybe.Base
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Data.Nat.Properties
import qualified MAlonzo.Code.Data.Parity.Base
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Data.Vec.Base
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core
import qualified MAlonzo.Code.Relation.Nullary.Reflects

import Raw
import Data.ByteString qualified as Haskell
import qualified Data.Vector.Strict as Strict
import PlutusCore.Data as Haskell
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
-- Utils.Byte
d_Byte_426 = ()
type T_Byte_426 = Byte
pattern C_byte_444 a0 a1 a2 a3 a4 a5 a6 a7 = Byte a0 a1 a2 a3 a4 a5 a6 a7
check_byte_444 ::
  Bool ->
  Bool -> Bool -> Bool -> Bool -> Bool -> Bool -> Bool -> T_Byte_426
check_byte_444 = Byte
cover_Byte_426 :: Byte -> ()
cover_Byte_426 x
  = case x of
      Byte _ _ _ _ _ _ _ _ -> ()
-- Utils.ᵇproj₁
d_'7495'proj'8321'_446 :: T_Byte_426 -> Bool
d_'7495'proj'8321'_446 v0
  = case coe v0 of
      C_byte_444 v1 v2 v3 v4 v5 v6 v7 v8 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Utils.ᵇproj₂
d_'7495'proj'8322'_448 :: T_Byte_426 -> Bool
d_'7495'proj'8322'_448 v0
  = case coe v0 of
      C_byte_444 v1 v2 v3 v4 v5 v6 v7 v8 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Utils.ᵇproj₃
d_'7495'proj'8323'_450 :: T_Byte_426 -> Bool
d_'7495'proj'8323'_450 v0
  = case coe v0 of
      C_byte_444 v1 v2 v3 v4 v5 v6 v7 v8 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Utils.ᵇproj₄
d_'7495'proj'8324'_452 :: T_Byte_426 -> Bool
d_'7495'proj'8324'_452 v0
  = case coe v0 of
      C_byte_444 v1 v2 v3 v4 v5 v6 v7 v8 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Utils.ᵇproj₅
d_'7495'proj'8325'_454 :: T_Byte_426 -> Bool
d_'7495'proj'8325'_454 v0
  = case coe v0 of
      C_byte_444 v1 v2 v3 v4 v5 v6 v7 v8 -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Utils.ᵇproj₆
d_'7495'proj'8326'_456 :: T_Byte_426 -> Bool
d_'7495'proj'8326'_456 v0
  = case coe v0 of
      C_byte_444 v1 v2 v3 v4 v5 v6 v7 v8 -> coe v6
      _ -> MAlonzo.RTE.mazUnreachableError
-- Utils.ᵇproj₇
d_'7495'proj'8327'_458 :: T_Byte_426 -> Bool
d_'7495'proj'8327'_458 v0
  = case coe v0 of
      C_byte_444 v1 v2 v3 v4 v5 v6 v7 v8 -> coe v7
      _ -> MAlonzo.RTE.mazUnreachableError
-- Utils.ᵇproj₈
d_'7495'proj'8328'_460 :: T_Byte_426 -> Bool
d_'7495'proj'8328'_460 v0
  = case coe v0 of
      C_byte_444 v1 v2 v3 v4 v5 v6 v7 v8 -> coe v8
      _ -> MAlonzo.RTE.mazUnreachableError
-- Utils.Bits
d_Bits_490 :: Integer -> ()
d_Bits_490 = erased
-- Utils.byteToBits
d_byteToBits_494 ::
  T_Byte_426 -> MAlonzo.Code.Data.Vec.Base.T_Vec_28
d_byteToBits_494 v0
  = case coe v0 of
      C_byte_444 v1 v2 v3 v4 v5 v6 v7 v8
        -> coe
             MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v8
             (coe
                MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v7
                (coe
                   MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v6
                   (coe
                      MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v5
                      (coe
                         MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v4
                         (coe
                            MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v3
                            (coe
                               MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v2
                               (coe
                                  MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v1
                                  (coe MAlonzo.Code.Data.Vec.Base.C_'91''93'_32))))))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Utils.bitsToByte
d_bitsToByte_512 ::
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 -> T_Byte_426
d_bitsToByte_512 v0
  = case coe v0 of
      MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v2 v3
        -> case coe v3 of
             MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v5 v6
               -> case coe v6 of
                    MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v8 v9
                      -> case coe v9 of
                           MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v11 v12
                             -> case coe v12 of
                                  MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v14 v15
                                    -> case coe v15 of
                                         MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v17 v18
                                           -> case coe v18 of
                                                MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v20 v21
                                                  -> case coe v21 of
                                                       MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v23 v24
                                                         -> coe
                                                              seq (coe v24)
                                                              (coe
                                                                 C_byte_444 (coe v23) (coe v20)
                                                                 (coe v17) (coe v14) (coe v11)
                                                                 (coe v8) (coe v5) (coe v2))
                                                       _ -> MAlonzo.RTE.mazUnreachableError
                                                _ -> MAlonzo.RTE.mazUnreachableError
                                         _ -> MAlonzo.RTE.mazUnreachableError
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Utils.addBits
d_addBits_532 ::
  Integer ->
  Bool ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28
d_addBits_532 ~v0 v1 v2 v3 = du_addBits_532 v1 v2 v3
du_addBits_532 ::
  Bool ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28 ->
  MAlonzo.Code.Data.Vec.Base.T_Vec_28
du_addBits_532 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Data.Vec.Base.C_'91''93'_32
        -> coe seq (coe v2) (coe v1)
      MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v4 v5
        -> case coe v2 of
             MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v7 v8
               -> coe
                    MAlonzo.Code.Data.Vec.Base.C__'8759'__38
                    (MAlonzo.Code.Data.Bool.Base.d__xor__36
                       (coe v0)
                       (coe MAlonzo.Code.Data.Bool.Base.d__xor__36 (coe v4) (coe v7)))
                    (coe
                       du_addBits_532
                       (coe
                          MAlonzo.Code.Data.Bool.Base.d__'8744'__30
                          (coe MAlonzo.Code.Data.Bool.Base.d__'8743'__24 (coe v4) (coe v7))
                          (coe
                             MAlonzo.Code.Data.Bool.Base.d__'8743'__24 (coe v0)
                             (coe MAlonzo.Code.Data.Bool.Base.d__xor__36 (coe v4) (coe v7))))
                       (coe v5) (coe v8))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Utils.plusByte
d_plusByte_546 :: T_Byte_426 -> T_Byte_426 -> T_Byte_426
d_plusByte_546 v0 v1
  = coe
      d_bitsToByte_512
      (coe
         du_addBits_532 (coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8)
         (coe d_byteToBits_494 (coe v0)) (coe d_byteToBits_494 (coe v1)))
-- Utils.ℕToBits
d_ℕToBits_554 ::
  Integer -> Integer -> MAlonzo.Code.Data.Vec.Base.T_Vec_28
d_ℕToBits_554 v0 v1
  = case coe v0 of
      0 -> coe MAlonzo.Code.Data.Vec.Base.C_'91''93'_32
      _ -> let v2 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (coe
                MAlonzo.Code.Data.Vec.Base.C__'8759'__38
                (coe
                   du_lsb_564 (coe MAlonzo.Code.Data.Nat.Base.d_parity_264 (coe v1)))
                (d_ℕToBits_554
                   (coe v2)
                   (coe
                      MAlonzo.Code.Data.Nat.Base.d_'8970'_'47'2'8971'_268 (coe v1))))
-- Utils._.lsb
d_lsb_564 ::
  Integer ->
  Integer -> MAlonzo.Code.Data.Parity.Base.T_Parity_6 -> Bool
d_lsb_564 ~v0 ~v1 v2 = du_lsb_564 v2
du_lsb_564 :: MAlonzo.Code.Data.Parity.Base.T_Parity_6 -> Bool
du_lsb_564 v0
  = case coe v0 of
      MAlonzo.Code.Data.Parity.Base.C_0ℙ_8
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
      MAlonzo.Code.Data.Parity.Base.C_1ℙ_10
        -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
      _ -> MAlonzo.RTE.mazUnreachableError
-- Utils.bitsToℕ
d_bitsToℕ_568 ::
  Integer -> MAlonzo.Code.Data.Vec.Base.T_Vec_28 -> Integer
d_bitsToℕ_568 v0 v1
  = case coe v0 of
      0 -> coe (0 :: Integer)
      _ -> let v2 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (case coe v1 of
                MAlonzo.Code.Data.Vec.Base.C__'8759'__38 v4 v5
                  -> coe
                       addInt
                       (coe
                          MAlonzo.Code.Data.Bool.Base.du_if_then_else__44 (coe v4)
                          (coe (1 :: Integer)) (coe (0 :: Integer)))
                       (coe
                          mulInt (coe (2 :: Integer)) (coe d_bitsToℕ_568 (coe v2) (coe v5)))
                _ -> MAlonzo.RTE.mazUnreachableError)
-- Utils.ℕToByte
d_ℕToByte_576 :: Integer -> T_Byte_426
d_ℕToByte_576 v0
  = coe
      d_bitsToByte_512 (coe d_ℕToBits_554 (coe (8 :: Integer)) (coe v0))
-- Utils.byteToℕ
d_byteToℕ_580 :: T_Byte_426 -> Integer
d_byteToℕ_580 v0
  = coe
      d_bitsToℕ_568 (coe (8 :: Integer)) (coe d_byteToBits_494 (coe v0))
-- Utils.ℤToByte
d_ℤToByte_588 ::
  Integer ->
  MAlonzo.Code.Data.Integer.Base.T_NonNegative_146 -> T_Byte_426
d_ℤToByte_588 v0 ~v1 = du_ℤToByte_588 v0
du_ℤToByte_588 :: Integer -> T_Byte_426
du_ℤToByte_588 v0 = coe d_ℕToByte_576 (coe v0)
-- Utils.byteToℤ
d_byteToℤ_592 :: T_Byte_426 -> Integer
d_byteToℤ_592 v0 = coe d_byteToℕ_580 (coe v0)
-- Utils.ByteString
d_ByteString_596 = ()
type T_ByteString_596 = ByteString
pattern C_'91''93'_598 = BSNil
pattern C__'8759'__600 a0 a1 = BSCons a0 a1
check_'91''93'_598 :: T_ByteString_596
check_'91''93'_598 = BSNil
check__'8759'__600 ::
  T_Byte_426 -> T_ByteString_596 -> T_ByteString_596
check__'8759'__600 = BSCons
cover_ByteString_596 :: ByteString -> ()
cover_ByteString_596 x
  = case x of
      BSNil -> ()
      BSCons _ _ -> ()
-- Utils.mkByteString
d_mkByteString_602
  = error
      "MAlonzo Runtime Error: postulate evaluated: Utils.mkByteString"
-- Utils.eqByte
d_eqByte_604 :: T_Byte_426 -> T_Byte_426 -> Bool
d_eqByte_604 v0 v1
  = case coe v0 of
      C_byte_444 v2 v3 v4 v5 v6 v7 v8 v9
        -> case coe v1 of
             C_byte_444 v10 v11 v12 v13 v14 v15 v16 v17
               -> coe
                    MAlonzo.Code.Data.Bool.Base.d__'8743'__24
                    (coe
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
                       (coe
                          MAlonzo.Code.Data.Bool.Properties.d__'8799'__3196 (coe v2)
                          (coe v10)))
                    (coe
                       MAlonzo.Code.Data.Bool.Base.d__'8743'__24
                       (coe
                          MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
                          (coe
                             MAlonzo.Code.Data.Bool.Properties.d__'8799'__3196 (coe v3)
                             (coe v11)))
                       (coe
                          MAlonzo.Code.Data.Bool.Base.d__'8743'__24
                          (coe
                             MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
                             (coe
                                MAlonzo.Code.Data.Bool.Properties.d__'8799'__3196 (coe v4)
                                (coe v12)))
                          (coe
                             MAlonzo.Code.Data.Bool.Base.d__'8743'__24
                             (coe
                                MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
                                (coe
                                   MAlonzo.Code.Data.Bool.Properties.d__'8799'__3196 (coe v5)
                                   (coe v13)))
                             (coe
                                MAlonzo.Code.Data.Bool.Base.d__'8743'__24
                                (coe
                                   MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
                                   (coe
                                      MAlonzo.Code.Data.Bool.Properties.d__'8799'__3196 (coe v6)
                                      (coe v14)))
                                (coe
                                   MAlonzo.Code.Data.Bool.Base.d__'8743'__24
                                   (coe
                                      MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
                                      (coe
                                         MAlonzo.Code.Data.Bool.Properties.d__'8799'__3196 (coe v7)
                                         (coe v15)))
                                   (coe
                                      MAlonzo.Code.Data.Bool.Base.d__'8743'__24
                                      (coe
                                         MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
                                         (coe
                                            MAlonzo.Code.Data.Bool.Properties.d__'8799'__3196
                                            (coe v8) (coe v16)))
                                      (coe
                                         MAlonzo.Code.Relation.Nullary.Decidable.Core.d_does_28
                                         (coe
                                            MAlonzo.Code.Data.Bool.Properties.d__'8799'__3196
                                            (coe v9) (coe v17)))))))))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Utils.eqByteString
d_eqByteString_642 :: T_ByteString_596 -> T_ByteString_596 -> Bool
d_eqByteString_642 v0 v1
  = let v2 = coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8 in
    coe
      (case coe v0 of
         C_'91''93'_598
           -> case coe v1 of
                C_'91''93'_598 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
                _ -> coe v2
         C__'8759'__600 v3 v4
           -> case coe v1 of
                C__'8759'__600 v5 v6
                  -> coe
                       MAlonzo.Code.Data.Bool.Base.d__'8743'__24
                       (coe d_eqByte_604 (coe v3) (coe v5))
                       (coe d_eqByteString_642 (coe v4) (coe v6))
                _ -> coe v2
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Utils.take
d_take_652 :: Integer -> T_ByteString_596 -> T_ByteString_596
d_take_652 v0 v1
  = coe
      MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
      (coe
         MAlonzo.Code.Data.Integer.Base.d__'8804''7495'__110 (coe v0)
         (coe MAlonzo.Code.Data.Integer.Base.d_0ℤ_12))
      (coe C_'91''93'_598)
      (coe du_'46'extendedlambda0_658 (coe v0) (coe v1))
-- Utils..extendedlambda0
d_'46'extendedlambda0_658 ::
  Integer -> T_ByteString_596 -> T_ByteString_596 -> T_ByteString_596
d_'46'extendedlambda0_658 v0 ~v1 v2
  = du_'46'extendedlambda0_658 v0 v2
du_'46'extendedlambda0_658 ::
  Integer -> T_ByteString_596 -> T_ByteString_596
du_'46'extendedlambda0_658 v0 v1
  = case coe v1 of
      C_'91''93'_598 -> coe v1
      C__'8759'__600 v2 v3
        -> coe
             C__'8759'__600 (coe v2)
             (coe
                d_take_652
                (coe
                   MAlonzo.Code.Data.Integer.Base.d__'45'__302 (coe v0)
                   (coe MAlonzo.Code.Data.Integer.Base.d_1ℤ_16))
                (coe v3))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Utils.dropB
d_dropB_664 :: Integer -> T_ByteString_596 -> T_ByteString_596
d_dropB_664 v0 v1
  = coe
      MAlonzo.Code.Data.Bool.Base.du_if_then_else__44
      (coe
         MAlonzo.Code.Data.Integer.Base.d__'8804''7495'__110 (coe v0)
         (coe MAlonzo.Code.Data.Integer.Base.d_0ℤ_12))
      (coe v1) (coe du_'46'extendedlambda1_670 (coe v0) (coe v1))
-- Utils..extendedlambda1
d_'46'extendedlambda1_670 ::
  Integer -> T_ByteString_596 -> T_ByteString_596 -> T_ByteString_596
d_'46'extendedlambda1_670 v0 ~v1 v2
  = du_'46'extendedlambda1_670 v0 v2
du_'46'extendedlambda1_670 ::
  Integer -> T_ByteString_596 -> T_ByteString_596
du_'46'extendedlambda1_670 v0 v1
  = case coe v1 of
      C_'91''93'_598 -> coe v1
      C__'8759'__600 v2 v3
        -> coe
             d_dropB_664
             (coe
                MAlonzo.Code.Data.Integer.Base.d__'45'__302 (coe v0)
                (coe MAlonzo.Code.Data.Integer.Base.d_1ℤ_16))
             (coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Utils._×_
d__'215'__678 a0 a1 = ()
type T__'215'__678 a0 a1 = Pair a0 a1
pattern C__'44'__692 a0 a1 = (,) a0 a1
check__'44'__692 ::
  forall xA. forall xB. xA -> xB -> T__'215'__678 xA xB
check__'44'__692 = (,)
cover__'215'__678 :: Pair a1 a2 -> ()
cover__'215'__678 x
  = case x of
      (,) _ _ -> ()
-- Utils._×_.proj₁
d_proj'8321'_688 :: T__'215'__678 AgdaAny AgdaAny -> AgdaAny
d_proj'8321'_688 v0
  = case coe v0 of
      C__'44'__692 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Utils._×_.proj₂
d_proj'8322'_690 :: T__'215'__678 AgdaAny AgdaAny -> AgdaAny
d_proj'8322'_690 v0
  = case coe v0 of
      C__'44'__692 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Utils.List
d_List_696 a0 = ()
type T_List_696 a0 = [] a0
pattern C_'91''93'_700 = []
pattern C__'8759'__702 a0 a1 = (:) a0 a1
check_'91''93'_700 :: forall xA. T_List_696 xA
check_'91''93'_700 = []
check__'8759'__702 ::
  forall xA. xA -> T_List_696 xA -> T_List_696 xA
check__'8759'__702 = (:)
cover_List_696 :: [] a1 -> ()
cover_List_696 x
  = case x of
      [] -> ()
      (:) _ _ -> ()
-- Utils.All
d_All_710 a0 a1 a2 a3 = ()
data T_All_710 = C_'91''93'_718 | C__'8759'__728 AgdaAny T_All_710
-- Utils.length
d_length_732 :: () -> T_List_696 AgdaAny -> Integer
d_length_732 ~v0 v1 = du_length_732 v1
du_length_732 :: T_List_696 AgdaAny -> Integer
du_length_732 v0
  = case coe v0 of
      C_'91''93'_700 -> coe (0 :: Integer)
      C__'8759'__702 v1 v2
        -> coe addInt (coe (1 :: Integer)) (coe du_length_732 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Utils.map
d_map_742 ::
  () ->
  () ->
  (AgdaAny -> AgdaAny) -> T_List_696 AgdaAny -> T_List_696 AgdaAny
d_map_742 ~v0 ~v1 v2 v3 = du_map_742 v2 v3
du_map_742 ::
  (AgdaAny -> AgdaAny) -> T_List_696 AgdaAny -> T_List_696 AgdaAny
du_map_742 v0 v1
  = case coe v1 of
      C_'91''93'_700 -> coe v1
      C__'8759'__702 v2 v3
        -> coe
             C__'8759'__702 (coe v0 v2) (coe du_map_742 (coe v0) (coe v3))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Utils.toList
d_toList_754 :: () -> T_List_696 AgdaAny -> [AgdaAny]
d_toList_754 ~v0 v1 = du_toList_754 v1
du_toList_754 :: T_List_696 AgdaAny -> [AgdaAny]
du_toList_754 v0
  = case coe v0 of
      C_'91''93'_700 -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      C__'8759'__702 v1 v2
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v1)
             (coe du_toList_754 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Utils.fromList
d_fromList_762 :: () -> [AgdaAny] -> T_List_696 AgdaAny
d_fromList_762 ~v0 v1 = du_fromList_762 v1
du_fromList_762 :: [AgdaAny] -> T_List_696 AgdaAny
du_fromList_762 v0
  = case coe v0 of
      [] -> coe C_'91''93'_700
      (:) v1 v2
        -> coe C__'8759'__702 (coe v1) (coe du_fromList_762 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Utils.dropLIST
d_dropLIST_770 ::
  () -> Integer -> T_List_696 AgdaAny -> T_List_696 AgdaAny
d_dropLIST_770 ~v0 v1 v2 = du_dropLIST_770 v1 v2
du_dropLIST_770 ::
  Integer -> T_List_696 AgdaAny -> T_List_696 AgdaAny
du_dropLIST_770 v0 v1
  = case coe v0 of
      _ | coe geqInt (coe v0) (coe (0 :: Integer)) ->
          coe du_drop_782 (coe v0) (coe v1)
      _ -> coe v1
-- Utils._.drop
d_drop_782 ::
  () ->
  Integer ->
  T_List_696 AgdaAny ->
  () -> Integer -> T_List_696 AgdaAny -> T_List_696 AgdaAny
d_drop_782 ~v0 ~v1 ~v2 ~v3 v4 v5 = du_drop_782 v4 v5
du_drop_782 :: Integer -> T_List_696 AgdaAny -> T_List_696 AgdaAny
du_drop_782 v0 v1
  = case coe v0 of
      0 -> coe v1
      _ -> let v2 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (case coe v1 of
                C_'91''93'_700 -> coe v1
                C__'8759'__702 v3 v4 -> coe du_drop_782 (coe v2) (coe v4)
                _ -> MAlonzo.RTE.mazUnreachableError)
-- Utils.map-cong
d_map'45'cong_806 ::
  () ->
  () ->
  [AgdaAny] ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_map'45'cong_806 = erased
-- Utils.sequence
d_sequence_822 ::
  () -> (() -> ()) -> T_Monad_254 -> T_List_696 AgdaAny -> AgdaAny
d_sequence_822 ~v0 ~v1 v2 v3 = du_sequence_822 v2 v3
du_sequence_822 :: T_Monad_254 -> T_List_696 AgdaAny -> AgdaAny
du_sequence_822 v0 v1
  = case coe v1 of
      C_'91''93'_700 -> coe d_return_270 v0 erased v1
      C__'8759'__702 v2 v3
        -> coe
             d__'62''62''61'__276 v0 erased erased v2
             (\ v4 ->
                coe
                  d__'62''62''61'__276 v0 erased erased
                  (coe du_sequence_822 (coe v0) (coe v3))
                  (\ v5 ->
                     coe d_return_270 v0 erased (coe C__'8759'__702 (coe v4) (coe v5))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Utils.mapM
d_mapM_840 ::
  () ->
  () ->
  (() -> ()) ->
  T_Monad_254 ->
  (AgdaAny -> AgdaAny) -> T_List_696 AgdaAny -> AgdaAny
d_mapM_840 ~v0 ~v1 ~v2 v3 v4 v5 = du_mapM_840 v3 v4 v5
du_mapM_840 ::
  T_Monad_254 ->
  (AgdaAny -> AgdaAny) -> T_List_696 AgdaAny -> AgdaAny
du_mapM_840 v0 v1 v2
  = coe du_sequence_822 (coe v0) (coe du_map_742 (coe v1) (coe v2))
-- Utils.Array
type T_Array_844 a0 = Strict.Vector a0
d_Array_844
  = error "MAlonzo Runtime Error: postulate evaluated: Utils.Array"
-- Utils.HSlengthOfArray
d_HSlengthOfArray_848 :: forall xA. () -> T_Array_844 xA -> Integer
d_HSlengthOfArray_848 = \() -> \as -> toInteger (Strict.length as)
-- Utils.HSlistToArray
d_HSlistToArray_852 ::
  forall xA. () -> T_List_696 xA -> T_Array_844 xA
d_HSlistToArray_852 = \() -> Strict.fromList
-- Utils.HSindexArray
d_HSindexArray_854 ::
  forall xA. () -> T_Array_844 xA -> Integer -> xA
d_HSindexArray_854
  = \() -> \as -> \i -> as Strict.! (fromInteger i)
-- Utils.mkArray
d_mkArray_858
  = error "MAlonzo Runtime Error: postulate evaluated: Utils.mkArray"
-- Utils.DATA
d_DATA_860 = ()
type T_DATA_860 = Data
pattern C_ConstrDATA_862 a0 a1 = Constr a0 a1
pattern C_MapDATA_864 a0 = Map a0
pattern C_ListDATA_866 a0 = List a0
pattern C_iDATA_868 a0 = I a0
pattern C_bDATA_870 a0 = B a0
check_ConstrDATA_862 ::
  Integer -> T_List_696 T_DATA_860 -> T_DATA_860
check_ConstrDATA_862 = Constr
check_MapDATA_864 ::
  T_List_696 (T__'215'__678 T_DATA_860 T_DATA_860) -> T_DATA_860
check_MapDATA_864 = Map
check_ListDATA_866 :: T_List_696 T_DATA_860 -> T_DATA_860
check_ListDATA_866 = List
check_iDATA_868 :: Integer -> T_DATA_860
check_iDATA_868 = I
check_bDATA_870 :: T_ByteString_596 -> T_DATA_860
check_bDATA_870 = B
cover_DATA_860 :: Data -> ()
cover_DATA_860 x
  = case x of
      Constr _ _ -> ()
      Map _ -> ()
      List _ -> ()
      I _ -> ()
      B _ -> ()
-- Utils.eqDATA
d_eqDATA_872 :: T_DATA_860 -> T_DATA_860 -> Bool
d_eqDATA_872 v0 v1
  = case coe v0 of
      C_ConstrDATA_862 v2 v3
        -> case coe v1 of
             C_ConstrDATA_862 v4 v5
               -> coe
                    MAlonzo.Code.Data.Bool.Base.d__'8743'__24
                    (coe
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.du_isYes_132
                       (coe
                          MAlonzo.Code.Data.Integer.Properties.d__'8799'__2800 (coe v2)
                          (coe v4)))
                    (coe
                       MAlonzo.Code.Data.Bool.ListAction.d_and_10
                       (coe
                          MAlonzo.Code.Data.List.Base.du_zipWith_104 (coe d_eqDATA_872)
                          (coe du_toList_754 (coe v3)) (coe du_toList_754 (coe v5))))
             C_MapDATA_864 v4 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             C_ListDATA_866 v4 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             C_iDATA_868 v4 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             C_bDATA_870 v4 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             _ -> MAlonzo.RTE.mazUnreachableError
      C_MapDATA_864 v2
        -> case coe v1 of
             C_ConstrDATA_862 v3 v4
               -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             C_MapDATA_864 v3
               -> coe
                    MAlonzo.Code.Data.Bool.ListAction.d_and_10
                    (coe
                       MAlonzo.Code.Data.List.Base.du_zipWith_104
                       (coe
                          (\ v4 v5 ->
                             MAlonzo.Code.Data.Bool.Base.d__'8743'__24
                               (coe
                                  d_eqDATA_872 (coe d_proj'8321'_688 (coe v4))
                                  (coe d_proj'8321'_688 (coe v5)))
                               (coe
                                  d_eqDATA_872 (coe d_proj'8322'_690 (coe v4))
                                  (coe d_proj'8322'_690 (coe v5)))))
                       (coe du_toList_754 (coe v2)) (coe du_toList_754 (coe v3)))
             C_ListDATA_866 v3 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             C_iDATA_868 v3 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             C_bDATA_870 v3 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             _ -> MAlonzo.RTE.mazUnreachableError
      C_ListDATA_866 v2
        -> case coe v1 of
             C_ConstrDATA_862 v3 v4
               -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             C_MapDATA_864 v3 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             C_ListDATA_866 v3
               -> coe
                    MAlonzo.Code.Data.Bool.ListAction.d_and_10
                    (coe
                       MAlonzo.Code.Data.List.Base.du_zipWith_104 (coe d_eqDATA_872)
                       (coe du_toList_754 (coe v2)) (coe du_toList_754 (coe v3)))
             C_iDATA_868 v3 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             C_bDATA_870 v3 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             _ -> MAlonzo.RTE.mazUnreachableError
      C_iDATA_868 v2
        -> case coe v1 of
             C_ConstrDATA_862 v3 v4
               -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             C_MapDATA_864 v3 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             C_ListDATA_866 v3 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             C_iDATA_868 v3
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.du_isYes_132
                    (coe
                       MAlonzo.Code.Data.Integer.Properties.d__'8799'__2800 (coe v2)
                       (coe v3))
             C_bDATA_870 v3 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             _ -> MAlonzo.RTE.mazUnreachableError
      C_bDATA_870 v2
        -> case coe v1 of
             C_ConstrDATA_862 v3 v4
               -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             C_MapDATA_864 v3 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             C_ListDATA_866 v3 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             C_iDATA_868 v3 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             C_bDATA_870 v3 -> coe d_eqByteString_642 (coe v2) (coe v3)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Utils.Bls12-381-G1-Element
type T_Bls12'45'381'45'G1'45'Element_1006 = G1.Element
d_Bls12'45'381'45'G1'45'Element_1006
  = error
      "MAlonzo Runtime Error: postulate evaluated: Utils.Bls12-381-G1-Element"
-- Utils.eqBls12-381-G1-Element
d_eqBls12'45'381'45'G1'45'Element_1008 ::
  T_Bls12'45'381'45'G1'45'Element_1006 ->
  T_Bls12'45'381'45'G1'45'Element_1006 -> Bool
d_eqBls12'45'381'45'G1'45'Element_1008 = (==)
-- Utils.Bls12-381-G2-Element
type T_Bls12'45'381'45'G2'45'Element_1010 = G2.Element
d_Bls12'45'381'45'G2'45'Element_1010
  = error
      "MAlonzo Runtime Error: postulate evaluated: Utils.Bls12-381-G2-Element"
-- Utils.eqBls12-381-G2-Element
d_eqBls12'45'381'45'G2'45'Element_1012 ::
  T_Bls12'45'381'45'G2'45'Element_1010 ->
  T_Bls12'45'381'45'G2'45'Element_1010 -> Bool
d_eqBls12'45'381'45'G2'45'Element_1012 = (==)
-- Utils.Bls12-381-MlResult
type T_Bls12'45'381'45'MlResult_1014 = Pairing.MlResult
d_Bls12'45'381'45'MlResult_1014
  = error
      "MAlonzo Runtime Error: postulate evaluated: Utils.Bls12-381-MlResult"
-- Utils.eqBls12-381-MlResult
d_eqBls12'45'381'45'MlResult_1016 ::
  T_Bls12'45'381'45'MlResult_1014 ->
  T_Bls12'45'381'45'MlResult_1014 -> Bool
d_eqBls12'45'381'45'MlResult_1016 = (==)
-- Utils.Value
type T_Value_1018 = V.Value
d_Value_1018
  = error "MAlonzo Runtime Error: postulate evaluated: Utils.Value"
-- Utils.eqValue
d_eqValue_1020 :: T_Value_1018 -> T_Value_1018 -> Bool
d_eqValue_1020 = (==)
-- Utils.valueFromList
d_valueFromList_1022
  = error
      "MAlonzo Runtime Error: postulate evaluated: Utils.valueFromList"
-- Utils.Kind
d_Kind_1024 = ()
type T_Kind_1024 = KIND
pattern C_'42'_1026 = Star
pattern C_'9839'_1028 = Sharp
pattern C__'8658'__1030 a0 a1 = Arrow a0 a1
check_'42'_1026 :: T_Kind_1024
check_'42'_1026 = Star
check_'9839'_1028 :: T_Kind_1024
check_'9839'_1028 = Sharp
check__'8658'__1030 :: T_Kind_1024 -> T_Kind_1024 -> T_Kind_1024
check__'8658'__1030 = Arrow
cover_Kind_1024 :: KIND -> ()
cover_Kind_1024 x
  = case x of
      Star -> ()
      Sharp -> ()
      Arrow _ _ -> ()
-- Utils.TRACE
d_TRACE_1040 ::
  () ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 -> AgdaAny -> AgdaAny
d_TRACE_1040 ~v0 ~v1 v2 = du_TRACE_1040 v2
du_TRACE_1040 :: AgdaAny -> AgdaAny
du_TRACE_1040 v0 = coe v0
