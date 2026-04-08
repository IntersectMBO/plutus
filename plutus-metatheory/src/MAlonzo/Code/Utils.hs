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
  = C_constructor_290 (() -> AgdaAny -> AgdaAny)
                      (() -> () -> AgdaAny -> (AgdaAny -> AgdaAny) -> AgdaAny)
-- Utils.Monad.return
d_return_262 :: T_Monad_246 -> () -> AgdaAny -> AgdaAny
d_return_262 v0
  = case coe v0 of
      C_constructor_290 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Utils.Monad._>>=_
d__'62''62''61'__268 ::
  T_Monad_246 ->
  () -> () -> AgdaAny -> (AgdaAny -> AgdaAny) -> AgdaAny
d__'62''62''61'__268 v0
  = case coe v0 of
      C_constructor_290 v1 v2 -> coe v2
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
d__'62''62'__294 ::
  (() -> ()) ->
  T_Monad_246 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d__'62''62'__294 ~v0 v1 = du__'62''62'__294 v1
du__'62''62'__294 ::
  T_Monad_246 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
du__'62''62'__294 v0 v1 v2 v3 v4
  = coe du__'62''62'__274 (coe v0) v3 v4
-- Utils._._>>=_
d__'62''62''61'__296 ::
  T_Monad_246 ->
  () -> () -> AgdaAny -> (AgdaAny -> AgdaAny) -> AgdaAny
d__'62''62''61'__296 v0 = coe d__'62''62''61'__268 (coe v0)
-- Utils._.fmap
d_fmap_298 ::
  (() -> ()) ->
  T_Monad_246 ->
  () -> () -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_fmap_298 ~v0 v1 = du_fmap_298 v1
du_fmap_298 ::
  T_Monad_246 ->
  () -> () -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du_fmap_298 v0 v1 v2 v3 v4 = coe du_fmap_284 (coe v0) v3 v4
-- Utils._.return
d_return_300 :: T_Monad_246 -> () -> AgdaAny -> AgdaAny
d_return_300 v0 = coe d_return_262 (coe v0)
-- Utils.MaybeMonad
d_MaybeMonad_302 :: T_Monad_246
d_MaybeMonad_302
  = coe
      C_constructor_290
      (coe (\ v0 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16))
      (coe
         (\ v0 v1 v2 v3 ->
            coe MAlonzo.Code.Data.Maybe.Base.du__'62''62''61'__72 v2 v3))
-- Utils.sumBind
d_sumBind_310 ::
  () ->
  () ->
  () ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  (AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30) ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_sumBind_310 ~v0 ~v1 ~v2 v3 v4 = du_sumBind_310 v3 v4
du_sumBind_310 ::
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  (AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30) ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_sumBind_310 v0 v1
  = case coe v0 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v2 -> coe v1 v2
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v2 -> coe v0
      _ -> MAlonzo.RTE.mazUnreachableError
-- Utils.SumMonad
d_SumMonad_324 :: () -> T_Monad_246
d_SumMonad_324 ~v0 = du_SumMonad_324
du_SumMonad_324 :: T_Monad_246
du_SumMonad_324
  = coe
      C_constructor_290
      (coe (\ v0 -> coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38))
      (coe (\ v0 v1 -> coe du_sumBind_310))
-- Utils.EitherMonad
d_EitherMonad_330 :: () -> T_Monad_246
d_EitherMonad_330 ~v0 = du_EitherMonad_330
du_EitherMonad_330 :: T_Monad_246
du_EitherMonad_330
  = coe
      C_constructor_290 (coe (\ v0 -> coe C_inj'8322'_14))
      (coe (\ v0 v1 -> coe du_eitherBind_54))
-- Utils.EitherP
d_EitherP_336 :: () -> T_Monad_246
d_EitherP_336 ~v0 = du_EitherP_336
du_EitherP_336 :: T_Monad_246
du_EitherP_336
  = coe
      C_constructor_290 (coe (\ v0 -> coe C_inj'8322'_14))
      (coe (\ v0 v1 -> coe du_eitherBind_54))
-- Utils.withE
d_withE_344 ::
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  T_Either_6 AgdaAny AgdaAny -> T_Either_6 AgdaAny AgdaAny
d_withE_344 ~v0 ~v1 ~v2 v3 v4 = du_withE_344 v3 v4
du_withE_344 ::
  (AgdaAny -> AgdaAny) ->
  T_Either_6 AgdaAny AgdaAny -> T_Either_6 AgdaAny AgdaAny
du_withE_344 v0 v1
  = case coe v1 of
      C_inj'8321'_12 v2 -> coe C_inj'8321'_12 (coe v0 v2)
      C_inj'8322'_14 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Utils.dec2Either
d_dec2Either_356 ::
  () ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  T_Either_6
    (AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) AgdaAny
d_dec2Either_356 ~v0 v1 = du_dec2Either_356 v1
du_dec2Either_356 ::
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  T_Either_6
    (AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) AgdaAny
du_dec2Either_356 v0
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
d_Writer_366 a0 a1 = ()
data T_Writer_366 = C__'44'__380 AgdaAny AgdaAny
-- Utils.Writer.wrvalue
d_wrvalue_376 :: T_Writer_366 -> AgdaAny
d_wrvalue_376 v0
  = case coe v0 of
      C__'44'__380 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Utils.Writer.accum
d_accum_378 :: T_Writer_366 -> AgdaAny
d_accum_378 v0
  = case coe v0 of
      C__'44'__380 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Utils.WriterMonad.WriterMonad
d_WriterMonad_390 ::
  () -> AgdaAny -> (AgdaAny -> AgdaAny -> AgdaAny) -> T_Monad_246
d_WriterMonad_390 ~v0 v1 v2 = du_WriterMonad_390 v1 v2
du_WriterMonad_390 ::
  AgdaAny -> (AgdaAny -> AgdaAny -> AgdaAny) -> T_Monad_246
du_WriterMonad_390 v0 v1
  = coe
      C_constructor_290
      (coe (\ v2 v3 -> coe C__'44'__380 (coe v3) (coe v0)))
      (coe
         (\ v2 v3 v4 ->
            case coe v4 of
              C__'44'__380 v5 v6
                -> coe
                     (\ v7 ->
                        coe
                          C__'44'__380 (coe d_wrvalue_376 (coe v7 v5))
                          (coe v1 v6 (d_accum_378 (coe v7 v5))))
              _ -> MAlonzo.RTE.mazUnreachableError))
-- Utils.WriterMonad.tell
d_tell_406 ::
  () ->
  AgdaAny ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny -> T_Writer_366
d_tell_406 ~v0 ~v1 ~v2 v3 = du_tell_406 v3
du_tell_406 :: AgdaAny -> T_Writer_366
du_tell_406 v0
  = coe
      C__'44'__380 (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8) (coe v0)
-- Utils.RuntimeError
d_RuntimeError_410 = ()
type T_RuntimeError_410 = RuntimeError
pattern C_gasError_412 = GasError
pattern C_userError_414 = UserError
pattern C_runtimeTypeError_416 = RuntimeTypeError
check_gasError_412 :: T_RuntimeError_410
check_gasError_412 = GasError
check_userError_414 :: T_RuntimeError_410
check_userError_414 = UserError
check_runtimeTypeError_416 :: T_RuntimeError_410
check_runtimeTypeError_416 = RuntimeTypeError
cover_RuntimeError_410 :: RuntimeError -> ()
cover_RuntimeError_410 x
  = case x of
      GasError -> ()
      UserError -> ()
      RuntimeTypeError -> ()
-- Utils.ByteString
type T_ByteString_418 = BS.ByteString
d_ByteString_418
  = error
      "MAlonzo Runtime Error: postulate evaluated: Utils.ByteString"
-- Utils.mkByteString
d_mkByteString_420
  = error
      "MAlonzo Runtime Error: postulate evaluated: Utils.mkByteString"
-- Utils.eqByteString
d_eqByteString_422 :: T_ByteString_418 -> T_ByteString_418 -> Bool
d_eqByteString_422 = (==)
-- Utils._×_
d__'215'__428 a0 a1 = ()
type T__'215'__428 a0 a1 = Pair a0 a1
pattern C__'44'__442 a0 a1 = (,) a0 a1
check__'44'__442 ::
  forall xA. forall xB. xA -> xB -> T__'215'__428 xA xB
check__'44'__442 = (,)
cover__'215'__428 :: Pair a1 a2 -> ()
cover__'215'__428 x
  = case x of
      (,) _ _ -> ()
-- Utils._×_.proj₁
d_proj'8321'_438 :: T__'215'__428 AgdaAny AgdaAny -> AgdaAny
d_proj'8321'_438 v0
  = case coe v0 of
      C__'44'__442 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Utils._×_.proj₂
d_proj'8322'_440 :: T__'215'__428 AgdaAny AgdaAny -> AgdaAny
d_proj'8322'_440 v0
  = case coe v0 of
      C__'44'__442 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Utils.List
d_List_446 a0 = ()
type T_List_446 a0 = [] a0
pattern C_'91''93'_450 = []
pattern C__'8759'__452 a0 a1 = (:) a0 a1
check_'91''93'_450 :: forall xA. T_List_446 xA
check_'91''93'_450 = []
check__'8759'__452 ::
  forall xA. xA -> T_List_446 xA -> T_List_446 xA
check__'8759'__452 = (:)
cover_List_446 :: [] a1 -> ()
cover_List_446 x
  = case x of
      [] -> ()
      (:) _ _ -> ()
-- Utils.All
d_All_460 a0 a1 a2 a3 = ()
data T_All_460 = C_'91''93'_468 | C__'8759'__478 AgdaAny T_All_460
-- Utils.length
d_length_482 :: () -> T_List_446 AgdaAny -> Integer
d_length_482 ~v0 v1 = du_length_482 v1
du_length_482 :: T_List_446 AgdaAny -> Integer
du_length_482 v0
  = case coe v0 of
      C_'91''93'_450 -> coe (0 :: Integer)
      C__'8759'__452 v1 v2
        -> coe addInt (coe (1 :: Integer)) (coe du_length_482 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Utils.map
d_map_492 ::
  () ->
  () ->
  (AgdaAny -> AgdaAny) -> T_List_446 AgdaAny -> T_List_446 AgdaAny
d_map_492 ~v0 ~v1 v2 v3 = du_map_492 v2 v3
du_map_492 ::
  (AgdaAny -> AgdaAny) -> T_List_446 AgdaAny -> T_List_446 AgdaAny
du_map_492 v0 v1
  = case coe v1 of
      C_'91''93'_450 -> coe v1
      C__'8759'__452 v2 v3
        -> coe
             C__'8759'__452 (coe v0 v2) (coe du_map_492 (coe v0) (coe v3))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Utils.toList
d_toList_504 :: () -> T_List_446 AgdaAny -> [AgdaAny]
d_toList_504 ~v0 v1 = du_toList_504 v1
du_toList_504 :: T_List_446 AgdaAny -> [AgdaAny]
du_toList_504 v0
  = case coe v0 of
      C_'91''93'_450 -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      C__'8759'__452 v1 v2
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v1)
             (coe du_toList_504 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Utils.fromList
d_fromList_512 :: () -> [AgdaAny] -> T_List_446 AgdaAny
d_fromList_512 ~v0 v1 = du_fromList_512 v1
du_fromList_512 :: [AgdaAny] -> T_List_446 AgdaAny
du_fromList_512 v0
  = case coe v0 of
      [] -> coe C_'91''93'_450
      (:) v1 v2
        -> coe C__'8759'__452 (coe v1) (coe du_fromList_512 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Utils.dropLIST
d_dropLIST_520 ::
  () -> Integer -> T_List_446 AgdaAny -> T_List_446 AgdaAny
d_dropLIST_520 ~v0 v1 v2 = du_dropLIST_520 v1 v2
du_dropLIST_520 ::
  Integer -> T_List_446 AgdaAny -> T_List_446 AgdaAny
du_dropLIST_520 v0 v1
  = case coe v0 of
      _ | coe geqInt (coe v0) (coe (0 :: Integer)) ->
          coe du_drop_532 (coe v0) (coe v1)
      _ -> coe v1
-- Utils._.drop
d_drop_532 ::
  () ->
  Integer ->
  T_List_446 AgdaAny ->
  () -> Integer -> T_List_446 AgdaAny -> T_List_446 AgdaAny
d_drop_532 ~v0 ~v1 ~v2 ~v3 v4 v5 = du_drop_532 v4 v5
du_drop_532 :: Integer -> T_List_446 AgdaAny -> T_List_446 AgdaAny
du_drop_532 v0 v1
  = case coe v0 of
      0 -> coe v1
      _ -> let v2 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (case coe v1 of
                C_'91''93'_450 -> coe v1
                C__'8759'__452 v3 v4 -> coe du_drop_532 (coe v2) (coe v4)
                _ -> MAlonzo.RTE.mazUnreachableError)
-- Utils.map-cong
d_map'45'cong_556 ::
  () ->
  () ->
  [AgdaAny] ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_map'45'cong_556 = erased
-- Utils.sequence
d_sequence_572 ::
  () -> (() -> ()) -> T_Monad_246 -> T_List_446 AgdaAny -> AgdaAny
d_sequence_572 ~v0 ~v1 v2 v3 = du_sequence_572 v2 v3
du_sequence_572 :: T_Monad_246 -> T_List_446 AgdaAny -> AgdaAny
du_sequence_572 v0 v1
  = case coe v1 of
      C_'91''93'_450 -> coe d_return_262 v0 erased v1
      C__'8759'__452 v2 v3
        -> coe
             d__'62''62''61'__268 v0 erased erased v2
             (\ v4 ->
                coe
                  d__'62''62''61'__268 v0 erased erased
                  (coe du_sequence_572 (coe v0) (coe v3))
                  (\ v5 ->
                     coe d_return_262 v0 erased (coe C__'8759'__452 (coe v4) (coe v5))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Utils.mapM
d_mapM_590 ::
  () ->
  () ->
  (() -> ()) ->
  T_Monad_246 ->
  (AgdaAny -> AgdaAny) -> T_List_446 AgdaAny -> AgdaAny
d_mapM_590 ~v0 ~v1 ~v2 v3 v4 v5 = du_mapM_590 v3 v4 v5
du_mapM_590 ::
  T_Monad_246 ->
  (AgdaAny -> AgdaAny) -> T_List_446 AgdaAny -> AgdaAny
du_mapM_590 v0 v1 v2
  = coe du_sequence_572 (coe v0) (coe du_map_492 (coe v1) (coe v2))
-- Utils.Array
type T_Array_594 a0 = Strict.Vector a0
d_Array_594
  = error "MAlonzo Runtime Error: postulate evaluated: Utils.Array"
-- Utils.HSlengthOfArray
d_HSlengthOfArray_598 :: forall xA. () -> T_Array_594 xA -> Integer
d_HSlengthOfArray_598 = \() -> \as -> toInteger (Strict.length as)
-- Utils.HSlistToArray
d_HSlistToArray_602 ::
  forall xA. () -> T_List_446 xA -> T_Array_594 xA
d_HSlistToArray_602 = \() -> Strict.fromList
-- Utils.HSindexArray
d_HSindexArray_604 ::
  forall xA. () -> T_Array_594 xA -> Integer -> xA
d_HSindexArray_604
  = \() -> \as -> \i -> as Strict.! (fromInteger i)
-- Utils.mkArray
d_mkArray_608
  = error "MAlonzo Runtime Error: postulate evaluated: Utils.mkArray"
-- Utils.DATA
d_DATA_610 = ()
type T_DATA_610 = Data
pattern C_ConstrDATA_612 a0 a1 = D.Constr a0 a1
pattern C_MapDATA_614 a0 = D.Map a0
pattern C_ListDATA_616 a0 = D.List a0
pattern C_iDATA_618 a0 = D.I a0
pattern C_bDATA_620 a0 = D.B a0
check_ConstrDATA_612 ::
  Integer -> T_List_446 T_DATA_610 -> T_DATA_610
check_ConstrDATA_612 = D.Constr
check_MapDATA_614 ::
  T_List_446 (T__'215'__428 T_DATA_610 T_DATA_610) -> T_DATA_610
check_MapDATA_614 = D.Map
check_ListDATA_616 :: T_List_446 T_DATA_610 -> T_DATA_610
check_ListDATA_616 = D.List
check_iDATA_618 :: Integer -> T_DATA_610
check_iDATA_618 = D.I
check_bDATA_620 :: T_ByteString_418 -> T_DATA_610
check_bDATA_620 = D.B
cover_DATA_610 :: Data -> ()
cover_DATA_610 x
  = case x of
      D.Constr _ _ -> ()
      D.Map _ -> ()
      D.List _ -> ()
      D.I _ -> ()
      D.B _ -> ()
-- Utils.eqDATA
d_eqDATA_622 :: T_DATA_610 -> T_DATA_610 -> Bool
d_eqDATA_622 = (==)
-- Utils.Bls12-381-G1-Element
type T_Bls12'45'381'45'G1'45'Element_756 = G1.Element
d_Bls12'45'381'45'G1'45'Element_756
  = error
      "MAlonzo Runtime Error: postulate evaluated: Utils.Bls12-381-G1-Element"
-- Utils.eqBls12-381-G1-Element
d_eqBls12'45'381'45'G1'45'Element_758 ::
  T_Bls12'45'381'45'G1'45'Element_756 ->
  T_Bls12'45'381'45'G1'45'Element_756 -> Bool
d_eqBls12'45'381'45'G1'45'Element_758 = (==)
-- Utils.Bls12-381-G2-Element
type T_Bls12'45'381'45'G2'45'Element_760 = G2.Element
d_Bls12'45'381'45'G2'45'Element_760
  = error
      "MAlonzo Runtime Error: postulate evaluated: Utils.Bls12-381-G2-Element"
-- Utils.eqBls12-381-G2-Element
d_eqBls12'45'381'45'G2'45'Element_762 ::
  T_Bls12'45'381'45'G2'45'Element_760 ->
  T_Bls12'45'381'45'G2'45'Element_760 -> Bool
d_eqBls12'45'381'45'G2'45'Element_762 = (==)
-- Utils.Bls12-381-MlResult
type T_Bls12'45'381'45'MlResult_764 = Pairing.MlResult
d_Bls12'45'381'45'MlResult_764
  = error
      "MAlonzo Runtime Error: postulate evaluated: Utils.Bls12-381-MlResult"
-- Utils.eqBls12-381-MlResult
d_eqBls12'45'381'45'MlResult_766 ::
  T_Bls12'45'381'45'MlResult_764 ->
  T_Bls12'45'381'45'MlResult_764 -> Bool
d_eqBls12'45'381'45'MlResult_766 = (==)
-- Utils.Kind
d_Kind_768 = ()
type T_Kind_768 = KIND
pattern C_'42'_770 = Star
pattern C_'9839'_772 = Sharp
pattern C__'8658'__774 a0 a1 = Arrow a0 a1
check_'42'_770 :: T_Kind_768
check_'42'_770 = Star
check_'9839'_772 :: T_Kind_768
check_'9839'_772 = Sharp
check__'8658'__774 :: T_Kind_768 -> T_Kind_768 -> T_Kind_768
check__'8658'__774 = Arrow
cover_Kind_768 :: KIND -> ()
cover_Kind_768 x
  = case x of
      Star -> ()
      Sharp -> ()
      Arrow _ _ -> ()
