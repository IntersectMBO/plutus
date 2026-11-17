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
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.String
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
-- Utils.intToFin
d_intToFin_140 ::
  Integer -> Integer -> Maybe MAlonzo.Code.Data.Fin.Base.T_Fin_10
d_intToFin_140 v0 v1
  = case coe v1 of
      _ | coe geqInt (coe v1) (coe (0 :: Integer)) ->
          coe d_natToFin_118 (coe v0) (coe v1)
      _ -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
-- Utils.cong₃
d_cong'8323'_166 ::
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
d_cong'8323'_166 = erased
-- Utils.≡-subst-removable
d_'8801''45'subst'45'removable_188 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> ()) ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8801''45'subst'45'removable_188 = erased
-- Utils._∔_≣_
d__'8724'_'8803'__194 a0 a1 a2 = ()
data T__'8724'_'8803'__194
  = C_start_198 | C_bubble_206 T__'8724'_'8803'__194
-- Utils.unique∔
d_unique'8724'_218 ::
  Integer ->
  Integer ->
  Integer ->
  T__'8724'_'8803'__194 ->
  T__'8724'_'8803'__194 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_unique'8724'_218 = erased
-- Utils.+2∔
d_'43'2'8724'_230 ::
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  T__'8724'_'8803'__194
d_'43'2'8724'_230 v0 ~v1 ~v2 ~v3 = du_'43'2'8724'_230 v0
du_'43'2'8724'_230 :: Integer -> T__'8724'_'8803'__194
du_'43'2'8724'_230 v0
  = case coe v0 of
      0 -> coe C_start_198
      _ -> let v1 = subInt (coe v0) (coe (1 :: Integer)) in
           coe (coe C_bubble_206 (coe du_'43'2'8724'_230 (coe v1)))
-- Utils.∔2+
d_'8724'2'43'_248 ::
  Integer ->
  Integer ->
  Integer ->
  T__'8724'_'8803'__194 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_'8724'2'43'_248 = erased
-- Utils.alldone
d_alldone_254 :: Integer -> T__'8724'_'8803'__194
d_alldone_254 v0 = coe du_'43'2'8724'_230 (coe v0)
-- Utils.Monad
d_Monad_260 a0 = ()
data T_Monad_260
  = C_constructor_304 (() -> AgdaAny -> AgdaAny)
                      (() -> () -> AgdaAny -> (AgdaAny -> AgdaAny) -> AgdaAny)
-- Utils.Monad.return
d_return_276 :: T_Monad_260 -> () -> AgdaAny -> AgdaAny
d_return_276 v0
  = case coe v0 of
      C_constructor_304 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Utils.Monad._>>=_
d__'62''62''61'__282 ::
  T_Monad_260 ->
  () -> () -> AgdaAny -> (AgdaAny -> AgdaAny) -> AgdaAny
d__'62''62''61'__282 v0
  = case coe v0 of
      C_constructor_304 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Utils.Monad._>>_
d__'62''62'__288 ::
  (() -> ()) ->
  T_Monad_260 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d__'62''62'__288 ~v0 v1 ~v2 ~v3 v4 v5 = du__'62''62'__288 v1 v4 v5
du__'62''62'__288 :: T_Monad_260 -> AgdaAny -> AgdaAny -> AgdaAny
du__'62''62'__288 v0 v1 v2
  = coe d__'62''62''61'__282 v0 erased erased v1 (\ v3 -> v2)
-- Utils.Monad.fmap
d_fmap_298 ::
  (() -> ()) ->
  T_Monad_260 ->
  () -> () -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_fmap_298 ~v0 v1 ~v2 ~v3 v4 v5 = du_fmap_298 v1 v4 v5
du_fmap_298 ::
  T_Monad_260 -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du_fmap_298 v0 v1 v2
  = coe
      d__'62''62''61'__282 v0 erased erased v2
      (\ v3 -> coe d_return_276 v0 erased (coe v1 v3))
-- Utils._._>>_
d__'62''62'__308 ::
  (() -> ()) ->
  T_Monad_260 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
d__'62''62'__308 ~v0 v1 = du__'62''62'__308 v1
du__'62''62'__308 ::
  T_Monad_260 -> () -> () -> AgdaAny -> AgdaAny -> AgdaAny
du__'62''62'__308 v0 v1 v2 v3 v4
  = coe du__'62''62'__288 (coe v0) v3 v4
-- Utils._._>>=_
d__'62''62''61'__310 ::
  T_Monad_260 ->
  () -> () -> AgdaAny -> (AgdaAny -> AgdaAny) -> AgdaAny
d__'62''62''61'__310 v0 = coe d__'62''62''61'__282 (coe v0)
-- Utils._.fmap
d_fmap_312 ::
  (() -> ()) ->
  T_Monad_260 ->
  () -> () -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
d_fmap_312 ~v0 v1 = du_fmap_312 v1
du_fmap_312 ::
  T_Monad_260 ->
  () -> () -> (AgdaAny -> AgdaAny) -> AgdaAny -> AgdaAny
du_fmap_312 v0 v1 v2 v3 v4 = coe du_fmap_298 (coe v0) v3 v4
-- Utils._.return
d_return_314 :: T_Monad_260 -> () -> AgdaAny -> AgdaAny
d_return_314 v0 = coe d_return_276 (coe v0)
-- Utils.MaybeMonad
d_MaybeMonad_316 :: T_Monad_260
d_MaybeMonad_316
  = coe
      C_constructor_304
      (coe (\ v0 -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16))
      (coe
         (\ v0 v1 v2 v3 ->
            coe MAlonzo.Code.Data.Maybe.Base.du__'62''62''61'__72 v2 v3))
-- Utils.sumBind
d_sumBind_324 ::
  () ->
  () ->
  () ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  (AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30) ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
d_sumBind_324 ~v0 ~v1 ~v2 v3 v4 = du_sumBind_324 v3 v4
du_sumBind_324 ::
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30 ->
  (AgdaAny -> MAlonzo.Code.Data.Sum.Base.T__'8846'__30) ->
  MAlonzo.Code.Data.Sum.Base.T__'8846'__30
du_sumBind_324 v0 v1
  = case coe v0 of
      MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v2 -> coe v1 v2
      MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v2 -> coe v0
      _ -> MAlonzo.RTE.mazUnreachableError
-- Utils.SumMonad
d_SumMonad_338 :: () -> T_Monad_260
d_SumMonad_338 ~v0 = du_SumMonad_338
du_SumMonad_338 :: T_Monad_260
du_SumMonad_338
  = coe
      C_constructor_304
      (coe (\ v0 -> coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38))
      (coe (\ v0 v1 -> coe du_sumBind_324))
-- Utils.EitherMonad
d_EitherMonad_344 :: () -> T_Monad_260
d_EitherMonad_344 ~v0 = du_EitherMonad_344
du_EitherMonad_344 :: T_Monad_260
du_EitherMonad_344
  = coe
      C_constructor_304 (coe (\ v0 -> coe C_inj'8322'_14))
      (coe (\ v0 v1 -> coe du_eitherBind_54))
-- Utils.EitherP
d_EitherP_350 :: () -> T_Monad_260
d_EitherP_350 ~v0 = du_EitherP_350
du_EitherP_350 :: T_Monad_260
du_EitherP_350
  = coe
      C_constructor_304 (coe (\ v0 -> coe C_inj'8322'_14))
      (coe (\ v0 v1 -> coe du_eitherBind_54))
-- Utils.withE
d_withE_358 ::
  () ->
  () ->
  () ->
  (AgdaAny -> AgdaAny) ->
  T_Either_6 AgdaAny AgdaAny -> T_Either_6 AgdaAny AgdaAny
d_withE_358 ~v0 ~v1 ~v2 v3 v4 = du_withE_358 v3 v4
du_withE_358 ::
  (AgdaAny -> AgdaAny) ->
  T_Either_6 AgdaAny AgdaAny -> T_Either_6 AgdaAny AgdaAny
du_withE_358 v0 v1
  = case coe v1 of
      C_inj'8321'_12 v2 -> coe C_inj'8321'_12 (coe v0 v2)
      C_inj'8322'_14 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Utils.dec2Either
d_dec2Either_370 ::
  () ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  T_Either_6
    (AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) AgdaAny
d_dec2Either_370 ~v0 v1 = du_dec2Either_370 v1
du_dec2Either_370 ::
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20 ->
  T_Either_6
    (AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) AgdaAny
du_dec2Either_370 v0
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
d_Writer_380 a0 a1 = ()
data T_Writer_380 = C__'44'__394 AgdaAny AgdaAny
-- Utils.Writer.wrvalue
d_wrvalue_390 :: T_Writer_380 -> AgdaAny
d_wrvalue_390 v0
  = case coe v0 of
      C__'44'__394 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Utils.Writer.accum
d_accum_392 :: T_Writer_380 -> AgdaAny
d_accum_392 v0
  = case coe v0 of
      C__'44'__394 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Utils.WriterMonad.WriterMonad
d_WriterMonad_404 ::
  () -> AgdaAny -> (AgdaAny -> AgdaAny -> AgdaAny) -> T_Monad_260
d_WriterMonad_404 ~v0 v1 v2 = du_WriterMonad_404 v1 v2
du_WriterMonad_404 ::
  AgdaAny -> (AgdaAny -> AgdaAny -> AgdaAny) -> T_Monad_260
du_WriterMonad_404 v0 v1
  = coe
      C_constructor_304
      (coe (\ v2 v3 -> coe C__'44'__394 (coe v3) (coe v0)))
      (coe
         (\ v2 v3 v4 ->
            case coe v4 of
              C__'44'__394 v5 v6
                -> coe
                     (\ v7 ->
                        coe
                          C__'44'__394 (coe d_wrvalue_390 (coe v7 v5))
                          (coe v1 v6 (d_accum_392 (coe v7 v5))))
              _ -> MAlonzo.RTE.mazUnreachableError))
-- Utils.WriterMonad.tell
d_tell_420 ::
  () ->
  AgdaAny ->
  (AgdaAny -> AgdaAny -> AgdaAny) -> AgdaAny -> T_Writer_380
d_tell_420 ~v0 ~v1 ~v2 v3 = du_tell_420 v3
du_tell_420 :: AgdaAny -> T_Writer_380
du_tell_420 v0
  = coe
      C__'44'__394 (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8) (coe v0)
-- Utils.RuntimeError
d_RuntimeError_424 = ()
type T_RuntimeError_424 = RuntimeError
pattern C_gasError_426 = GasError
pattern C_userError_428 = UserError
pattern C_runtimeTypeError_430 = RuntimeTypeError
check_gasError_426 :: T_RuntimeError_424
check_gasError_426 = GasError
check_userError_428 :: T_RuntimeError_424
check_userError_428 = UserError
check_runtimeTypeError_430 :: T_RuntimeError_424
check_runtimeTypeError_430 = RuntimeTypeError
cover_RuntimeError_424 :: RuntimeError -> ()
cover_RuntimeError_424 x
  = case x of
      GasError -> ()
      UserError -> ()
      RuntimeTypeError -> ()
-- Utils.ByteString
type T_ByteString_432 = BS.ByteString
d_ByteString_432
  = error
      "MAlonzo Runtime Error: postulate evaluated: Utils.ByteString"
-- Utils.mkByteString
d_mkByteString_434
  = error
      "MAlonzo Runtime Error: postulate evaluated: Utils.mkByteString"
-- Utils.eqByteString
d_eqByteString_436 :: T_ByteString_432 -> T_ByteString_432 -> Bool
d_eqByteString_436 = (==)
-- Utils._×_
d__'215'__442 a0 a1 = ()
type T__'215'__442 a0 a1 = Pair a0 a1
pattern C__'44'__456 a0 a1 = (,) a0 a1
check__'44'__456 ::
  forall xA. forall xB. xA -> xB -> T__'215'__442 xA xB
check__'44'__456 = (,)
cover__'215'__442 :: Pair a1 a2 -> ()
cover__'215'__442 x
  = case x of
      (,) _ _ -> ()
-- Utils._×_.proj₁
d_proj'8321'_452 :: T__'215'__442 AgdaAny AgdaAny -> AgdaAny
d_proj'8321'_452 v0
  = case coe v0 of
      C__'44'__456 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Utils._×_.proj₂
d_proj'8322'_454 :: T__'215'__442 AgdaAny AgdaAny -> AgdaAny
d_proj'8322'_454 v0
  = case coe v0 of
      C__'44'__456 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Utils.List
d_List_460 a0 = ()
type T_List_460 a0 = [] a0
pattern C_'91''93'_464 = []
pattern C__'8759'__466 a0 a1 = (:) a0 a1
check_'91''93'_464 :: forall xA. T_List_460 xA
check_'91''93'_464 = []
check__'8759'__466 ::
  forall xA. xA -> T_List_460 xA -> T_List_460 xA
check__'8759'__466 = (:)
cover_List_460 :: [] a1 -> ()
cover_List_460 x
  = case x of
      [] -> ()
      (:) _ _ -> ()
-- Utils.All
d_All_474 a0 a1 a2 a3 = ()
data T_All_474 = C_'91''93'_482 | C__'8759'__492 AgdaAny T_All_474
-- Utils.length
d_length_496 :: () -> T_List_460 AgdaAny -> Integer
d_length_496 ~v0 v1 = du_length_496 v1
du_length_496 :: T_List_460 AgdaAny -> Integer
du_length_496 v0
  = case coe v0 of
      C_'91''93'_464 -> coe (0 :: Integer)
      C__'8759'__466 v1 v2
        -> coe addInt (coe (1 :: Integer)) (coe du_length_496 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Utils.map
d_map_506 ::
  () ->
  () ->
  (AgdaAny -> AgdaAny) -> T_List_460 AgdaAny -> T_List_460 AgdaAny
d_map_506 ~v0 ~v1 v2 v3 = du_map_506 v2 v3
du_map_506 ::
  (AgdaAny -> AgdaAny) -> T_List_460 AgdaAny -> T_List_460 AgdaAny
du_map_506 v0 v1
  = case coe v1 of
      C_'91''93'_464 -> coe v1
      C__'8759'__466 v2 v3
        -> coe
             C__'8759'__466 (coe v0 v2) (coe du_map_506 (coe v0) (coe v3))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Utils.toList
d_toList_518 :: () -> T_List_460 AgdaAny -> [AgdaAny]
d_toList_518 ~v0 v1 = du_toList_518 v1
du_toList_518 :: T_List_460 AgdaAny -> [AgdaAny]
du_toList_518 v0
  = case coe v0 of
      C_'91''93'_464 -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      C__'8759'__466 v1 v2
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v1)
             (coe du_toList_518 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Utils.fromList
d_fromList_526 :: () -> [AgdaAny] -> T_List_460 AgdaAny
d_fromList_526 ~v0 v1 = du_fromList_526 v1
du_fromList_526 :: [AgdaAny] -> T_List_460 AgdaAny
du_fromList_526 v0
  = case coe v0 of
      [] -> coe C_'91''93'_464
      (:) v1 v2
        -> coe C__'8759'__466 (coe v1) (coe du_fromList_526 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Utils.dropLIST
d_dropLIST_534 ::
  () -> Integer -> T_List_460 AgdaAny -> T_List_460 AgdaAny
d_dropLIST_534 ~v0 v1 v2 = du_dropLIST_534 v1 v2
du_dropLIST_534 ::
  Integer -> T_List_460 AgdaAny -> T_List_460 AgdaAny
du_dropLIST_534 v0 v1
  = case coe v0 of
      _ | coe geqInt (coe v0) (coe (0 :: Integer)) ->
          coe du_drop_546 (coe v0) (coe v1)
      _ -> coe v1
-- Utils._.drop
d_drop_546 ::
  () ->
  Integer ->
  T_List_460 AgdaAny ->
  () -> Integer -> T_List_460 AgdaAny -> T_List_460 AgdaAny
d_drop_546 ~v0 ~v1 ~v2 ~v3 v4 v5 = du_drop_546 v4 v5
du_drop_546 :: Integer -> T_List_460 AgdaAny -> T_List_460 AgdaAny
du_drop_546 v0 v1
  = case coe v0 of
      0 -> coe v1
      _ -> let v2 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (case coe v1 of
                C_'91''93'_464 -> coe v1
                C__'8759'__466 v3 v4 -> coe du_drop_546 (coe v2) (coe v4)
                _ -> MAlonzo.RTE.mazUnreachableError)
-- Utils.map-cong
d_map'45'cong_570 ::
  () ->
  () ->
  [AgdaAny] ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_map'45'cong_570 = erased
-- Utils.sequence
d_sequence_586 ::
  () -> (() -> ()) -> T_Monad_260 -> T_List_460 AgdaAny -> AgdaAny
d_sequence_586 ~v0 ~v1 v2 v3 = du_sequence_586 v2 v3
du_sequence_586 :: T_Monad_260 -> T_List_460 AgdaAny -> AgdaAny
du_sequence_586 v0 v1
  = case coe v1 of
      C_'91''93'_464 -> coe d_return_276 v0 erased v1
      C__'8759'__466 v2 v3
        -> coe
             d__'62''62''61'__282 v0 erased erased v2
             (\ v4 ->
                coe
                  d__'62''62''61'__282 v0 erased erased
                  (coe du_sequence_586 (coe v0) (coe v3))
                  (\ v5 ->
                     coe d_return_276 v0 erased (coe C__'8759'__466 (coe v4) (coe v5))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Utils.mapM
d_mapM_604 ::
  () ->
  () ->
  (() -> ()) ->
  T_Monad_260 ->
  (AgdaAny -> AgdaAny) -> T_List_460 AgdaAny -> AgdaAny
d_mapM_604 ~v0 ~v1 ~v2 v3 v4 v5 = du_mapM_604 v3 v4 v5
du_mapM_604 ::
  T_Monad_260 ->
  (AgdaAny -> AgdaAny) -> T_List_460 AgdaAny -> AgdaAny
du_mapM_604 v0 v1 v2
  = coe du_sequence_586 (coe v0) (coe du_map_506 (coe v1) (coe v2))
-- Utils.Array
type T_Array_608 a0 = Strict.Vector a0
d_Array_608
  = error "MAlonzo Runtime Error: postulate evaluated: Utils.Array"
-- Utils.mkArray
d_mkArray_612
  = error "MAlonzo Runtime Error: postulate evaluated: Utils.mkArray"
-- Utils.DATA
d_DATA_614 = ()
type T_DATA_614 = Data
pattern C_ConstrDATA_616 a0 a1 = D.Constr a0 a1
pattern C_MapDATA_618 a0 = D.Map a0
pattern C_ListDATA_620 a0 = D.List a0
pattern C_iDATA_622 a0 = D.I a0
pattern C_bDATA_624 a0 = D.B a0
check_ConstrDATA_616 ::
  Integer -> T_List_460 T_DATA_614 -> T_DATA_614
check_ConstrDATA_616 = D.Constr
check_MapDATA_618 ::
  T_List_460 (T__'215'__442 T_DATA_614 T_DATA_614) -> T_DATA_614
check_MapDATA_618 = D.Map
check_ListDATA_620 :: T_List_460 T_DATA_614 -> T_DATA_614
check_ListDATA_620 = D.List
check_iDATA_622 :: Integer -> T_DATA_614
check_iDATA_622 = D.I
check_bDATA_624 :: T_ByteString_432 -> T_DATA_614
check_bDATA_624 = D.B
cover_DATA_614 :: Data -> ()
cover_DATA_614 x
  = case x of
      D.Constr _ _ -> ()
      D.Map _ -> ()
      D.List _ -> ()
      D.I _ -> ()
      D.B _ -> ()
-- Utils.eqDATA
d_eqDATA_626 :: T_DATA_614 -> T_DATA_614 -> Bool
d_eqDATA_626 = (==)
-- Utils.Bls12-381-G1-Element
type T_Bls12'45'381'45'G1'45'Element_760 = G1.Element
d_Bls12'45'381'45'G1'45'Element_760
  = error
      "MAlonzo Runtime Error: postulate evaluated: Utils.Bls12-381-G1-Element"
-- Utils.eqBls12-381-G1-Element
d_eqBls12'45'381'45'G1'45'Element_762 ::
  T_Bls12'45'381'45'G1'45'Element_760 ->
  T_Bls12'45'381'45'G1'45'Element_760 -> Bool
d_eqBls12'45'381'45'G1'45'Element_762 = (==)
-- Utils.Bls12-381-G2-Element
type T_Bls12'45'381'45'G2'45'Element_764 = G2.Element
d_Bls12'45'381'45'G2'45'Element_764
  = error
      "MAlonzo Runtime Error: postulate evaluated: Utils.Bls12-381-G2-Element"
-- Utils.eqBls12-381-G2-Element
d_eqBls12'45'381'45'G2'45'Element_766 ::
  T_Bls12'45'381'45'G2'45'Element_764 ->
  T_Bls12'45'381'45'G2'45'Element_764 -> Bool
d_eqBls12'45'381'45'G2'45'Element_766 = (==)
-- Utils.Bls12-381-MlResult
type T_Bls12'45'381'45'MlResult_768 = Pairing.MlResult
d_Bls12'45'381'45'MlResult_768
  = error
      "MAlonzo Runtime Error: postulate evaluated: Utils.Bls12-381-MlResult"
-- Utils.eqBls12-381-MlResult
d_eqBls12'45'381'45'MlResult_770 ::
  T_Bls12'45'381'45'MlResult_768 ->
  T_Bls12'45'381'45'MlResult_768 -> Bool
d_eqBls12'45'381'45'MlResult_770 = (==)
-- Utils.Value
type T_Value_772 = V.Value
d_Value_772
  = error "MAlonzo Runtime Error: postulate evaluated: Utils.Value"
-- Utils.eqValue
d_eqValue_774 :: T_Value_772 -> T_Value_772 -> Bool
d_eqValue_774 = (==)
-- Utils.valueFromList
d_valueFromList_776
  = error
      "MAlonzo Runtime Error: postulate evaluated: Utils.valueFromList"
-- Utils.Kind
d_Kind_778 = ()
type T_Kind_778 = KIND
pattern C_'42'_780 = Star
pattern C_'9839'_782 = Sharp
pattern C__'8658'__784 a0 a1 = Arrow a0 a1
check_'42'_780 :: T_Kind_778
check_'42'_780 = Star
check_'9839'_782 :: T_Kind_778
check_'9839'_782 = Sharp
check__'8658'__784 :: T_Kind_778 -> T_Kind_778 -> T_Kind_778
check__'8658'__784 = Arrow
cover_Kind_778 :: KIND -> ()
cover_Kind_778 x
  = case x of
      Star -> ()
      Sharp -> ()
      Arrow _ _ -> ()
-- Utils.TRACE
d_TRACE_794 ::
  () ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 -> AgdaAny -> AgdaAny
d_TRACE_794 ~v0 ~v1 v2 = du_TRACE_794 v2
du_TRACE_794 :: AgdaAny -> AgdaAny
du_TRACE_794 v0 = coe v0
