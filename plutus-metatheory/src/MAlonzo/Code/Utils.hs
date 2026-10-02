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
import qualified MAlonzo.Code.Data.Integer.Properties
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Data.Maybe.Base
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Data.Nat.Properties
import qualified MAlonzo.Code.Data.Sum.Base
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
data Byte = Byte Bool Bool Bool Bool Bool Bool Bool Bool

data ByteString = BSNil | BSCons Byte ByteString

toHS :: ByteString -> Haskell.ByteString
toHS = undefined

fromHS :: Haskell.ByteString -> ByteString
fromHS = undefined

actualHash :: Haskell.ByteString -> Haskell.ByteString
actualHash = undefined

hash :: ByteString -> ByteString
hash bs = fromHS (actualHash (toHS bs))
type Pair a b = (a , b)
data Data
  = Constr Integer
  | Map [(Data, Data)]
  | List [Data]
  | I Integer
  | B ByteString

dataToHSData :: Data -> Haskell.Data
dataToHSData = undefined

dataFromHSData :: Haskell.Data -> Data
dataFromHSData = undefined
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
-- Utils.ByteString
d_ByteString_446 = ()
type T_ByteString_446 = ByteString
pattern C_'91''93'_448 = BSNil
pattern C__'8759'__450 a0 a1 = BSCons a0 a1
check_'91''93'_448 :: T_ByteString_446
check_'91''93'_448 = BSNil
check__'8759'__450 ::
  T_Byte_426 -> T_ByteString_446 -> T_ByteString_446
check__'8759'__450 = BSCons
cover_ByteString_446 :: ByteString -> ()
cover_ByteString_446 x
  = case x of
      BSNil -> ()
      BSCons _ _ -> ()
-- Utils.mkByteString
d_mkByteString_452
  = error
      "MAlonzo Runtime Error: postulate evaluated: Utils.mkByteString"
-- Utils.eqByte
d_eqByte_454 :: T_Byte_426 -> T_Byte_426 -> Bool
d_eqByte_454 v0 v1
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
d_eqByteString_492 :: T_ByteString_446 -> T_ByteString_446 -> Bool
d_eqByteString_492 v0 v1
  = let v2 = coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8 in
    coe
      (case coe v0 of
         C_'91''93'_448
           -> case coe v1 of
                C_'91''93'_448 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_true_10
                _ -> coe v2
         C__'8759'__450 v3 v4
           -> case coe v1 of
                C__'8759'__450 v5 v6
                  -> coe
                       MAlonzo.Code.Data.Bool.Base.d__'8743'__24
                       (coe d_eqByte_454 (coe v3) (coe v5))
                       (coe d_eqByteString_492 (coe v4) (coe v6))
                _ -> coe v2
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Utils._×_
d__'215'__506 a0 a1 = ()
type T__'215'__506 a0 a1 = Pair a0 a1
pattern C__'44'__520 a0 a1 = (,) a0 a1
check__'44'__520 ::
  forall xA. forall xB. xA -> xB -> T__'215'__506 xA xB
check__'44'__520 = (,)
cover__'215'__506 :: Pair a1 a2 -> ()
cover__'215'__506 x
  = case x of
      (,) _ _ -> ()
-- Utils._×_.proj₁
d_proj'8321'_516 :: T__'215'__506 AgdaAny AgdaAny -> AgdaAny
d_proj'8321'_516 v0
  = case coe v0 of
      C__'44'__520 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Utils._×_.proj₂
d_proj'8322'_518 :: T__'215'__506 AgdaAny AgdaAny -> AgdaAny
d_proj'8322'_518 v0
  = case coe v0 of
      C__'44'__520 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Utils.List
d_List_524 a0 = ()
type T_List_524 a0 = [] a0
pattern C_'91''93'_528 = []
pattern C__'8759'__530 a0 a1 = (:) a0 a1
check_'91''93'_528 :: forall xA. T_List_524 xA
check_'91''93'_528 = []
check__'8759'__530 ::
  forall xA. xA -> T_List_524 xA -> T_List_524 xA
check__'8759'__530 = (:)
cover_List_524 :: [] a1 -> ()
cover_List_524 x
  = case x of
      [] -> ()
      (:) _ _ -> ()
-- Utils.All
d_All_538 a0 a1 a2 a3 = ()
data T_All_538 = C_'91''93'_546 | C__'8759'__556 AgdaAny T_All_538
-- Utils.length
d_length_560 :: () -> T_List_524 AgdaAny -> Integer
d_length_560 ~v0 v1 = du_length_560 v1
du_length_560 :: T_List_524 AgdaAny -> Integer
du_length_560 v0
  = case coe v0 of
      C_'91''93'_528 -> coe (0 :: Integer)
      C__'8759'__530 v1 v2
        -> coe addInt (coe (1 :: Integer)) (coe du_length_560 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Utils.map
d_map_570 ::
  () ->
  () ->
  (AgdaAny -> AgdaAny) -> T_List_524 AgdaAny -> T_List_524 AgdaAny
d_map_570 ~v0 ~v1 v2 v3 = du_map_570 v2 v3
du_map_570 ::
  (AgdaAny -> AgdaAny) -> T_List_524 AgdaAny -> T_List_524 AgdaAny
du_map_570 v0 v1
  = case coe v1 of
      C_'91''93'_528 -> coe v1
      C__'8759'__530 v2 v3
        -> coe
             C__'8759'__530 (coe v0 v2) (coe du_map_570 (coe v0) (coe v3))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Utils.toList
d_toList_582 :: () -> T_List_524 AgdaAny -> [AgdaAny]
d_toList_582 ~v0 v1 = du_toList_582 v1
du_toList_582 :: T_List_524 AgdaAny -> [AgdaAny]
du_toList_582 v0
  = case coe v0 of
      C_'91''93'_528 -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      C__'8759'__530 v1 v2
        -> coe
             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v1)
             (coe du_toList_582 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Utils.fromList
d_fromList_590 :: () -> [AgdaAny] -> T_List_524 AgdaAny
d_fromList_590 ~v0 v1 = du_fromList_590 v1
du_fromList_590 :: [AgdaAny] -> T_List_524 AgdaAny
du_fromList_590 v0
  = case coe v0 of
      [] -> coe C_'91''93'_528
      (:) v1 v2
        -> coe C__'8759'__530 (coe v1) (coe du_fromList_590 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Utils.dropLIST
d_dropLIST_598 ::
  () -> Integer -> T_List_524 AgdaAny -> T_List_524 AgdaAny
d_dropLIST_598 ~v0 v1 v2 = du_dropLIST_598 v1 v2
du_dropLIST_598 ::
  Integer -> T_List_524 AgdaAny -> T_List_524 AgdaAny
du_dropLIST_598 v0 v1
  = case coe v0 of
      _ | coe geqInt (coe v0) (coe (0 :: Integer)) ->
          coe du_drop_610 (coe v0) (coe v1)
      _ -> coe v1
-- Utils._.drop
d_drop_610 ::
  () ->
  Integer ->
  T_List_524 AgdaAny ->
  () -> Integer -> T_List_524 AgdaAny -> T_List_524 AgdaAny
d_drop_610 ~v0 ~v1 ~v2 ~v3 v4 v5 = du_drop_610 v4 v5
du_drop_610 :: Integer -> T_List_524 AgdaAny -> T_List_524 AgdaAny
du_drop_610 v0 v1
  = case coe v0 of
      0 -> coe v1
      _ -> let v2 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (case coe v1 of
                C_'91''93'_528 -> coe v1
                C__'8759'__530 v3 v4 -> coe du_drop_610 (coe v2) (coe v4)
                _ -> MAlonzo.RTE.mazUnreachableError)
-- Utils.map-cong
d_map'45'cong_634 ::
  () ->
  () ->
  [AgdaAny] ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_map'45'cong_634 = erased
-- Utils.sequence
d_sequence_650 ::
  () -> (() -> ()) -> T_Monad_254 -> T_List_524 AgdaAny -> AgdaAny
d_sequence_650 ~v0 ~v1 v2 v3 = du_sequence_650 v2 v3
du_sequence_650 :: T_Monad_254 -> T_List_524 AgdaAny -> AgdaAny
du_sequence_650 v0 v1
  = case coe v1 of
      C_'91''93'_528 -> coe d_return_270 v0 erased v1
      C__'8759'__530 v2 v3
        -> coe
             d__'62''62''61'__276 v0 erased erased v2
             (\ v4 ->
                coe
                  d__'62''62''61'__276 v0 erased erased
                  (coe du_sequence_650 (coe v0) (coe v3))
                  (\ v5 ->
                     coe d_return_270 v0 erased (coe C__'8759'__530 (coe v4) (coe v5))))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Utils.mapM
d_mapM_668 ::
  () ->
  () ->
  (() -> ()) ->
  T_Monad_254 ->
  (AgdaAny -> AgdaAny) -> T_List_524 AgdaAny -> AgdaAny
d_mapM_668 ~v0 ~v1 ~v2 v3 v4 v5 = du_mapM_668 v3 v4 v5
du_mapM_668 ::
  T_Monad_254 ->
  (AgdaAny -> AgdaAny) -> T_List_524 AgdaAny -> AgdaAny
du_mapM_668 v0 v1 v2
  = coe du_sequence_650 (coe v0) (coe du_map_570 (coe v1) (coe v2))
-- Utils.Array
type T_Array_672 a0 = Strict.Vector a0
d_Array_672
  = error "MAlonzo Runtime Error: postulate evaluated: Utils.Array"
-- Utils.HSlengthOfArray
d_HSlengthOfArray_676 :: forall xA. () -> T_Array_672 xA -> Integer
d_HSlengthOfArray_676 = \() -> \as -> toInteger (Strict.length as)
-- Utils.HSlistToArray
d_HSlistToArray_680 ::
  forall xA. () -> T_List_524 xA -> T_Array_672 xA
d_HSlistToArray_680 = \() -> Strict.fromList
-- Utils.HSindexArray
d_HSindexArray_682 ::
  forall xA. () -> T_Array_672 xA -> Integer -> xA
d_HSindexArray_682
  = \() -> \as -> \i -> as Strict.! (fromInteger i)
-- Utils.mkArray
d_mkArray_686
  = error "MAlonzo Runtime Error: postulate evaluated: Utils.mkArray"
-- Utils.DATA
d_DATA_688 = ()
type T_DATA_688 = Data
pattern C_ConstrDATA_690 a0 a1 = Constr a0 a1
pattern C_MapDATA_692 a0 = Map a0
pattern C_ListDATA_694 a0 = List a0
pattern C_iDATA_696 a0 = I a0
pattern C_bDATA_698 a0 = B a0
check_ConstrDATA_690 ::
  Integer -> T_List_524 T_DATA_688 -> T_DATA_688
check_ConstrDATA_690 = Constr
check_MapDATA_692 ::
  T_List_524 (T__'215'__506 T_DATA_688 T_DATA_688) -> T_DATA_688
check_MapDATA_692 = Map
check_ListDATA_694 :: T_List_524 T_DATA_688 -> T_DATA_688
check_ListDATA_694 = List
check_iDATA_696 :: Integer -> T_DATA_688
check_iDATA_696 = I
check_bDATA_698 :: T_ByteString_446 -> T_DATA_688
check_bDATA_698 = B
cover_DATA_688 :: Data -> ()
cover_DATA_688 x
  = case x of
      Constr _ _ -> ()
      Map _ -> ()
      List _ -> ()
      I _ -> ()
      B _ -> ()
-- Utils.eqDATA
d_eqDATA_700 :: T_DATA_688 -> T_DATA_688 -> Bool
d_eqDATA_700 v0 v1
  = case coe v0 of
      C_ConstrDATA_690 v2 v3
        -> case coe v1 of
             C_ConstrDATA_690 v4 v5
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
                          MAlonzo.Code.Data.List.Base.du_zipWith_104 (coe d_eqDATA_700)
                          (coe du_toList_582 (coe v3)) (coe du_toList_582 (coe v5))))
             C_MapDATA_692 v4 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             C_ListDATA_694 v4 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             C_iDATA_696 v4 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             C_bDATA_698 v4 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             _ -> MAlonzo.RTE.mazUnreachableError
      C_MapDATA_692 v2
        -> case coe v1 of
             C_ConstrDATA_690 v3 v4
               -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             C_MapDATA_692 v3
               -> coe
                    MAlonzo.Code.Data.Bool.ListAction.d_and_10
                    (coe
                       MAlonzo.Code.Data.List.Base.du_zipWith_104
                       (coe
                          (\ v4 v5 ->
                             MAlonzo.Code.Data.Bool.Base.d__'8743'__24
                               (coe
                                  d_eqDATA_700 (coe d_proj'8321'_516 (coe v4))
                                  (coe d_proj'8321'_516 (coe v5)))
                               (coe
                                  d_eqDATA_700 (coe d_proj'8322'_518 (coe v4))
                                  (coe d_proj'8322'_518 (coe v5)))))
                       (coe du_toList_582 (coe v2)) (coe du_toList_582 (coe v3)))
             C_ListDATA_694 v3 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             C_iDATA_696 v3 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             C_bDATA_698 v3 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             _ -> MAlonzo.RTE.mazUnreachableError
      C_ListDATA_694 v2
        -> case coe v1 of
             C_ConstrDATA_690 v3 v4
               -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             C_MapDATA_692 v3 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             C_ListDATA_694 v3
               -> coe
                    MAlonzo.Code.Data.Bool.ListAction.d_and_10
                    (coe
                       MAlonzo.Code.Data.List.Base.du_zipWith_104 (coe d_eqDATA_700)
                       (coe du_toList_582 (coe v2)) (coe du_toList_582 (coe v3)))
             C_iDATA_696 v3 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             C_bDATA_698 v3 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             _ -> MAlonzo.RTE.mazUnreachableError
      C_iDATA_696 v2
        -> case coe v1 of
             C_ConstrDATA_690 v3 v4
               -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             C_MapDATA_692 v3 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             C_ListDATA_694 v3 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             C_iDATA_696 v3
               -> coe
                    MAlonzo.Code.Relation.Nullary.Decidable.Core.du_isYes_132
                    (coe
                       MAlonzo.Code.Data.Integer.Properties.d__'8799'__2800 (coe v2)
                       (coe v3))
             C_bDATA_698 v3 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             _ -> MAlonzo.RTE.mazUnreachableError
      C_bDATA_698 v2
        -> case coe v1 of
             C_ConstrDATA_690 v3 v4
               -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             C_MapDATA_692 v3 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             C_ListDATA_694 v3 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             C_iDATA_696 v3 -> coe MAlonzo.Code.Agda.Builtin.Bool.C_false_8
             C_bDATA_698 v3 -> coe d_eqByteString_492 (coe v2) (coe v3)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Utils.Bls12-381-G1-Element
type T_Bls12'45'381'45'G1'45'Element_834 = G1.Element
d_Bls12'45'381'45'G1'45'Element_834
  = error
      "MAlonzo Runtime Error: postulate evaluated: Utils.Bls12-381-G1-Element"
-- Utils.eqBls12-381-G1-Element
d_eqBls12'45'381'45'G1'45'Element_836 ::
  T_Bls12'45'381'45'G1'45'Element_834 ->
  T_Bls12'45'381'45'G1'45'Element_834 -> Bool
d_eqBls12'45'381'45'G1'45'Element_836 = (==)
-- Utils.Bls12-381-G2-Element
type T_Bls12'45'381'45'G2'45'Element_838 = G2.Element
d_Bls12'45'381'45'G2'45'Element_838
  = error
      "MAlonzo Runtime Error: postulate evaluated: Utils.Bls12-381-G2-Element"
-- Utils.eqBls12-381-G2-Element
d_eqBls12'45'381'45'G2'45'Element_840 ::
  T_Bls12'45'381'45'G2'45'Element_838 ->
  T_Bls12'45'381'45'G2'45'Element_838 -> Bool
d_eqBls12'45'381'45'G2'45'Element_840 = (==)
-- Utils.Bls12-381-MlResult
type T_Bls12'45'381'45'MlResult_842 = Pairing.MlResult
d_Bls12'45'381'45'MlResult_842
  = error
      "MAlonzo Runtime Error: postulate evaluated: Utils.Bls12-381-MlResult"
-- Utils.eqBls12-381-MlResult
d_eqBls12'45'381'45'MlResult_844 ::
  T_Bls12'45'381'45'MlResult_842 ->
  T_Bls12'45'381'45'MlResult_842 -> Bool
d_eqBls12'45'381'45'MlResult_844 = (==)
-- Utils.Value
type T_Value_846 = V.Value
d_Value_846
  = error "MAlonzo Runtime Error: postulate evaluated: Utils.Value"
-- Utils.eqValue
d_eqValue_848 :: T_Value_846 -> T_Value_846 -> Bool
d_eqValue_848 = (==)
-- Utils.valueFromList
d_valueFromList_850
  = error
      "MAlonzo Runtime Error: postulate evaluated: Utils.valueFromList"
-- Utils.Kind
d_Kind_852 = ()
type T_Kind_852 = KIND
pattern C_'42'_854 = Star
pattern C_'9839'_856 = Sharp
pattern C__'8658'__858 a0 a1 = Arrow a0 a1
check_'42'_854 :: T_Kind_852
check_'42'_854 = Star
check_'9839'_856 :: T_Kind_852
check_'9839'_856 = Sharp
check__'8658'__858 :: T_Kind_852 -> T_Kind_852 -> T_Kind_852
check__'8658'__858 = Arrow
cover_Kind_852 :: KIND -> ()
cover_Kind_852 x
  = case x of
      Star -> ()
      Sharp -> ()
      Arrow _ _ -> ()
-- Utils.TRACE
d_TRACE_868 ::
  () ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 -> AgdaAny -> AgdaAny
d_TRACE_868 ~v0 ~v1 v2 = du_TRACE_868 v2
du_TRACE_868 :: AgdaAny -> AgdaAny
du_TRACE_868 v0 = coe v0
