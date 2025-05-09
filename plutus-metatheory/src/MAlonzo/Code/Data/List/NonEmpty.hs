{-# LANGUAGE BangPatterns              #-}
{-# LANGUAGE EmptyCase                 #-}
{-# LANGUAGE EmptyDataDecls            #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE OverloadedStrings         #-}
{-# LANGUAGE PatternSynonyms           #-}
{-# LANGUAGE RankNTypes                #-}
{-# LANGUAGE ScopedTypeVariables       #-}

{-# OPTIONS_GHC -Wno-overlapping-patterns #-}

module MAlonzo.Code.Data.List.NonEmpty where

import Data.Text qualified
import MAlonzo.Code.Agda.Primitive qualified
import MAlonzo.Code.Data.List.NonEmpty.Base qualified
import MAlonzo.RTE (AgdaAny, add64, addInt, coe, eq64, eqInt, erased, geqInt, lt64, ltInt, mul64,
                    mulInt, quot64, quotInt, rem64, remInt, sub64, subInt, word64FromNat,
                    word64ToNat)
import MAlonzo.RTE qualified

-- Data.List.NonEmpty._∷ʳ'_
d__'8759''691'''__14 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  [AgdaAny] ->
  AgdaAny -> MAlonzo.Code.Data.List.NonEmpty.Base.T_SnocView_304
d__'8759''691'''__14 ~v0 ~v1 = du__'8759''691'''__14
du__'8759''691'''__14 ::
  [AgdaAny] ->
  AgdaAny -> MAlonzo.Code.Data.List.NonEmpty.Base.T_SnocView_304
du__'8759''691'''__14
  = coe
      MAlonzo.Code.Data.List.NonEmpty.Base.C__'8759''691''8242'__312
