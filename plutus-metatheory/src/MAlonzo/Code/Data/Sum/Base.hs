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

module MAlonzo.Code.Data.Sum.Base where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Function.Base

-- Data.Sum.Base._⊎_
d__'8846'__30 a0 a1 a2 a3 = ()
data T__'8846'__30
  = C_inj'8321'_38 AgdaAny | C_inj'8322'_42 AgdaAny
-- Data.Sum.Base.[_,_]
d_'91'_'44'_'93'_52 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (T__'8846'__30 -> ()) ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) -> T__'8846'__30 -> AgdaAny
d_'91'_'44'_'93'_52 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 v8
  = du_'91'_'44'_'93'_52 v6 v7 v8
du_'91'_'44'_'93'_52 ::
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) -> T__'8846'__30 -> AgdaAny
du_'91'_'44'_'93'_52 v0 v1 v2
  = case coe v2 of
      C_inj'8321'_38 v3 -> coe v0 v3
      C_inj'8322'_42 v3 -> coe v1 v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Sum.Base.[_,_]′
d_'91'_'44'_'93''8242'_66 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) -> T__'8846'__30 -> AgdaAny
d_'91'_'44'_'93''8242'_66 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5
  = du_'91'_'44'_'93''8242'_66
du_'91'_'44'_'93''8242'_66 ::
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) -> T__'8846'__30 -> AgdaAny
du_'91'_'44'_'93''8242'_66 = coe du_'91'_'44'_'93'_52
-- Data.Sum.Base.fromInj₁
d_fromInj'8321'_68 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> (AgdaAny -> AgdaAny) -> T__'8846'__30 -> AgdaAny
d_fromInj'8321'_68 ~v0 ~v1 ~v2 ~v3 = du_fromInj'8321'_68
du_fromInj'8321'_68 ::
  (AgdaAny -> AgdaAny) -> T__'8846'__30 -> AgdaAny
du_fromInj'8321'_68 = coe du_'91'_'44'_'93''8242'_66 (\ v0 -> v0)
-- Data.Sum.Base.fromInj₂
d_fromInj'8322'_72 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> (AgdaAny -> AgdaAny) -> T__'8846'__30 -> AgdaAny
d_fromInj'8322'_72 ~v0 ~v1 ~v2 ~v3 v4 = du_fromInj'8322'_72 v4
du_fromInj'8322'_72 ::
  (AgdaAny -> AgdaAny) -> T__'8846'__30 -> AgdaAny
du_fromInj'8322'_72 v0
  = coe du_'91'_'44'_'93''8242'_66 v0 (\ v1 -> v1)
-- Data.Sum.Base.reduce
d_reduce_76 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> T__'8846'__30 -> AgdaAny
d_reduce_76 ~v0 ~v1 = du_reduce_76
du_reduce_76 :: T__'8846'__30 -> AgdaAny
du_reduce_76
  = coe du_'91'_'44'_'93''8242'_66 (\ v0 -> v0) (\ v0 -> v0)
-- Data.Sum.Base.swap
d_swap_78 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> T__'8846'__30 -> T__'8846'__30
d_swap_78 ~v0 ~v1 ~v2 ~v3 v4 = du_swap_78 v4
du_swap_78 :: T__'8846'__30 -> T__'8846'__30
du_swap_78 v0
  = case coe v0 of
      C_inj'8321'_38 v1 -> coe C_inj'8322'_42 (coe v1)
      C_inj'8322'_42 v1 -> coe C_inj'8321'_38 (coe v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Sum.Base.map
d_map_84 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) -> T__'8846'__30 -> T__'8846'__30
d_map_84 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 v9 = du_map_84 v8 v9
du_map_84 ::
  (AgdaAny -> AgdaAny) ->
  (AgdaAny -> AgdaAny) -> T__'8846'__30 -> T__'8846'__30
du_map_84 v0 v1
  = coe
      du_'91'_'44'_'93''8242'_66 (\ v2 -> coe C_inj'8321'_38 (coe v0 v2))
      (\ v2 -> coe C_inj'8322'_42 (coe v1 v2))
-- Data.Sum.Base.map₁
d_map'8321'_90 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> (AgdaAny -> AgdaAny) -> T__'8846'__30 -> T__'8846'__30
d_map'8321'_90 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 = du_map'8321'_90 v6
du_map'8321'_90 ::
  (AgdaAny -> AgdaAny) -> T__'8846'__30 -> T__'8846'__30
du_map'8321'_90 v0 = coe du_map_84 (coe v0) (coe (\ v1 -> v1))
-- Data.Sum.Base.map₂
d_map'8322'_94 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> (AgdaAny -> AgdaAny) -> T__'8846'__30 -> T__'8846'__30
d_map'8322'_94 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 = du_map'8322'_94
du_map'8322'_94 ::
  (AgdaAny -> AgdaAny) -> T__'8846'__30 -> T__'8846'__30
du_map'8322'_94 = coe du_map_84 (coe (\ v0 -> v0))
-- Data.Sum.Base.assocʳ
d_assoc'691'_96 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> T__'8846'__30 -> T__'8846'__30
d_assoc'691'_96 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 = du_assoc'691'_96
du_assoc'691'_96 :: T__'8846'__30 -> T__'8846'__30
du_assoc'691'_96
  = coe
      du_'91'_'44'_'93''8242'_66
      (coe du_map'8322'_94 (coe C_inj'8321'_38))
      (coe
         MAlonzo.Code.Function.Base.du__'8728''8242'__216
         (coe C_inj'8322'_42) (coe C_inj'8322'_42))
-- Data.Sum.Base.assocˡ
d_assoc'737'_98 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () -> T__'8846'__30 -> T__'8846'__30
d_assoc'737'_98 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 = du_assoc'737'_98
du_assoc'737'_98 :: T__'8846'__30 -> T__'8846'__30
du_assoc'737'_98
  = coe
      du_'91'_'44'_'93''8242'_66
      (coe
         MAlonzo.Code.Function.Base.du__'8728''8242'__216
         (coe C_inj'8321'_38) (coe C_inj'8321'_38))
      (coe du_map'8321'_90 (coe C_inj'8322'_42))
-- Data.Sum.Base._-⊎-_
d__'45''8846''45'__100 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  (AgdaAny -> AgdaAny -> ()) ->
  (AgdaAny -> AgdaAny -> ()) -> AgdaAny -> AgdaAny -> ()
d__'45''8846''45'__100 = erased
