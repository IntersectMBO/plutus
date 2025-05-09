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

module MAlonzo.Code.Data.Tree.AVL.Height where

import Data.Text qualified
import MAlonzo.Code.Data.Fin.Base qualified
import MAlonzo.RTE (AgdaAny, add64, addInt, coe, eq64, eqInt, erased, geqInt, lt64, ltInt, mul64,
                    mulInt, quot64, quotInt, rem64, remInt, sub64, subInt, word64FromNat,
                    word64ToNat)
import MAlonzo.RTE qualified

-- Data.Tree.AVL.Height.ℕ₂
d_ℕ'8322'_8 :: ()
d_ℕ'8322'_8 = erased
-- Data.Tree.AVL.Height._⊕_
d__'8853'__16 ::
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> Integer -> Integer
d__'8853'__16 v0 v1
  = case coe v0 of
      MAlonzo.Code.Data.Fin.Base.C_zero_12 -> coe v1
      MAlonzo.Code.Data.Fin.Base.C_suc_16 v3
        -> coe addInt (coe (1 :: Integer)) (coe v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Data.Tree.AVL.Height.pred[_⊕_]
d_pred'91'_'8853'_'93'_22 ::
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> Integer -> Integer
d_pred'91'_'8853'_'93'_22 v0 v1
  = case coe v1 of
      0 -> coe (0 :: Integer)
      _ -> let v2 = subInt (coe v1) (coe (1 :: Integer)) in
           coe (coe d__'8853'__16 (coe v0) (coe v2))
-- Data.Tree.AVL.Height._∼_⊔_
d__'8764'_'8852'__30 a0 a1 a2 = ()
data T__'8764'_'8852'__30
  = C_'8764''43'_34 | C_'8764'0_38 | C_'8764''45'_42
-- Data.Tree.AVL.Height.max∼
d_max'8764'_50 ::
  Integer ->
  Integer -> Integer -> T__'8764'_'8852'__30 -> T__'8764'_'8852'__30
d_max'8764'_50 ~v0 ~v1 ~v2 v3 = du_max'8764'_50 v3
du_max'8764'_50 :: T__'8764'_'8852'__30 -> T__'8764'_'8852'__30
du_max'8764'_50 v0
  = case coe v0 of
      C_'8764''43'_34 -> coe C_'8764''45'_42
      C_'8764'0_38    -> coe C_'8764'0_38
      C_'8764''45'_42 -> coe C_'8764'0_38
      _               -> MAlonzo.RTE.mazUnreachableError
-- Data.Tree.AVL.Height.∼max
d_'8764'max_58 ::
  Integer ->
  Integer -> Integer -> T__'8764'_'8852'__30 -> T__'8764'_'8852'__30
d_'8764'max_58 ~v0 ~v1 ~v2 v3 = du_'8764'max_58 v3
du_'8764'max_58 :: T__'8764'_'8852'__30 -> T__'8764'_'8852'__30
du_'8764'max_58 v0
  = case coe v0 of
      C_'8764''43'_34 -> coe C_'8764'0_38
      C_'8764'0_38    -> coe C_'8764'0_38
      C_'8764''45'_42 -> coe C_'8764''43'_34
      _               -> MAlonzo.RTE.mazUnreachableError
