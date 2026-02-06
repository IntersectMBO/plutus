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

module MAlonzo.Code.Type where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Builtin.Constant.Type
import qualified MAlonzo.Code.Data.Vec.Base
import qualified MAlonzo.Code.Utils

-- Type.Ctx⋆
d_Ctx'8902'_2 = ()
data T_Ctx'8902'_2
  = C_'8709'_4 |
    C__'44''8902'__6 T_Ctx'8902'_2 MAlonzo.Code.Utils.T_Kind_754
-- Type._∋⋆_
d__'8715''8902'__14 a0 a1 = ()
data T__'8715''8902'__14 = C_Z_16 | C_S_18 T__'8715''8902'__14
-- Type._⊢⋆_
d__'8866''8902'__20 a0 a1 = ()
data T__'8866''8902'__20
  = C_'96'_22 T__'8715''8902'__14 |
    C_Π_24 MAlonzo.Code.Utils.T_Kind_754 T__'8866''8902'__20 |
    C__'8658'__26 T__'8866''8902'__20 T__'8866''8902'__20 |
    C_ƛ_28 T__'8866''8902'__20 |
    C__'183'__30 MAlonzo.Code.Utils.T_Kind_754 T__'8866''8902'__20
                 T__'8866''8902'__20 |
    C_μ_32 MAlonzo.Code.Utils.T_Kind_754 T__'8866''8902'__20
           T__'8866''8902'__20 |
    C_'94'_34 MAlonzo.Code.Builtin.Constant.Type.T_TyCon_6 |
    C_con_36 T__'8866''8902'__20 |
    C_SOP_40 Integer MAlonzo.Code.Data.Vec.Base.T_Vec_28
