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

module MAlonzo.Code.Type where

import Data.Text qualified
import MAlonzo.Code.Builtin.Constant.Type qualified
import MAlonzo.Code.Data.Vec.Base qualified
import MAlonzo.Code.Utils qualified
import MAlonzo.RTE (AgdaAny, add64, addInt, coe, eq64, eqInt, erased, geqInt, lt64, ltInt, mul64,
                    mulInt, quot64, quotInt, rem64, remInt, sub64, subInt, word64FromNat,
                    word64ToNat)
import MAlonzo.RTE qualified

-- Type.Ctx⋆
d_Ctx'8902'_2 = ()
data T_Ctx'8902'_2
  = C_'8709'_4 |
    C__'44''8902'__6 T_Ctx'8902'_2 MAlonzo.Code.Utils.T_Kind_636
-- Type._∋⋆_
d__'8715''8902'__14 a0 a1 = ()
data T__'8715''8902'__14 = C_Z_16 | C_S_18 T__'8715''8902'__14
-- Type._⊢⋆_
d__'8866''8902'__20 a0 a1 = ()
data T__'8866''8902'__20
  = C_'96'_22 T__'8715''8902'__14 |
    C_Π_24 MAlonzo.Code.Utils.T_Kind_636 T__'8866''8902'__20 |
    C__'8658'__26 T__'8866''8902'__20 T__'8866''8902'__20 |
    C_ƛ_28 T__'8866''8902'__20 |
    C__'183'__30 MAlonzo.Code.Utils.T_Kind_636 T__'8866''8902'__20
                 T__'8866''8902'__20 |
    C_μ_32 MAlonzo.Code.Utils.T_Kind_636 T__'8866''8902'__20
           T__'8866''8902'__20 |
    C_'94'_34 MAlonzo.Code.Builtin.Constant.Type.T_TyCon_6 |
    C_con_36 T__'8866''8902'__20 |
    C_SOP_40 Integer MAlonzo.Code.Data.Vec.Base.T_Vec_28
