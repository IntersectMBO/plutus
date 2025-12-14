{-# LANGUAGE NumericUnderscores #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE NoImplicitPrelude #-}

module PlutusBenchmark.SHA512 (sha512) where

import GHC.ByteOrder (ByteOrder (BigEndian))
import PlutusTx.Prelude

-- Based on https://datatracker.ietf.org/doc/html/rfc6234
sha512 :: BuiltinByteString -> BuiltinByteString
sha512 = extract . runSha initialState processBlock . pad
{-# INLINEABLE sha512 #-}

-- Helpers

newtype UInt64 = UInt64 BuiltinByteString

uint64ToBS :: UInt64 -> BuiltinByteString
uint64ToBS (UInt64 x) = x
{-# INLINEABLE uint64ToBS #-}

uint64ToInteger :: UInt64 -> Integer
uint64ToInteger (UInt64 x) = byteStringToInteger BigEndian x
{-# INLINEABLE uint64ToInteger #-}

integerToUInt64 :: Integer -> UInt64
integerToUInt64 = UInt64 . integerToByteString BigEndian 8
{-# INLINEABLE integerToUInt64 #-}

rot :: Integer -> UInt64 -> UInt64
rot rotation (UInt64 x) = UInt64 . flip rotateByteString rotation $ x
{-# INLINEABLE rot #-}

xor :: UInt64 -> UInt64 -> UInt64
xor (UInt64 x) (UInt64 y) = UInt64 (xorByteString True x y)
{-# INLINEABLE xor #-}

shiftU :: Integer -> UInt64 -> UInt64
shiftU shift (UInt64 x) = UInt64 . flip shiftByteString shift $ x
{-# INLINEABLE shiftU #-}

lsig512_0 :: UInt64 -> UInt64
lsig512_0 x = rot (-1) x `xor` rot (-8) x `xor` shiftU (-7) x
{-# INLINEABLE lsig512_0 #-}

lsig512_1 :: UInt64 -> UInt64
lsig512_1 x = rot (-19) x `xor` rot (-61) x `xor` shiftU (-6) x
{-# INLINEABLE lsig512_1 #-}

(#+) :: UInt64 -> UInt64 -> UInt64
(#+) x y =
  let xI = uint64ToInteger x
      yI = uint64ToInteger y
      added = xI + yI
   in integerToUInt64
        . (\z -> if limit < added then (added - limit) - 1 else z)
        $ added
  where
    limit :: Integer
    limit = 18_446_744_073_709_551_615
{-# INLINEABLE (#+) #-}

complementU :: UInt64 -> UInt64
complementU (UInt64 bs) = UInt64 $ complementByteString bs
{-# INLINEABLE complementU #-}

infixl 6 #+

(.&.) :: UInt64 -> UInt64 -> UInt64
(UInt64 x) .&. (UInt64 y) = UInt64 (andByteString True x y)
{-# INLINEABLE (.&.) #-}

infixl 7 .&.

(.|.) :: UInt64 -> UInt64 -> UInt64
(UInt64 x) .|. (UInt64 y) = UInt64 (orByteString True x y)
{-# INLINEABLE (.|.) #-}

infixl 5 .|.

data SHA512State
  = SHA512State
      UInt64
      UInt64
      UInt64
      UInt64
      UInt64
      UInt64
      UInt64
      UInt64

initialState :: SHA512State
initialState =
  SHA512State
    (integerToUInt64 0x6a09_e667_f3bc_c908)
    (integerToUInt64 0xbb67_ae85_84ca_a73b)
    (integerToUInt64 0x3c6e_f372_fe94_f82b)
    (integerToUInt64 0xa54f_f53a_5f1d_36f1)
    (integerToUInt64 0x510e_527f_ade6_82d1)
    (integerToUInt64 0x9b05_688c_2b3e_6c1f)
    (integerToUInt64 0x1f83_d9ab_fb41_bd6b)
    (integerToUInt64 0x5be0_cd19_137e_2179)
{-# INLINEABLE initialState #-}

extract :: SHA512State -> BuiltinByteString
extract (SHA512State x1 x2 x3 x4 x5 x6 x7 x8) =
  uint64ToBS x1
    <> uint64ToBS x2
    <> uint64ToBS x3
    <> uint64ToBS x4
    <> uint64ToBS x5
    <> uint64ToBS x6
    <> uint64ToBS x7
    <> uint64ToBS x8
{-# INLINEABLE extract #-}

data SHA512Sched
  = SHA512Sched
      UInt64
      UInt64
      UInt64
      UInt64
      UInt64 --  0- 4
      UInt64
      UInt64
      UInt64
      UInt64
      UInt64 --  5- 9
      UInt64
      UInt64
      UInt64
      UInt64
      UInt64 -- 10-14
      UInt64
      UInt64
      UInt64
      UInt64
      UInt64 -- 15-19
      UInt64
      UInt64
      UInt64
      UInt64
      UInt64 -- 20-24
      UInt64
      UInt64
      UInt64
      UInt64
      UInt64 -- 25-29
      UInt64
      UInt64
      UInt64
      UInt64
      UInt64 -- 30-34
      UInt64
      UInt64
      UInt64
      UInt64
      UInt64 -- 35-39
      UInt64
      UInt64
      UInt64
      UInt64
      UInt64 -- 40-44
      UInt64
      UInt64
      UInt64
      UInt64
      UInt64 -- 45-49
      UInt64
      UInt64
      UInt64
      UInt64
      UInt64 -- 50-54
      UInt64
      UInt64
      UInt64
      UInt64
      UInt64 -- 55-59
      UInt64
      UInt64
      UInt64
      UInt64
      UInt64 -- 60-64
      UInt64
      UInt64
      UInt64
      UInt64
      UInt64 -- 65-69
      UInt64
      UInt64
      UInt64
      UInt64
      UInt64 -- 70-74
      UInt64
      UInt64
      UInt64
      UInt64
      UInt64 -- 75-79

getSHA512Sched :: BuiltinByteString -> (SHA512Sched, BuiltinByteString)
getSHA512Sched bs =
  let (w00, rest00) = next64 bs
      (w01, rest01) = next64 rest00
      (w02, rest02) = next64 rest01
      (w03, rest03) = next64 rest02
      (w04, rest04) = next64 rest03
      (w05, rest05) = next64 rest04
      (w06, rest06) = next64 rest05
      (w07, rest07) = next64 rest06
      (w08, rest08) = next64 rest07
      (w09, rest09) = next64 rest08
      (w10, rest10) = next64 rest09
      (w11, rest11) = next64 rest10
      (w12, rest12) = next64 rest11
      (w13, rest13) = next64 rest12
      (w14, rest14) = next64 rest13
      (w15, cont) = next64 rest14
      w16 = lsig512_1 w14 #+ w09 #+ lsig512_0 w01 #+ w00
      w17 = lsig512_1 w15 #+ w10 #+ lsig512_0 w02 #+ w01
      w18 = lsig512_1 w16 #+ w11 #+ lsig512_0 w03 #+ w02
      w19 = lsig512_1 w17 #+ w12 #+ lsig512_0 w04 #+ w03
      w20 = lsig512_1 w18 #+ w13 #+ lsig512_0 w05 #+ w04
      w21 = lsig512_1 w19 #+ w14 #+ lsig512_0 w06 #+ w05
      w22 = lsig512_1 w20 #+ w15 #+ lsig512_0 w07 #+ w06
      w23 = lsig512_1 w21 #+ w16 #+ lsig512_0 w08 #+ w07
      w24 = lsig512_1 w22 #+ w17 #+ lsig512_0 w09 #+ w08
      w25 = lsig512_1 w23 #+ w18 #+ lsig512_0 w10 #+ w09
      w26 = lsig512_1 w24 #+ w19 #+ lsig512_0 w11 #+ w10
      w27 = lsig512_1 w25 #+ w20 #+ lsig512_0 w12 #+ w11
      w28 = lsig512_1 w26 #+ w21 #+ lsig512_0 w13 #+ w12
      w29 = lsig512_1 w27 #+ w22 #+ lsig512_0 w14 #+ w13
      w30 = lsig512_1 w28 #+ w23 #+ lsig512_0 w15 #+ w14
      w31 = lsig512_1 w29 #+ w24 #+ lsig512_0 w16 #+ w15
      w32 = lsig512_1 w30 #+ w25 #+ lsig512_0 w17 #+ w16
      w33 = lsig512_1 w31 #+ w26 #+ lsig512_0 w18 #+ w17
      w34 = lsig512_1 w32 #+ w27 #+ lsig512_0 w19 #+ w18
      w35 = lsig512_1 w33 #+ w28 #+ lsig512_0 w20 #+ w19
      w36 = lsig512_1 w34 #+ w29 #+ lsig512_0 w21 #+ w20
      w37 = lsig512_1 w35 #+ w30 #+ lsig512_0 w22 #+ w21
      w38 = lsig512_1 w36 #+ w31 #+ lsig512_0 w23 #+ w22
      w39 = lsig512_1 w37 #+ w32 #+ lsig512_0 w24 #+ w23
      w40 = lsig512_1 w38 #+ w33 #+ lsig512_0 w25 #+ w24
      w41 = lsig512_1 w39 #+ w34 #+ lsig512_0 w26 #+ w25
      w42 = lsig512_1 w40 #+ w35 #+ lsig512_0 w27 #+ w26
      w43 = lsig512_1 w41 #+ w36 #+ lsig512_0 w28 #+ w27
      w44 = lsig512_1 w42 #+ w37 #+ lsig512_0 w29 #+ w28
      w45 = lsig512_1 w43 #+ w38 #+ lsig512_0 w30 #+ w29
      w46 = lsig512_1 w44 #+ w39 #+ lsig512_0 w31 #+ w30
      w47 = lsig512_1 w45 #+ w40 #+ lsig512_0 w32 #+ w31
      w48 = lsig512_1 w46 #+ w41 #+ lsig512_0 w33 #+ w32
      w49 = lsig512_1 w47 #+ w42 #+ lsig512_0 w34 #+ w33
      w50 = lsig512_1 w48 #+ w43 #+ lsig512_0 w35 #+ w34
      w51 = lsig512_1 w49 #+ w44 #+ lsig512_0 w36 #+ w35
      w52 = lsig512_1 w50 #+ w45 #+ lsig512_0 w37 #+ w36
      w53 = lsig512_1 w51 #+ w46 #+ lsig512_0 w38 #+ w37
      w54 = lsig512_1 w52 #+ w47 #+ lsig512_0 w39 #+ w38
      w55 = lsig512_1 w53 #+ w48 #+ lsig512_0 w40 #+ w39
      w56 = lsig512_1 w54 #+ w49 #+ lsig512_0 w41 #+ w40
      w57 = lsig512_1 w55 #+ w50 #+ lsig512_0 w42 #+ w41
      w58 = lsig512_1 w56 #+ w51 #+ lsig512_0 w43 #+ w42
      w59 = lsig512_1 w57 #+ w52 #+ lsig512_0 w44 #+ w43
      w60 = lsig512_1 w58 #+ w53 #+ lsig512_0 w45 #+ w44
      w61 = lsig512_1 w59 #+ w54 #+ lsig512_0 w46 #+ w45
      w62 = lsig512_1 w60 #+ w55 #+ lsig512_0 w47 #+ w46
      w63 = lsig512_1 w61 #+ w56 #+ lsig512_0 w48 #+ w47
      w64 = lsig512_1 w62 #+ w57 #+ lsig512_0 w49 #+ w48
      w65 = lsig512_1 w63 #+ w58 #+ lsig512_0 w50 #+ w49
      w66 = lsig512_1 w64 #+ w59 #+ lsig512_0 w51 #+ w50
      w67 = lsig512_1 w65 #+ w60 #+ lsig512_0 w52 #+ w51
      w68 = lsig512_1 w66 #+ w61 #+ lsig512_0 w53 #+ w52
      w69 = lsig512_1 w67 #+ w62 #+ lsig512_0 w54 #+ w53
      w70 = lsig512_1 w68 #+ w63 #+ lsig512_0 w55 #+ w54
      w71 = lsig512_1 w69 #+ w64 #+ lsig512_0 w56 #+ w55
      w72 = lsig512_1 w70 #+ w65 #+ lsig512_0 w57 #+ w56
      w73 = lsig512_1 w71 #+ w66 #+ lsig512_0 w58 #+ w57
      w74 = lsig512_1 w72 #+ w67 #+ lsig512_0 w59 #+ w58
      w75 = lsig512_1 w73 #+ w68 #+ lsig512_0 w60 #+ w59
      w76 = lsig512_1 w74 #+ w69 #+ lsig512_0 w61 #+ w60
      w77 = lsig512_1 w75 #+ w70 #+ lsig512_0 w62 #+ w61
      w78 = lsig512_1 w76 #+ w71 #+ lsig512_0 w63 #+ w62
      w79 = lsig512_1 w77 #+ w72 #+ lsig512_0 w64 #+ w63
   in (,cont)
        $ SHA512Sched
          w00
          w01
          w02
          w03
          w04
          w05
          w06
          w07
          w08
          w09
          w10
          w11
          w12
          w13
          w14
          w15
          w16
          w17
          w18
          w19
          w20
          w21
          w22
          w23
          w24
          w25
          w26
          w27
          w28
          w29
          w30
          w31
          w32
          w33
          w34
          w35
          w36
          w37
          w38
          w39
          w40
          w41
          w42
          w43
          w44
          w45
          w46
          w47
          w48
          w49
          w50
          w51
          w52
          w53
          w54
          w55
          w56
          w57
          w58
          w59
          w60
          w61
          w62
          w63
          w64
          w65
          w66
          w67
          w68
          w69
          w70
          w71
          w72
          w73
          w74
          w75
          w76
          w77
          w78
          w79
{-# INLINEABLE getSHA512Sched #-}

next64 :: BuiltinByteString -> (UInt64, BuiltinByteString)
next64 bs = (UInt64 . sliceByteString 0 8 $ bs, sliceByteString 8 len bs)
  where
    len :: Integer
    len = lengthOfByteString bs
{-# INLINEABLE next64 #-}

pad :: BuiltinByteString -> BuiltinByteString
pad bs = bs <> padding
  where
    padding :: BuiltinByteString
    padding =
      let lenBits = 8 * lengthOfByteString bs
          r = 896 - lenBits `modulo` 1024 - 1
          k = if r <= (-1) then r + 1024 else r
          -- INVARIANT: k is necessarily > 0, and (k + 1) is a
          -- multiple of 8.
          kBytes = (k + 1) `divide` 8
          zeroBytes = kBytes - 1
          paddingZeroes = replicateByte zeroBytes 0x0
          paddingWith1 = consByteString 0x80 paddingZeroes
          lengthSuffix = integerToByteString BigEndian 16 lenBits
       in paddingWith1 <> lengthSuffix
{-# INLINEABLE pad #-}

processBlock :: BuiltinByteString -> SHA512State -> (SHA512State, BuiltinByteString)
processBlock bs s00@(SHA512State a00 b00 c00 d00 e00 f00 g00 h00) =
  let ( SHA512Sched
          w00
          w01
          w02
          w03
          w04
          w05
          w06
          w07
          w08
          w09
          w10
          w11
          w12
          w13
          w14
          w15
          w16
          w17
          w18
          w19
          w20
          w21
          w22
          w23
          w24
          w25
          w26
          w27
          w28
          w29
          w30
          w31
          w32
          w33
          w34
          w35
          w36
          w37
          w38
          w39
          w40
          w41
          w42
          w43
          w44
          w45
          w46
          w47
          w48
          w49
          w50
          w51
          w52
          w53
          w54
          w55
          w56
          w57
          w58
          w59
          w60
          w61
          w62
          w63
          w64
          w65
          w66
          w67
          w68
          w69
          w70
          w71
          w72
          w73
          w74
          w75
          w76
          w77
          w78
          w79
        , cont
        ) = getSHA512Sched bs
      s01 = step512 s00 0x428a_2f98_d728_ae22 w00
      s02 = step512 s01 0x7137_4491_23ef_65cd w01
      s03 = step512 s02 0xb5c0_fbcf_ec4d_3b2f w02
      s04 = step512 s03 0xe9b5_dba5_8189_dbbc w03
      s05 = step512 s04 0x3956_c25b_f348_b538 w04
      s06 = step512 s05 0x59f1_11f1_b605_d019 w05
      s07 = step512 s06 0x923f_82a4_af19_4f9b w06
      s08 = step512 s07 0xab1c_5ed5_da6d_8118 w07
      s09 = step512 s08 0xd807_aa98_a303_0242 w08
      s10 = step512 s09 0x1283_5b01_4570_6fbe w09
      s11 = step512 s10 0x2431_85be_4ee4_b28c w10
      s12 = step512 s11 0x550c_7dc3_d5ff_b4e2 w11
      s13 = step512 s12 0x72be_5d74_f27b_896f w12
      s14 = step512 s13 0x80de_b1fe_3b16_96b1 w13
      s15 = step512 s14 0x9bdc_06a7_25c7_1235 w14
      s16 = step512 s15 0xc19b_f174_cf69_2694 w15
      s17 = step512 s16 0xe49b_69c1_9ef1_4ad2 w16
      s18 = step512 s17 0xefbe_4786_384f_25e3 w17
      s19 = step512 s18 0x0fc1_9dc6_8b8c_d5b5 w18
      s20 = step512 s19 0x240c_a1cc_77ac_9c65 w19
      s21 = step512 s20 0x2de9_2c6f_592b_0275 w20
      s22 = step512 s21 0x4a74_84aa_6ea6_e483 w21
      s23 = step512 s22 0x5cb0_a9dc_bd41_fbd4 w22
      s24 = step512 s23 0x76f9_88da_8311_53b5 w23
      s25 = step512 s24 0x983e_5152_ee66_dfab w24
      s26 = step512 s25 0xa831_c66d_2db4_3210 w25
      s27 = step512 s26 0xb003_27c8_98fb_213f w26
      s28 = step512 s27 0xbf59_7fc7_beef_0ee4 w27
      s29 = step512 s28 0xc6e0_0bf3_3da8_8fc2 w28
      s30 = step512 s29 0xd5a7_9147_930a_a725 w29
      s31 = step512 s30 0x06ca_6351_e003_826f w30
      s32 = step512 s31 0x1429_2967_0a0e_6e70 w31
      s33 = step512 s32 0x27b7_0a85_46d2_2ffc w32
      s34 = step512 s33 0x2e1b_2138_5c26_c926 w33
      s35 = step512 s34 0x4d2c_6dfc_5ac4_2aed w34
      s36 = step512 s35 0x5338_0d13_9d95_b3df w35
      s37 = step512 s36 0x650a_7354_8baf_63de w36
      s38 = step512 s37 0x766a_0abb_3c77_b2a8 w37
      s39 = step512 s38 0x81c2_c92e_47ed_aee6 w38
      s40 = step512 s39 0x9272_2c85_1482_353b w39
      s41 = step512 s40 0xa2bf_e8a1_4cf1_0364 w40
      s42 = step512 s41 0xa81a_664b_bc42_3001 w41
      s43 = step512 s42 0xc24b_8b70_d0f8_9791 w42
      s44 = step512 s43 0xc76c_51a3_0654_be30 w43
      s45 = step512 s44 0xd192_e819_d6ef_5218 w44
      s46 = step512 s45 0xd699_0624_5565_a910 w45
      s47 = step512 s46 0xf40e_3585_5771_202a w46
      s48 = step512 s47 0x106a_a070_32bb_d1b8 w47
      s49 = step512 s48 0x19a4_c116_b8d2_d0c8 w48
      s50 = step512 s49 0x1e37_6c08_5141_ab53 w49
      s51 = step512 s50 0x2748_774c_df8e_eb99 w50
      s52 = step512 s51 0x34b0_bcb5_e19b_48a8 w51
      s53 = step512 s52 0x391c_0cb3_c5c9_5a63 w52
      s54 = step512 s53 0x4ed8_aa4a_e341_8acb w53
      s55 = step512 s54 0x5b9c_ca4f_7763_e373 w54
      s56 = step512 s55 0x682e_6ff3_d6b2_b8a3 w55
      s57 = step512 s56 0x748f_82ee_5def_b2fc w56
      s58 = step512 s57 0x78a5_636f_4317_2f60 w57
      s59 = step512 s58 0x84c8_7814_a1f0_ab72 w58
      s60 = step512 s59 0x8cc7_0208_1a64_39ec w59
      s61 = step512 s60 0x90be_fffa_2363_1e28 w60
      s62 = step512 s61 0xa450_6ceb_de82_bde9 w61
      s63 = step512 s62 0xbef9_a3f7_b2c6_7915 w62
      s64 = step512 s63 0xc671_78f2_e372_532b w63
      s65 = step512 s64 0xca27_3ece_ea26_619c w64
      s66 = step512 s65 0xd186_b8c7_21c0_c207 w65
      s67 = step512 s66 0xeada_7dd6_cde0_eb1e w66
      s68 = step512 s67 0xf57d_4f7f_ee6e_d178 w67
      s69 = step512 s68 0x06f0_67aa_7217_6fba w68
      s70 = step512 s69 0x0a63_7dc5_a2c8_98a6 w69
      s71 = step512 s70 0x113f_9804_bef9_0dae w70
      s72 = step512 s71 0x1b71_0b35_131c_471b w71
      s73 = step512 s72 0x28db_77f5_2304_7d84 w72
      s74 = step512 s73 0x32ca_ab7b_40c7_2493 w73
      s75 = step512 s74 0x3c9e_be0a_15c9_bebc w74
      s76 = step512 s75 0x431d_67c4_9c10_0d4c w75
      s77 = step512 s76 0x4cc5_d4be_cb3e_42b6 w76
      s78 = step512 s77 0x597f_299c_fc65_7e2a w77
      s79 = step512 s78 0x5fcb_6fab_3ad6_faec w78
      s80 = step512 s79 0x6c44_198c_4a47_5817 w79
      SHA512State a80 b80 c80 d80 e80 f80 g80 h80 = s80
      newState =
        SHA512State
          (a00 #+ a80)
          (b00 #+ b80)
          (c00 #+ c80)
          (d00 #+ d80)
          (e00 #+ e80)
          (f00 #+ f80)
          (g00 #+ g80)
          (h00 #+ h80)
   in (newState, cont)
{-# INLINEABLE processBlock #-}

step512 :: SHA512State -> Integer -> UInt64 -> SHA512State
step512 (SHA512State x1 x2 x3 x4 x5 x6 x7 x8) k w =
  SHA512State x1' x1 x2 x3 x5' x5 x6 x7
  where
    k' :: UInt64
    k' = integerToUInt64 k
    t1 :: UInt64
    t1 = x8 #+ bsig512_1 x5 #+ ch x5 x6 x7 #+ k' #+ w
    t2 :: UInt64
    t2 = bsig512_0 x1 #+ maj x1 x2 x3
    x1' :: UInt64
    x1' = t1 #+ t2
    x5' :: UInt64
    x5' = x4 #+ t1
{-# INLINEABLE step512 #-}

bsig512_0 :: UInt64 -> UInt64
bsig512_0 x = rot (-28) x `xor` rot (-34) x `xor` rot (-39) x
{-# INLINEABLE bsig512_0 #-}

bsig512_1 :: UInt64 -> UInt64
bsig512_1 x = rot (-14) x `xor` rot (-18) x `xor` rot (-41) x
{-# INLINEABLE bsig512_1 #-}

ch :: UInt64 -> UInt64 -> UInt64 -> UInt64
ch x y z = (x .&. y) `xor` (complementU x .&. z)
{-# INLINEABLE ch #-}

maj :: UInt64 -> UInt64 -> UInt64 -> UInt64
maj x y z = (x .&. (y .|. z)) .|. (y .&. z)
{-# INLINEABLE maj #-}

runSha
  :: SHA512State
  -> (BuiltinByteString -> SHA512State -> (SHA512State, BuiltinByteString))
  -> BuiltinByteString
  -> SHA512State
runSha state next input
  | lengthOfByteString input == 0 = state
  | otherwise =
      let (state', rest) = next input state
       in runSha state' next rest
{-# INLINEABLE runSha #-}
