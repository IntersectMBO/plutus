module Test.E.Arbitrary where

import Test.E
import Test.Tasty.QuickCheck

-- GENERATED START

instance () => Arbitrary E2 where
  arbitrary =
    do
      x <- choose (0 :: Int, 1)
      case x of
        0 -> return E2_1
        1 -> return E2_2
        _ -> error "FATAL ERROR: Arbitrary instance, logic bug"

instance () => Arbitrary E3 where
  arbitrary =
    do
      x <- choose (0 :: Int, 2)
      case x of
        0 -> return E3_1
        1 -> return E3_2
        2 -> return E3_3
        _ -> error "FATAL ERROR: Arbitrary instance, logic bug"

instance () => Arbitrary E4 where
  arbitrary =
    do
      x <- choose (0 :: Int, 3)
      case x of
        0 -> return E4_1
        1 -> return E4_2
        2 -> return E4_3
        3 -> return E4_4
        _ -> error "FATAL ERROR: Arbitrary instance, logic bug"

instance () => Arbitrary E8 where
  arbitrary =
    do
      x <- choose (0 :: Int, 7)
      case x of
        0 -> return E8_1
        1 -> return E8_2
        2 -> return E8_3
        3 -> return E8_4
        4 -> return E8_5
        5 -> return E8_6
        6 -> return E8_7
        7 -> return E8_8
        _ -> error "FATAL ERROR: Arbitrary instance, logic bug"

instance () => Arbitrary E16 where
  arbitrary =
    do
      x <- choose (0 :: Int, 15)
      case x of
        0 -> return E16_1
        1 -> return E16_2
        2 -> return E16_3
        3 -> return E16_4
        4 -> return E16_5
        5 -> return E16_6
        6 -> return E16_7
        7 -> return E16_8
        8 -> return E16_9
        9 -> return E16_10
        10 -> return E16_11
        11 -> return E16_12
        12 -> return E16_13
        13 -> return E16_14
        14 -> return E16_15
        15 -> return E16_16
        _ -> error "FATAL ERROR: Arbitrary instance, logic bug"

instance () => Arbitrary E17 where
  arbitrary =
    do
      x <- choose (0 :: Int, 16)
      case x of
        0 -> return E17_1
        1 -> return E17_2
        2 -> return E17_3
        3 -> return E17_4
        4 -> return E17_5
        5 -> return E17_6
        6 -> return E17_7
        7 -> return E17_8
        8 -> return E17_9
        9 -> return E17_10
        10 -> return E17_11
        11 -> return E17_12
        12 -> return E17_13
        13 -> return E17_14
        14 -> return E17_15
        15 -> return E17_16
        16 -> return E17_17
        _ -> error "FATAL ERROR: Arbitrary instance, logic bug"

instance () => Arbitrary E32 where
  arbitrary =
    do
      x <- choose (0 :: Int, 31)
      case x of
        0 -> return E32_1
        1 -> return E32_2
        2 -> return E32_3
        3 -> return E32_4
        4 -> return E32_5
        5 -> return E32_6
        6 -> return E32_7
        7 -> return E32_8
        8 -> return E32_9
        9 -> return E32_10
        10 -> return E32_11
        11 -> return E32_12
        12 -> return E32_13
        13 -> return E32_14
        14 -> return E32_15
        15 -> return E32_16
        16 -> return E32_17
        17 -> return E32_18
        18 -> return E32_19
        19 -> return E32_20
        20 -> return E32_21
        21 -> return E32_22
        22 -> return E32_23
        23 -> return E32_24
        24 -> return E32_25
        25 -> return E32_26
        26 -> return E32_27
        27 -> return E32_28
        28 -> return E32_29
        29 -> return E32_30
        30 -> return E32_31
        31 -> return E32_32
        _ -> error "FATAL ERROR: Arbitrary instance, logic bug"
