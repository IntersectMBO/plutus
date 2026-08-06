{-# LANGUAGE TypeApplications #-}

module MatchingCpuRuntime.Arguments
  ( Term
  , match_benchmark_constr_flat_d1_w1_c1_arg
  , match_benchmark_constr_flat_d1_w16_c4_arg
  , match_benchmark_constr_flat_d1_w1000_c1_arg
  , match_benchmark_constr_flat_d1_w1000_c16_arg
  , match_benchmark_constr_spine_front_d4_w16_c8_arg
  , match_benchmark_constr_spine_middle_d4_w16_c8_arg
  , match_benchmark_constr_spine_last_d4_w16_c8_arg
  , match_benchmark_constr_spine_irregular_d4_w16_c8_arg
  , match_benchmark_constr_spine_irregular_d8_w8_c8_arg
  , match_benchmark_constr_spine_front_d64_w2_c8_arg
  , match_benchmark_constr_spine_zigzag_d100_w2_c10_arg
  , match_benchmark_constr_binary_d3_w16_c8_arg
  , match_benchmark_constr_ternary_d3_w8_c10_arg
  , match_benchmark_constr_quaternary_d3_w8_c17_arg
  , match_benchmark_constr_rootfork2_d6_w12_c8_arg
  , match_benchmark_constr_rootfork3_d5_w10_c9_arg
  , match_benchmark_constr_rootfork4_d4_w8_c8_arg
  , match_benchmark_constr_spine_stress_d10_w100_c20_arg
  , match_benchmark_constr_binary_stress_d8_w8_c32_arg
  , match_benchmark_constr_alt_spine_d16_w8_c8_arg
  , match_benchmark_constr_alt_rootfork3_d5_w10_c9_arg
  , match_benchmark_constr_alt_binary_d8_w8_c32_arg
  )
where

import PlutusCore qualified as PLC
import PlutusCore.Data qualified as PLCData
import PlutusCore.MkPlc (mkConstant)
import UntypedPlutusCore qualified as UPLC

type Term = UPLC.Term PLC.NamedDeBruijn PLC.DefaultUni PLC.DefaultFun ()

-- Scalar field f of Constr n is I ((n - 1) * W + f + 1). "..." omits fields/subtrees.

mkDataTerm :: PLCData.Data -> Term
mkDataTerm = mkConstant @PLCData.Data ()

constrNode :: Int -> Int -> [(Int, PLCData.Data)] -> PLCData.Data
constrNode width nodeId children =
  PLCData.Constr
    (toInteger nodeId)
    [ case lookup fieldIndex children of
        Just child -> child
        Nothing -> scalarField width nodeId fieldIndex
    | fieldIndex <- [0 .. width - 1]
    ]

scalarField :: Int -> Int -> Int -> PLCData.Data
scalarField width nodeId fieldIndex =
  PLCData.I . toInteger $ (nodeId - 1) * width + fieldIndex + 1

-- Data: Constr 1 [I 1].
match_benchmark_constr_flat_d1_w1_c1_arg :: Term
match_benchmark_constr_flat_d1_w1_c1_arg =
  mkDataTerm $ constrNode 1 1 []

-- Data: Constr 1 [I 1, I 2, ..., I 16].
match_benchmark_constr_flat_d1_w16_c4_arg :: Term
match_benchmark_constr_flat_d1_w16_c4_arg =
  mkDataTerm $ constrNode 16 1 []

-- Data: Constr 1 [I 1, I 2, ..., I 1000].
match_benchmark_constr_flat_d1_w1000_c1_arg :: Term
match_benchmark_constr_flat_d1_w1000_c1_arg =
  mkDataTerm $ constrNode 1000 1 []

-- Data: Constr 1 [I 1, I 2, ..., I 1000].
match_benchmark_constr_flat_d1_w1000_c16_arg :: Term
match_benchmark_constr_flat_d1_w1000_c16_arg =
  mkDataTerm $ constrNode 1000 1 []

-- Data: Constr 1 [Constr 2 [Constr 3 [Constr 4 [I 49, ..., I 64],
--       I 34, ..., I 48], I 18, ..., I 32], I 2, ..., I 16].
match_benchmark_constr_spine_front_d4_w16_c8_arg :: Term
match_benchmark_constr_spine_front_d4_w16_c8_arg =
  mkDataTerm $ go 1 [0, 0, 0]
  where
    go :: Int -> [Int] -> PLCData.Data
    go nodeId remainingPositions =
      constrNode 16 nodeId $
        case remainingPositions of
          [] -> []
          childPosition : laterPositions ->
            [(childPosition, go (nodeId + 1) laterPositions)]

-- Data: Constr 1 [I 1, ..., I 8, Constr 2 [I 17, ..., I 24,
--       Constr 3 [I 33, ..., I 40, Constr 4 [I 49, ..., I 64],
--       I 42, ..., I 48], I 26, ..., I 32], I 10, ..., I 16].
match_benchmark_constr_spine_middle_d4_w16_c8_arg :: Term
match_benchmark_constr_spine_middle_d4_w16_c8_arg =
  mkDataTerm $ go 1 [8, 8, 8]
  where
    go :: Int -> [Int] -> PLCData.Data
    go nodeId remainingPositions =
      constrNode 16 nodeId $
        case remainingPositions of
          [] -> []
          childPosition : laterPositions ->
            [(childPosition, go (nodeId + 1) laterPositions)]

-- Data: Constr 1 [I 1, ..., I 15, Constr 2 [I 17, ..., I 31,
--       Constr 3 [I 33, ..., I 47, Constr 4 [I 49, ..., I 64]]]].
match_benchmark_constr_spine_last_d4_w16_c8_arg :: Term
match_benchmark_constr_spine_last_d4_w16_c8_arg =
  mkDataTerm $ go 1 [15, 15, 15]
  where
    go :: Int -> [Int] -> PLCData.Data
    go nodeId remainingPositions =
      constrNode 16 nodeId $
        case remainingPositions of
          [] -> []
          childPosition : laterPositions ->
            [(childPosition, go (nodeId + 1) laterPositions)]

-- Data: Constr 1 [I 1, I 2, I 3, Constr 2 [I 17, ..., I 28,
--       Constr 3 [I 33, ..., I 37, Constr 4 [I 49, ..., I 64],
--       I 39, ..., I 48], I 30, I 31, I 32], I 5, ..., I 16].
match_benchmark_constr_spine_irregular_d4_w16_c8_arg :: Term
match_benchmark_constr_spine_irregular_d4_w16_c8_arg =
  mkDataTerm $ go 1 [3, 12, 5]
  where
    go :: Int -> [Int] -> PLCData.Data
    go nodeId remainingPositions =
      constrNode 16 nodeId $
        case remainingPositions of
          [] -> []
          childPosition : laterPositions ->
            [(childPosition, go (nodeId + 1) laterPositions)]

-- Data: Constr 1 [Constr 2 [... Constr 3 [... Constr 4 [... Constr 5
--       [... Constr 6 [... Constr 7 [... Constr 8 [I 57, ..., I 64]]]]]]],
--       I 2, ..., I 8]; child fields [0,4,7,2,6,1,5].
match_benchmark_constr_spine_irregular_d8_w8_c8_arg :: Term
match_benchmark_constr_spine_irregular_d8_w8_c8_arg =
  mkDataTerm $ go 1 [0, 4, 7, 2, 6, 1, 5]
  where
    go :: Int -> [Int] -> PLCData.Data
    go nodeId remainingPositions =
      constrNode 8 nodeId $
        case remainingPositions of
          [] -> []
          childPosition : laterPositions ->
            [(childPosition, go (nodeId + 1) laterPositions)]

-- Data: Constr 1 [Constr 2 [... Constr 64 [I 127, I 128] ...], I 2].
match_benchmark_constr_spine_front_d64_w2_c8_arg :: Term
match_benchmark_constr_spine_front_d64_w2_c8_arg =
  mkDataTerm $ go 1 (replicate 63 0)
  where
    go :: Int -> [Int] -> PLCData.Data
    go nodeId remainingPositions =
      constrNode 2 nodeId $
        case remainingPositions of
          [] -> []
          childPosition : laterPositions ->
            [(childPosition, go (nodeId + 1) laterPositions)]

-- Data: Constr 1 [Constr 2 [I 3, Constr 3 [... Constr 100 [I 199, I 200]
--       ...]], I 2]; child fields [0,1,0,1,...].
match_benchmark_constr_spine_zigzag_d100_w2_c10_arg :: Term
match_benchmark_constr_spine_zigzag_d100_w2_c10_arg =
  mkDataTerm $
    go 1 [if odd nodeId then 0 else 1 | nodeId <- [1 :: Int .. 99]]
  where
    go :: Int -> [Int] -> PLCData.Data
    go nodeId remainingPositions =
      constrNode 2 nodeId $
        case remainingPositions of
          [] -> []
          childPosition : laterPositions ->
            [(childPosition, go (nodeId + 1) laterPositions)]

-- Data: Constr 1 [Constr 2 [Constr 3 [I 33, ..., I 48], I 18, ..., I 31,
--       Constr 4 [I 49, ..., I 64]], I 2, ..., I 15,
--       Constr 5 [Constr 6 [I 81, ..., I 96], I 66, ..., I 79,
--       Constr 7 [I 97, ..., I 112]]].
match_benchmark_constr_binary_d3_w16_c8_arg :: Term
match_benchmark_constr_binary_d3_w16_c8_arg =
  mkDataTerm root
  where
    root = constrNode 16 1 [(0, node2), (15, node5)]
    node2 = constrNode 16 2 [(0, node3), (15, node4)]
    node3 = constrNode 16 3 []
    node4 = constrNode 16 4 []
    node5 = constrNode 16 5 [(0, node6), (15, node7)]
    node6 = constrNode 16 6 []
    node7 = constrNode 16 7 []

-- Data: Constr 1 [Constr 2 [Constr 3 [...], ..., Constr 4 [...], ...,
--       Constr 5 [...]], I 2, I 3, I 4,
--       Constr 6 [Constr 7 [...], ..., Constr 8 [...], ..., Constr 9 [...]],
--       I 6, I 7, Constr 10 [Constr 11 [...], ..., Constr 12 [...], ...,
--       Constr 13 [...]]].
match_benchmark_constr_ternary_d3_w8_c10_arg :: Term
match_benchmark_constr_ternary_d3_w8_c10_arg =
  mkDataTerm root
  where
    root = constrNode 8 1 [(0, node2), (4, node6), (7, node10)]
    node2 = constrNode 8 2 [(0, node3), (4, node4), (7, node5)]
    node3 = constrNode 8 3 []
    node4 = constrNode 8 4 []
    node5 = constrNode 8 5 []
    node6 = constrNode 8 6 [(0, node7), (4, node8), (7, node9)]
    node7 = constrNode 8 7 []
    node8 = constrNode 8 8 []
    node9 = constrNode 8 9 []
    node10 = constrNode 8 10 [(0, node11), (4, node12), (7, node13)]
    node11 = constrNode 8 11 []
    node12 = constrNode 8 12 []
    node13 = constrNode 8 13 []

-- Data: Constr 1 [Constr 2 [Constr 3 [...], ..., Constr 4 [...], ...,
--       Constr 5 [...], ..., Constr 6 [...]], I 2,
--       Constr 7 [Constr 8 [...], ..., Constr 9 [...], ..., Constr 10 [...],
--       ..., Constr 11 [...]], I 4, I 5, Constr 12 [...], I 7, Constr 17 [...]].
match_benchmark_constr_quaternary_d3_w8_c17_arg :: Term
match_benchmark_constr_quaternary_d3_w8_c17_arg =
  mkDataTerm root
  where
    root = constrNode 8 1 [(0, node2), (2, node7), (5, node12), (7, node17)]
    node2 = constrNode 8 2 [(0, node3), (2, node4), (5, node5), (7, node6)]
    node3 = constrNode 8 3 []
    node4 = constrNode 8 4 []
    node5 = constrNode 8 5 []
    node6 = constrNode 8 6 []
    node7 = constrNode 8 7 [(0, node8), (2, node9), (5, node10), (7, node11)]
    node8 = constrNode 8 8 []
    node9 = constrNode 8 9 []
    node10 = constrNode 8 10 []
    node11 = constrNode 8 11 []
    node12 = constrNode 8 12 [(0, node13), (2, node14), (5, node15), (7, node16)]
    node13 = constrNode 8 13 []
    node14 = constrNode 8 14 []
    node15 = constrNode 8 15 []
    node16 = constrNode 8 16 []
    node17 = constrNode 8 17 [(0, node18), (2, node19), (5, node20), (7, node21)]
    node18 = constrNode 8 18 []
    node19 = constrNode 8 19 []
    node20 = constrNode 8 20 []
    node21 = constrNode 8 21 []

-- Data: Constr 1 [I 1, I 2, Constr 2 [Constr 3 [... Constr 4
--       [... Constr 5 [... Constr 6 [...]]]]], I 4, ..., I 10,
--       Constr 7 [... Constr 8 [... Constr 9 [...]]], I 12].
match_benchmark_constr_rootfork2_d6_w12_c8_arg :: Term
match_benchmark_constr_rootfork2_d6_w12_c8_arg =
  mkDataTerm root
  where
    root = constrNode 12 1 [(2, branch1Node2), (10, branch2Node7)]

    branch1Node2 = constrNode 12 2 [(0, branch1Node3)]
    branch1Node3 = constrNode 12 3 [(7, branch1Node4)]
    branch1Node4 = constrNode 12 4 [(11, branch1Node5)]
    branch1Node5 = constrNode 12 5 [(4, branch1Node6)]
    branch1Node6 = constrNode 12 6 []

    branch2Node7 = constrNode 12 7 [(9, branch2Node8)]
    branch2Node8 = constrNode 12 8 [(1, branch2Node9)]
    branch2Node9 = constrNode 12 9 []

-- Data: Constr 1 [Constr 2 [... Constr 3 [... Constr 4 [... Constr 5 [...]]]],
--       I 2, ..., I 5, Constr 6 [... Constr 7 [... Constr 8 [...]]],
--       I 7, I 8, I 9, Constr 9 [... Constr 10 [...]]].
match_benchmark_constr_rootfork3_d5_w10_c9_arg :: Term
match_benchmark_constr_rootfork3_d5_w10_c9_arg =
  mkDataTerm root
  where
    root = constrNode 10 1 [(0, branch1Node2), (5, branch2Node6), (9, branch3Node9)]

    branch1Node2 = constrNode 10 2 [(2, branch1Node3)]
    branch1Node3 = constrNode 10 3 [(8, branch1Node4)]
    branch1Node4 = constrNode 10 4 [(4, branch1Node5)]
    branch1Node5 = constrNode 10 5 []

    branch2Node6 = constrNode 10 6 [(7, branch2Node7)]
    branch2Node7 = constrNode 10 7 [(1, branch2Node8)]
    branch2Node8 = constrNode 10 8 []

    branch3Node9 = constrNode 10 9 [(5, branch3Node10)]
    branch3Node10 = constrNode 10 10 []

-- Data: Constr 1 [Constr 2 [... Constr 3 [... Constr 4 [...]]], I 2,
--       Constr 5 [... Constr 6 [...]], I 4, I 5, Constr 7 [...], I 7,
--       Constr 8 [...]].
match_benchmark_constr_rootfork4_d4_w8_c8_arg :: Term
match_benchmark_constr_rootfork4_d4_w8_c8_arg =
  mkDataTerm root
  where
    root =
      constrNode
        8
        1
        [ (0, branch1Node2)
        , (2, branch2Node5)
        , (5, branch3Node7)
        , (7, branch4Node8)
        ]

    branch1Node2 = constrNode 8 2 [(3, branch1Node3)]
    branch1Node3 = constrNode 8 3 [(7, branch1Node4)]
    branch1Node4 = constrNode 8 4 []

    branch2Node5 = constrNode 8 5 [(1, branch2Node6)]
    branch2Node6 = constrNode 8 6 []

    branch3Node7 = constrNode 8 7 []
    branch4Node8 = constrNode 8 8 []

-- Data: Constr 1 [Constr 2 [... Constr 3 [... Constr 4 [... Constr 5
--       [... Constr 6 [... Constr 7 [... Constr 8 [... Constr 9
--       [... Constr 10 [I 901, ..., I 1000]]]]]]]]], I 2, ..., I 100];
--       child fields [0,50,99,20,80,10,60,30,90].
match_benchmark_constr_spine_stress_d10_w100_c20_arg :: Term
match_benchmark_constr_spine_stress_d10_w100_c20_arg =
  mkDataTerm $ go 1 [0, 50, 99, 20, 80, 10, 60, 30, 90]
  where
    go :: Int -> [Int] -> PLCData.Data
    go nodeId remainingPositions =
      constrNode 100 nodeId $
        case remainingPositions of
          [] -> []
          childPosition : laterPositions ->
            [(childPosition, go (nodeId + 1) laterPositions)]

-- Data: Constr 1
--       [ Constr 2 [I 9, I 10, Constr 3 [...], I 12, I 13,
--                    Constr 66 [...], I 15, I 16]
--       , I 2, ..., I 7
--       , Constr 129 [I 1025, I 1026, Constr 130 [...], I 1028, I 1029,
--                     Constr 193 [...], I 1031, I 1032]
--       ].
match_benchmark_constr_binary_stress_d8_w8_c32_arg :: Term
match_benchmark_constr_binary_stress_d8_w8_c32_arg =
  mkDataTerm $ tree 1 8 1
  where
    tree :: Int -> Int -> Int -> PLCData.Data
    tree level remainingHeight nodeId
      | remainingHeight == 1 = constrNode 8 nodeId []
      | otherwise =
          let (leftField, rightField) =
                if odd level then (0, 7) else (2, 5)
              rightChildId = nodeId + 2 ^ (remainingHeight - 1)
           in constrNode
                8
                nodeId
                [ (leftField, tree (level + 1) (remainingHeight - 1) (nodeId + 1))
                , (rightField, tree (level + 1) (remainingHeight - 1) rightChildId)
                ]

-- Data: Constr 1 [Constr 2 [... Constr 3 [... Constr 16
--       [I 121, ..., I 128] ...] ...], I 2, ..., I 8];
--       child fields [0,7,2,5,0,7,2,5,0,7,2,5,0,7,2].
match_benchmark_constr_alt_spine_d16_w8_c8_arg :: Term
match_benchmark_constr_alt_spine_d16_w8_c8_arg =
  mkDataTerm $
    go 1 [0, 7, 2, 5, 0, 7, 2, 5, 0, 7, 2, 5, 0, 7, 2]
  where
    go :: Int -> [Int] -> PLCData.Data
    go nodeId remainingPositions =
      constrNode 8 nodeId $
        case remainingPositions of
          [] -> []
          childPosition : laterPositions ->
            [(childPosition, go (nodeId + 1) laterPositions)]

-- Data: Constr 1 [Constr 2 [... Constr 3 [... Constr 4 [... Constr 5 [...]]]],
--       I 2, ..., I 5, Constr 6 [... Constr 7 [... Constr 8 [...]]],
--       I 7, I 8, I 9, Constr 9 [... Constr 10 [...]]].
match_benchmark_constr_alt_rootfork3_d5_w10_c9_arg :: Term
match_benchmark_constr_alt_rootfork3_d5_w10_c9_arg =
  mkDataTerm root
  where
    root = constrNode 10 1 [(0, branch1Node2), (5, branch2Node6), (9, branch3Node9)]

    branch1Node2 = constrNode 10 2 [(2, branch1Node3)]
    branch1Node3 = constrNode 10 3 [(8, branch1Node4)]
    branch1Node4 = constrNode 10 4 [(4, branch1Node5)]
    branch1Node5 = constrNode 10 5 []

    branch2Node6 = constrNode 10 6 [(7, branch2Node7)]
    branch2Node7 = constrNode 10 7 [(1, branch2Node8)]
    branch2Node8 = constrNode 10 8 []

    branch3Node9 = constrNode 10 9 [(5, branch3Node10)]
    branch3Node10 = constrNode 10 10 []

-- Data: Constr 1
--       [ Constr 2 [I 9, I 10, Constr 3 [...], I 12, I 13,
--                    Constr 66 [...], I 15, I 16]
--       , I 2, ..., I 7
--       , Constr 129 [I 1025, I 1026, Constr 130 [...], I 1028, I 1029,
--                     Constr 193 [...], I 1031, I 1032]
--       ].
match_benchmark_constr_alt_binary_d8_w8_c32_arg :: Term
match_benchmark_constr_alt_binary_d8_w8_c32_arg =
  mkDataTerm $ tree 1 8 1
  where
    tree :: Int -> Int -> Int -> PLCData.Data
    tree level remainingHeight nodeId
      | remainingHeight == 1 = constrNode 8 nodeId []
      | otherwise =
          let (leftField, rightField) =
                if odd level then (0, 7) else (2, 5)
              rightChildId = nodeId + 2 ^ (remainingHeight - 1)
           in constrNode
                8
                nodeId
                [ (leftField, tree (level + 1) (remainingHeight - 1) (nodeId + 1))
                , (rightField, tree (level + 1) (remainingHeight - 1) rightChildId)
                ]
