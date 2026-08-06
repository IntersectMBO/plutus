{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications #-}

-- | Explicit traditional Data.Constr matchers for the CPU runtime comparison.
module MatchingCpuRuntime.Matchers where

import Control.Monad.Except (runExcept)
import Data.Either (fromRight)
import Data.List (foldl', sortOn)
import Data.Vector qualified as Vector
import PlutusBenchmark.Common (Term)
import PlutusCore (freshName, runQuote)
import PlutusCore qualified as PLC
import PlutusCore.MkPlc (mkConstant)
import UntypedPlutusCore qualified as UPLC

matching_implementation :: String
matching_implementation = "traditional"

type NamedTerm = UPLC.Term UPLC.Name PLC.DefaultUni PLC.DefaultFun ()

type FieldMatcher = UPLC.Name -> NamedTerm -> PLC.Quote NamedTerm

debruijnTermUnsafe
  :: UPLC.Term UPLC.Name PLC.DefaultUni PLC.DefaultFun ()
  -> Term
debruijnTermUnsafe =
  fromRight (error "debruijnTermUnsafe")
    . runExcept @UPLC.FreeVariableError
    . UPLC.deBruijnTerm

traditionalMatcher :: (UPLC.Name -> PLC.Quote NamedTerm) -> Term
traditionalMatcher makeBody =
  debruijnTermUnsafe $ runQuote $ do
    argumentName <- freshName "argument"
    body <- makeBody argumentName
    bodyWithSharedTailList <-
      hoistRepeatedBuiltin PLC.TailList (freshName "tailList") body
    bodyWithSharedListBuiltins <-
      hoistRepeatedBuiltin PLC.DropList (freshName "dropList") bodyWithSharedTailList
    pure $ UPLC.LamAbs () argumentName bodyWithSharedListBuiltins

-- Share a forced polymorphic list builtin only when the matcher uses it repeatedly.
hoistRepeatedBuiltin
  :: PLC.DefaultFun
  -> PLC.Quote UPLC.Name
  -> NamedTerm
  -> PLC.Quote NamedTerm
hoistRepeatedBuiltin builtinName makeName body
  | forcedBuiltinOccurrences builtinName body <= 1 = pure body
  | otherwise = do
      name <- makeName
      pure $
        UPLC.Apply
          ()
          (UPLC.LamAbs () name $ replaceForcedBuiltin builtinName name body)
          (UPLC.Force () $ UPLC.Builtin () builtinName)

forcedBuiltinOccurrences :: PLC.DefaultFun -> NamedTerm -> Int
forcedBuiltinOccurrences builtinName = go
  where
    go = \case
      UPLC.Var {} -> 0
      UPLC.LamAbs _ _ body -> go body
      UPLC.Apply _ function argument -> go function + go argument
      UPLC.Force _ (UPLC.Builtin _ foundBuiltin)
        | foundBuiltin == builtinName -> 1
      UPLC.Force _ term -> go term
      UPLC.Delay _ term -> go term
      UPLC.Constant {} -> 0
      UPLC.Builtin {} -> 0
      UPLC.Error {} -> 0
      UPLC.Constr _ _ fields -> sum $ fmap go fields
      UPLC.Case _ scrutinee branches -> go scrutinee + sum (fmap go branches)

replaceForcedBuiltin :: PLC.DefaultFun -> UPLC.Name -> NamedTerm -> NamedTerm
replaceForcedBuiltin builtinName replacement = go
  where
    go term = case term of
      UPLC.Var {} -> term
      UPLC.LamAbs ann name body -> UPLC.LamAbs ann name $ go body
      UPLC.Apply ann function argument -> UPLC.Apply ann (go function) (go argument)
      UPLC.Force ann (UPLC.Builtin _ foundBuiltin)
        | foundBuiltin == builtinName -> UPLC.Var ann replacement
      UPLC.Force ann forced -> UPLC.Force ann $ go forced
      UPLC.Delay ann delayed -> UPLC.Delay ann $ go delayed
      UPLC.Constant {} -> term
      UPLC.Builtin {} -> term
      UPLC.Error {} -> term
      UPLC.Constr ann tag fields -> UPLC.Constr ann tag $ fmap go fields
      UPLC.Case ann scrutinee branches ->
        UPLC.Case ann (go scrutinee) $ fmap go branches

sumCapturedIntegers :: [UPLC.Name] -> NamedTerm
sumCapturedIntegers [] = mkConstant @Integer () 0
sumCapturedIntegers (firstCapture : laterCaptures) =
  foldl'
    ( \acc captureName ->
        UPLC.Apply
          ()
          (UPLC.Apply () (UPLC.Builtin () PLC.AddInteger) acc)
          (UPLC.Var () captureName)
    )
    (UPLC.Var () firstCapture)
    laterCaptures

builtinApp :: Int -> PLC.DefaultFun -> [NamedTerm] -> NamedTerm
builtinApp typeArgumentCount builtinName arguments =
  foldl'
    (UPLC.Apply ())
    (foldr (const $ UPLC.Force ()) (UPLC.Builtin () builtinName) [1 .. typeArgumentCount])
    arguments

chooseData
  :: NamedTerm
  -> NamedTerm
  -> NamedTerm
  -> NamedTerm
  -> NamedTerm
  -> NamedTerm
  -> NamedTerm
chooseData value whenConstr whenMap whenList whenI whenB =
  UPLC.Force () $
    builtinApp
      1
      PLC.ChooseData
      (value : fmap (UPLC.Delay ()) [whenConstr, whenMap, whenList, whenI, whenB])

captureIntegerField :: UPLC.Name -> FieldMatcher
captureIntegerField captureName fieldName continuation =
  pure $
    UPLC.Apply
      ()
      (UPLC.LamAbs () captureName continuation)
      (builtinApp 0 PLC.UnIData [UPLC.Var () fieldName])

captureIntegerAlternatives :: UPLC.Name -> FieldMatcher
captureIntegerAlternatives captureName fieldName continuation =
  pure $
    UPLC.Apply
      ()
      (UPLC.LamAbs () captureName continuation)
      ( chooseData
          (UPLC.Var () fieldName)
          (UPLC.Error ())
          (UPLC.Error ())
          (UPLC.Error ())
          (builtinApp 0 PLC.UnIData [UPLC.Var () fieldName])
          (builtinApp 0 PLC.UnBData [UPLC.Var () fieldName])
      )

capturedFieldsAtNodeWith
  :: (Int -> UPLC.Name -> FieldMatcher)
  -> Int
  -> Int
  -> [(Int, UPLC.Name)]
  -> [(Int, FieldMatcher)]
capturedFieldsAtNodeWith captureField width nodeId capturePairs =
  [ ((captureValue - 1) `mod` width, captureField captureValue captureName)
  | (captureValue, captureName) <- capturePairs
  , captureValue > (nodeId - 1) * width
  , captureValue <= nodeId * width
  ]

capturedFieldsAtNode
  :: Int
  -> Int
  -> [(Int, UPLC.Name)]
  -> [(Int, FieldMatcher)]
capturedFieldsAtNode =
  capturedFieldsAtNodeWith $ const captureIntegerField

withCapturedValues
  :: [Int]
  -> ([(Int, UPLC.Name)] -> NamedTerm -> PLC.Quote NamedTerm)
  -> PLC.Quote NamedTerm
withCapturedValues captureValues makeBody = do
  captureNames <- traverse (const $ freshName "capture") captureValues
  makeBody (zip captureValues captureNames) (sumCapturedIntegers captureNames)

ignoreField :: FieldMatcher
ignoreField _ continuation = pure continuation

dropFields :: Int -> NamedTerm -> NamedTerm
dropFields count fields
  | count == 0 = fields
  | count <= 3 =
      foldl'
        (\current _ -> builtinApp 1 PLC.TailList [current])
        fields
        [1 .. count]
  | otherwise =
      builtinApp
        1
        PLC.DropList
        [mkConstant @Integer () $ toInteger count, fields]

{-| Bind only selected fields, use 'TailList' for gaps of at most three and
'DropList' for larger gaps, and require exactly @width@ fields. The final
field is inspected even when otherwise unused, so a short list cannot pass. -}
matchFieldsExact
  :: Int
  -> [(Int, FieldMatcher)]
  -> NamedTerm
  -> NamedTerm
  -> PLC.Quote NamedTerm
matchFieldsExact width fieldsToMatch fields continuation =
  go 0 fields operations
  where
    orderedFields = sortOn fst fieldsToMatch
    operations =
      if any ((== width - 1) . fst) orderedFields
        then orderedFields
        else orderedFields <> [(width - 1, ignoreField)]

    go _ _ [] = error "matchFieldsExact: missing final field operation"
    go nextIndex current ((fieldIndex, matchField) : laterFields)
      | fieldIndex < nextIndex =
          error "matchFieldsExact: duplicate or descending field operation"
      | otherwise = do
          fieldName <- freshName "field"
          tailName <- freshName "fields"
          let atField = dropFields (fieldIndex - nextIndex) current
          body <-
            case laterFields of
              [] -> do
                unexpectedHead <- freshName "unexpected-field"
                unexpectedTail <- freshName "unexpected-fields"
                checked <- matchField fieldName continuation
                pure $
                  UPLC.Case
                    ()
                    (UPLC.Var () tailName)
                    ( Vector.fromList
                        [ UPLC.LamAbs () unexpectedHead $
                            UPLC.LamAbs () unexpectedTail $
                              UPLC.Error ()
                        , checked
                        ]
                    )
              _ -> do
                rest <- go (fieldIndex + 1) (UPLC.Var () tailName) laterFields
                matchField fieldName rest
          pure $
            UPLC.Case
              ()
              atField
              ( Vector.singleton $
                  UPLC.LamAbs () fieldName $
                    UPLC.LamAbs () tailName body
              )

{-| Use legacy builtins only: 'UnConstrData', builtin-pair/list 'Case',
'EqualsInteger', and sparse 'TailList'/'DropList' traversal. -}
matchConstrNode
  :: Int
  -> Int
  -> [(Int, FieldMatcher)]
  -> UPLC.Name
  -> NamedTerm
  -> PLC.Quote NamedTerm
matchConstrNode width expectedTag fieldsToMatch scrutinee continuation = do
  tagName <- freshName "tag"
  fieldsName <- freshName "fields"
  fieldsBody <-
    matchFieldsExact
      width
      fieldsToMatch
      (UPLC.Var () fieldsName)
      continuation
  let tagMatches =
        builtinApp
          0
          PLC.EqualsInteger
          [ UPLC.Var () tagName
          , mkConstant @Integer () $ toInteger expectedTag
          ]
      pairHandler =
        UPLC.LamAbs () tagName $
          UPLC.LamAbs () fieldsName $
            UPLC.Case
              ()
              tagMatches
              (Vector.fromList [UPLC.Error (), fieldsBody])
  pure $
    UPLC.Case
      ()
      (builtinApp 0 PLC.UnConstrData [UPLC.Var () scrutinee])
      (Vector.singleton pairHandler)

-- Sketch: unConstrData; case the pair/list; drop wildcard gaps; unIData selected fields.

-- Match: Constr 1 [@d1]; d1 ~ I @ => 1.
match_benchmark_constr_flat_d1_w1_c1_traditional :: Term
match_benchmark_constr_flat_d1_w1_c1_traditional =
  traditionalMatcher $ \argumentName -> do
    let captureValues = [1] :: [Int]
    withCapturedValues captureValues $ \capturePairs result ->
      matchConstrNode 1 1 (capturedFieldsAtNode 1 1 capturePairs) argumentName result

-- Match: Constr 1 [@d1, _, ..., @d6, _, ..., @d11, _, ..., @d16]; d* ~ I @ => 34.
match_benchmark_constr_flat_d1_w16_c4_traditional :: Term
match_benchmark_constr_flat_d1_w16_c4_traditional =
  traditionalMatcher $ \argumentName -> do
    let captureValues = [1, 6, 11, 16] :: [Int]
    withCapturedValues captureValues $ \capturePairs result ->
      matchConstrNode 16 1 (capturedFieldsAtNode 16 1 capturePairs) argumentName result

-- Match: Constr 1 [_, ..., @d997, _, _, _]; d997 ~ I @ => 997.
match_benchmark_constr_flat_d1_w1000_c1_traditional :: Term
match_benchmark_constr_flat_d1_w1000_c1_traditional =
  traditionalMatcher $ \argumentName -> do
    let captureValues = [997] :: [Int]
    withCapturedValues captureValues $ \capturePairs result ->
      matchConstrNode 1000 1 (capturedFieldsAtNode 1000 1 capturePairs) argumentName result

-- Match: Constr 1 [...] with @d at f[6,60,117,...,976,999]; d* ~ I @ => 8452.
match_benchmark_constr_flat_d1_w1000_c16_traditional :: Term
match_benchmark_constr_flat_d1_w1000_c16_traditional =
  traditionalMatcher $ \argumentName -> do
    let captureValues =
          [ 7
          , 61
          , 118
          , 203
          , 277
          , 349
          , 412
          , 508
          , 577
          , 643
          , 711
          , 806
          , 872
          , 931
          , 977
          , 1000
          ]
            :: [Int]
    withCapturedValues captureValues $ \capturePairs result ->
      matchConstrNode 1000 1 (capturedFieldsAtNode 1000 1 capturePairs) argumentName result

-- Match: Constr 1 [@c2,...]; c2 ~ Constr 2 [@c3,...];
--        c3 ~ Constr 3 [@c4,...]; c4 ~ Constr 4 [...]; d[2,15,...,51,62] ~ I @ => 266.
match_benchmark_constr_spine_front_d4_w16_c8_traditional :: Term
match_benchmark_constr_spine_front_d4_w16_c8_traditional =
  traditionalMatcher $ \argumentName -> do
    let captureValues = [2, 15, 21, 28, 40, 47, 51, 62] :: [Int]
        childPositions = [0, 0, 0] :: [Int]
    withCapturedValues captureValues $ \capturePairs result -> do
      let go nodeId remainingPositions scrutinee continuation = do
            let scalarFields = capturedFieldsAtNode 16 nodeId capturePairs
                childFields = case remainingPositions of
                  [] -> []
                  childPosition : laterPositions ->
                    [(childPosition, go (nodeId + 1) laterPositions)]
                fieldsToMatch = scalarFields <> childFields
            matchConstrNode
              16
              nodeId
              fieldsToMatch
              scrutinee
              continuation
      go 1 childPositions argumentName result

-- Match: Constr 1 [...,@c2,...]; c2 ~ Constr 2 [...,@c3,...];
--        c3 ~ Constr 3 [...,@c4,...]; c4 ~ Constr 4 [...]; d[2,15,...,51,62] ~ I @ => 266.
match_benchmark_constr_spine_middle_d4_w16_c8_traditional :: Term
match_benchmark_constr_spine_middle_d4_w16_c8_traditional =
  traditionalMatcher $ \argumentName -> do
    let captureValues = [2, 15, 21, 28, 40, 47, 51, 62] :: [Int]
        childPositions = [8, 8, 8] :: [Int]
    withCapturedValues captureValues $ \capturePairs result -> do
      let go nodeId remainingPositions scrutinee continuation = do
            let scalarFields = capturedFieldsAtNode 16 nodeId capturePairs
                childFields = case remainingPositions of
                  [] -> []
                  childPosition : laterPositions ->
                    [(childPosition, go (nodeId + 1) laterPositions)]
                fieldsToMatch = scalarFields <> childFields
            matchConstrNode
              16
              nodeId
              fieldsToMatch
              scrutinee
              continuation
      go 1 childPositions argumentName result

-- Match: Constr 1 [...,@c2]; c2 ~ Constr 2 [...,@c3];
--        c3 ~ Constr 3 [...,@c4]; c4 ~ Constr 4 [...]; d[2,15,...,51,62] ~ I @ => 266.
match_benchmark_constr_spine_last_d4_w16_c8_traditional :: Term
match_benchmark_constr_spine_last_d4_w16_c8_traditional =
  traditionalMatcher $ \argumentName -> do
    let captureValues = [2, 15, 21, 28, 40, 47, 51, 62] :: [Int]
        childPositions = [15, 15, 15] :: [Int]
    withCapturedValues captureValues $ \capturePairs result -> do
      let go nodeId remainingPositions scrutinee continuation = do
            let scalarFields = capturedFieldsAtNode 16 nodeId capturePairs
                childFields = case remainingPositions of
                  [] -> []
                  childPosition : laterPositions ->
                    [(childPosition, go (nodeId + 1) laterPositions)]
                fieldsToMatch = scalarFields <> childFields
            matchConstrNode
              16
              nodeId
              fieldsToMatch
              scrutinee
              continuation
      go 1 childPositions argumentName result

-- Match: Constr 1 [...,@c2,...]; c2 ~ Constr 2 [...,@c3,...];
--        c3 ~ Constr 3 [...,@c4,...]; c4 ~ Constr 4 [...]; d[2,15,...,51,62] ~ I @ => 266.
match_benchmark_constr_spine_irregular_d4_w16_c8_traditional :: Term
match_benchmark_constr_spine_irregular_d4_w16_c8_traditional =
  traditionalMatcher $ \argumentName -> do
    let captureValues = [2, 15, 21, 28, 40, 47, 51, 62] :: [Int]
        childPositions = [3, 12, 5] :: [Int]
    withCapturedValues captureValues $ \capturePairs result -> do
      let go nodeId remainingPositions scrutinee continuation = do
            let scalarFields = capturedFieldsAtNode 16 nodeId capturePairs
                childFields = case remainingPositions of
                  [] -> []
                  childPosition : laterPositions ->
                    [(childPosition, go (nodeId + 1) laterPositions)]
                fieldsToMatch = scalarFields <> childFields
            matchConstrNode
              16
              nodeId
              fieldsToMatch
              scrutinee
              continuation
      go 1 childPositions argumentName result

-- Match: Constr 1 [@c2,...]; c2 ~ Constr 2 [...,@c3,...]; ...;
--        c7 ~ Constr 7 [...,@c8,...]; c8 ~ Constr 8 [...]; d[4,12,...,52,61] ~ I @ => 257.
match_benchmark_constr_spine_irregular_d8_w8_c8_traditional :: Term
match_benchmark_constr_spine_irregular_d8_w8_c8_traditional =
  traditionalMatcher $ \argumentName -> do
    let captureValues = [4, 12, 20, 28, 36, 44, 52, 61] :: [Int]
        childPositions = [0, 4, 7, 2, 6, 1, 5] :: [Int]
    withCapturedValues captureValues $ \capturePairs result -> do
      let go nodeId remainingPositions scrutinee continuation = do
            let scalarFields = capturedFieldsAtNode 8 nodeId capturePairs
                childFields = case remainingPositions of
                  [] -> []
                  childPosition : laterPositions ->
                    [(childPosition, go (nodeId + 1) laterPositions)]
                fieldsToMatch = scalarFields <> childFields
            matchConstrNode
              8
              nodeId
              fieldsToMatch
              scrutinee
              continuation
      go 1 childPositions argumentName result

-- Match: Constr n [@next,_/@d]; next ~ Constr (n+1) [...] (n=1..63);
--        Constr 64 [_,@d]; d ~ I @ at n=[1,10,19,28,37,46,55,64] => 520.
match_benchmark_constr_spine_front_d64_w2_c8_traditional :: Term
match_benchmark_constr_spine_front_d64_w2_c8_traditional =
  traditionalMatcher $ \argumentName -> do
    let captureValues = [2, 20, 38, 56, 74, 92, 110, 128] :: [Int]
        childPositions = replicate 63 0
    withCapturedValues captureValues $ \capturePairs result -> do
      let go nodeId remainingPositions scrutinee continuation = do
            let scalarFields = capturedFieldsAtNode 2 nodeId capturePairs
                childFields = case remainingPositions of
                  [] -> []
                  childPosition : laterPositions ->
                    [(childPosition, go (nodeId + 1) laterPositions)]
                fieldsToMatch = scalarFields <> childFields
            matchConstrNode
              2
              nodeId
              fieldsToMatch
              scrutinee
              continuation
      go 1 childPositions argumentName result

-- Match: Constr n [@next,_/@d] / Constr n [_/@d,@next] (n=1..99);
--        Constr 100 [@d,_]; d ~ I @ at n=[1,12,23,...,89,100] => 1005.
match_benchmark_constr_spine_zigzag_d100_w2_c10_traditional :: Term
match_benchmark_constr_spine_zigzag_d100_w2_c10_traditional =
  traditionalMatcher $ \argumentName -> do
    let captureValues = [2, 23, 46, 67, 90, 111, 134, 155, 178, 199] :: [Int]
        childPositions = [if odd nodeId then 0 else 1 | nodeId <- [1 :: Int .. 99]]
    withCapturedValues captureValues $ \capturePairs result -> do
      let go nodeId remainingPositions scrutinee continuation = do
            let scalarFields = capturedFieldsAtNode 2 nodeId capturePairs
                childFields = case remainingPositions of
                  [] -> []
                  childPosition : laterPositions ->
                    [(childPosition, go (nodeId + 1) laterPositions)]
                fieldsToMatch = scalarFields <> childFields
            matchConstrNode
              2
              nodeId
              fieldsToMatch
              scrutinee
              continuation
      go 1 childPositions argumentName result

-- Match: Constr 1 [@c2,...]; c2 ~ Constr 2 [...,@c3,...]; ...;
--        child f=[0,50,99,20,80,10,60,30,90]; d(f16/f82) ~ I @ => 10000.
match_benchmark_constr_spine_stress_d10_w100_c20_traditional :: Term
match_benchmark_constr_spine_stress_d10_w100_c20_traditional =
  traditionalMatcher $ \argumentName -> do
    let captureValues =
          [ 17
          , 83
          , 117
          , 183
          , 217
          , 283
          , 317
          , 383
          , 417
          , 483
          , 517
          , 583
          , 617
          , 683
          , 717
          , 783
          , 817
          , 883
          , 917
          , 983
          ]
            :: [Int]
        childPositions = [0, 50, 99, 20, 80, 10, 60, 30, 90] :: [Int]
    withCapturedValues captureValues $ \capturePairs result -> do
      let go nodeId remainingPositions scrutinee continuation = do
            let scalarFields = capturedFieldsAtNode 100 nodeId capturePairs
                childFields = case remainingPositions of
                  [] -> []
                  childPosition : laterPositions ->
                    [(childPosition, go (nodeId + 1) laterPositions)]
                fieldsToMatch = scalarFields <> childFields
            matchConstrNode
              100
              nodeId
              fieldsToMatch
              scrutinee
              continuation
      go 1 childPositions argumentName result

-- Match: Constr 1 [@c2,...,@c5]; c2 ~ Constr 2 [@c3,...,@c4];
--        c5 ~ Constr 5 [@c6,...,@c7]; c3/c4/c6/c7 ~ Constr [...]; d* ~ I @ => 504.
match_benchmark_constr_binary_d3_w16_c8_traditional :: Term
match_benchmark_constr_binary_d3_w16_c8_traditional =
  traditionalMatcher $ \argumentName -> do
    let captureValues = [7, 21, 40, 59, 72, 88, 105, 112] :: [Int]
        children nodeId = case nodeId of
          1 -> [(0, 2), (15, 5)]
          2 -> [(0, 3), (15, 4)]
          5 -> [(0, 6), (15, 7)]
          _ -> []
    withCapturedValues captureValues $ \capturePairs result -> do
      let go nodeId scrutinee continuation = do
            let scalarFields = capturedFieldsAtNode 16 nodeId capturePairs
                childFields =
                  [(fieldIndex, go childId) | (fieldIndex, childId) <- children nodeId]
            matchConstrNode
              16
              nodeId
              (scalarFields <> childFields)
              scrutinee
              continuation
      go 1 argumentName result

-- Match: Constr 1 [@c2,...,@c6,...,@c10]; c2 ~ Constr 2 [@c3,...,@c4,...,@c5];
--        c6 ~ Constr 6 [@c7,...,@c8,...,@c9]; c10 ~ Constr 10 [@c11,...,@c12,...,@c13];
--        d[4,18,...,94,104] ~ I @ => 556.
match_benchmark_constr_ternary_d3_w8_c10_traditional :: Term
match_benchmark_constr_ternary_d3_w8_c10_traditional =
  traditionalMatcher $ \argumentName -> do
    let captureValues = [4, 18, 30, 40, 52, 61, 71, 82, 94, 104] :: [Int]
        children nodeId = case nodeId of
          1 -> [(0, 2), (4, 6), (7, 10)]
          2 -> [(0, 3), (4, 4), (7, 5)]
          6 -> [(0, 7), (4, 8), (7, 9)]
          10 -> [(0, 11), (4, 12), (7, 13)]
          _ -> []
    withCapturedValues captureValues $ \capturePairs result -> do
      let go nodeId scrutinee continuation = do
            let scalarFields = capturedFieldsAtNode 8 nodeId capturePairs
                childFields =
                  [(fieldIndex, go childId) | (fieldIndex, childId) <- children nodeId]
            matchConstrNode
              8
              nodeId
              (scalarFields <> childFields)
              scrutinee
              continuation
      go 1 argumentName result

-- Match: Constr 1 [@c2,@d2,@c7,_,_,@c12,_,@c17];
--        c2 ~ Constr 2 [@c3,@d10,@c4,_,_,@c5,_,@c6];
--        c7/c12 ~ Constr [@leaf,_,@leaf,@d,_,@leaf,_,@leaf];
--        c17 ~ Constr 17 [@c18,@d130,@c19,_,_,@c20,_,@c21]; d* ~ I @ => 1485.
match_benchmark_constr_quaternary_d3_w8_c17_traditional :: Term
match_benchmark_constr_quaternary_d3_w8_c17_traditional =
  traditionalMatcher $ \argumentName -> do
    let captureValues =
          [ 2
          , 10
          , 20
          , 31
          , 52
          , 58
          , 71
          , 77
          , 92
          , 98
          , 111
          , 117
          , 130
          , 140
          , 151
          , 157
          , 168
          ]
            :: [Int]
        children nodeId = case nodeId of
          1 -> [(0, 2), (2, 7), (5, 12), (7, 17)]
          2 -> [(0, 3), (2, 4), (5, 5), (7, 6)]
          7 -> [(0, 8), (2, 9), (5, 10), (7, 11)]
          12 -> [(0, 13), (2, 14), (5, 15), (7, 16)]
          17 -> [(0, 18), (2, 19), (5, 20), (7, 21)]
          _ -> []
    withCapturedValues captureValues $ \capturePairs result -> do
      let go nodeId scrutinee continuation = do
            let scalarFields = capturedFieldsAtNode 8 nodeId capturePairs
                childFields =
                  [(fieldIndex, go childId) | (fieldIndex, childId) <- children nodeId]
            matchConstrNode
              8
              nodeId
              (scalarFields <> childFields)
              scrutinee
              continuation
      go 1 argumentName result

-- Match: Constr 1 [@d1,_,@c2,...,@c7,_]; c2 ~ Constr 2 [@c3,...]; ...;
--        c7 ~ Constr 7 [...,@c8,...]; c8 ~ Constr 8 [_,@c9,...]; d* ~ I @ => 389.
match_benchmark_constr_rootfork2_d6_w12_c8_traditional :: Term
match_benchmark_constr_rootfork2_d6_w12_c8_traditional =
  traditionalMatcher $ \argumentName -> do
    let captureValues = [1, 14, 27, 40, 54, 71, 74, 108] :: [Int]
        children nodeId = case nodeId of
          1 -> [(2, 2), (10, 7)]
          2 -> [(0, 3)]
          3 -> [(7, 4)]
          4 -> [(11, 5)]
          5 -> [(4, 6)]
          7 -> [(9, 8)]
          8 -> [(1, 9)]
          _ -> []
    withCapturedValues captureValues $ \capturePairs result -> do
      let go nodeId scrutinee continuation = do
            let scalarFields = capturedFieldsAtNode 12 nodeId capturePairs
                childFields =
                  [(fieldIndex, go childId) | (fieldIndex, childId) <- children nodeId]
            matchConstrNode
              12
              nodeId
              (scalarFields <> childFields)
              scrutinee
              continuation
      go 1 argumentName result

-- Match: Constr 1 [@c2,...,@c6,...,@c9]; c2 ~ Constr 2 [...,@c3,...] ~ ...;
--        c6 ~ Constr 6 [...,@c7,...] ~ ...; c9 ~ Constr 9 [...,@c10,...]; d* ~ I @ => 469.
match_benchmark_constr_rootfork3_d5_w10_c9_traditional :: Term
match_benchmark_constr_rootfork3_d5_w10_c9_traditional =
  traditionalMatcher $ \argumentName -> do
    let captureValues = [5, 11, 27, 50, 52, 68, 74, 83, 99] :: [Int]
        children nodeId = case nodeId of
          1 -> [(0, 2), (5, 6), (9, 9)]
          2 -> [(2, 3)]
          3 -> [(8, 4)]
          4 -> [(4, 5)]
          6 -> [(7, 7)]
          7 -> [(1, 8)]
          9 -> [(5, 10)]
          _ -> []
    withCapturedValues captureValues $ \capturePairs result -> do
      let go nodeId scrutinee continuation = do
            let scalarFields = capturedFieldsAtNode 10 nodeId capturePairs
                childFields =
                  [(fieldIndex, go childId) | (fieldIndex, childId) <- children nodeId]
            matchConstrNode
              10
              nodeId
              (scalarFields <> childFields)
              scrutinee
              continuation
      go 1 argumentName result

-- Match: Constr 1 [@c2,_,@c5,...,@c7,_,@c8]; c2 ~ Constr 2 [...,@c3,...] ~ ...;
--        c5 ~ Constr 5 [_,@c6,...]; c6/c7/c8 ~ Constr [...]; d* ~ I @ => 261.
match_benchmark_constr_rootfork4_d4_w8_c8_traditional :: Term
match_benchmark_constr_rootfork4_d4_w8_c8_traditional =
  traditionalMatcher $ \argumentName -> do
    let captureValues = [4, 9, 21, 32, 35, 47, 51, 62] :: [Int]
        children nodeId = case nodeId of
          1 -> [(0, 2), (2, 5), (5, 7), (7, 8)]
          2 -> [(3, 3)]
          3 -> [(7, 4)]
          5 -> [(1, 6)]
          _ -> []
    withCapturedValues captureValues $ \capturePairs result -> do
      let go nodeId scrutinee continuation = do
            let scalarFields = capturedFieldsAtNode 8 nodeId capturePairs
                childFields =
                  [(fieldIndex, go childId) | (fieldIndex, childId) <- children nodeId]
            matchConstrNode
              8
              nodeId
              (scalarFields <> childFields)
              scrutinee
              continuation
      go 1 argumentName result

-- Match: Constr 1 [@c2,_,_,_,_,_,_,@c129];
--        c2 ~ Constr 2 [_,_,@c3,_,_,@c66,_,_]; ...;
--        leaf tags [8,15,...,244,251] bind f3; d* ~ I @ => 33024.
match_benchmark_constr_binary_stress_d8_w8_c32_traditional :: Term
match_benchmark_constr_binary_stress_d8_w8_c32_traditional =
  traditionalMatcher $ \argumentName -> do
    let captureValues =
          [ 60
          , 116
          , 180
          , 236
          , 308
          , 364
          , 428
          , 484
          , 564
          , 620
          , 684
          , 740
          , 812
          , 868
          , 932
          , 988
          , 1076
          , 1132
          , 1196
          , 1252
          , 1324
          , 1380
          , 1444
          , 1500
          , 1580
          , 1636
          , 1700
          , 1756
          , 1828
          , 1884
          , 1948
          , 2004
          ]
            :: [Int]

        children :: Int -> Int -> Int -> [(Int, Int)]
        children treeLevel remainingHeight nodeId
          | remainingHeight <= 1 = []
          | otherwise =
              let (leftField, rightField) =
                    if odd treeLevel
                      then (0, 7)
                      else (2, 5)
                  rightChildOffset = 2 ^ (remainingHeight - 1)
               in [ (leftField, nodeId + 1)
                  , (rightField, nodeId + rightChildOffset)
                  ]
    withCapturedValues captureValues $ \capturePairs result -> do
      let go treeLevel remainingHeight nodeId scrutinee continuation = do
            let scalarFields = capturedFieldsAtNode 8 nodeId capturePairs
                childFields =
                  [ ( fieldIndex
                    , go (treeLevel + 1) (remainingHeight - 1) childId
                    )
                  | (fieldIndex, childId) <- children treeLevel remainingHeight nodeId
                  ]
            matchConstrNode
              8
              nodeId
              (scalarFields <> childFields)
              scrutinee
              continuation
      go 1 8 1 argumentName result

-- Match: Constr 1 [@c2,_,_,_,_,_,_,@d] ~ ... ~ Constr 16 [...];
--        d ~ {B @ | I @}; captured integers => 544.
match_benchmark_constr_alt_spine_d16_w8_c8_traditional :: Term
match_benchmark_constr_alt_spine_d16_w8_c8_traditional =
  traditionalMatcher $ \argumentName -> do
    let captureValues = [8, 28, 44, 60, 76, 92, 108, 128] :: [Int]
        childPositions = [0, 7, 2, 5, 0, 7, 2, 5, 0, 7, 2, 5, 0, 7, 2] :: [Int]
    withCapturedValues captureValues $ \capturePairs result -> do
      let go nodeId remainingPositions scrutinee continuation = do
            let captureField captureValue =
                  if captureValue == 8
                    then captureIntegerAlternatives
                    else captureIntegerField
                scalarFields =
                  capturedFieldsAtNodeWith captureField 8 nodeId capturePairs
                childFields = case remainingPositions of
                  [] -> []
                  childPosition : laterPositions ->
                    [(childPosition, go (nodeId + 1) laterPositions)]
            matchConstrNode
              8
              nodeId
              (scalarFields <> childFields)
              scrutinee
              continuation
      go 1 childPositions argumentName result

-- Match: Constr 1 [@c2,...,@c6,...,@c9] ~ ... ~ Constr 9 [...,@c10,...,@d];
--        d ~ {B @ | I @}; captured integers => 469.
match_benchmark_constr_alt_rootfork3_d5_w10_c9_traditional :: Term
match_benchmark_constr_alt_rootfork3_d5_w10_c9_traditional =
  traditionalMatcher $ \argumentName -> do
    let captureValues = [11, 14, 27, 50, 52, 68, 74, 83, 90] :: [Int]
        children nodeId = case nodeId of
          1 -> [(0, 2), (5, 6), (9, 9)]
          2 -> [(2, 3)]
          3 -> [(8, 4)]
          4 -> [(4, 5)]
          6 -> [(7, 7)]
          7 -> [(1, 8)]
          9 -> [(5, 10)]
          _ -> []
    withCapturedValues captureValues $ \capturePairs result -> do
      let go nodeId scrutinee continuation = do
            let captureField captureValue =
                  if captureValue == 90
                    then captureIntegerAlternatives
                    else captureIntegerField
                scalarFields =
                  capturedFieldsAtNodeWith captureField 10 nodeId capturePairs
                childFields =
                  [(fieldIndex, go childId) | (fieldIndex, childId) <- children nodeId]
            matchConstrNode
              10
              nodeId
              (scalarFields <> childFields)
              scrutinee
              continuation
      go 1 argumentName result

-- Match: Constr 1 [@c2,_,_,_,_,_,_,@c129] ~ ... ~ Constr 129 [...,@d];
--        d ~ {B @ | I @}; captured integers => 33024.
match_benchmark_constr_alt_binary_d8_w8_c32_traditional :: Term
match_benchmark_constr_alt_binary_d8_w8_c32_traditional =
  traditionalMatcher $ \argumentName -> do
    let captureValues =
          [ 60
          , 116
          , 180
          , 236
          , 308
          , 364
          , 428
          , 484
          , 564
          , 620
          , 684
          , 740
          , 812
          , 868
          , 932
          , 1032
          , 1076
          , 1132
          , 1196
          , 1252
          , 1324
          , 1380
          , 1444
          , 1500
          , 1580
          , 1636
          , 1700
          , 1756
          , 1828
          , 1884
          , 1948
          , 1960
          ]
            :: [Int]

        children :: Int -> Int -> Int -> [(Int, Int)]
        children treeLevel remainingHeight nodeId
          | remainingHeight <= 1 = []
          | otherwise =
              let (leftField, rightField) =
                    if odd treeLevel
                      then (0, 7)
                      else (2, 5)
                  rightChildOffset = 2 ^ (remainingHeight - 1)
               in [ (leftField, nodeId + 1)
                  , (rightField, nodeId + rightChildOffset)
                  ]
    withCapturedValues captureValues $ \capturePairs result -> do
      let go treeLevel remainingHeight nodeId scrutinee continuation = do
            let captureField captureValue =
                  if captureValue == 1032
                    then captureIntegerAlternatives
                    else captureIntegerField
                scalarFields =
                  capturedFieldsAtNodeWith captureField 8 nodeId capturePairs
                childFields =
                  [ ( fieldIndex
                    , go (treeLevel + 1) (remainingHeight - 1) childId
                    )
                  | (fieldIndex, childId) <- children treeLevel remainingHeight nodeId
                  ]
            matchConstrNode
              8
              nodeId
              (scalarFields <> childFields)
              scrutinee
              continuation
      go 1 8 1 argumentName result
