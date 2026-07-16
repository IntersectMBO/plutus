{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications #-}

module PlutusBenchmark.Matching where

import Control.Monad (forM, replicateM)
import Control.Monad.Except
import Data.ByteString qualified as BS
import Data.Either
import Data.Int (Int64)
import Data.List (foldl')
import Data.Vector qualified as V
import Data.Word (Word64)
import PlutusBenchmark.Common (Term)
import PlutusCore (DefaultUni, freshName, runQuote)
import PlutusCore qualified as PLC
import PlutusCore.Data qualified as PLCData
import PlutusCore.Default
  ( DefaultBuiltinPattern (..)
  , DefaultFun
  )
import PlutusCore.MkPlc
import PlutusCore.Name.Unique (Name (..), Unique (..))
import UntypedPlutusCore qualified as UPLC

debruijnTermUnsafe
  :: UPLC.Term UPLC.Name uni fun pat ann
  -> UPLC.Term UPLC.NamedDeBruijn uni fun pat ann
debruijnTermUnsafe =
  fromRight (Prelude.error "debruijnTermUnsafe")
    . runExcept @UPLC.FreeVariableError
    . UPLC.deBruijnTerm

-- | Repeated minimal matches. This isolates the fixed fused Match/selection overhead.
matchingWildcard :: Integer -> Term
matchingWildcard i =
  foldr
    ( \_ handler ->
        UPLC.Match () (mkConstant @Integer () 0) $
          V.singleton (DefaultPatternWildcard, handler)
    )
    (mkConstant @Integer () 0)
    [1 .. i]

-- | Repeated one-word integer literal matches, charged incrementally as the matcher traverses them.
matchingInteger :: Integer -> Term
matchingInteger i =
  foldr
    ( \_ handler ->
        UPLC.Match () (mkConstant @Integer () 0) $
          V.singleton
            ( DefaultPatternInteger 0
            , handler
            )
    )
    (mkConstant @Integer () 0)
    [1 .. i]

-- | One wide exact-list match, exercising the fused wildcard streaming traversal.
matchingExactList :: Integer -> Term
matchingExactList i =
  let width = fromIntegral i
   in UPLC.Match
        ()
        (mkConstant @[Integer] () $ replicate width 0)
        ( V.singleton
            ( DefaultPatternList $ V.replicate width DefaultPatternWildcard
            , mkConstant @Integer () 0
            )
        )

-- | A wide successful match in which every field is captured and applied to a handler.
matchingCaptureList :: Integer -> Term
matchingCaptureList i =
  let width = fromIntegral i
      binder = UPLC.NamedDeBruijn "capture" (UPLC.Index 0)
      handler = foldr (const $ UPLC.LamAbs () binder) (mkConstant @Integer () 0) [1 .. i]
   in UPLC.Match
        ()
        (mkConstant @[Integer] () $ replicate width 0)
        ( V.singleton
            ( DefaultPatternList $ V.replicate width DefaultPatternCapture
            , handler
            )
        )

-- | A long ordered chain of late-mismatching scalar alternatives followed by a wildcard.
matchingAlternatives :: Integer -> Term
matchingAlternatives i =
  let width = fromIntegral i
      miss =
        ( DefaultPatternInteger 1
        , mkConstant @Integer () 1
        )
   in UPLC.Match
        ()
        (mkConstant @Integer () 0)
        ( V.replicate width miss
            <> V.singleton (DefaultPatternWildcard, mkConstant @Integer () 0)
        )

{-| Four equivalent successful checks of a @Data.Constr 42@ value with exactly the requested
number of fields. The first result uses @UnConstrData@ directly, the second first checks the Data
constructor with @ChooseData@, and the final two use 'Match' with wildcard and capture fields.

Keeping the terms together here makes the Criterion comparison use the same tag, field values,
success result, fallback result, and exact-arity traversal at every width. -}
dataConstrMatchComparison :: Integer -> (Term, Term, Term, Term)
dataConstrMatchComparison requestedWidth =
  ( debruijnTermUnsafe directUnConstr
  , debruijnTermUnsafe checkedUnConstr
  , debruijnTermUnsafe wildcardMatch
  , debruijnTermUnsafe captureMatch
  )
  where
    width = max 0 $ fromIntegral requestedWidth
    scrutinee = mkConstant @PLCData.Data () . PLCData.Constr 42 $ replicate width (PLCData.I 0)
    success = mkConstant @Integer () 1
    fallback = mkConstant @Integer () 0
    tagName = Name "tag" (Unique 1000)
    fieldsName = Name "fields" (Unique 1001)
    fieldName index = Name "field" . Unique $ 2000 + 2 * index
    restName index = Name "rest" . Unique $ 2001 + 2 * index
    captureName index = Name "capture" . Unique $ 3000 + index

    exactFields index fields
      | index == width =
          UPLC.Case
            ()
            fields
            ( V.fromList
                [ UPLC.LamAbs () (fieldName index) $
                    UPLC.LamAbs () (restName index) fallback
                , success
                ]
            )
      | otherwise =
          UPLC.Case
            ()
            fields
            ( V.fromList
                [ UPLC.LamAbs () (fieldName index) $
                    UPLC.LamAbs () (restName index) $
                      exactFields (index + 1) (UPLC.Var () $ restName index)
                , fallback
                ]
            )

    tagMatches =
      mkIterAppNoAnn
        (UPLC.Builtin () PLC.EqualsInteger)
        [UPLC.Var () tagName, mkConstant @Integer () 42]
    directUnConstr =
      UPLC.Case
        ()
        (mkIterAppNoAnn (UPLC.Builtin () PLC.UnConstrData) [scrutinee])
        ( V.singleton $
            UPLC.LamAbs () tagName $
              UPLC.LamAbs () fieldsName $
                UPLC.Case
                  ()
                  tagMatches
                  ( V.fromList
                      [ fallback
                      , exactFields 0 (UPLC.Var () fieldsName)
                      ]
                  )
        )
    checkedUnConstr =
      UPLC.Force () $
        mkIterAppNoAnn
          (UPLC.Force () $ UPLC.Builtin () PLC.ChooseData)
          [ scrutinee
          , UPLC.Delay () directUnConstr
          , UPLC.Delay () fallback
          , UPLC.Delay () fallback
          , UPLC.Delay () fallback
          , UPLC.Delay () fallback
          ]
    wildcardMatch =
      UPLC.Match
        ()
        scrutinee
        ( V.fromList
            [
              ( DefaultPatternDataConstr 42 $ V.replicate width DefaultPatternWildcard
              , success
              )
            , (DefaultPatternWildcard, fallback)
            ]
        )
    captureHandler =
      foldr (UPLC.LamAbs () . captureName) success [0 .. width - 1]
    captureMatch =
      UPLC.Match
        ()
        scrutinee
        ( V.fromList
            [
              ( DefaultPatternDataConstr 42 $ V.replicate width DefaultPatternCapture
              , captureHandler
              )
            , (DefaultPatternWildcard, fallback)
            ]
        )

type NamedTerm = UPLC.Term UPLC.Name DefaultUni DefaultFun DefaultBuiltinPattern ()

{-| Repeatedly execute a match through a call-by-value fixed-point combinator.

The scrutinee is evaluated once outside the recursive loop and captured in its environment. Hence
the timed recursion repeatedly traverses the same pattern and reached value rather than rebuilding
either of them. The integer paired with each alternative is the number of captures its handler
accepts before recurring.

This is the call-by-value Z combinator rather than Y: the recursive self-application is suspended
under an extra lambda, so constructing the fixed point itself does not diverge. -}
loopingMatch
  :: NamedTerm
  -> [(DefaultBuiltinPattern, Int)]
  -> Term
loopingMatch scrutinee branchShapes = debruijnTermUnsafe $ runQuote $ do
  scrutineeName <- freshName "scrutinee"
  functionName <- freshName "function"
  leftSelfName <- freshName "left-self"
  leftArgumentName <- freshName "left-argument"
  rightSelfName <- freshName "right-self"
  rightArgumentName <- freshName "right-argument"
  loopName <- freshName "loop"
  loopArgumentName <- freshName "loop-argument"
  let unit = mkConstant @() () ()
      recur = UPLC.Apply () (UPLC.Var () loopName) unit
      suspendedSelf selfName argumentName =
        UPLC.LamAbs () argumentName $
          UPLC.Apply
            ()
            (UPLC.Apply () (UPLC.Var () selfName) (UPLC.Var () selfName))
            (UPLC.Var () argumentName)
      fixHalf selfName argumentName =
        UPLC.LamAbs () selfName $
          UPLC.Apply
            ()
            (UPLC.Var () functionName)
            (suspendedSelf selfName argumentName)
      callByValueFix =
        UPLC.LamAbs () functionName $
          UPLC.Apply
            ()
            (fixHalf leftSelfName leftArgumentName)
            (fixHalf rightSelfName rightArgumentName)
  alternatives <-
    forM branchShapes $ \(pat, captureCount) -> do
      captureNames <- replicateM captureCount $ freshName "capture"
      pure (pat, foldr (UPLC.LamAbs ()) recur captureNames)
  let loopBody =
        UPLC.Match
          ()
          (UPLC.Var () scrutineeName)
          (V.fromList alternatives)
      loopFunction =
        UPLC.LamAbs () loopName $
          UPLC.LamAbs () loopArgumentName loopBody
      runLoop =
        UPLC.Apply
          ()
          (UPLC.Apply () callByValueFix loopFunction)
          unit
  pure $ UPLC.Apply () (UPLC.LamAbs () scrutineeName runLoop) scrutinee

-- | Repeated successful traversal of a wide exact list pattern.
matchingFixpointExactList :: Integer -> Term
matchingFixpointExactList requestedWidth =
  let width = max 1 $ fromIntegral requestedWidth
      pat = DefaultPatternList $ V.replicate width DefaultPatternWildcard
   in loopingMatch
        (mkConstant @[Integer] () $ replicate width 0)
        [(pat, 0)]

-- | Repeated traversal to a mismatch at the final list element, followed by a wildcard fallback.
matchingFixpointLateListMismatch :: Integer -> Term
matchingFixpointLateListMismatch requestedWidth =
  let width = max 1 $ fromIntegral requestedWidth
      finalMismatch = DefaultPatternInteger 1
      children = V.replicate (width - 1) DefaultPatternWildcard `V.snoc` finalMismatch
      pat = DefaultPatternList children
   in loopingMatch
        (mkConstant @[Integer] () $ replicate width 0)
        [(pat, 0), (DefaultPatternWildcard, 0)]

{-| Repeated late list mismatch after accumulating a long capture prefix. The failed alternative's
captures must be abandoned without either reversing them or applying its handler. -}
matchingFixpointAbandonedCaptures :: Integer -> Term
matchingFixpointAbandonedCaptures requestedWidth =
  let width = max 1 $ fromIntegral requestedWidth
      finalMismatch = DefaultPatternInteger 1
      children = V.replicate (width - 1) DefaultPatternCapture `V.snoc` finalMismatch
      pat = DefaultPatternList children
   in loopingMatch
        (mkConstant @[Integer] () $ replicate width 0)
        [(pat, width - 1), (DefaultPatternWildcard, 0)]

-- | Repeated exact-list arity mismatch after consuming the entire common prefix.
matchingFixpointListArityMismatch :: Integer -> Integer -> Term
matchingFixpointListArityMismatch requestedPatternWidth requestedDelta =
  let patternWidth = max 1 $ fromIntegral requestedPatternWidth
      scrutineeWidth = max 0 $ patternWidth + fromIntegral requestedDelta
      pat = DefaultPatternList $ V.replicate patternWidth DefaultPatternWildcard
   in loopingMatch
        (mkConstant @[Integer] () $ replicate scrutineeWidth 0)
        [(pat, 0), (DefaultPatternWildcard, 0)]

-- | Repeated successful wide match in which every field is captured and applied to the handler.
matchingFixpointCaptureList :: Integer -> Term
matchingFixpointCaptureList requestedWidth =
  let width = max 1 $ fromIntegral requestedWidth
      pat = DefaultPatternList $ V.replicate width DefaultPatternCapture
   in loopingMatch
        (mkConstant @[Integer] () $ replicate width 0)
        [(pat, width)]

-- | Repeated ordered traversal of many scalar alternatives before taking a wildcard fallback.
matchingFixpointAlternatives :: Integer -> Term
matchingFixpointAlternatives requestedWidth =
  let width = max 1 $ fromIntegral requestedWidth
      miss = DefaultPatternInteger 1
   in loopingMatch
        (mkConstant @Integer () 0)
        (replicate width (miss, 0) <> [(DefaultPatternWildcard, 0)])

-- | Repeated alternatives that each traverse a substantial list prefix before their late failure.
matchingFixpointWideAlternatives :: Integer -> Integer -> Term
matchingFixpointWideAlternatives requestedAlternatives requestedWidth =
  let alternativeCount = max 1 $ fromIntegral requestedAlternatives
      width = max 1 $ fromIntegral requestedWidth
      finalMismatch = DefaultPatternInteger 1
      children = V.replicate (width - 1) DefaultPatternWildcard `V.snoc` finalMismatch
      miss = DefaultPatternList children
   in loopingMatch
        (mkConstant @[Integer] () $ replicate width 0)
        (replicate alternativeCount (miss, 0) <> [(DefaultPatternWildcard, 0)])

-- | Repeated traversal of a deeply nested built-in 'Data' pattern.
matchingFixpointNestedData :: Integer -> Term
matchingFixpointNestedData requestedDepth =
  let depth = max 1 (fromIntegral requestedDepth) :: Int
      pat =
        foldl'
          (\child _ -> DefaultPatternDataList $ V.singleton child)
          DefaultPatternWildcard
          [1 .. depth]
      value = foldl' (\child _ -> PLCData.List [child]) (PLCData.I 0) [1 .. depth]
   in loopingMatch (mkConstant @PLCData.Data () value) [(pat, 0)]

-- | Repeated traversal of a deeply nested built-in @Data.Constr 0 [child]@ pattern and value.
matchingFixpointNestedDataConstr :: Integer -> Term
matchingFixpointNestedDataConstr requestedDepth =
  let depth = max 1 (fromIntegral requestedDepth) :: Int
      pat =
        foldl'
          (\child _ -> DefaultPatternDataConstr 0 $ V.singleton child)
          DefaultPatternWildcard
          [1 .. depth]
      value = foldl' (\child _ -> PLCData.Constr 0 [child]) (PLCData.I 0) [1 .. depth]
   in loopingMatch (mkConstant @PLCData.Data () value) [(pat, 0)]

-- | Repeated streaming traversal of all fields in a wide 'Data.Constr'.
matchingFixpointWideDataConstr :: Integer -> Term
matchingFixpointWideDataConstr requestedWidth =
  let width = max 1 $ fromIntegral requestedWidth
      pat = DefaultPatternDataConstr 0 $ V.replicate width DefaultPatternWildcard
      value = PLCData.Constr 0 $ replicate width (PLCData.I 0)
   in loopingMatch (mkConstant @PLCData.Data () value) [(pat, 0)]

-- | Repeated successful match of the smallest 'Data.Constr' pattern and value.
matchingFixpointEmptyDataConstr :: Term
matchingFixpointEmptyDataConstr =
  let pat = DefaultPatternDataConstr 0 V.empty
   in loopingMatch (mkConstant @PLCData.Data () $ PLCData.Constr 0 []) [(pat, 0)]

-- | Repeated equality of an immediate 'Integer', the cheapest scalar representation.
matchingFixpointSmallInteger :: Term
matchingFixpointSmallInteger =
  let pat = DefaultPatternInteger 0
   in loopingMatch (mkConstant @Integer () 0) [(pat, 0)]

-- | Repeated equality of distinct one-byte payloads, covering the shortest bytestring scalar path.
matchingFixpointSmallByteString :: Term
matchingFixpointSmallByteString =
  let expected = BS.singleton 0x5A
      actual = BS.copy expected
      pat = DefaultPatternByteString expected
   in loopingMatch (mkConstant @BS.ByteString () actual) [(pat, 0)]

-- | Repeated equality at the upper boundary of a signed integer pattern.
matchingFixpointMaxInteger :: Term
matchingFixpointMaxInteger =
  let expected = maxBound :: Int64
      actual = toInteger expected
      pat = DefaultPatternInteger expected
   in loopingMatch (mkConstant @Integer () actual) [(pat, 0)]

-- | Repeated equality of separately allocated large bytestring pattern and scrutinee payloads.
matchingFixpointLargeByteString :: Integer -> Term
matchingFixpointLargeByteString requestedWords =
  let words64 = max 1 $ fromIntegral requestedWords
      expected = BS.replicate (8 * words64) 0x5A
      actual = BS.copy expected
      pat = DefaultPatternByteString expected
   in loopingMatch (mkConstant @BS.ByteString () actual) [(pat, 0)]

-- | Repeated equality at the upper boundary of a 'Data.Constr' pattern tag.
matchingFixpointMaxDataTag :: Term
matchingFixpointMaxDataTag =
  let expected = maxBound :: Word64
      actual = toInteger expected
      pat = DefaultPatternDataConstr expected V.empty
   in loopingMatch (mkConstant @PLCData.Data () $ PLCData.Constr actual []) [(pat, 0)]
