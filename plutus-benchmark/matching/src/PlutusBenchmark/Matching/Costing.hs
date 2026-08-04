{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications #-}

{-| Production-matcher workloads for calibrating the four CEK costs used by @UPLC.Match@.

Every workload has a paired control and a semantic design row. The Criterion driver collapses the
design row onto the production 'BMatch', 'BPattern', 'BStructural', and 'BMatchNext' topology and
checks those exact dynamic counts before measuring anything. Keeping the semantic components here
also exposes work that the four-kind topology necessarily aliases. The two ordinary CEK categories
used by the direct calibration equations, 'Case' and 'LamAbs', are counted as well. -}
module PlutusBenchmark.Matching.Costing
  ( CostingCase (..)
  , MatchStepCounts (..)
  , Unit (..)
  , calibrationCases
  , calibrationSizes
  )
where

import Data.ByteString qualified as BS
import Data.Vector qualified as Vector
import PlutusBenchmark.Common (Term)
import PlutusBenchmark.Matching qualified as Matching
import PlutusCore.Data qualified as PLC
import PlutusCore.Default
  ( DefaultBuiltinPattern (..)
  , DefaultPatternFieldEnd (..)
  )
import PlutusCore.MkPlc (mkConstant)
import UntypedPlutusCore qualified as UPLC

-- | Semantic counts used to derive the exact four-kind benchmark invariant and calibration row.
data MatchStepCounts = MatchStepCounts
  { matchCount :: !Integer
  , captureCount :: !Integer
  , captureFinishCount :: !Integer
  , byteStringBaseCount :: !Integer
  , byteStringWordCount :: !Integer
  , endpointCount :: !Integer
  , containerCount :: !Integer
  , pairCount :: !Integer
  , structuralCount :: !Integer
  , structuralDispatchCount :: !Integer
  , nextCount :: !Integer
  , caseCount :: !Integer
  , lamCount :: !Integer
  }
  deriving stock (Eq, Show)

data CostingCase = CostingCase
  { costingCaseName :: !String
  , costingCaseUnits :: !Integer
  , costingCaseExpected :: !MatchStepCounts
  , -- Keep only a recipe here. Criterion constructs and retains the term for the benchmark that is
    -- currently running; keeping every fully forced calibration term alive at once materially
    -- changes the cache and GC behaviour of otherwise identical controls.
    costingCaseTerm :: !(Unit -> Term)
  }

data Unit = Unit

-- Include the requested 100-step point, a smaller noise check, and a larger slope check.
calibrationSizes :: [Integer]
calibrationSizes = [10, 100, 1000]

calibrationCases :: [CostingCase]
calibrationCases = calibrationSizes >>= casesAtSize

casesAtSize :: Integer -> [CostingCase]
casesAtSize units =
  concat
    [ paired
        "match-wildcard"
        units
        (defer caseChain units)
        (caseOnly units)
        (defer matchWildcardBoolChain units)
        (matchOnly units)
    , paired
        "match-integer"
        units
        (defer (uncurry caseChainOn) (units, mkConstant @Integer () 0))
        (caseOnly units)
        ( defer
            buildMatchChainOn
            (units, mkConstant @Integer () 0, DefaultPatternInteger 0, id)
        )
        (matchOnly units)
    , paired
        "match-bool"
        units
        (defer caseChain units)
        (caseOnly units)
        (defer matchBoolChain units)
        (matchOnly units)
    , paired
        "match-unit"
        units
        (defer (uncurry caseChainOn) (units, mkConstant @() () ()))
        (caseOnly units)
        ( defer
            buildMatchChainOn
            (units, mkConstant @() () (), DefaultPatternUnit, id)
        )
        (matchOnly units)
    , paired
        "bytestring-empty"
        units
        (defer (uncurry byteStringEmptyChain) (units, DefaultPatternWildcard))
        (matchOnly units)
        ( defer
            (uncurry byteStringEmptyChain)
            (units, DefaultPatternByteString BS.empty)
        )
        ((matchOnly units) {byteStringBaseCount = units})
    , paired
        "bytestring-word"
        units
        (defer byteStringWordsMatch 1)
        ( (matchOnly 1)
            { byteStringBaseCount = 1
            , byteStringWordCount = 1
            }
        )
        (defer byteStringWordsMatch $ units + 1)
        ( (matchOnly 1)
            { byteStringBaseCount = 1
            , byteStringWordCount = units + 1
            }
        )
    , paired
        "capture-success"
        units
        (defer (uncurry exactIntegerListMatch) (units, DefaultPatternWildcard))
        ( (matchOnly 1)
            { containerCount = 1
            , structuralCount = units
            , structuralDispatchCount = 1
            }
        )
        (defer Matching.matchingCaptureList units)
        ( (matchOnly 1)
            { captureCount = units
            , captureFinishCount = 1
            , containerCount = 1
            , structuralCount = units
            , structuralDispatchCount = 1
            , lamCount = units
            }
        )
    , paired
        "capture-abandoned"
        units
        (defer (uncurry abandonedCaptureMatch) (units, DefaultPatternWildcard))
        (abandonedCaptureCounts units 0)
        (defer (uncurry abandonedCaptureMatch) (units, DefaultPatternCapture))
        (abandonedCaptureCounts units units)
    , paired
        "endpoint"
        units
        ( defer
            listPatternChain
            ( units
            , mkConstant @[Integer] () []
            , DefaultPatternFieldsExact
            , Vector.empty
            )
        )
        ((matchOnly units) {containerCount = units})
        ( defer
            listPatternChain
            ( units
            , mkConstant @[Integer] () []
            , DefaultPatternFieldsPrefixWildcard
            , Vector.empty
            )
        )
        ( (matchOnly units)
            { endpointCount = units
            , containerCount = units
            }
        )
    , paired
        "structural-wildcard"
        units
        (defer (uncurry exactIntegerListMatch) (0, DefaultPatternWildcard))
        ((matchOnly 1) {containerCount = 1})
        (defer (uncurry exactIntegerListMatch) (units, DefaultPatternWildcard))
        ( (matchOnly 1)
            { containerCount = 1
            , structuralCount = units
            , structuralDispatchCount = 1
            }
        )
    , paired
        "structural-integer"
        units
        (defer (uncurry exactIntegerListMatch) (0, DefaultPatternInteger 0))
        ((matchOnly 1) {containerCount = 1})
        (defer (uncurry exactIntegerListMatch) (units, DefaultPatternInteger 0))
        ( (matchOnly 1)
            { containerCount = 1
            , structuralCount = units
            , structuralDispatchCount = units
            }
        )
    , paired
        "structural-bool"
        units
        (defer exactBoolListMatch 0)
        ((matchOnly 1) {containerCount = 1})
        (defer exactBoolListMatch units)
        ( (matchOnly 1)
            { containerCount = 1
            , structuralCount = units
            , structuralDispatchCount = units
            }
        )
    , paired
        "structural-unit"
        units
        (defer exactUnitListMatch 0)
        ((matchOnly 1) {containerCount = 1})
        (defer exactUnitListMatch units)
        ( (matchOnly 1)
            { containerCount = 1
            , structuralCount = units
            , structuralDispatchCount = units
            }
        )
    , repeatedStructuralCases units
    , paired
        "next-integer"
        units
        (defer wildcardMatch $ mkConstant @Integer () 0)
        (matchOnly 1)
        ( defer
            rejectedAlternatives
            ( units
            , mkConstant @Integer () 0
            , DefaultPatternInteger 1
            )
        )
        ((matchOnly 1) {nextCount = units})
    , paired
        "next-bool"
        units
        (defer wildcardMatch $ mkConstant @Bool () False)
        (matchOnly 1)
        ( defer
            rejectedAlternatives
            ( units
            , mkConstant @Bool () False
            , DefaultPatternBool True
            )
        )
        ((matchOnly 1) {nextCount = units})
    , paired
        "next-unit"
        units
        (defer wildcardMatch $ mkConstant @Bool () False)
        (matchOnly 1)
        ( defer
            rejectedAlternatives
            ( units
            , mkConstant @Bool () False
            , DefaultPatternUnit
            )
        )
        ((matchOnly 1) {nextCount = units})
    , paired
        "next-data-i"
        units
        (defer wildcardMatch $ mkConstant @PLC.Data () $ PLC.B BS.empty)
        (matchOnly 1)
        ( defer
            rejectedAlternatives
            ( units
            , mkConstant @PLC.Data () $ PLC.B BS.empty
            , DefaultPatternDataI DefaultPatternWildcard
            )
        )
        ((matchOnly 1) {nextCount = units})
    , paired
        "next-data-b"
        units
        (defer wildcardMatch $ mkConstant @PLC.Data () $ PLC.I 0)
        (matchOnly 1)
        ( defer
            rejectedAlternatives
            ( units
            , mkConstant @PLC.Data () $ PLC.I 0
            , DefaultPatternDataB DefaultPatternWildcard
            )
        )
        ((matchOnly 1) {nextCount = units})
    , paired
        "container"
        units
        (defer (uncurry containerChain) (units, DefaultPatternWildcard))
        (matchOnly units)
        (defer (uncurry containerChain) (units, emptyDataConstrPattern))
        ((matchOnly units) {containerCount = units})
    , paired
        "pair"
        units
        (defer (uncurry pairChain) (units, DefaultPatternWildcard))
        (matchOnly units)
        ( defer
            (uncurry pairChain)
            ( units
            , DefaultPatternPair DefaultPatternWildcard DefaultPatternWildcard
            )
        )
        ( (matchOnly units)
            { pairCount = units
            , structuralCount = 2 * units
            }
        )
    , paired
        "pair-reject"
        units
        ( defer
            failedThenAlternativeChain
            ( units
            , mkConstant @Integer () 0
            , DefaultPatternInteger 1
            , DefaultPatternWildcard
            )
        )
        ((matchOnly units) {nextCount = units})
        ( defer
            failedThenAlternativeChain
            ( units
            , mkConstant @Integer () 0
            , DefaultPatternPair DefaultPatternWildcard DefaultPatternWildcard
            , DefaultPatternWildcard
            )
        )
        ( (matchOnly units)
            { pairCount = units
            , nextCount = units
            }
        )
    , patternAuditCases units
    , nestedConstructorAuditCases units
    ]

-- Final edges and too-short non-final edges take different branches from the streaming middle of
-- a wide exact list. Repeat independent list Matches so every measured edge has the selected
-- topology. Every requested child edge emits Structural. Dispatched children additionally emit
-- StructuralDispatch, and exact final edges always emit both regardless of child shape.
repeatedStructuralCases :: Integer -> [CostingCase]
repeatedStructuralCases units =
  concat
    [ finalEdge
        "structural-simple-final"
        (mkConstant @[Integer] () [])
        (mkConstant @[Integer] () [0])
        DefaultPatternWildcard
        finalDelta
    , finalEdge
        "structural-dispatch-final-integer"
        (mkConstant @[Integer] () [])
        (mkConstant @[Integer] () [0])
        (DefaultPatternInteger 0)
        finalDelta
    , finalEdge
        "structural-dispatch-final-bool"
        (mkConstant @[Bool] () [])
        (mkConstant @[Bool] () [False])
        (DefaultPatternBool False)
        finalDelta
    , finalEdge
        "structural-dispatch-final-unit"
        (mkConstant @[()] () [])
        (mkConstant @[()] () [()])
        DefaultPatternUnit
        finalDelta
    , tooShort
        "structural-simple-reject"
        (mkConstant @[Integer] () [0])
        (mkConstant @[Integer] () [])
        DefaultPatternWildcard
        simpleRejectDelta
    , dispatchTooShort
        "structural-dispatch-reject-integer"
        (mkConstant @[Integer] () [])
        (DefaultPatternInteger 0)
        dispatchRejectDelta
    , dispatchTooShort
        "structural-dispatch-reject-bool"
        (mkConstant @[Bool] () [])
        (DefaultPatternBool False)
        dispatchRejectDelta
    , dispatchTooShort
        "structural-dispatch-reject-unit"
        (mkConstant @[()] () [])
        DefaultPatternUnit
        dispatchRejectDelta
    ]
  where
    roots = (matchOnly units) {containerCount = units}
    rejects = roots {nextCount = units}
    finalDelta =
      roots
        { structuralCount = units
        , structuralDispatchCount = units
        }
    simpleRejectDelta = rejects {structuralCount = units}
    dispatchRejectDelta =
      rejects
        { structuralCount = units
        , structuralDispatchCount = units
        }

    finalEdge name emptyValue singletonValue child expected =
      paired
        name
        units
        (defer exactListChain (units, emptyValue, Vector.empty))
        roots
        (defer exactListChain (units, singletonValue, Vector.singleton child))
        expected

    -- The control rejects an exact-empty pattern against a singleton list. The work asks for two
    -- children from an empty list, so the reached missing edge is deliberately non-final. Match,
    -- Container, and Next counts agree; only the work side charges that first requested edge.
    tooShort name singletonValue emptyValue child expected =
      paired
        name
        units
        (defer rejectingExactListChain (units, singletonValue, Vector.empty))
        rejects
        ( defer
            rejectingExactListChain
            (units, emptyValue, Vector.replicate 2 child)
        )
        expected

    -- Both sides request the same missing non-final edge and therefore pay Structural. Changing
    -- only the requested child from Wildcard to a scalar makes the paired delta exactly the
    -- additional StructuralDispatch event.
    dispatchTooShort name emptyValue child expected =
      paired
        name
        units
        ( defer
            rejectingExactListChain
            ( units
            , emptyValue
            , Vector.replicate 2 DefaultPatternWildcard
            )
        )
        simpleRejectDelta
        ( defer
            rejectingExactListChain
            (units, emptyValue, Vector.replicate 2 child)
        )
        expected

-- Constructor audits retain coverage of every production pattern shape. They compare a requested
-- pattern with wildcard over the same value, so constant payload construction and Match entry are
-- shared. Pair and Data.I/B necessarily reach Structural events, and successful captures evaluate
-- their handler lambdas; all are included in the exact design rows.
patternAuditCases :: Integer -> [CostingCase]
patternAuditCases units =
  concat
    [ audit
        "pattern-audit-integer"
        (mkConstant @Integer () 0)
        (DefaultPatternInteger 0)
        id
        (matchOnly units)
    , audit
        "pattern-audit-bool"
        (mkConstant @Bool () False)
        (DefaultPatternBool False)
        id
        (matchOnly units)
    , audit
        "pattern-audit-unit"
        (mkConstant @() () ())
        DefaultPatternUnit
        id
        (matchOnly units)
    , audit
        "pattern-audit-bytestring-empty"
        (mkConstant @BS.ByteString () BS.empty)
        (DefaultPatternByteString BS.empty)
        id
        ((matchOnly units) {byteStringBaseCount = units})
    , let oneWord = bytesForWords 1
       in audit
            "pattern-audit-bytestring-word"
            (mkConstant @BS.ByteString () $ copyByteString oneWord)
            (DefaultPatternByteString oneWord)
            id
            ( (matchOnly units)
                { byteStringBaseCount = units
                , byteStringWordCount = units
                }
            )
    , audit
        "pattern-audit-wildcard"
        (mkConstant @Integer () 0)
        DefaultPatternWildcard
        id
        (matchOnly units)
    , audit
        "pattern-audit-capture"
        (mkConstant @Integer () 0)
        DefaultPatternCapture
        captureHandler
        ( (matchOnly units)
            { captureCount = units
            , captureFinishCount = units
            , lamCount = units
            }
        )
    , audit
        "pattern-audit-list"
        (mkConstant @[Integer] () [])
        (DefaultPatternList DefaultPatternFieldsExact Vector.empty)
        id
        ((matchOnly units) {containerCount = units})
    , audit
        "pattern-audit-pair"
        (mkConstant @(Integer, Integer) () (0, 0))
        (DefaultPatternPair DefaultPatternWildcard DefaultPatternWildcard)
        id
        ( (matchOnly units)
            { pairCount = units
            , structuralCount = 2 * units
            }
        )
    , audit
        "pattern-audit-data-constr"
        (mkConstant @PLC.Data () $ PLC.Constr 0 [])
        emptyDataConstrPattern
        id
        ((matchOnly units) {containerCount = units})
    , audit
        "pattern-audit-data-map"
        (mkConstant @PLC.Data () $ PLC.Map [])
        (DefaultPatternDataMap DefaultPatternFieldsExact Vector.empty)
        id
        ((matchOnly units) {containerCount = units})
    , audit
        "pattern-audit-data-list"
        (mkConstant @PLC.Data () $ PLC.List [])
        (DefaultPatternDataList DefaultPatternFieldsExact Vector.empty)
        id
        ((matchOnly units) {containerCount = units})
    , audit
        "pattern-audit-data-i"
        (mkConstant @PLC.Data () $ PLC.I 0)
        (DefaultPatternDataI DefaultPatternWildcard)
        id
        ((matchOnly units) {structuralCount = units})
    , audit
        "pattern-audit-data-b"
        (mkConstant @PLC.Data () $ PLC.B BS.empty)
        (DefaultPatternDataB DefaultPatternWildcard)
        id
        ((matchOnly units) {structuralCount = units})
    ]
  where
    audit name scrutinee patternToMatch makeHandler expected =
      paired
        name
        units
        ( defer
            buildMatchChainOn
            (units, scrutinee, DefaultPatternWildcard, id)
        )
        (matchOnly units)
        ( defer
            buildMatchChainOn
            (units, scrutinee, patternToMatch, makeHandler)
        )
        expected

-- Exercise non-scalar nested roots in the first child of repeated two-element exact Lists. The
-- wildcard control and nested work traverse the same two Structural edges and both reach the
-- final second StructuralDispatch edge. The first work edge additionally dispatches its nested
-- child, so every paired slope is StructuralDispatch plus the nested specialized work; no
-- Structural subtraction remains in the residual.
nestedConstructorAuditCases :: Integer -> [CostingCase]
nestedConstructorAuditCases units =
  concat
    [ nested
        "pattern-audit-nested-bytestring-empty"
        (mkConstant @[BS.ByteString] () [BS.empty, BS.empty])
        (DefaultPatternByteString BS.empty)
        (dispatchOnly {byteStringBaseCount = units})
    , let oneWord = bytesForWords 1
       in nested
            "pattern-audit-nested-bytestring-word"
            ( mkConstant @[BS.ByteString]
                ()
                [copyByteString oneWord, copyByteString oneWord]
            )
            (DefaultPatternByteString oneWord)
            ( dispatchOnly
                { byteStringBaseCount = units
                , byteStringWordCount = units
                }
            )
    , nested
        "pattern-audit-nested-list-empty"
        (mkConstant @[[Integer]] () [[], []])
        (DefaultPatternList DefaultPatternFieldsExact Vector.empty)
        (dispatchOnly {containerCount = 2 * units})
    , nested
        "pattern-audit-nested-pair"
        (mkConstant @[(Integer, Integer)] () [(0, 0), (0, 0)])
        (DefaultPatternPair DefaultPatternWildcard DefaultPatternWildcard)
        ( dispatchOnly
            { pairCount = units
            , structuralCount = 4 * units
            }
        )
    , nested
        "pattern-audit-nested-data-i"
        (mkConstant @[PLC.Data] () [PLC.I 0, PLC.I 0])
        (DefaultPatternDataI DefaultPatternWildcard)
        (dispatchOnly {structuralCount = 3 * units})
    , nested
        "pattern-audit-nested-data-b"
        (mkConstant @[PLC.Data] () [PLC.B BS.empty, PLC.B BS.empty])
        (DefaultPatternDataB DefaultPatternWildcard)
        (dispatchOnly {structuralCount = 3 * units})
    ]
  where
    outerControl =
      (matchOnly units)
        { containerCount = units
        , structuralCount = 2 * units
        , structuralDispatchCount = units
        }
    dispatchOnly =
      (matchOnly units)
        { containerCount = units
        , structuralCount = 2 * units
        , structuralDispatchCount = 2 * units
        }
    nested name value child expected =
      paired
        name
        units
        ( defer
            exactListChain
            (units, value, Vector.replicate 2 DefaultPatternWildcard)
        )
        outerControl
        ( defer
            exactListChain
            ( units
            , value
            , Vector.fromList [child, DefaultPatternWildcard]
            )
        )
        expected

zeroCounts :: MatchStepCounts
zeroCounts = MatchStepCounts 0 0 0 0 0 0 0 0 0 0 0 0 0

matchOnly :: Integer -> MatchStepCounts
matchOnly count = zeroCounts {matchCount = count}

caseOnly :: Integer -> MatchStepCounts
caseOnly count = zeroCounts {caseCount = count}

abandonedCaptureCounts :: Integer -> Integer -> MatchStepCounts
abandonedCaptureCounts width captures =
  (matchOnly 1)
    { captureCount = captures
    , containerCount = 1
    , structuralCount = width + 1
    , structuralDispatchCount = 1
    , nextCount = 1
    }

captureHandler :: Term -> Term
captureHandler = UPLC.LamAbs () binder
  where
    binder = UPLC.NamedDeBruijn "capture" (UPLC.Index 0)

paired
  :: String
  -> Integer
  -> (Unit -> Term)
  -> MatchStepCounts
  -> (Unit -> Term)
  -> MatchStepCounts
  -> [CostingCase]
paired family units control controlCounts work workCounts =
  [ CostingCase (caseName "control") units controlCounts control
  , CostingCase (caseName "work") units workCounts work
  ]
  where
    caseName role = family <> "/" <> show units <> "/" <> role

-- Opaqueness prevents full-laziness from floating the built term into the retained recipe. Calling
-- a recipe therefore allocates a fresh term without memoizing it in 'calibrationCases'.
defer :: (a -> Term) -> a -> Unit -> Term
defer build input Unit = build input
{-# OPAQUE defer #-}

result :: Term
result = mkConstant @Integer () 0

-- The control and work both evaluate one scrutinee Constant and one result Constant per layer.
caseChain :: Integer -> Term
caseChain depth = caseChainOn depth $ mkConstant @Bool () False

caseChainOn :: Integer -> Term -> Term
caseChainOn depth scrutinee =
  foldr
    (\_ handler -> UPLC.Case () scrutinee $ Vector.singleton handler)
    result
    [1 .. depth]

matchBoolChain :: Integer -> Term
matchBoolChain depth = matchChain depth $ DefaultPatternBool False

matchWildcardBoolChain :: Integer -> Term
matchWildcardBoolChain depth = matchChain depth DefaultPatternWildcard

matchChain :: Integer -> DefaultBuiltinPattern -> Term
matchChain depth pat = matchChainOn depth (mkConstant @Bool () False) pat id

matchChainOn
  :: Integer
  -> Term
  -> DefaultBuiltinPattern
  -> (Term -> Term)
  -> Term
matchChainOn depth scrutinee pat makeHandler =
  foldr
    ( \_ handler ->
        UPLC.Match
          ()
          scrutinee
          (Vector.singleton (pat, makeHandler handler))
    )
    result
    [1 .. depth]

buildMatchChainOn
  :: (Integer, Term, DefaultBuiltinPattern, Term -> Term)
  -> Term
buildMatchChainOn (depth, scrutinee, pat, makeHandler) =
  matchChainOn depth scrutinee pat makeHandler

-- Repeat independent exact-list matches. This makes every singleton child a final edge and keeps
-- the outer Match/Container work identical between empty controls and singleton work terms.
exactListChain
  :: (Integer, Term, Vector.Vector DefaultBuiltinPattern)
  -> Term
exactListChain (depth, scrutinee, children) =
  listPatternChain
    (depth, scrutinee, DefaultPatternFieldsExact, children)

listPatternChain
  :: ( Integer
     , Term
     , DefaultPatternFieldEnd
     , Vector.Vector DefaultBuiltinPattern
     )
  -> Term
listPatternChain (depth, scrutinee, fieldEnd, children) =
  matchChainOn
    depth
    scrutinee
    (DefaultPatternList fieldEnd children)
    id

-- Repeat a deliberately rejected exact-list alternative followed by a successful wildcard. The
-- requested child is charged before the matcher discovers that the value list is too short.
rejectingExactListChain
  :: (Integer, Term, Vector.Vector DefaultBuiltinPattern)
  -> Term
rejectingExactListChain (depth, scrutinee, children) =
  foldr
    ( \_ handler ->
        UPLC.Match () scrutinee $
          Vector.fromList
            [ (DefaultPatternList DefaultPatternFieldsExact children, result)
            , (DefaultPatternWildcard, handler)
            ]
    )
    result
    [1 .. depth]

wildcardMatch :: Term -> Term
wildcardMatch scrutinee =
  UPLC.Match () scrutinee $ Vector.singleton (DefaultPatternWildcard, result)

-- The first root is covered by Match. Every rejected root emits Next before the matcher probes the
-- following root, so the slope assigns transition plus the selected scalar/root dispatch to Next.
rejectedAlternatives
  :: (Integer, Term, DefaultBuiltinPattern)
  -> Term
rejectedAlternatives (count, scrutinee, rejectedPattern) =
  UPLC.Match () scrutinee $
    Vector.replicate (fromIntegral count) (rejectedPattern, result)
      <> Vector.singleton (DefaultPatternWildcard, result)

failedThenAlternativeChain
  :: (Integer, Term, DefaultBuiltinPattern, DefaultBuiltinPattern)
  -> Term
failedThenAlternativeChain (depth, scrutinee, rejectedPattern, nextPattern) =
  foldr
    ( \_ handler ->
        UPLC.Match () scrutinee $
          Vector.fromList
            [ (rejectedPattern, result)
            , (nextPattern, handler)
            ]
    )
    result
    [1 .. depth]

bytesForWords :: Integer -> BS.ByteString
bytesForWords wordsToCompare =
  BS.replicate (8 * fromIntegral wordsToCompare) 0x5a

copyByteString :: BS.ByteString -> BS.ByteString
copyByteString = BS.copy
{-# OPAQUE copyByteString #-}

byteStringEmptyChain :: Integer -> DefaultBuiltinPattern -> Term
byteStringEmptyChain depth pat =
  matchChainOn depth (mkConstant @BS.ByteString () BS.empty) pat id

byteStringLiteralMatch :: BS.ByteString -> Term
byteStringLiteralMatch expected =
  UPLC.Match
    ()
    (mkConstant @BS.ByteString () $ copyByteString expected)
    (Vector.singleton (DefaultPatternByteString expected, result))

byteStringWordsMatch :: Integer -> Term
byteStringWordsMatch = byteStringLiteralMatch . bytesForWords

exactIntegerListMatch :: Integer -> DefaultBuiltinPattern -> Term
exactIntegerListMatch width child =
  UPLC.Match
    ()
    (mkConstant @[Integer] () $ replicate (fromIntegral width) 0)
    ( Vector.singleton
        ( DefaultPatternList
            DefaultPatternFieldsExact
            (Vector.replicate (fromIntegral width) child)
        , result
        )
    )

exactBoolListMatch :: Integer -> Term
exactBoolListMatch width =
  UPLC.Match
    ()
    (mkConstant @[Bool] () $ replicate (fromIntegral width) False)
    ( Vector.singleton
        ( DefaultPatternList
            DefaultPatternFieldsExact
            (Vector.replicate (fromIntegral width) $ DefaultPatternBool False)
        , result
        )
    )

exactUnitListMatch :: Integer -> Term
exactUnitListMatch width =
  UPLC.Match
    ()
    (mkConstant @[()] () $ replicate (fromIntegral width) ())
    ( Vector.singleton
        ( DefaultPatternList
            DefaultPatternFieldsExact
            (Vector.replicate (fromIntegral width) DefaultPatternUnit)
        , result
        )
    )

emptyDataConstrPattern :: DefaultBuiltinPattern
emptyDataConstrPattern =
  DefaultPatternDataConstr 0 DefaultPatternFieldsExact Vector.empty

containerChain :: Integer -> DefaultBuiltinPattern -> Term
containerChain depth pat =
  matchChainOn depth (mkConstant @PLC.Data () $ PLC.Constr 0 []) pat id

pairChain :: Integer -> DefaultBuiltinPattern -> Term
pairChain depth pat =
  matchChainOn depth (mkConstant @(Integer, Integer) () (0, 0)) pat id

-- Work and control fail at the same final Integer pattern and take the same wildcard fallback.
-- The work side changes only the reached prefix fields from wildcard to capture; its failed handler
-- is never evaluated, so no LamAbs subtraction is needed.
abandonedCaptureMatch :: Integer -> DefaultBuiltinPattern -> Term
abandonedCaptureMatch width prefixPattern =
  UPLC.Match
    ()
    (mkConstant @[Integer] () $ replicate (fromIntegral width + 1) 0)
    ( Vector.fromList
        [
          ( DefaultPatternList DefaultPatternFieldsExact children
          , failedHandler
          )
        , (DefaultPatternWildcard, result)
        ]
    )
  where
    children =
      Vector.replicate (fromIntegral width) prefixPattern
        `Vector.snoc` DefaultPatternInteger 1
    binder = UPLC.NamedDeBruijn "capture" (UPLC.Index 0)
    failedHandler = foldr (const $ UPLC.LamAbs () binder) result [1 .. width]
