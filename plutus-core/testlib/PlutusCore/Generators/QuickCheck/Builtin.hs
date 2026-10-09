-- editorconfig-checker-disable
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeApplications #-}
{-# OPTIONS_GHC -Wno-dodgy-imports #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

module PlutusCore.Generators.QuickCheck.Builtin where

import PlutusPrelude

import PlutusCore hiding (Constr)
import PlutusCore.Builtin
import PlutusCore.Crypto.BLS12_381.G1 qualified as BLS12_381.G1
import PlutusCore.Crypto.BLS12_381.G2 qualified as BLS12_381.G2
import PlutusCore.Crypto.BLS12_381.Pairing qualified as BLS12_381.Pairing
import PlutusCore.Data
import PlutusCore.Generators.QuickCheck.GenerateKinds ()
import PlutusCore.Generators.QuickCheck.Split (multiSplit0, multiSplit1, multiSplit1In)
import PlutusCore.Generators.QuickCheck.Utils (uniqueVectorOf)
import PlutusCore.MkPlc (mkTyBuiltinOf)
import PlutusCore.Value (Value)
import PlutusCore.Value qualified as Value

import Data.ByteString (ByteString, empty)
import Data.ByteString.Base16 qualified as Base16
import Data.ByteString.Char8 qualified as BC
import Data.Int
import Data.Maybe (mapMaybe)
import Data.Proxy
import Data.Text (Text)
import Data.Text qualified as Text
import Data.Text.Encoding qualified as Text
import Data.Vector.Strict qualified as Strict
import Test.QuickCheck hiding (Some (..))
import Test.QuickCheck.Instances.ByteString ()
import Test.QuickCheck.Instances.Vector ()

{-| Same as 'Arbitrary' but specifically for Plutus built-in types, so that we are not tied to
the default implementation of the methods for a built-in type. -}
class ArbitraryBuiltin a where
  arbitraryBuiltin :: Gen a
  default arbitraryBuiltin :: Arbitrary a => Gen a
  arbitraryBuiltin = arbitrary

  shrinkBuiltin :: a -> [a]
  default shrinkBuiltin :: Arbitrary a => a -> [a]
  shrinkBuiltin = shrink

instance ArbitraryBuiltin ()
instance ArbitraryBuiltin Bool

{- Note [QuickCheck and integral types]
The 'Arbitrary' instances for 'Integer' and 'Int' only generate small integers:

    >>> :set -XTypeApplications
    >>> fmap (any ((> 30) . abs) . concat . concat . concat) . sample' $ arbitrary @[[[Integer]]]
    False
    >>> fmap (any ((> 30) . abs) . concat . concat . concat) . sample' $ arbitrary @[[[Int]]]
    False

We want to generate larger ones, including converted-to-Integer 'minBound' and 'maxBound' of various
integral types. Hence we declare 'nextInterestingBound' and 'highInterestingBound' to specify the
"interesting" ranges to generate positive integers within. We also make it likely to hit either end
of each of those ranges.
-}

-- See Note [QuickCheck and integral types].
nextInterestingBound :: Integer -> Integer
nextInterestingBound 1 = 127
nextInterestingBound x = (x + 1) ^ (2 :: Int) * 2 - 1

-- See Note [QuickCheck and integral types].
highInterestingBound :: Integer
highInterestingBound = toInteger (maxBound :: Int64) * 16

{-| A list of ranges.

>>> import Data.Int
>>> magnitudesPositive (* 10) (toInteger (maxBound :: Int16))
[(1,10),(11,100),(101,1000),(1001,10000),(10001,32767)]
>>> magnitudesPositive nextInterestingBound (toInteger (maxBound :: Int64))
[(1,127),(128,32767),(32768,2147483647),(2147483648,9223372036854775807)] -}
magnitudesPositive :: (Integer -> Integer) -> Integer -> [(Integer, Integer)]
magnitudesPositive next high =
  zipWith (\lo hi -> (lo + 1, hi)) borders (tail borders)
  where
    preborders = tail . takeWhile (\x -> next x < high) $ iterate next 1
    borders = 0 : preborders ++ [next $ last preborders, high]

chooseIntegerPreferEnds :: (Integer, Integer) -> Gen Integer
chooseIntegerPreferEnds (lo, hi)
  | hi - lo < 20 = chooseInteger (lo, hi)
  | otherwise =
      frequency $
        concat
          [ zip (50 : [9, 8 .. 1]) $ map pure [lo ..]
          , zip (50 : [9, 8 .. 1]) $ map pure [hi, hi - 1]
          , [(200, chooseInteger (lo + 10, hi - 10))]
          ]

{-| Generate asymptotically larger positive negative numbers (sans zero) with exponentially lower
chance, stop at the geometric mean of the range and start increasing the probability of
generating larger numbers, so that we generate we're most likely to generate numbers that are
either fairly small or really big. Numbers at the beginning of the range are more likely to get
generated than at the very end, but only by a fairly small factor. The size parameter is ignored,
which is perhaps wrong and should be fixed. -}
arbitraryPositive :: (Integer -> Integer) -> Integer -> Gen Integer
arbitraryPositive next high = frequency . zip freqs $ map chooseIntegerPreferEnds magnitudes
  where
    magnitudes = magnitudesPositive next high
    prefreqs = map floor $ iterate (* 1.1) (100 :: Double)
    freqs =
      concat
        [ reverse (take (length magnitudes `div` 2) prefreqs)
        , map (floor . (/ (1.5 :: Double)) . fromIntegral) prefreqs
        ]

-- | Same as 'arbitraryPositive' except produces negative integers.
arbitraryNegative :: (Integer -> Integer) -> Integer -> Gen Integer
arbitraryNegative next high = negate <$> arbitraryPositive next high

arbitrarySigned :: (Integer -> Integer) -> Integer -> Gen Integer
arbitrarySigned next high =
  frequency
    [ (48, arbitraryNegative next high)
    , (4, pure 0)
    , (48, arbitraryPositive next high)
    ]

{-| Same as 'shrinkIntegral' except includes the square root of the given number (or of its
negative if the number is negative, in which case the square root is negated too). We need the
former because 'shrinkIntegral' at most divides the number by two, which makes the number smaller
way too slow, hence we add square root to speed up the process.

>>> shrinkIntegralFast (0 :: Integer)
[]
>>> shrinkIntegralFast (1 :: Integer)
[0]
>>> shrinkIntegralFast (9 :: Integer)
[0,3,5,7,8]
>>> shrinkIntegralFast (-10000 :: Integer)
[0,10000,-100,-5000,-7500,-8750,-9375,-9688,-9844,-9922,-9961,-9981,-9991,-9996,-9998,-9999] -}
shrinkIntegralFast :: Integral a => a -> [a]
shrinkIntegralFast x =
  concat
    [ [0 | x /= 0]
    , [-x | x < 0]
    , [signum x * floor (sqrt @Double $ fromIntegral xA) | let xA = abs x, xA > 4]
    , drop 1 . map (x -) . takeWhile (/= 0) $ iterate (`quot` 2) x
    ]

instance ArbitraryBuiltin Integer where
  -- See Note [QuickCheck and integral types].
  arbitraryBuiltin = arbitrarySigned nextInterestingBound highInterestingBound
  shrinkBuiltin = shrinkIntegralFast

{-|

>>> shrinkBuiltin $ Text.pack "abcd"
["","cd","ab","bcd","acd","abd","abc","aacd","abad","abbd","abca","abcb","abcc"] -}
instance ArbitraryBuiltin Text where
  arbitraryBuiltin = Text.pack . getPrintableString <$> arbitrary
  shrinkBuiltin = map (Text.pack . getPrintableString) . shrink . PrintableString . Text.unpack

instance ArbitraryBuiltin ByteString where
  arbitraryBuiltin = Text.encodeUtf8 <$> arbitraryBuiltin
  shrinkBuiltin = map Text.encodeUtf8 . shrinkBuiltin . Text.decodeUtf8

-- | Generate a tag for the 'Constr' constructor.
genConstrTag :: Gen Integer
genConstrTag =
  frequency
    [ -- We want to generate most plausible constructor IDs most often.
      (6, chooseInteger (0, 2))
    , -- Less plausible -- less often.
      (3, chooseInteger (3, 5))
    , -- And some meaningless garbage occasionally just to have good coverage.
      (1, (`mod` toInteger (maxBound :: Int64)) <$> arbitraryBuiltin)
    ]

{-| Generate a 'Data' object using a @spine :: [()]@ as a hint. It's helpful to make the spine a
list of units rather than a 'Word' or something, because we have useful functions for arbitrary
list splitting. -}
genDataFromSpine :: [()] -> Gen Data
genDataFromSpine [] =
  oneof
    [ Constr <$> genConstrTag <*> pure []
    , pure $ List []
    , pure $ Map []
    ]
genDataFromSpine [()] = oneof [I <$> arbitraryBuiltin, B <$> arbitraryBuiltin]
genDataFromSpine els =
  oneof
    [ Constr <$> genConstrTag <*> (multiSplit0 0.1 els >>= traverse genDataFromSpine)
    , List <$> (multiSplit0 0.1 els >>= traverse genDataFromSpine)
    , do
        elss <- multiSplit1 els
        Map
          <$> frequency
            [ -- Generate maps from 'ByteString's most often.

              ( 6
              , for elss $ \(NonEmpty els') ->
                  (,) . B <$> arbitraryBuiltin <*> genDataFromSpine (drop 1 els')
              )
            , -- Generate maps from 'Integer's less often.

              ( 3
              , for elss $ \(NonEmpty els') ->
                  (,) . I <$> arbitraryBuiltin <*> genDataFromSpine (drop 1 els')
              )
            , -- Occasionally generate maps with random nonsense in place of keys.

              ( 1
              , for elss $ \(NonEmpty els') -> do
                  splitRes <- multiSplit1In 2 els'
                  case splitRes of
                    [] ->
                      (,) <$> genDataFromSpine [] <*> genDataFromSpine []
                    [NonEmpty elsL'] ->
                      (,) <$> genDataFromSpine elsL' <*> genDataFromSpine []
                    [NonEmpty elsL', NonEmpty elsR'] ->
                      (,) <$> genDataFromSpine elsL' <*> genDataFromSpine elsR'
                    _ -> error "Panic: 'multiSplit1In 2' returned a list longer than 2 elements"
              )
            ]
    ]

pureIfNull :: (Foldable f, Applicative f) => a -> f a -> f a
pureIfNull x xs = if null xs then pure x else xs

instance ArbitraryBuiltin Data where
  arbitraryBuiltin = arbitrary >>= genDataFromSpine

  -- We arbitrarily assume that @I 0@ is the smallest 'Data' object just so that anything else in
  -- a counterexample gives us a clue as to what the culprit may be. Hence @I 0@ needs to be
  -- reachable from all nodes apart from @I 0@ itself. For all nodes but 'I' we achieve this by
  -- returning @[I 0]@ if there's no other way to shrink the value, i.e. either shrinking keeps
  -- going or it's time to return the smallest object. The clause for @I i@ doesn't require
  -- mentioning @I 0@ explicitly, since we get it through general shrinking of @i@ (unless @i@
  -- equals @0@, as desired).
  shrinkBuiltin (Constr i ds) =
    pureIfNull (I 0) $
      concat
        [ ds
        , map (Constr i) $ shrinkBuiltin ds
        , map (flip Constr ds) $ shrinkBuiltin i
        ]
  shrinkBuiltin (Map ps) =
    pureIfNull (I 0) $
      concat
        [ map fst ps
        , map snd ps
        , map Map $ shrinkBuiltin ps
        ]
  shrinkBuiltin (List ds) =
    pureIfNull (I 0) $
      concat
        [ ds
        , map List $ shrinkBuiltin ds
        ]
  shrinkBuiltin (B b) = pureIfNull (I 0) . map B $ shrinkBuiltin b
  shrinkBuiltin (I i) = map I $ shrinkBuiltin i

instance Arbitrary Data where
  arbitrary = arbitraryBuiltin
  shrink = shrinkBuiltin

---------------Generator for Builtin Value---------------

{-| Return how many candidates to randomly choose from to fill the given number of cells. For
example, if we only need to fill a single cell, we choose from 6 different candidates, and if we
need to fill 5 cells, we choose from 11 candidates.

>>> map (\i -> (i, toCellCandidatesNumber i)) [1..13]
[(1,6),(2,6),(3,6),(4,8),(5,11),(6,14),(7,18),(8,22),(9,27),(10,31),(11,36),(12,41),(13,46)] -}
toCellCandidatesNumber :: Int -> Int
toCellCandidatesNumber i = max 6 . floor @Double $ fromIntegral i ** 1.5

{-| Generate a 'ByteString' by picking one of the predetermined ones, given a number of
cells to fill (see 'toCellCandidatesNumber'). The idea is that we want to occasionally generate
the same 'CurrencySymbol' or 'TokenName' for different 'Value's to have decent test coverage,
hence to make name clashing more likely we pick from a predetermined set of
'ByteString's. Otherwise the chance of generating the same 'ByteString' for two
different 'Value's would be virtually zero. -}
genShortHex :: Int -> Gen Value.K
genShortHex i =
  (Base16.encode . BC.pack . show <$> elements [0 .. toCellCandidatesNumber i])
    `suchThatMap` Value.k

{-| Annotate each element of the give list with a @name@, given a function turning
'ByteString' into names. -}
uniqueNames :: Eq name => (Value.K -> name) -> [b] -> Gen [(name, b)]
uniqueNames wrap ys = do
  let len = length ys
  -- We always generate unique 'CurrencySymbol's within a single 'Value' and 'TokenName' within a
  -- single 'CurrencySymbol', because functions over 'Value' don't handle duplicated names anyway.
  -- Note that we can generate the same 'TokenName' within different 'CurrencySymbol's within the
  -- same 'Value'.
  xs <- uniqueVectorOf len $ wrap <$> genShortHex len
  pure $ zip xs ys

instance ArbitraryBuiltin Value.K where
  arbitraryBuiltin = arbitraryBuiltin `suchThatMap` Value.k

instance Arbitrary Value.K where
  arbitrary = arbitraryBuiltin
  shrink = shrinkBuiltin

instance ArbitraryBuiltin Value.Quantity where
  arbitraryBuiltin =
    chooseInteger (Value.unQuantity minBound, Value.unQuantity maxBound)
      `suchThatMap` Value.quantity
  shrinkBuiltin =
    mapMaybe Value.quantity . shrinkIntegralFast @Integer . Value.unQuantity

instance Arbitrary Value.Quantity where
  arbitrary = arbitraryBuiltin
  shrink = shrinkBuiltin

{-| A wrapper for satisfying an @Arbitrary a@ constraint without implementing an 'Arbitrary'
instance for @a@. -}
newtype NoArbitrary a = NoArbitrary
  { unNoArbitrary :: a
  }

-- | 'arbitrary' throws, 'shrink' neither throws nor shrinks.
instance Arbitrary (NoArbitrary a) where
  arbitrary = error "arbitrary @(NoArbitrary a)"
  shrink _ = []

instance ArbitraryBuiltin Value where
  arbitraryBuiltin = do
    -- Generate values for all of the 'TokenName's in the final 'Value' and split them into a
    -- list of lists.
    quantities <- multiSplit0 0.2 =<< arbitraryBuiltin
    -- Generate 'TokenName's and 'CurrencySymbol's.
    currencies <- uniqueNames id =<< traverse (uniqueNames id) quantities
    case Value.fromList currencies of
      BuiltinSuccess v -> pure v
      BuiltinSuccessWithLogs _ v -> pure v
      BuiltinFailure logs _ -> error $ "Failed to generate valid Value: " <> show logs

  shrinkBuiltin =
    mapMaybe
      ( \keys -> case Value.fromList keys of
          BuiltinSuccess v -> Just v
          BuiltinSuccessWithLogs _ v -> Just v
          BuiltinFailure {} -> Nothing
      )
      . coerce (shrink @[(NoArbitrary Value.K, [(NoArbitrary Value.K, Value.Quantity)])])
      . Value.toList

instance Arbitrary Value where
  arbitrary = arbitraryBuiltin
  shrink = shrinkBuiltin

instance ArbitraryBuiltin BLS12_381.G1.Element where
  arbitraryBuiltin =
    BLS12_381.G1.hashToGroup <$> arbitrary <*> pure Data.ByteString.empty >>= \case
      -- We should only get a failure if the second argument is greater than 255 bytes, which
      -- it isn't.
      Left err -> error $ show err
      Right p -> pure p

  -- It's difficult to come up with a sensible shrinking function here given
  -- that there's no sensible order on the elements of G1, let alone one
  -- that's compatible with the group structure.  We can't try shrinking the
  -- x-coordinate of a known point for example because only about only about
  -- 1/10^39 of the field elements are the x-coordinate of a point in G1, so
  -- we're highly unlikely to find a suitable x value.
  shrinkBuiltin _ = []

instance ArbitraryBuiltin BLS12_381.G2.Element where
  arbitraryBuiltin =
    BLS12_381.G2.hashToGroup <$> arbitrary <*> pure Data.ByteString.empty >>= \case
      -- We should only get a failure if the second argument is greater than 255 bytes, which
      -- it isn't.
      Left err -> error $ show err
      Right p -> pure p

  -- See the comment about shrinking for G1; G2 is even worse.
  shrinkBuiltin _ = []

instance ArbitraryBuiltin BLS12_381.Pairing.MlResult where
  arbitraryBuiltin = BLS12_381.Pairing.millerLoop <$> arbitraryBuiltin <*> arbitraryBuiltin

  -- Shrinking here is even more difficult than for G1 and G2 since we don't
  -- have direct access to elements of MlResult.
  shrinkBuiltin _ = []

{-| For providing an 'Arbitrary' instance deferring to 'ArbitraryBuiltin'. Useful for implementing
'ArbitraryBuiltin' for a polymorphic built-in type by taking the logic for handling spines from
the 'Arbitrary' class and the logic for handling elements from 'ArbitraryBuiltin'. -}
newtype AsArbitraryBuiltin a = AsArbitraryBuiltin
  { unAsArbitraryBuiltin :: a
  }
  deriving newtype (Show, Eq, Ord, Num)

instance ArbitraryBuiltin a => Arbitrary (AsArbitraryBuiltin a) where
  arbitrary = coerce $ arbitraryBuiltin @a
  shrink = coerce $ shrinkBuiltin @a

-- We could do this and the next one generically using 'ElaborateBuiltin', but it would be more
-- code, so we keep it simple.
instance ArbitraryBuiltin a => ArbitraryBuiltin [a] where
  arbitraryBuiltin = do
    spine <- arbitrary
    let len = length spine
    for spine $ \() ->
      -- Scale the elements, so that generating a list of lists of lists doesn't take
      -- exponential size (and thus time).
      scale (`div` len) . coerce $ arbitrary @(AsArbitraryBuiltin a)
  shrinkBuiltin = coerce $ shrink @[AsArbitraryBuiltin a]

instance ArbitraryBuiltin a => ArbitraryBuiltin (Strict.Vector a) where
  arbitraryBuiltin = Strict.fromList <$> arbitraryBuiltin
  shrinkBuiltin = map Strict.fromList . shrinkBuiltin . Strict.toList

instance (ArbitraryBuiltin a, ArbitraryBuiltin b) => ArbitraryBuiltin (a, b) where
  arbitraryBuiltin = do
    (,)
      <$> coerce (scale (`div` 2) $ arbitrary @(AsArbitraryBuiltin a))
      <*> coerce (scale (`div` 2) $ arbitrary @(AsArbitraryBuiltin b))
  shrinkBuiltin = coerce $ shrink @(AsArbitraryBuiltin a, AsArbitraryBuiltin b)

-- | Fully instantiated constant types, with size-limited recursive arguments.
instance Arbitrary (Some DefaultUni) where
  arbitrary = sized $ \size ->
    oneof $ map pure primitives ++ [compound | size > 10]
    where
      primitives =
        [ Some DefaultUniInteger
        , Some DefaultUniByteString
        , Some DefaultUniString
        , Some DefaultUniUnit
        , Some DefaultUniBool
        , Some DefaultUniData
        , Some DefaultUniBLS12_381_G1_Element
        , Some DefaultUniBLS12_381_G2_Element
        , Some DefaultUniBLS12_381_MlResult
        , Some DefaultUniValue
        ]
      compound =
        scale (`div` 5) arbitrary >>= \(Some a) ->
          oneof
            [ pure $ Some $ DefaultUniList a
            , pure $ Some $ DefaultUniArray a
            , scale (`div` 5) arbitrary >>= \(Some b) ->
                pure $ Some $ DefaultUniPair a b
            ]
  shrink = shrinkBuiltinType

instance Arbitrary (Some (ValueOf DefaultUni)) where
  arbitrary =
    arbitrary >>= \(Some uni) ->
      bring (Proxy @ArbitraryBuiltin) uni $ Some . ValueOf uni <$> arbitraryBuiltin
  shrink (Some (ValueOf DefaultUniUnit ())) = []
  shrink (Some (ValueOf uni x)) = someValue () : bring (Proxy @ArbitraryBuiltin) uni (map (Some . ValueOf uni) $ shrinkBuiltin x)

-- | Generate built-in type syntax at the requested kind, including partial pairs.
genBuiltinTypeOf :: Kind () -> Gen (Maybe (Type TyName DefaultUni ()))
genBuiltinTypeOf (Type ()) =
  arbitrary >>= \(Some uni) ->
    pure $ Just $ mkTyBuiltinOf () uni
genBuiltinTypeOf kind@(KindArrow _ dom cod) = do
  let heads = [TyBuiltin () headRep | headRep <- [minBound .. maxBound], kindOfBuiltinType headRep == kind]
  partialPairs <- case (dom, cod) of
    (Type (), Type ()) ->
      arbitrary >>= \(Some uni) ->
        pure [TyApp () (TyBuiltin () DefaultUniPairHead) (mkTyBuiltinOf () uni)]
    (Type (), KindArrow {}) -> pure []
    (KindArrow {}, Type ()) -> pure []
    (KindArrow {}, KindArrow {}) -> pure []
  case heads ++ partialPairs of
    [] -> pure Nothing
    candidates -> Just <$> elements candidates

-- | Drop a constant type to unit, its children, or smaller recursive arguments.
shrinkBuiltinType :: Some DefaultUni -> [Some DefaultUni]
shrinkBuiltinType (Some uni) = case uni of
  DefaultUniUnit -> []
  DefaultUniInteger -> [unit]
  DefaultUniByteString -> [unit]
  DefaultUniString -> [unit]
  DefaultUniBool -> [unit]
  DefaultUniData -> [unit]
  DefaultUniBLS12_381_G1_Element -> [unit]
  DefaultUniBLS12_381_G2_Element -> [unit]
  DefaultUniBLS12_381_MlResult -> [unit]
  DefaultUniValue -> [unit]
  DefaultUniList a ->
    unit : Some a : [Some (DefaultUniList a') | Some a' <- shrinkBuiltinType (Some a)]
  DefaultUniArray a ->
    unit : Some a : [Some (DefaultUniArray a') | Some a' <- shrinkBuiltinType (Some a)]
  DefaultUniPair a b ->
    [unit, Some a, Some b]
      ++ [Some (DefaultUniPair a' b) | Some a' <- shrinkBuiltinType (Some a)]
      ++ [Some (DefaultUniPair a b') | Some b' <- shrinkBuiltinType (Some b)]
  where
    unit = Some DefaultUniUnit

-- | Recognize fully instantiated constant types for term generation and shrinking.
constantTypeTag :: Type tyname DefaultUni ann -> Maybe (Some DefaultUni)
constantTypeTag (TyBuiltin _ headRep) = case headRep of
  DefaultUniIntegerHead -> Just $ Some DefaultUniInteger
  DefaultUniByteStringHead -> Just $ Some DefaultUniByteString
  DefaultUniStringHead -> Just $ Some DefaultUniString
  DefaultUniUnitHead -> Just $ Some DefaultUniUnit
  DefaultUniBoolHead -> Just $ Some DefaultUniBool
  DefaultUniDataHead -> Just $ Some DefaultUniData
  DefaultUniBLS12_381_G1_ElementHead -> Just $ Some DefaultUniBLS12_381_G1_Element
  DefaultUniBLS12_381_G2_ElementHead -> Just $ Some DefaultUniBLS12_381_G2_Element
  DefaultUniBLS12_381_MlResultHead -> Just $ Some DefaultUniBLS12_381_MlResult
  DefaultUniValueHead -> Just $ Some DefaultUniValue
  DefaultUniListHead -> Nothing
  DefaultUniArrayHead -> Nothing
  DefaultUniPairHead -> Nothing
constantTypeTag (TyApp _ (TyBuiltin _ DefaultUniListHead) arg) = do
  Some a <- constantTypeTag arg
  pure $ Some $ DefaultUniList a
constantTypeTag (TyApp _ (TyBuiltin _ DefaultUniArrayHead) arg) = do
  Some a <- constantTypeTag arg
  pure $ Some $ DefaultUniArray a
constantTypeTag (TyApp _ (TyApp _ (TyBuiltin _ DefaultUniPairHead) left) right) = do
  Some a <- constantTypeTag left
  Some b <- constantTypeTag right
  pure $ Some $ DefaultUniPair a b
constantTypeTag TyVar {} = Nothing
constantTypeTag TyFun {} = Nothing
constantTypeTag TyIFix {} = Nothing
constantTypeTag TyForall {} = Nothing
constantTypeTag TyLam {} = Nothing
constantTypeTag TyApp {} = Nothing
constantTypeTag TySOP {} = Nothing
