{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE ViewPatterns #-}

module PlutusCore.Value
  ( Value -- Do not expose data constructor
  , K -- Do not expose data constructor
  , k
  , unK
  , maxKeyLen
  , Quantity -- Do not expose data constructor
  , quantity
  , unQuantity
  , zeroQuantity
  , addQuantity
  , negativeAmounts
  , NestedMap
  , unpack
  , pack
  , empty
  , fromList
  , toList
  , toFlatList
  , totalSize
  , maxInnerSize
  , insertCoin
  , deleteCoin
  , scaleValue
  , lookupCoin
  , valueContains
  , unionValue
  , valueData
  , unValueData
  ) where

import Codec.Serialise qualified as CBOR
import Control.DeepSeq (NFData)
import Data.Bifunctor
import Data.Bitraversable
import Data.ByteString (ByteString)
import Data.ByteString qualified as B
import Data.ByteString.Base64 qualified as Base64
import Data.Foldable (find)
import Data.Hashable (Hashable (..))
import Data.IntMap.Strict (IntMap)
import Data.IntMap.Strict qualified as IntMap
import Data.Map.Merge.Strict qualified as M
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Text.Encoding qualified as Text
import GHC.Generics
import GHC.Stack
  ( HasCallStack
  , callStack
  , getCallStack
  )

import PlutusCore.Builtin.Result
import PlutusCore.Data (Data (..))
import PlutusCore.Flat qualified as Flat
import PlutusPrelude (Pretty (..))

-- Max length (in bytes) for currency symbols and token names in `Value`,
-- both of which cannot exceed 32 bytes. Currency symbols are in fact either
-- empty or 28 bytes, but for simplicity we allow anything between 0 and 32 bytes.
maxKeyLen :: Int
maxKeyLen = 32
{-# INLINE maxKeyLen #-}

----------------------------------------------------------------------------------------------------
-- Newtype-wrapper for keys used in the nested maps ------------------------------------------------

-- | A `ByteString` with maximum length of `maxKeyLen` bytes.
newtype K = UnsafeK {unK :: ByteString}
  deriving newtype (Eq, Ord, Show, Hashable, NFData)
  deriving stock (Generic)

k :: ByteString -> Maybe K
k b = if B.length b <= maxKeyLen then Just (UnsafeK b) else Nothing
{-# INLINEABLE k #-}

instance Flat.Flat K where
  encode (UnsafeK b) = Flat.encode b
  {-# INLINE encode #-}
  decode = do
    b <- Flat.decode
    maybe (fail $ "Invalid Value key: " <> show (B.unpack b)) pure (k b)
  {-# INLINEABLE decode #-}

instance CBOR.Serialise K where
  encode (UnsafeK b) = CBOR.encode b
  {-# INLINE encode #-}
  decode = do
    b <- CBOR.decode
    maybe (fail $ "Invalid Value key: " <> show (B.unpack b)) pure (k b)
  {-# INLINEABLE decode #-}

----------------------------------------------------------------------------------------------------
-- Quantity: Signed 128-bit Integer ----------------------------------------------------------------

-- | A signed 128-bit integer quantity.
newtype Quantity = UnsafeQuantity {unQuantity :: Integer}
  deriving newtype (Eq, Ord, Show, NFData, Hashable)
  deriving stock (Generic)

instance CBOR.Serialise Quantity where
  encode (UnsafeQuantity i) = CBOR.encode i
  {-# INLINE encode #-}
  decode = do
    i <- CBOR.decode
    case quantity i of
      Just q -> pure q
      Nothing -> fail $ "Quantity out of signed 128-bit integer bounds: " <> show i
  {-# INLINEABLE decode #-}

instance Flat.Flat Quantity where
  encode (UnsafeQuantity i) = Flat.encode i
  {-# INLINE encode #-}
  decode = do
    i <- Flat.decode
    case quantity i of
      Just q -> pure q
      Nothing -> fail $ "Quantity out of signed 128-bit integer bounds: " <> show i
  {-# INLINEABLE decode #-}

instance Pretty Quantity where
  pretty (UnsafeQuantity i) = pretty i

instance Bounded Quantity where
  minBound = UnsafeQuantity (-(2 ^ (127 :: Integer)))
  {-# INLINE minBound #-}
  maxBound = UnsafeQuantity (2 ^ (127 :: Integer) - 1)
  {-# INLINE maxBound #-}

-- | Smart constructor for Quantity that validates bounds.
quantity :: Integer -> Maybe Quantity
quantity i
  | i >= unQuantity minBound && i <= unQuantity maxBound = Just (UnsafeQuantity i)
  | otherwise = Nothing
{-# INLINEABLE quantity #-}

-- | The zero quantity.
zeroQuantity :: Quantity
zeroQuantity = UnsafeQuantity 0
{-# INLINE zeroQuantity #-}

-- | Safely add two quantities, checking for overflow.
addQuantity :: Quantity -> Quantity -> Maybe Quantity
addQuantity (UnsafeQuantity x) (UnsafeQuantity y) = quantity (x + y)
{-# INLINEABLE addQuantity #-}

-- | Safely scale a quantity with given integer, checking for overflow.
scaleQuantity :: Integer -> Quantity -> Maybe Quantity
scaleQuantity x (UnsafeQuantity y) = quantity (x * y)
{-# INLINEABLE scaleQuantity #-}

----------------------------------------------------------------------------------------------------
-- Builtin Value definition ------------------------------------------------------------------------

type NestedMap = Map K (Map K Quantity)

-- | The underlying type of the UPLC built-in type @Value@.
data Value
  = Value
      !NestedMap
      {-^ Map from (currency symbol, token name) to quantity.

      Invariants: no empty inner map, and no zero quantity. -}
      !(IntMap Int)
      {-^ Map from size to the number of inner maps that have that size.
      This allows efficient retrieval of the size of the largest inner map,
      which is useful for costing of operations like `lookupCoin`.

      Invariant: all values are positive. -}
      {-# UNPACK #-} !Int
      {-^ Total size, i.e., sum total of inner map sizes. This avoids recomputing
      the total size during the costing of operations like `unionValue`. -}
      {-# UNPACK #-} !Int
      -- ^ The number of negative amounts it contains.
  deriving stock (Eq, Show, Generic)
  deriving anyclass (NFData)

instance Hashable Value where
  hash = hash . unpack
  {-# INLINE hash #-}
  hashWithSalt salt = hashWithSalt salt . unpack
  {-# INLINE hashWithSalt #-}

instance CBOR.Serialise Value where
  encode (Value v _ _ _) = CBOR.encode v
  {-# INLINE encode #-}
  decode = pack <$> CBOR.decode
  {-# INLINE decode #-}

instance Flat.Flat Value where
  encode (Value v _ _ _) = Flat.encode v
  {-# INLINE encode #-}
  decode = pack <$> Flat.decode
  {-# INLINE decode #-}

{-| Unpack a `Value` into a map from (currency symbol, token name) to quantity.

The map is guaranteed to not contain empty inner map or zero quantity. -}
unpack :: Value -> NestedMap
unpack (Value v _ _ _) = v
{-# INLINE unpack #-}

{-| Pack a map from (currency symbol, token name) to quantity into a `Value`.

The map will be filtered so that it does not contain empty inner map or zero quantity. -}
pack :: NestedMap -> Value
pack = pack' . normalize
{-# INLINE pack #-}

-- | Like `pack` but does not normalize.
pack' :: NestedMap -> Value
pack' v = Value v sizes size neg
  where
    (sizes, size, neg) = Map.foldl' alg (mempty, 0, 0) v
    alg (ss, s, n) inner =
      ( IntMap.alter (maybe (Just 1) (Just . (+ 1))) (Map.size inner) ss
      , s + Map.size inner
      , n + Map.size (Map.filter (< zeroQuantity) inner)
      )
{-# INLINEABLE pack' #-}

{-| Total size, i.e., the number of distinct `(currency symbol, token name)` pairs
contained in the `Value`. -}
totalSize :: Value -> Int
totalSize (Value _ _ size _) = size
{-# INLINE totalSize #-}

-- | Size of the largest inner map.
maxInnerSize :: Value -> Int
maxInnerSize (Value _ sizes _ _) = maybe 0 fst (IntMap.lookupMax sizes)
{-# INLINE maxInnerSize #-}

negativeAmounts :: Value -> Int
negativeAmounts (Value _ _ _ neg) = neg
{-# INLINE negativeAmounts #-}

empty :: Value
empty = Value mempty mempty 0 0
{-# INLINE empty #-}

toList :: Value -> [(K, [(K, Quantity)])]
toList = Map.toList . Map.map Map.toList . unpack
{-# INLINEABLE toList #-}

toFlatList :: Value -> [(K, K, Quantity)]
toFlatList (toList -> xs) = [(c, t, a) | (c, ys) <- xs, (t, a) <- ys]
{-# INLINEABLE toFlatList #-}

fromList :: [(K, [(K, Quantity)])] -> BuiltinResult Value
fromList xs = do
  -- Use unchecked addition during construction
  let outerMap =
        Map.fromListWith
          (Map.unionWith unsafeAddQuantity) -- combine inner maps with unchecked addition
          (second (Map.fromListWith unsafeAddQuantity) <$> xs)
  -- Validate all quantities are within bounds
  pack <$> validateQuantities outerMap
{-# INLINEABLE fromList #-}

-- | Unsafe addition of quantities without bounds checking.
unsafeAddQuantity :: Quantity -> Quantity -> Quantity
unsafeAddQuantity (UnsafeQuantity x) (UnsafeQuantity y) = UnsafeQuantity (x + y)
{-# INLINE unsafeAddQuantity #-}

-- | Validate all quantities in a nested map are within bounds.
validateQuantities :: HasCallStack => NestedMap -> BuiltinResult NestedMap
validateQuantities nestedMap =
  case find isOutOfBounds allQuantities of
    Just (UnsafeQuantity i) -> fail $ context <> ": quantity out of bounds: " <> show i
    Nothing -> pure nestedMap
  where
    allQuantities = concatMap Map.elems $ Map.elems nestedMap
    isOutOfBounds (UnsafeQuantity i) =
      i < unQuantity minBound || i > unQuantity maxBound
    context = case getCallStack callStack of
      (fnName, _) : _ -> fnName
      [] -> "<unknown>"
{-# INLINEABLE validateQuantities #-}

normalize :: NestedMap -> NestedMap
normalize = Map.filter (not . Map.null) . Map.map (Map.filter (/= zeroQuantity))
{-# INLINEABLE normalize #-}

instance Pretty Value where
  pretty = pretty . fmap (bimap toText (fmap (first toText))) . toList
    where
      toText = Text.decodeLatin1 . Base64.encode . unK

{-| \(O(\log \max(m, k))\), where \(m\) is the size of the outer map, and \(k\) is
the size of the largest inner map. -}
insertCoin :: ByteString -> ByteString -> Integer -> Value -> BuiltinResult Value
insertCoin unsafeCurrency unsafeToken unsafeAmount v@(Value outer sizes size neg)
  | unsafeAmount == 0 = pure $ deleteCoin unsafeCurrency unsafeToken v
  | otherwise = case (k unsafeCurrency, k unsafeToken, quantity unsafeAmount) of
      (Nothing, _, _) -> fail $ "insertCoin: invalid currency: " <> show (B.unpack unsafeCurrency)
      (_, Nothing, _) -> fail $ "insertCoin: invalid token: " <> show (B.unpack unsafeToken)
      (_, _, Nothing) -> fail $ "insertCoin: quantity out of bounds: " <> show unsafeAmount
      (Just currency, Just token, Just qty) ->
        let f
              :: Maybe (Map K Quantity)
              -> ( -- Left (old size of inner map) if the total size grows by 1,
                   -- otherwise, Right (old quantity)
                   Either Int Quantity
                 , Maybe (Map K Quantity)
                 )
            f = \case
              Nothing -> (Left 0, Just (Map.singleton token qty))
              Just inner ->
                let (mOldQuantity, inner') =
                      Map.insertLookupWithKey (\_ _ _ -> qty) token qty inner
                 in (maybe (Left (Map.size inner)) Right mOldQuantity, Just inner')
            (res, outer') = Map.alterF f currency outer
            (sizes', size', neg') = case res of
              Left oldSize ->
                ( updateSizes oldSize (oldSize + 1) sizes
                , size + 1
                , if qty < zeroQuantity then neg + 1 else neg
                )
              Right oldQuantity ->
                ( sizes
                , size
                , if oldQuantity < zeroQuantity && qty > zeroQuantity
                    then neg - 1
                    else
                      if oldQuantity > zeroQuantity && qty < zeroQuantity
                        then neg + 1
                        else neg
                )
         in pure $ Value outer' sizes' size' neg'
{-# INLINEABLE insertCoin #-}

-- | \(O(\log \max(m, k))\)
deleteCoin :: ByteString -> ByteString -> Value -> Value
deleteCoin (UnsafeK -> currency) (UnsafeK -> token) (Value outer sizes size neg) =
  Value outer' sizes' size' neg'
  where
    (mold, outer') = Map.alterF f currency outer
    (sizes', size', neg') = case mold of
      Just (oldSize, oldQuantity) ->
        ( updateSizes oldSize (oldSize - 1) sizes
        , size - 1
        , if oldQuantity < zeroQuantity then neg - 1 else neg
        )
      Nothing -> (sizes, size, neg)
    f
      :: Maybe (Map K Quantity)
      -> ( -- Just (old size of inner map, old quantity) if the total size shrinks by 1,
           -- otherwise Nothing
           Maybe (Int, Quantity)
         , Maybe (Map K Quantity)
         )
    f = \case
      Nothing -> (Nothing, Nothing)
      Just inner ->
        let (qty, inner') = Map.updateLookupWithKey (\_ _ -> Nothing) token inner
         in ((Map.size inner,) <$> qty, if Map.null inner' then Nothing else Just inner')

-- | \(O(\log \max(m, k))\)
lookupCoin :: ByteString -> ByteString -> Value -> Integer
lookupCoin (UnsafeK -> currency) (UnsafeK -> token) (unpack -> outer) =
  case Map.lookup currency outer of
    Nothing -> 0
    Just inner -> unQuantity $ Map.findWithDefault zeroQuantity token inner

{-| \(O(n_{2}\log \max(m_{1}, k_{1}))\), where \(n_{2}\) is the total size of the second
`Value`, \(m_{1}\) is the size of the outer map in the first `Value` and \(k_{1}\) is
the size of the largest inner map in the first `Value`.

@a@ contains @b@ if for each @(currency, token, quantity)@ in @b@,
@lookup currency token a >= quantity@.

Both values must not contain negative amounts. -}
valueContains :: Value -> Value -> BuiltinResult Bool
valueContains v1 v2
  | negativeAmounts v1 > 0 = fail "valueContains: first value contains negative amounts"
  | negativeAmounts v2 > 0 = fail "valueContains: second value contains negative amounts"
  | totalSize v1 < totalSize v2 = False -- v1 can't possibly contain v2 because v2's too big.
  | otherwise = BuiltinSuccess $ Map.isSubmapOfBy (Map.isSubmapOfBy (<=)) (unpack v2) (unpack v1)
{-# INLINEABLE valueContains #-}

{-| \(O(n_{1}) + O(n_{2})\), where \(n_{1}\) and \(n_{2}\) are the total sizes
(i.e., sum of inner map sizes) of the two maps.

Shortcircuits if either value is empty.

Since 'unionValue' is commutative, we switch the arguments whenever the second
value is larger in total size than the first one. We have found through experimentation
that this results in better performance in practice. -}
unionValue :: Value -> Value -> BuiltinResult Value
unionValue vA vB
  | totalSize vA == 0 = BuiltinSuccess vB
  | totalSize vB == 0 = BuiltinSuccess vA
  | otherwise =
      pack'
        <$> M.mergeA
          M.preserveMissing
          M.preserveMissing
          ( M.zipWithMaybeAMatched \_ innerA innerB ->
              fmap (\inner -> if Map.null inner then Nothing else Just inner) $
                M.mergeA
                  M.preserveMissing
                  M.preserveMissing
                  ( M.zipWithMaybeAMatched \_ x y ->
                      case addQuantity x y of
                        Just z -> pure if z == zeroQuantity then Nothing else Just z
                        Nothing ->
                          fail "unionValue: quantity is out of the signed 128-bit integer bounds"
                  )
                  innerA
                  innerB
          )
          v1
          v2
  where
    (v1, v2) =
      if totalSize vB > totalSize vA
        then (unpack vB, unpack vA)
        else (unpack vA, unpack vB)
{-# INLINEABLE unionValue #-}

{-| \(O(n)\). Encodes `Value` as `Data`, in the same way as non-builtin @Value@.
This is the denotation of @ValueData@ in Plutus V1, V2 and V3. -}
valueData :: Value -> Data
valueData = Map . fmap (bimap (B . unK) tokensData) . Map.toList . unpack
  where
    tokensData :: Map K Quantity -> Data
    tokensData = Map . fmap (bimap (B . unK) (I . unQuantity)) . Map.toList
{-# INLINEABLE valueData #-}

{-| \(O(n \log n)\). Decodes `Data` into `Value`, in the same way as non-builtin @Value@.
This is the denotation of @UnValueData@ in Plutus V1, V2 and V3. -}
unValueData :: Data -> BuiltinResult Value
unValueData =
  fmap pack . \case
    Map cs -> do
      -- Use unchecked addition during construction
      outerMap <-
        Map.fromListWith (Map.unionWith unsafeAddQuantity) <$> traverse (bitraverse unB unTokens) cs
      -- Validate all quantities are within bounds
      validateQuantities outerMap
    _ -> fail "unValueData: non-Map constructor"
  where
    unB :: Data -> BuiltinResult K
    unB = \case
      B b -> maybe (fail $ "unValueData: invalid key: " <> show (B.unpack b)) pure (k b)
      _ -> fail "unValueData: non-B constructor"

    unQ :: Data -> BuiltinResult Quantity
    unQ = \case
      I i -> pure (UnsafeQuantity i)
      _ -> fail "unValueData: non-I constructor"

    unTokens :: Data -> BuiltinResult (Map K Quantity)
    unTokens = \case
      Map ts -> fmap (Map.fromListWith unsafeAddQuantity) (traverse (bitraverse unB unQ) ts)
      _ -> fail "unValueData: non-Map constructor"
{-# INLINEABLE unValueData #-}

-- | Decrement bucket @old@, and increment bucket @new@.
updateSizes :: Int -> Int -> IntMap Int -> IntMap Int
updateSizes old new = dec . inc
  where
    inc =
      if new == 0
        then id
        else IntMap.alter (maybe (Just 1) (Just . (+ 1))) new
    dec =
      if old == 0
        then id
        else IntMap.update (\n -> if n <= 1 then Nothing else Just (n - 1)) old
{-# INLINEABLE updateSizes #-}

-- | \(O(n)\). Scale each token by the given constant factor.
scaleValue :: Integer -> Value -> BuiltinResult Value
scaleValue c (Value outer sizes size neg)
  -- When scaling by positive factor, no need to change sizes and number of negative amounts.
  | c > 0 = do
      outer' <- go outer
      BuiltinSuccess $ Value outer' sizes size neg
  -- When scaling by negative factor, only need to "flip" negative amounts.
  | c < 0 = do
      outer' <- go outer
      BuiltinSuccess $ Value outer' sizes size (size - neg)
  -- Scaling by 0 is always empty value
  | otherwise = BuiltinSuccess empty
  where
    go :: NestedMap -> BuiltinResult NestedMap
    go x = traverse (traverse goScale) x
    goScale :: Quantity -> BuiltinResult Quantity
    goScale x =
      case scaleQuantity c x of
        Nothing ->
          fail $
            "scaleValue: quantity out of bounds: "
              <> show c
              <> " * "
              <> show (unQuantity x)
        Just q -> pure q
