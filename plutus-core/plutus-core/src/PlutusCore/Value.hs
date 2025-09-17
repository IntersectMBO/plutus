{-# LANGUAGE DeriveAnyClass    #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE ViewPatterns      #-}

module PlutusCore.Value (
  Value, -- Do not expose data constructor
  NestedMap,
  unpack,
  pack,
  empty,
  fromList,
  toList,
  toFlatList,
  totalSize,
  maxInnerSize,
  insertCoin,
  deleteCoin,
  unionValue,
  valueData,
  unValueData,
) where

import Codec.Serialise (Serialise)
import Control.DeepSeq (NFData)
import Data.Bifunctor
import Data.Bitraversable
import Data.ByteString (ByteString)
import Data.ByteString.Base64 qualified as Base64
import Data.Hashable (Hashable)
import Data.IntMap.Strict (IntMap)
import Data.IntMap.Strict qualified as IntMap
import Data.Map.Merge.Strict qualified as M
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Maybe
import Data.Text.Encoding qualified as Text
import GHC.Generics
import PlutusCore.Builtin.Result
import PlutusCore.Data (Data (..))
import PlutusPrelude (Pretty (..))

type NestedMap = Map ByteString (Map ByteString Integer)

-- | The underlying type of the UPLC built-in type @Value@.
data Value
  = Value
      !NestedMap
      {- ^ Map from (currency symbol, token name) to amount.

      Invariants: no empty inner map, and no zero amount.
      -}
      !(IntMap Int)
      {- ^ Map from size to the number of inner maps that have that size,
      useful for efficient retrieval of the size of the largest inner map.

      Invariant: all values are positive.
      -}
      {-# UNPACK #-} !Int
      -- ^ Total size, i.e., sum total of inner map sizes
  deriving stock (Eq, Show, Generic)
  deriving anyclass (Hashable, Serialise, NFData)

{-| Unpack a `Value` into a map from (currency symbol, token name) to amount.

The map is guaranteed to not contain empty inner map or zero amount.
-}
unpack :: Value -> NestedMap
unpack (Value v _ _) = v
{-# INLINE unpack #-}

{-| Pack a map from (currency symbol, token name) to amount into a `Value`.

The map will be filtered so that it does not contain empty inner map or zero amount.
-}
pack :: NestedMap -> Value
pack = pack' . normalize
{-# INLINE pack #-}

-- | Like `pack` but does not normalize.
pack' :: NestedMap -> Value
pack' (normalize -> v) = Value v sizes size
 where
  (sizes, size) = Map.foldl' alg (mempty, 0) v
  alg (ss, s) inner =
    ( IntMap.alter (maybe (Just 1) (Just . (+ 1))) (Map.size inner) ss
    , s + Map.size inner
    )
{-# INLINEABLE pack' #-}

{-| Total size, i.e., the number of distinct `(currency symbol, token name)` pairs
contained in the `Value`.
-}
totalSize :: Value -> Int
totalSize (Value _ _ size) = size
{-# INLINE totalSize #-}

-- | Size of the largest inner map.
maxInnerSize :: Value -> Int
maxInnerSize (Value _ sizes _) = maybe 0 fst (IntMap.lookupMax sizes)
{-# INLINE maxInnerSize #-}

empty :: Value
empty = Value mempty mempty 0
{-# INLINE empty #-}

toList :: Value -> [(ByteString, [(ByteString, Integer)])]
toList = Map.toList . Map.map Map.toList . unpack
{-# INLINEABLE toList #-}

toFlatList :: Value -> [(ByteString, ByteString, Integer)]
toFlatList (toList -> xs) = [(c, t, a) | (c, ys) <- xs, (t, a) <- ys]
{-# INLINEABLE toFlatList #-}

fromList :: [(ByteString, [(ByteString, Integer)])] -> Value
fromList =
  pack
    . Map.fromListWith (Map.unionWith (+))
    . fmap (second (Map.fromListWith (+)))

normalize :: NestedMap -> NestedMap
normalize = Map.filter (not . Map.null) . Map.map (Map.filter (/= 0))
{-# INLINEABLE normalize #-}

instance Pretty Value where
  pretty = pretty . fmap (bimap toText (fmap (first toText))) . toList
   where
    toText = Text.decodeLatin1 . Base64.encode

{-| \(O(\log \max(m, k))\), where \(m\) is the size of the outer map, and \(k\) is
the size of the largest inner map.
-}
insertCoin :: ByteString -> ByteString -> Integer -> Value -> Value
insertCoin currency token amt v@(Value outer sizes size)
  | amt == 0 = deleteCoin currency token v
  | otherwise =
      let (mold, outer') = Map.alterF f currency outer
          (sizes', size') = case mold of
            Just old -> (updateSizes old (old + 1) sizes, size + 1)
            Nothing  -> (sizes, size)
       in Value outer' sizes' size'
 where
  f
    :: Maybe (Map ByteString Integer)
    -> ( Maybe Int -- Just (old size of inner map) if the total size grows by 1, otherwise Nothing
       , Maybe (Map ByteString Integer)
       )
  f = \case
    Nothing -> (Just 0, Just (Map.singleton token amt))
    Just inner ->
      let (isJust -> exists, inner') = Map.insertLookupWithKey (\_ _ _ -> amt) token amt inner
       in (if exists then Nothing else Just (Map.size inner), Just inner')
{-# INLINEABLE insertCoin #-}

-- TODO: implement properly
deleteCoin :: ByteString -> ByteString -> Value -> Value
deleteCoin currency token (Value outer _ _) =
  pack $ case Map.lookup currency outer of
    Nothing    -> outer
    Just inner -> Map.insert currency (Map.delete token inner) outer

{-| The precise complexity is complicated, but an upper bound
is \(O(n_{1} \log n_{2}) + O(m)\), where \(n_{1}\) is the total size of the smaller
value, \(n_{2}\) is the total size of the bigger value, and \(m\) is the
combined size of the outer maps.
-}
unionValue :: Value -> Value -> Value
unionValue (unpack -> vA) (unpack -> vB) =
  pack' $
    M.merge
      M.preserveMissing
      M.preserveMissing
      ( M.zipWithMaybeMatched $ \_ innerA innerB ->
          let inner =
                M.merge
                  M.preserveMissing
                  M.preserveMissing
                  ( M.zipWithMaybeMatched $ \_ x y ->
                      let z = x + y in if z == 0 then Nothing else Just z
                  )
                  innerA
                  innerB
           in if Map.null inner
                then Nothing
                else
                  Just inner
      )
      vA
      vB
{-# INLINEABLE unionValue #-}

-- | \(O(n)\). Encodes `Value` as `Data`, in the same way as non-builtin @Value@.
-- This is the denotation of @ValueData@ in Plutus V1, V2 and V3.
valueData :: Value -> Data
valueData = Map . fmap (bimap B tokensData) . Map.toList . unpack
  where
    tokensData :: Map ByteString Integer -> Data
    tokensData = Map . fmap (bimap B I) . Map.toList
{-# INLINEABLE valueData #-}

-- | \(O(n \log n)\). Decodes `Data` into `Value`, in the same way as non-builtin @Value@.
-- This is the denotation of @UnValueData@ in Plutus V1, V2 and V3.
unValueData :: Data -> BuiltinResult Value
unValueData = fmap pack . \case
  Map cs -> fmap (Map.fromListWith (Map.unionWith (+))) (traverse (bitraverse unB unTokens) cs)
  _ -> fail "unValueData: non-Map constructor"
  where
    unB :: Data -> BuiltinResult ByteString
    unB = \case
      B b -> pure b
      _ -> fail "unValueData: non-B constructor"

    unI :: Data -> BuiltinResult Integer
    unI = \case
      I i -> pure i
      _ -> fail "unValueData: non-I constructor"

    unTokens :: Data -> BuiltinResult (Map ByteString Integer)
    unTokens = \case
      Map ts -> fmap (Map.fromListWith (+)) (traverse (bitraverse unB unI) ts)
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
