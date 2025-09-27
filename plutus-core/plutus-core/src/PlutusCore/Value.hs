{-# LANGUAGE DeriveAnyClass    #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE ViewPatterns      #-}

module PlutusCore.Value (
  Value, -- Do not expose data constructor
  K, -- Do not expose data constructor
  k,
  unK,
  maxKeyLen,
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
  lookupCoin,
  valueContains,
  unionValue,
  valueData,
  unValueData,
) where

import Codec.Serialise qualified as CBOR
import Control.DeepSeq (NFData)
import Data.Bifunctor
import Data.Bitraversable
import Data.ByteString (ByteString)
import Data.ByteString qualified as B
import Data.ByteString.Base64 qualified as Base64
import Data.Functor
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
import PlutusCore.Flat qualified as Flat
import PlutusPrelude (Pretty (..))

-- Max length (in bytes) for currency symbols and token names in `Value`,
-- both of which cannot exceed 32 bytes. Currency symbols are in fact either
-- empty or 28 bytes, but for simplicity we allow anything between 0 and 32 bytes.
maxKeyLen :: Int
maxKeyLen = 32
{-# INLINE maxKeyLen #-}

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

type NestedMap = Map K (Map K Integer)

-- | The underlying type of the UPLC built-in type @Value@.
data Value
  = Value
      !NestedMap
      {- ^ Map from (currency symbol, token name) to amount.

      Invariants: no empty inner map, and no zero amount.
      -}
      !(IntMap Int)
      {- ^ Map from size to the number of inner maps that have that size.
      This allows efficient retrieval of the size of the largest inner map,
      which is useful for costing of operations like `lookupCoin`.

      Invariant: all values are positive.
      -}
      {-# UNPACK #-} !Int
      {- ^ Total size, i.e., sum total of inner map sizes. This avoids recomputing
      the total size during the costing of operations like `unionValue`.
      -}
  deriving stock (Eq, Show, Generic)
  deriving anyclass (Hashable, NFData)

instance CBOR.Serialise Value where
  encode (Value v _ _) = CBOR.encode v
  {-# INLINE encode #-}
  decode = pack <$> CBOR.decode
  {-# INLINE decode #-}

instance Flat.Flat Value where
  encode (Value v _ _) = Flat.encode v
  {-# INLINE encode #-}
  decode = pack <$> Flat.decode
  {-# INLINE decode #-}

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
pack' v = Value v sizes size
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

toList :: Value -> [(K, [(K, Integer)])]
toList = Map.toList . Map.map Map.toList . unpack
{-# INLINEABLE toList #-}

toFlatList :: Value -> [(K, K, Integer)]
toFlatList (toList -> xs) = [(c, t, a) | (c, ys) <- xs, (t, a) <- ys]
{-# INLINEABLE toFlatList #-}

fromList :: [(K, [(K, Integer)])] -> Value
fromList =
  pack
    . Map.fromListWith (Map.unionWith (+))
    . fmap (second (Map.fromListWith (+)))
{-# INLINEABLE fromList #-}

normalize :: NestedMap -> NestedMap
normalize = Map.filter (not . Map.null) . Map.map (Map.filter (/= 0))
{-# INLINEABLE normalize #-}

instance Pretty Value where
  pretty = pretty . fmap (bimap toText (fmap (first toText))) . toList
   where
    toText = Text.decodeLatin1 . Base64.encode . unK

{-| \(O(\log \max(m, k))\), where \(m\) is the size of the outer map, and \(k\) is
the size of the largest inner map.
-}
insertCoin :: ByteString -> ByteString -> Integer -> Value -> BuiltinResult Value
insertCoin currency token amt v@(Value outer sizes size)
  | amt == 0 = pure $ deleteCoin currency token v
  | otherwise = case (k currency, k token) of
      (Nothing, _) -> fail $ "insertCoin: invalid currency: " <> show (B.unpack currency)
      (_, Nothing) -> fail $ "insertCoin: invalid token: " <> show (B.unpack token)
      (Just ck, Just tk) ->
        let f
              :: Maybe (Map K Integer)
              -> ( -- Just (old size of inner map) if the total size grows by 1,
                   -- otherwise Nothing
                   Maybe Int
                 , Maybe (Map K Integer)
                 )
            f = \case
              Nothing -> (Just 0, Just (Map.singleton tk amt))
              Just inner ->
                let (isJust -> exists, inner') =
                      Map.insertLookupWithKey (\_ _ _ -> amt) tk amt inner
                 in (if exists then Nothing else Just (Map.size inner), Just inner')
            (mold, outer') = Map.alterF f ck outer
            (sizes', size') = case mold of
              Just old -> (updateSizes old (old + 1) sizes, size + 1)
              Nothing  -> (sizes, size)
         in pure $ Value outer' sizes' size'
{-# INLINEABLE insertCoin #-}

-- | \(O(\log \max(m, k))\)
deleteCoin :: ByteString -> ByteString -> Value -> Value
deleteCoin (UnsafeK -> currency) (UnsafeK -> token) (Value outer sizes size) =
  Value outer' sizes' size'
 where
  (mold, outer') = Map.alterF f currency outer
  (sizes', size') = case mold of
    Just old -> (updateSizes old (old - 1) sizes, size - 1)
    Nothing  -> (sizes, size)
  f
    :: Maybe (Map K Integer)
    -> ( -- Just (old size of inner map) if the total size shrinks by 1, otherwise Nothing
         Maybe Int
       , Maybe (Map K Integer)
       )
  f = \case
    Nothing -> (Nothing, Nothing)
    Just inner ->
      let (amt, inner') = Map.updateLookupWithKey (\_ _ -> Nothing) token inner
       in (amt $> Map.size inner, if Map.null inner' then Nothing else Just inner')

-- | \(O(\log \max(m, k))\)
lookupCoin :: ByteString -> ByteString -> Value -> Integer
lookupCoin (UnsafeK -> currency) (UnsafeK -> token) (unpack -> outer) =
  case Map.lookup currency outer of
    Nothing    -> 0
    Just inner -> Map.findWithDefault 0 token inner

{-| \(O(n_{2}\log \max(m_{1}, k_{1}))\), where \(n_{2}\) is the total size of the second
`Value`, \(m_{1}\) is the size of the outer map in the first `Value` and \(k_{1}\) is
the size of the largest inner map in the first `Value`.

@a@ contains @b@ if for each @(currency, token, amount)@ in @b@, if @amount > 0@, then
@lookup currency token a >= amount@, and if @amount < 0@, then
@lookup currency token a == amount@.
-}
valueContains :: Value -> Value -> Bool
valueContains v = Map.foldrWithKey' go True . unpack
 where
  go c inner = (&&) (Map.foldrWithKey' goInner True inner)
   where
    goInner t a2 =
      (&&)
        ( let a1 = lookupCoin (unK c) (unK t) v
           in if a2 > 0
                then a1 >= a2
                else a1 == a2
        )

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

{-| \(O(n)\). Encodes `Value` as `Data`, in the same way as non-builtin @Value@.
This is the denotation of @ValueData@ in Plutus V1, V2 and V3.
-}
valueData :: Value -> Data
valueData = Map . fmap (bimap (B . unK) tokensData) . Map.toList . unpack
 where
  tokensData :: Map K Integer -> Data
  tokensData = Map . fmap (bimap (B . unK) I) . Map.toList
{-# INLINEABLE valueData #-}

{-| \(O(n \log n)\). Decodes `Data` into `Value`, in the same way as non-builtin @Value@.
This is the denotation of @UnValueData@ in Plutus V1, V2 and V3.
-}
unValueData :: Data -> BuiltinResult Value
unValueData =
  fmap pack . \case
    Map cs -> fmap (Map.fromListWith (Map.unionWith (+))) (traverse (bitraverse unB unTokens) cs)
    _ -> fail "unValueData: non-Map constructor"
 where
  unB :: Data -> BuiltinResult K
  unB = \case
    B b -> pure (UnsafeK b)
    _ -> fail "unValueData: non-B constructor"

  unI :: Data -> BuiltinResult Integer
  unI = \case
    I i -> pure i
    _ -> fail "unValueData: non-I constructor"

  unTokens :: Data -> BuiltinResult (Map K Integer)
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
