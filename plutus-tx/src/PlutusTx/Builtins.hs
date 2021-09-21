{-# OPTIONS_GHC -fno-omit-interface-pragmas #-}
{-# OPTIONS_GHC -fno-ignore-interface-pragmas #-}

-- | Primitive names and functions for working with Plutus Core builtins.
module PlutusTx.Builtins (
                                -- * Bytestring builtins
                                BuiltinByteString
                                , appendByteString
                                , consByteString
                                , sliceByteString
                                , lengthOfByteString
                                , indexByteString
                                , emptyByteString
                                , equalsByteString
                                , lessThanByteString
                                , lessThanEqualsByteString
                                , greaterThanByteString
                                , greaterThanEqualsByteString
                                , sha2_256
                                , sha3_256
                                , blake2b_256
                                , verifySignature
                                , decodeUtf8
                                -- * Integer builtins
                                , Integer
                                , addInteger
                                , subtractInteger
                                , multiplyInteger
                                , divideInteger
                                , modInteger
                                , quotientInteger
                                , remainderInteger
                                , greaterThanInteger
                                , greaterThanEqualsInteger
                                , lessThanInteger
                                , lessThanEqualsInteger
                                , equalsInteger
                                -- * Error
                                , error
                                -- * Data
                                , BuiltinData
                                , chooseData
                                , matchData
                                , matchData'
                                , equalsData
                                , mkConstr
                                , mkMap
                                , mkList
                                , mkI
                                , mkB
                                , unsafeDataAsConstr
                                , unsafeDataAsMap
                                , unsafeDataAsList
                                , unsafeDataAsI
                                , unsafeDataAsB
                                , BI.builtinDataToData
                                , BI.dataToBuiltinData
                                -- * Strings
                                , BuiltinString
                                , appendString
                                , emptyString
                                , equalsString
                                , encodeUtf8
                                -- * Lists
                                , matchList
                                -- * Tracing
                                , trace
                                -- * Conversions
                                , fromBuiltin
                                , toBuiltin
                                ) where

import           PlutusTx.Base              (const, uncurry)
import           PlutusTx.Bool              (Bool (..))
import           PlutusTx.Builtins.Class
import           PlutusTx.Builtins.Internal (BuiltinByteString (..), BuiltinData, BuiltinString)
import qualified PlutusTx.Builtins.Internal as BI
import           PlutusTx.Integer           (Integer)

{-# INLINABLE appendByteString #-}
-- | Concatenates two 'ByteString's.
appendByteString :: BuiltinByteString -> BuiltinByteString -> BuiltinByteString
appendByteString = BI.appendByteString

{-# INLINABLE consByteString #-}
-- | Adds a byte to the front of a 'ByteString'.
consByteString :: Integer -> BuiltinByteString -> BuiltinByteString
consByteString n bs = BI.consByteString (toBuiltin n) bs

{-# INLINABLE sliceByteString #-}
-- | Returns the substring of a 'ByteString' from index 'start' of length 'n'.
sliceByteString :: Integer -> Integer -> BuiltinByteString -> BuiltinByteString
sliceByteString start n bs = BI.sliceByteString (toBuiltin start) (toBuiltin n) bs

{-# INLINABLE lengthOfByteString #-}
-- | Returns the length of a 'ByteString'.
lengthOfByteString :: BuiltinByteString -> Integer
lengthOfByteString = BI.lengthOfByteString

{-# INLINABLE indexByteString #-}
-- | Returns the byte of a 'ByteString' at index.
indexByteString :: BuiltinByteString -> Integer -> Integer
indexByteString b n = BI.indexByteString b (toBuiltin n)

{-# INLINABLE emptyByteString #-}
-- | An empty 'ByteString'.
emptyByteString :: BuiltinByteString
emptyByteString = BI.emptyByteString

{-# INLINABLE sha2_256 #-}
-- | The SHA2-256 hash of a 'ByteString'
sha2_256 :: BuiltinByteString -> BuiltinByteString
sha2_256 = BI.sha2_256

{-# INLINABLE sha3_256 #-}
-- | The SHA3-256 hash of a 'ByteString'
sha3_256 :: BuiltinByteString -> BuiltinByteString
sha3_256 = BI.sha3_256

{-# INLINABLE blake2b_256 #-}
-- | The BLAKE2B-256 hash of a 'ByteString'
blake2b_256 :: BuiltinByteString -> BuiltinByteString
blake2b_256 = BI.blake2b_256

{-# INLINABLE verifySignature #-}
-- | Verify that the signature is a signature of the message by the public key.
verifySignature :: BuiltinByteString -> BuiltinByteString -> BuiltinByteString -> Bool
verifySignature pubKey message signature = fromBuiltin (BI.verifySignature pubKey message signature)

{-# INLINABLE equalsByteString #-}
-- | Check if two 'ByteString's are equal.
equalsByteString :: BuiltinByteString -> BuiltinByteString -> Bool
equalsByteString x y = fromBuiltin (BI.equalsByteString x y)

{-# INLINABLE lessThanByteString #-}
-- | Check if one 'ByteString' is less than another.
lessThanByteString :: BuiltinByteString -> BuiltinByteString -> Bool
lessThanByteString x y = fromBuiltin (BI.lessThanByteString x y)

{-# INLINABLE lessThanEqualsByteString #-}
-- | Check if one 'ByteString' is less than or equal to another.
lessThanEqualsByteString :: BuiltinByteString -> BuiltinByteString -> Bool
lessThanEqualsByteString x y = fromBuiltin (BI.lessThanEqualsByteString x y)

{-# INLINABLE greaterThanByteString #-}
-- | Check if one 'ByteString' is greater than another.
greaterThanByteString :: BuiltinByteString -> BuiltinByteString -> Bool
greaterThanByteString x y = BI.ifThenElse (BI.lessThanEqualsByteString x y) False True

{-# INLINABLE greaterThanEqualsByteString #-}
-- | Check if one 'ByteString' is greater than another.
greaterThanEqualsByteString :: BuiltinByteString -> BuiltinByteString -> Bool
greaterThanEqualsByteString x y = BI.ifThenElse (BI.lessThanByteString x y) False True

{-# INLINABLE decodeUtf8 #-}
-- | Converts a ByteString to a String.
decodeUtf8 :: BuiltinByteString -> BuiltinString
decodeUtf8 = BI.decodeUtf8

{-# INLINABLE addInteger #-}
-- | Add two 'Integer's.
addInteger :: Integer -> Integer -> Integer
addInteger x y = fromBuiltin (BI.addInteger (toBuiltin x) (toBuiltin y))

{-# INLINABLE subtractInteger #-}
-- | Subtract two 'Integer's.
subtractInteger :: Integer -> Integer -> Integer
subtractInteger x y = fromBuiltin (BI.subtractInteger (toBuiltin x) (toBuiltin y))

{-# INLINABLE multiplyInteger #-}
-- | Multiply two 'Integer's.
multiplyInteger :: Integer -> Integer -> Integer
multiplyInteger x y = fromBuiltin (BI.multiplyInteger (toBuiltin x) (toBuiltin y))

{-# INLINABLE divideInteger #-}
-- | Divide two integers.
divideInteger :: Integer -> Integer -> Integer
divideInteger x y = fromBuiltin (BI.divideInteger (toBuiltin x) (toBuiltin y))

{-# INLINABLE modInteger #-}
-- | Integer modulo operation.
modInteger :: Integer -> Integer -> Integer
modInteger x y = fromBuiltin (BI.modInteger (toBuiltin x) (toBuiltin y))

{-# INLINABLE quotientInteger #-}
-- | Quotient of two integers.
quotientInteger :: Integer -> Integer -> Integer
quotientInteger x y = fromBuiltin (BI.quotientInteger (toBuiltin x) (toBuiltin y))

{-# INLINABLE remainderInteger #-}
-- | Take the remainder of dividing two 'Integer's.
remainderInteger :: Integer -> Integer -> Integer
remainderInteger x y = fromBuiltin (BI.remainderInteger (toBuiltin x) (toBuiltin y))

{-# INLINABLE greaterThanInteger #-}
-- | Check whether one 'Integer' is greater than another.
greaterThanInteger :: Integer -> Integer -> Bool
greaterThanInteger x y = BI.ifThenElse (BI.lessThanEqualsInteger x y ) False True

{-# INLINABLE greaterThanEqualsInteger #-}
-- | Check whether one 'Integer' is greater than or equal to another.
greaterThanEqualsInteger :: Integer -> Integer -> Bool
greaterThanEqualsInteger x y = BI.ifThenElse (BI.lessThanInteger x y) False True

{-# INLINABLE lessThanInteger #-}
-- | Check whether one 'Integer' is less than another.
lessThanInteger :: Integer -> Integer -> Bool
lessThanInteger x y = fromBuiltin (BI.lessThanInteger (toBuiltin x) (toBuiltin y))

{-# INLINABLE lessThanEqualsInteger #-}
-- | Check whether one 'Integer' is less than or equal to another.
lessThanEqualsInteger :: Integer -> Integer -> Bool
lessThanEqualsInteger x y = fromBuiltin (BI.lessThanEqualsInteger (toBuiltin x) (toBuiltin y))

{-# INLINABLE equalsInteger #-}
-- | Check if two 'Integer's are equal.
equalsInteger :: Integer -> Integer -> Bool
equalsInteger x y = fromBuiltin (BI.equalsInteger (toBuiltin x) (toBuiltin y))

{-# INLINABLE error #-}
-- | Aborts evaluation with an error.
error :: () -> a
error x = BI.error (toBuiltin x)

{-# INLINABLE appendString #-}
-- | Append two 'String's.
appendString :: BuiltinString -> BuiltinString -> BuiltinString
appendString = BI.appendString

{-# INLINABLE emptyString #-}
-- | An empty 'String'.
emptyString :: BuiltinString
emptyString = BI.emptyString

{-# INLINABLE equalsString #-}
-- | Check if two strings are equal
equalsString :: BuiltinString -> BuiltinString -> Bool
equalsString x y = fromBuiltin (BI.equalsString x y)

{-# INLINABLE trace #-}
-- | Emit the given string as a trace message before evaluating the argument.
trace :: BuiltinString -> a -> a
trace = BI.trace

{-# INLINABLE encodeUtf8 #-}
-- | Convert a String into a ByteString.
encodeUtf8 :: BuiltinString -> BuiltinByteString
encodeUtf8 = BI.encodeUtf8

matchList :: forall a r . BI.BuiltinList a -> r -> (a -> BI.BuiltinList a -> r) -> r
matchList l nilCase consCase = BI.chooseList l (const nilCase) (\_ -> consCase (BI.head l) (BI.tail l)) ()

{-# INLINABLE chooseData #-}
-- | Given five values for the five different constructors of 'BuiltinData', selects
-- one depending on which corresponds to the actual constructor of the given value.
chooseData :: forall a . BuiltinData -> a -> a -> a -> a -> a -> a
chooseData = BI.chooseData

{-# INLINABLE mkConstr #-}
-- | Constructs a 'BuiltinData' value with the @Constr@ constructor.
mkConstr :: Integer -> [BuiltinData] -> BuiltinData
mkConstr i args = BI.mkConstr (toBuiltin i) (toBuiltin args)

{-# INLINABLE mkMap #-}
-- | Constructs a 'BuiltinData' value with the @Map@ constructor.
mkMap :: [(BuiltinData, BuiltinData)] -> BuiltinData
mkMap es = BI.mkMap (toBuiltin es)

{-# INLINABLE mkList #-}
-- | Constructs a 'BuiltinData' value with the @List@ constructor.
mkList :: [BuiltinData] -> BuiltinData
mkList l = BI.mkList (toBuiltin l)

{-# INLINABLE mkI #-}
-- | Constructs a 'BuiltinData' value with the @I@ constructor.
mkI :: Integer -> BuiltinData
mkI = BI.mkI

{-# INLINABLE mkB #-}
-- | Constructs a 'BuiltinData' value with the @B@ constructor.
mkB :: BuiltinByteString -> BuiltinData
mkB = BI.mkB

{-# INLINABLE unsafeDataAsConstr #-}
-- | Deconstructs a 'BuiltinData' as a @Constr@, or fails if it is not one.
unsafeDataAsConstr :: BuiltinData -> (Integer, [BuiltinData])
unsafeDataAsConstr d = fromBuiltin (BI.unsafeDataAsConstr d)

{-# INLINABLE unsafeDataAsMap #-}
-- | Deconstructs a 'BuiltinData' as a @Map@, or fails if it is not one.
unsafeDataAsMap :: BuiltinData -> [(BuiltinData, BuiltinData)]
unsafeDataAsMap d = fromBuiltin (BI.unsafeDataAsMap d)

{-# INLINABLE unsafeDataAsList #-}
-- | Deconstructs a 'BuiltinData' as a @List@, or fails if it is not one.
unsafeDataAsList :: BuiltinData -> [BuiltinData]
unsafeDataAsList d = fromBuiltin (BI.unsafeDataAsList d)

{-# INLINABLE unsafeDataAsI #-}
-- | Deconstructs a 'BuiltinData' as an @I@, or fails if it is not one.
unsafeDataAsI :: BuiltinData -> Integer
unsafeDataAsI d = fromBuiltin (BI.unsafeDataAsI d)

{-# INLINABLE unsafeDataAsB #-}
-- | Deconstructs a 'BuiltinData' as a @B@, or fails if it is not one.
unsafeDataAsB :: BuiltinData -> BuiltinByteString
unsafeDataAsB = BI.unsafeDataAsB

{-# INLINABLE equalsData #-}
-- | Check if two 'BuiltinData's are equal.
equalsData :: BuiltinData -> BuiltinData -> Bool
equalsData d1 d2 = fromBuiltin (BI.equalsData d1 d2)

{-# INLINABLE matchData #-}
-- | Given a 'BuiltinData' value and matching functions for the five constructors,
-- applies the appropriate matcher to the arguments of the constructor and returns the result.
matchData
    :: BuiltinData
    -> (Integer -> [BuiltinData] -> r)
    -> ([(BuiltinData, BuiltinData)] -> r)
    -> ([BuiltinData] -> r)
    -> (Integer -> r)
    -> (BuiltinByteString -> r)
    -> r
matchData d constrCase mapCase listCase iCase bCase =
   chooseData
   d
   (\_ -> uncurry constrCase (unsafeDataAsConstr d))
   (\_ -> mapCase (unsafeDataAsMap d))
   (\_ -> listCase (unsafeDataAsList d))
   (\_ -> iCase (unsafeDataAsI d))
   (\_ -> bCase (unsafeDataAsB d))
   ()

{-# INLINABLE matchData' #-}
-- | Given a 'BuiltinData' value and matching functions for the five constructors,
-- applies the appropriate matcher to the arguments of the constructor and returns the result.
matchData'
    :: BuiltinData
    -> (Integer -> BI.BuiltinList BuiltinData -> r)
    -> (BI.BuiltinList (BI.BuiltinPair BuiltinData BuiltinData) -> r)
    -> (BI.BuiltinList BuiltinData -> r)
    -> (Integer -> r)
    -> (BuiltinByteString -> r)
    -> r
matchData' d constrCase mapCase listCase iCase bCase =
   chooseData
   d
   (\_ -> let tup = BI.unsafeDataAsConstr d in constrCase (BI.fst tup) (BI.snd tup))
   (\_ -> mapCase (BI.unsafeDataAsMap d))
   (\_ -> listCase (BI.unsafeDataAsList d))
   (\_ -> iCase (unsafeDataAsI d))
   (\_ -> bCase (unsafeDataAsB d))
   ()
