{-# LANGUAGE FlexibleContexts, OverlappingInstances #-}
module Tests.Marshal (
  tests
) where

import Test.Framework (Test, testGroup)
import Test.Framework.Providers.QuickCheck2 (testProperty)
import GHCJS.Marshal.Pure (PFromJSVal(..), PToJSVal(..))
import GHCJS.Marshal (FromJSVal(..), ToJSVal(..))
import Tests.QuickCheckUtils (eq)
import Test.QuickCheck.Monadic (run, monadicIO)
import Test.QuickCheck (once, Arbitrary(..), Property)
import Data.Int (Int32, Int16, Int8)
import Data.Word (Word32, Word16, Word8)
import Data.Text (Text)
import qualified Data.Text as T (unpack, pack)
import Data.JSString (JSString)

newtype TypeName a = TypeName String

pure_to_from_jsval' :: (PToJSVal a, PFromJSVal a, Eq a) => a -> Bool
pure_to_from_jsval' a = pFromJSVal (pToJSVal a) == a

pure_to_from_jsval :: (PToJSVal a, PFromJSVal a, Eq a) => TypeName a -> a -> Bool
pure_to_from_jsval _ = pure_to_from_jsval'

pure_to_from_jsval_maybe :: (PToJSVal a, PFromJSVal a, Eq a) => TypeName a -> Maybe a -> Bool
pure_to_from_jsval_maybe _ = pure_to_from_jsval'

to_from_jsval' :: (ToJSVal a, FromJSVal a, Eq a) => a -> Property
to_from_jsval' a = monadicIO $ do
    b <- run $ toJSVal a >>= fromJSValUnchecked
    return $ b == a

to_from_jsval :: (ToJSVal a, FromJSVal a, Eq a) => TypeName a -> a -> Property
to_from_jsval _ = to_from_jsval'

to_from_jsval_maybe :: (ToJSVal a, FromJSVal a, Eq a) => TypeName a -> Maybe a -> Property
to_from_jsval_maybe _ = to_from_jsval'

to_from_jsval_list :: (ToJSVal a, FromJSVal a, Eq a) => TypeName a -> [a] -> Property
to_from_jsval_list _ = to_from_jsval'

to_from_jsval_list_maybe :: (ToJSVal a, FromJSVal a, Eq a) => TypeName a -> [Maybe a] -> Property
to_from_jsval_list_maybe _ = to_from_jsval'

to_from_jsval_list_list :: (ToJSVal a, FromJSVal a, Eq a) => TypeName a -> [[a]] -> Property
to_from_jsval_list_list _ = to_from_jsval'

to_from_jsval_maybe_list :: (ToJSVal a, FromJSVal a, Eq a) => TypeName a -> Maybe [a] -> Property
to_from_jsval_maybe_list _ = to_from_jsval'

pureMarshalTestGroup :: (PToJSVal a, PFromJSVal a, ToJSVal a, FromJSVal a, Eq a, Show a, Arbitrary a) => TypeName a -> Test
pureMarshalTestGroup t@(TypeName n) =
    testGroup n [
        testProperty "pure_to_from_jsval"       (pure_to_from_jsval t),
        testProperty "pure_to_from_jsval_maybe" (pure_to_from_jsval_maybe t),
        testProperty "to_from_jsval"            (to_from_jsval t),
        testProperty "to_from_jsval_maybe"      (to_from_jsval_maybe t),
        testProperty "to_from_jsval_list"       (to_from_jsval_list t),
        testProperty "to_from_jsval_list_maybe" (to_from_jsval_list_maybe t),
        testProperty "to_from_jsval_list_list"  (once $ to_from_jsval_list_list t),
        testProperty "to_from_jsval_maybe_list" (to_from_jsval_maybe_list t)
    ]

marshalTestGroup :: (ToJSVal a, FromJSVal a, Eq a, Show a, Arbitrary a) => TypeName a -> Test
marshalTestGroup t@(TypeName n) =
  testGroup n [testProperty "to_from_jsval" (to_from_jsval t)]

instance Arbitrary Text where
    arbitrary = T.pack <$> arbitrary
    shrink = map T.pack . shrink . T.unpack

tests :: Test
tests =
  testGroup "Marshal" [
    pureMarshalTestGroup (TypeName "Bool"     :: TypeName Bool    ),
    pureMarshalTestGroup (TypeName "Int"      :: TypeName Int     ),
    pureMarshalTestGroup (TypeName "Int8"     :: TypeName Int8    ),
    pureMarshalTestGroup (TypeName "Int16"    :: TypeName Int16   ),
    pureMarshalTestGroup (TypeName "Int32"    :: TypeName Int32   ),
    pureMarshalTestGroup (TypeName "Word"     :: TypeName Word    ),
    pureMarshalTestGroup (TypeName "Word8"    :: TypeName Word8   ),
    pureMarshalTestGroup (TypeName "Word16"   :: TypeName Word16  ),
    pureMarshalTestGroup (TypeName "Word32"   :: TypeName Word32  ),
    pureMarshalTestGroup (TypeName "Float"    :: TypeName Float   ),
    pureMarshalTestGroup (TypeName "Double"   :: TypeName Double  ),
    pureMarshalTestGroup (TypeName "[Char]"   :: TypeName [Char]  ),
    pureMarshalTestGroup (TypeName "Text"     :: TypeName Text    ),
    pureMarshalTestGroup (TypeName "JSString" :: TypeName JSString)
  ]
