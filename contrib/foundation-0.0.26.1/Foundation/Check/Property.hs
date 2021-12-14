{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE FlexibleInstances #-}
module Foundation.Check.Property
    ( Property(..)
    , PropertyTestArg(..)
    , IsProperty
    , PropertyCheck(..)
    , property
    , checkHasSucceed
    , checkHasFailed
    -- * Properties
    , forAll
    , (===)
    , propertyCompare
    , propertyCompareWith
    , propertyAnd
    , propertyFail
    ) where

import Basement.Imports hiding (Typeable)
import Data.Proxy (Proxy(..))
import Basement.Compat.Typeable
import Foundation.Check.Gen
import Foundation.Check.Arbitrary

import Data.Typeable

type PropertyTestResult = Bool

-- | The type of check this test did for a property
data PropertyCheck =
      PropertyBoolean  PropertyTestResult
    | PropertyNamed    PropertyTestResult String
    | PropertyBinaryOp PropertyTestResult String String String
    | PropertyAnd      PropertyTestResult PropertyCheck PropertyCheck
    | PropertyFail     PropertyTestResult String

checkHasSucceed :: PropertyCheck -> PropertyTestResult
checkHasSucceed (PropertyBoolean b)        = b
checkHasSucceed (PropertyNamed b _)        = b
checkHasSucceed (PropertyBinaryOp b _ _ _) = b
checkHasSucceed (PropertyAnd b _ _)        = b
checkHasSucceed (PropertyFail b _)         = b

checkHasFailed :: PropertyCheck -> PropertyTestResult
checkHasFailed = not . checkHasSucceed

-- | A linked-list of arguments to this test
data PropertyTestArg = PropertyEOA PropertyCheck
                     | PropertyArg String PropertyTestArg

data Property = Prop { unProp :: Gen PropertyTestArg }

class IsProperty p where
    property :: p -> Property

instance IsProperty Bool where
    property b = Prop $ pure (PropertyEOA $ PropertyBoolean b)
instance IsProperty (String, Bool) where
    property (name, b) = Prop $ pure (PropertyEOA $ PropertyNamed b name)
instance IsProperty PropertyCheck where
    property check = Prop $ pure (PropertyEOA check)
instance IsProperty Property where
    property p = p
instance (Show a, Arbitrary a, IsProperty prop) => IsProperty (a -> prop) where
    property p = forAll arbitrary p

-- | Running a generator for a specific type under a property
forAll :: (Show a, IsProperty prop) => Gen a -> (a -> prop) -> Property
forAll generator tst = Prop $ do
    a <- generator
    augment a <$> unProp (property (tst a))
  where
    augment a arg = PropertyArg (show a) arg

-- | A property that check for equality of its 2 members.
(===) :: (Show a, Eq a, Typeable a) => a -> a -> PropertyCheck
(===) a b =
    let sa = pretty a Proxy
        sb = pretty b Proxy
     in PropertyBinaryOp (a == b) "==" sa sb
infix 4 ===

pretty :: (Show a, Typeable a) => a -> Proxy a -> String
pretty a pa = show a <> " :: " <> show (typeRep pa)

-- | A property that check for a specific comparaison of its 2 members.
--
-- This is equivalent to `===` but with `compare`
propertyCompare :: (Show a, Typeable a)
                => String           -- ^ name of the function used for comparaison, e.g. (<)
                -> (a -> a -> Bool) -- ^ function used for value comparaison
                -> a                -- ^ value left of the operator
                -> a                -- ^ value right of the operator
                -> PropertyCheck
propertyCompare name op = propertyCompareWith name op (flip pretty Proxy)

-- | A property that check for a specific comparaison of its 2 members.
--
-- This is equivalent to `===` but with `compare` and a given method to
-- pretty print the values.
--
propertyCompareWith :: String           -- ^ name of the function used for comparaison, e.g. (<)
                    -> (a -> a -> Bool) -- ^ function used for value comparaison
                    -> (a -> String)    -- ^ function used to pretty print the values
                    -> a                -- ^ value left of the operator
                    -> a                -- ^ value right of the operator
                    -> PropertyCheck
propertyCompareWith name op display a b =
    let sa = display a
        sb = display b
     in PropertyBinaryOp (a `op` b) name sa sb

-- | A conjuctive property composed of 2 properties that need to pass
propertyAnd :: PropertyCheck -> PropertyCheck -> PropertyCheck
propertyAnd c1 c2 =
    PropertyAnd (checkHasSucceed c1 && checkHasSucceed c2) c1 c2

propertyFail :: String -> PropertyCheck
propertyFail = PropertyFail False
