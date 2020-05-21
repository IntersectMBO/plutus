{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE TypeFamilies          #-}

module NonDefault
    ( test_nonDefault
    ) where

import           Text.PrettyBy

import           Data.Char                 (intToDigit)
import           Data.Text                 (Text)
import           Data.Text.Prettyprint.Doc
import           Numeric                   (showIntAtBase)
import           Test.Tasty
import           Test.Tasty.HUnit

-- | A pretty-printing config.
data CustomDefaults = CustomDefaults
    { _noDefaultsIntBase :: Integer  -- ^ At what base to pretty-print an 'Integer'.
    , _noDefaultsListDef :: Bool     -- ^ Whether to pretty-print a list using 'prettyListBy'
                                     -- (of the 'PrettyBy' class) or as any 'Functor' via
                                     -- 'defaultPrettyFunctorBy'.
    }

-- Disable pretty-printing defaults.
type instance HasPrettyDefaults CustomDefaults = 'False

-- Use the default pretty-printing for 'Char'
instance NonDefaultPrettyBy CustomDefaults Char

-- Use the default pretty-printing for 'Char'
instance NonDefaultPrettyBy CustomDefaults Text

-- Pretty-print an 'Integer' at base stored in the config.
instance NonDefaultPrettyBy CustomDefaults Integer where
    nonDefaultPrettyBy (CustomDefaults base _) i = pretty $ showIntAtBase base intToDigit i ""

instance PrettyBy CustomDefaults a => NonDefaultPrettyBy CustomDefaults (Maybe a) where
    -- By default 'Nothing' gets pretty-printed as an empty string and @Just x@ as @x@,
    -- here we overload that behavior.
    nonDefaultPrettyBy _      Nothing  = "Nothing"
    nonDefaultPrettyBy config (Just x) = "Just" <+> parens (prettyBy config x)

    -- Directly pretty-print a list of 'Maybe's without filtering out all the 'Nothing's first
    -- (which is the default behavior).
    nonDefaultPrettyListBy = defaultPrettyFunctorBy

-- Pretty-print a list either using the 'prettyListBy' function of 'PrettyBy' (the default) or
-- as any 'Functor' via 'defaultPrettyFunctorBy' depending on the value of the '_noDefaultsListDef'
-- field of the config.
instance PrettyBy CustomDefaults a => NonDefaultPrettyBy CustomDefaults [a] where
    nonDefaultPrettyBy config@(CustomDefaults _ listDef)
        | listDef   = prettyListBy config
        | otherwise = defaultPrettyFunctorBy config

makeTestCase
    :: (PrettyBy CustomDefaults a, Show a)
    => String -> CustomDefaults -> a -> String -> TestTree
makeTestCase name config x res = testCase header $ show (prettyBy config x) @?= res where
    header = (if null name then "" else name ++ ": ") ++ show x ++ " ~> " ++ res

test_nonDefault :: TestTree
test_nonDefault = testGroup "default"
    [ makeTestCase "" (CustomDefaults 2 True) 'a' "a"
    , makeTestCase "base = 2"  (CustomDefaults 2  True) (12 :: Integer) "1100"
    , makeTestCase "base = 8"  (CustomDefaults 8  True) (12 :: Integer) "14"
    , makeTestCase "base = 10" (CustomDefaults 10 True) (12 :: Integer) "12"
      -- Default pretty-printing for a list of 'Char's is not overloaded, hence depending on whether
      -- default pretty-printing of lists is enabled or not, results are different
    , makeTestCase "listDef = True " (CustomDefaults 2 True)  ("ab12" :: String) "ab12"
    , makeTestCase "listDef = False" (CustomDefaults 2 False) ("ab12" :: String) "[a, b, 1, 2]"
      -- ... and the same holds if the list is stored in a 'Just'.
    , makeTestCase "listDef = True " (CustomDefaults 2 True)  (Just ("ab12" :: String)) "Just (ab12)"
    , makeTestCase "listDef = False" (CustomDefaults 2 False) (Just ("ab12" :: String)) "Just ([a, b, 1, 2])"
      -- Default pretty-printing for a list of 'Maybe's is overloaded, hence regardless of whether
      -- default pretty-printing of lists is enabled or not, the result is the same.
    , makeTestCase "listDef = True " (CustomDefaults 2 True)
        [Just 'a', Nothing, Just 'b'] "[Just (a), Nothing, Just (b)]"
    , makeTestCase "listDef = False" (CustomDefaults 2 False)
        [Just 'a', Nothing, Just 'b'] "[Just (a), Nothing, Just (b)]"
    ]
