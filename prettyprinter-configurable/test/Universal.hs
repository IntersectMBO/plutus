{-# OPTIONS_GHC -fno-warn-missing-methods #-}  -- 'Pretty' weirdly gives a warning.

{-# LANGUAGE DeriveAnyClass        #-}
{-# LANGUAGE DerivingStrategies    #-}
{-# LANGUAGE DerivingVia           #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE StandaloneDeriving    #-}
{-# LANGUAGE UndecidableInstances  #-}

module Universal
    ( test_universal
    ) where

import           Text.Pretty
import           Text.PrettyBy

import           Test.Tasty
import           Test.Tasty.HUnit

data ViaPretty
    = ViaPretty
    deriving stock (Show)

instance Pretty a => PrettyBy ViaPretty (PrettyAny a) where
    prettyBy ViaPretty (PrettyAny x) =
        "Proudly printed via Pretty:" <+> pretty x

data D
    = C1
    | C2
    deriving stock (Show)
    deriving anyclass (Pretty)

deriving via PrettyAny D instance PrettyBy ViaPretty D

makeTestCase :: (PrettyBy config a, Show config, Show a) => config -> a -> String -> TestTree
makeTestCase config x res = testCase header $ show (prettyBy config x) @?= res where
    header = show config ++ " # " ++ show x ++ " ~> " ++ res

test_universalViaPretty :: TestTree
test_universalViaPretty = testGroup "ViaPretty"
    [ makeTestCase ViaPretty C1 "Proudly printed via Pretty: C1"
    , makeTestCase ViaPretty C2 "Proudly printed via Pretty: C2"
    ]

data Config1
    = Config1
    deriving stock (Show)

data Config2
    = Config2
    deriving stock (Show)

instance PrettyBy Config1 D where
    prettyBy Config1 C1 = "Config1_C1"
    prettyBy Config1 C2 = "Config1_C2"

instance PrettyBy Config2 D where
    prettyBy Config2 C1 = "Config2_C1"
    prettyBy Config2 C2 = "Config2_C2"

data ConfigSum
    = ConfigSum1 Config1
    | ConfigSum2 Config2
    deriving stock (Show)

instance (PrettyBy Config1 a, PrettyBy Config2 a) => PrettyBy ConfigSum (PrettyAny a) where
    prettyBy (ConfigSum1 Config1) = prettyBy Config1 . unPrettyAny
    prettyBy (ConfigSum2 Config2) = prettyBy Config2 . unPrettyAny

deriving via PrettyAny D instance PrettyBy ConfigSum D

test_universalConfigSum :: TestTree
test_universalConfigSum = testGroup "ConfigSum"
    [ makeTestCase (ConfigSum1 Config1) C1 "Config1_C1"
    , makeTestCase (ConfigSum1 Config1) C2 "Config1_C2"
    , makeTestCase (ConfigSum2 Config2) C1 "Config2_C1"
    , makeTestCase (ConfigSum2 Config2) C2 "Config2_C2"
    ]

test_universal :: TestTree
test_universal = testGroup "universal"
    [ test_universalViaPretty
    , test_universalConfigSum
    ]
