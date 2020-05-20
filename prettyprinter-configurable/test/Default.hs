{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TypeApplications      #-}

module Default where

import           Text.PrettyBy
import           Text.PrettyBy.Fixity
import           Text.PrettyBy.Monad

import           Data.Proxy
import           Data.Text                 (Text)
import qualified Data.Text                 as Text
import           Data.Text.Prettyprint.Doc
import           Test.QuickCheck
import           Test.Tasty
import           Test.Tasty.QuickCheck

data TestCase = TestCase
    { _testCaseExprType    :: String
    , _testCaseExpr        :: String
    , _testCaseViaPretty   :: String
    , _testCaseViaPrettyBy :: String
    }

newtype OnlyType = OnlyType RenderContext

instance HasRenderContext OnlyType where
    renderContext f (OnlyType context) = OnlyType <$> f context

instance PrettyBy OnlyType (Proxy a) => PrettyBy OnlyType (Proxy [a]) where
    prettyBy =
        viaPrettyM $ \_ ->
            compoundDocM unitFixity $ \prettyIn ->
                brackets $ prettyIn Forward botFixity (Proxy @a)

instance PrettyBy OnlyType (Proxy a) => PrettyBy OnlyType (Proxy (Maybe a)) where
    prettyBy =
        viaPrettyM $ \_ ->
            sequenceDocM juxtFixity $ \prettyEl ->
                "Maybe" <+> prettyEl (Proxy @a)

instance (PrettyBy OnlyType (Proxy a), PrettyBy OnlyType (Proxy b)) =>
            PrettyBy OnlyType (Proxy (a, b)) where
    prettyBy =
        viaPrettyM $ \_ ->
            compoundDocM unitFixity $ \prettyIn -> mconcat
                [ "("
                , prettyIn Forward botFixity $ Proxy @a
                , ", "
                , prettyIn Forward botFixity $ Proxy @b
                , ")"
                ]

instance PrettyBy OnlyType (Proxy Integer) where
    prettyBy = viaPrettyM $ \_ -> unitDocM "Integer"

instance PrettyBy OnlyType (Proxy Char) where
    prettyBy = viaPrettyM $ \_ -> unitDocM "Char"

instance PrettyBy OnlyType (Proxy Text) where
    prettyBy = viaPrettyM $ \_ -> unitDocM "Text"

makeTestCase :: (Show a, Pretty a, PrettyBy () a, PrettyBy OnlyType (Proxy a)) => a -> TestCase
makeTestCase (x :: a) =
    TestCase
        (show . prettyBy (OnlyType botRenderContext) $ Proxy @a)
        (show x)
        (show $ pretty x)
        (show $ prettyBy () x) -- ++ show (prettyBy () x))

maybeOf :: Gen a -> Gen (Maybe a)
maybeOf genX = frequency
    [ (1, pure Nothing)
    , (3, Just <$> genX)
    ]

genPrettyPrintable :: Gen TestCase
genPrettyPrintable = go 13 $ fmap makeTestCase where
    go
        :: Int
        -> (forall a. (Show a, Pretty a, PrettyBy () a, PrettyBy OnlyType (Proxy a)) => Gen a -> Gen r)
        -> Gen r
    go i k = frequency $ filter ((> 0) . fst)
      [ (i, go (i - 3) $ k . vectorOf (2 * i))
      , (i, go (i - 3) $ k . maybeOf)
      , (i, go (i `div` 2) $ \genX -> go (i `div` 2) $ \genY -> k $ (,) <$> genX <*> genY)
      , (14 - i, k $ arbitrarySizedIntegral @Integer)
      , (14 - i, k arbitraryPrintableChar)
      , (14 - i, k $ Text.pack <$> listOf arbitraryPrintableChar)
      ]

test_default :: TestTree
test_default =
    testProperty "default" . withMaxSuccess 500 $
        forAllBlind genPrettyPrintable $ \(TestCase exprType expr viaPretty viaPrettyBy) ->
            let message = unlines
                    [ "Mismatch for: " ++ expr
                    , "via Pretty: " ++ viaPretty
                    , "via PrettyBy: " ++ viaPrettyBy
                    ]
            in collect exprType $ counterexample message $ viaPretty == viaPrettyBy
