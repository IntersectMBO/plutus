{-# LANGUAGE ConstraintKinds           #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleContexts          #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE MultiParamTypeClasses     #-}
{-# LANGUAGE OverloadedStrings         #-}
{-# LANGUAGE RankNTypes                #-}
{-# LANGUAGE ScopedTypeVariables       #-}
{-# LANGUAGE TypeApplications          #-}

-- | Testing that @PrettyBy config@ and @Pretty@ instances are in sync for types that have
-- peculiar default pretty-printing behavior (@Char@, @Maybe@, @[]@) and for types with regular
-- pretty-printing behavior (@Integer@, @(,)@, @Text@).

module Default
    ( test_default
    ) where

import Text.Pretty
import Text.PrettyBy
import Text.PrettyBy.Fixity

import Data.Proxy
import Data.Text qualified as Text
import Data.Text.Arbitrary
import Test.QuickCheck
import Test.Tasty
import Test.Tasty.QuickCheck

newtype OnlyType = OnlyType RenderContext

instance HasRenderContext OnlyType where
    renderContext f (OnlyType context) = OnlyType <$> f context

instance PrettyBy OnlyType (Proxy a) => PrettyBy OnlyType (Proxy [a]) where
    prettyBy = inContextM $ \_ ->
        withPrettyAt ToTheRight botFixity $ \prettyBot ->
            unitDocM . brackets . prettyBot $ Proxy @a

instance PrettyBy OnlyType (Proxy a) => PrettyBy OnlyType (Proxy (Maybe a)) where
    prettyBy = inContextM $ \_ ->
        sequenceDocM ToTheRight juxtFixity $ \prettyEl ->
            "Maybe" <+> prettyEl (Proxy @a)

instance (PrettyBy OnlyType (Proxy a), PrettyBy OnlyType (Proxy b)) =>
            PrettyBy OnlyType (Proxy (a, b)) where
    prettyBy = inContextM $ \_ ->
        withPrettyAt ToTheRight botFixity $ \prettyBot ->
            unitDocM $ mconcat
                [ "("
                , prettyBot $ Proxy @a
                , ", "
                , prettyBot $ Proxy @b
                , ")"
                ]

instance PrettyBy OnlyType (Proxy Integer) where
    prettyBy = inContextM $ \_ ->
        "Integer"

instance PrettyBy OnlyType (Proxy Char) where
    prettyBy = inContextM $ \_ ->
        "Char"

instance PrettyBy OnlyType (Proxy Text) where
    prettyBy = inContextM $ \_ ->
        "Text"

type TestCaseConstr a = (Show a, Pretty a, PrettyBy () a, PrettyBy OnlyType (Proxy a), Arbitrary a)

data TestCase = forall a. TestCaseConstr a => TestCase a

maybeOf :: Gen a -> Gen (Maybe a)
maybeOf genX = frequency
    [ (1, pure Nothing)
    , (3, Just <$> genX)
    ]

instance Arbitrary TestCase where
    arbitrary = go 13 $ fmap TestCase where
        go
            :: Int
            -> (forall a. TestCaseConstr a => Gen a -> Gen TestCase)
            -> Gen TestCase
        go i k = frequency $ filter ((> 0) . fst)
          [ (i, go (i - 3) $ k . vectorOf (2 * i))
          , (i, go (i - 3) $ k . maybeOf)
          , (i, go (i `div` 2) $ \genX -> go (i `div` 2) $ \genY -> k $ (,) <$> genX <*> genY)
          , (14 - i, k $ arbitrarySizedIntegral @Integer)
          , (14 - i, k arbitraryPrintableChar)
          , (14 - i, k $ Text.pack <$> listOf arbitraryPrintableChar)
          ]

    -- We do not attempt to shrink types of generated expressions, only expressions themselves.
    shrink (TestCase x) = map TestCase $ shrink x

prettyByRespectsDefaults :: Blind TestCase -> Property
prettyByRespectsDefaults (Blind (TestCase (x :: a))) =
    label exprType $ counterexample err $ viaPretty == viaPrettyBy
  where
    exprType    = show . prettyBy (OnlyType botRenderContext) $ Proxy @a
    exprRepr    = show x
    viaPretty   = show $ pretty x
    viaPrettyBy = show $ prettyBy () x

    err = unlines
        [ "Mismatch for: " ++ exprRepr
        , "Via Pretty: " ++ viaPretty
        , "Via PrettyBy: " ++ viaPrettyBy
        ]

test_default :: TestTree
test_default = testProperty "default" $ withMaxSuccess 500 prettyByRespectsDefaults
