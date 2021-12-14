{-# LANGUAGE ExistentialQuantification  #-}
{-# LANGUAGE Rank2Types                 #-}
{-# LANGUAGE GADTs                      #-}
{-# LANGUAGE OverloadedStrings          #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE FlexibleContexts           #-}
module Foundation.Check.Print
    ( propertyToResult
    , PropertyResult(..)
    , diffBlame
    ) where

import           Foundation.Check.Property
import           Foundation.Check.Types
import           Basement.Imports
import           Foundation.Collection
import           Basement.Compat.Bifunctor (bimap)
import           Foundation.Numerical

propertyToResult :: PropertyTestArg -> (PropertyResult, Bool)
propertyToResult propertyTestArg =
        let args   = propertyGetArgs propertyTestArg
            checks = getChecks propertyTestArg
         in if checkHasFailed checks
                then printError args checks
                else (PropertySuccess, not (null args))
  where
    printError args checks = (PropertyFailed (mconcat $ loop 1 args), False)
      where
        loop :: Word -> [String] -> [String]
        loop _ []      = printChecks checks
        loop !i (a:as) = "parameter " <> show i <> " : " <> a <> "\n" : loop (i+1) as
    printChecks (PropertyBinaryOp True _ _ _)     = []
    printChecks (PropertyBinaryOp False n a b) =
        [ "Property `a " <> n <> " b' failed where:\n"
        , "    a = " <> a <> "\n"
        , "        " <> bl1 <> "\n"
        , "    b = " <> b <> "\n"
        , "        " <> bl2 <> "\n"
        ]
      where
        (bl1, bl2) = diffBlame a b
    printChecks (PropertyNamed True _)            = []
    printChecks (PropertyNamed False e)           = ["Property " <> e <> " failed"]
    printChecks (PropertyBoolean True)            = []
    printChecks (PropertyBoolean False)           = ["Property failed"]
    printChecks (PropertyFail _ e)                = ["Property failed: " <> e]
    printChecks (PropertyAnd True _ _)            = []
    printChecks (PropertyAnd False a1 a2) =
            [ "Property `cond1 && cond2' failed where:\n"
            , "   cond1 = " <> h1 <> "\n"

            ]
            <> ((<>) "           " <$>  hs1)
            <>
            [ "   cond2 = " <> h2 <> "\n"
            ]
            <> ((<>) "           " <$> hs2)
      where
        (h1, hs1) = f a1
        (h2, hs2) = f a2
        f a = case printChecks a of
                      [] -> ("Succeed", [])
                      (x:xs) -> (x, xs)

    propertyGetArgs (PropertyArg a p) = a : propertyGetArgs p
    propertyGetArgs (PropertyEOA _) = []

    getChecks (PropertyArg _ p) = getChecks p
    getChecks (PropertyEOA c  ) = c

diffBlame :: String -> String -> (String, String)
diffBlame a b = bimap fromList fromList $ go ([], []) (toList a) (toList b)
  where
    go (acc1, acc2) [] [] = (acc1, acc2)
    go (acc1, acc2) l1 [] = (acc1 <> blaming (length l1), acc2)
    go (acc1, acc2) [] l2 = (acc1                       , acc2 <> blaming (length l2))
    go (acc1, acc2) (x:xs) (y:ys)
        | x == y    = go (acc1 <> " ", acc2 <> " ") xs ys
        | otherwise = go (acc1 <> "^", acc2 <> "^") xs ys
    blaming n = replicate n '^'
