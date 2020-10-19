{-# LANGUAGE TemplateHaskell #-}
{-# OPTIONS_HADDOCK hide #-}
module Errors.TH.GenCodes (genCodes) where

import           Data.Traversable
import           ErrorCode
import           Language.Haskell.TH          as TH
import           Language.Haskell.TH.Datatype as TH

-- | Takes a list of errors names (dataconstructors)
-- and maps it to a list that will evaluate to their actuall error codes :: [Natural]
genCodes :: [TH.Name] -> Q TH.Exp
genCodes cs = do
   method <- [| errorCode |]    -- the errorCode method
   undef <- [| undefined |]   -- the 'undefined' exp
   fmap ListE . for cs $ \ c -> do
       cInfo <- TH.reifyConstructor c
       pure $ method `AppE` genSaturatedCon cInfo undef

-- | Given some data-constructor info (number of args and name),
-- generate a fully-applied (saturated) value of the constructor by
-- fully applying it to `undefined` values.
-- e.g. `(Nothing), (Just undefined), (undefined,undefined,undefined), etc`
-- Note: breaks on data-constructors containing bangs.
genSaturatedCon :: TH.ConstructorInfo -> TH.Exp -> TH.Exp
genSaturatedCon cInfo undef =
    foldr (const $ \ acc -> acc `AppE` undef)
    (ConE $ constructorName cInfo) $ constructorFields cInfo
