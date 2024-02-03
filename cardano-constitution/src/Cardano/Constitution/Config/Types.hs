{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell   #-}
{-# LANGUAGE TupleSections     #-}
{-# LANGUAGE TypeApplications  #-}
module Cardano.Constitution.Config.Types
    ( ConstitutionConfig(..)
    , ParamConfig(..)
    , ParamId
    ) where

import Cardano.Constitution.Config.Predicate.Types

import PlutusTx as Tx (makeLift)
import PlutusTx.AssocMap qualified as AssocMap
import PlutusTx.SortedMap qualified as SortedMap
import Prelude as Haskell

import Data.Aeson as Aeson
import Data.Aeson.Key qualified as Aeson (toText)
import Data.Aeson.KeyMap qualified as Aeson (toAscList)
import Data.Map qualified as M
import Data.Traversable
import Language.Haskell.TH.Syntax as TH (Lift)

-- | Promised to be a stable identifier (stable at least for a whole cardano era)
type ParamId = Haskell.Integer

newtype ConstitutionConfig = ConstitutionConfig
    { unConstitutionConfig :: SortedMap.SortedMap ParamId ParamConfig
    }
    deriving stock (TH.Lift)
    deriving newtype (Eq, Show)

newtype ParamConfig = ParamConfig { unParamConfig :: AssocMap.Map PredName PredValue }
    deriving stock (TH.Lift)
    deriving newtype (Eq, Show)

instance FromJSON ConstitutionConfig where
    parseJSON = withObject "ConstitutionConfig" $ \km ->
                   fmap (ConstitutionConfig . SortedMap.fromListSafe) .
                       for (Aeson.toAscList km) $ \(outerKey, outerValue) -> do
                           index <- case fromJSONKey @ParamId of
                                       FromJSONKeyTextParser parseInteger ->
                                           parseInteger $ Aeson.toText outerKey
                                       _   -> error "invalid FromJSONKey parser of ParamId"
                           (index,) <$> withObject "ParamConfig"
                                        (\innerMap -> innerMap .: predicatesKey) outerValue

instance FromJSON ParamConfig where
    -- it's like `deriving via Data.Map`
    parseJSON = fmap (ParamConfig . AssocMap.fromListSafe . M.toAscList)
              . parseJSON @(M.Map PredName PredValue)

predicatesKey :: Aeson.Key
predicatesKey = "predicates"

-- `Tx.makeLift` seems to be sensitive to re-ordering. So do not reorder the following two.
Tx.makeLift ''ParamConfig
Tx.makeLift ''ConstitutionConfig
