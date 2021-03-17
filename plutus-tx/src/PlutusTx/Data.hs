{-# LANGUAGE BangPatterns       #-}
{-# LANGUAGE DeriveAnyClass     #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE LambdaCase         #-}
{-# LANGUAGE OverloadedStrings  #-}
{-# LANGUAGE ViewPatterns       #-}

module PlutusTx.Data (Data (..)) where

import           Codec.Serialise           (Serialise)
import           Control.DeepSeq           (NFData)
import qualified Data.ByteString           as BS
import           Data.Text.Prettyprint.Doc
import           GHC.Generics
import           Prelude

-- | A generic "data" type.
--
-- The main constructor 'Constr' represents a datatype value in sum-of-products
-- form: @Constr i args@ represents a use of the @i@th constructor along with its arguments.
--
-- The other constructors are various primitives.
data Data =
      Constr Integer [Data]
    | Map [(Data, Data)]
    | List [Data]
    | I Integer
    | B BS.ByteString
    deriving stock (Show, Eq, Ord, Generic)
    deriving anyclass (Serialise, NFData)

instance Pretty Data where
    pretty = \case
        Constr _ ds -> angles (sep (punctuate comma (fmap pretty ds)))
        Map entries -> braces (sep (punctuate comma (fmap (\(k, v) -> pretty k <> ":" <+> pretty v) entries)))
        List ds     -> brackets (sep (punctuate comma (fmap pretty ds)))
        I i         -> pretty i
        B b         -> viaShow b
