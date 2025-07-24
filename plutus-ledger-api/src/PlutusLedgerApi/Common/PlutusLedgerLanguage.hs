{-# LANGUAGE DeriveAnyClass #-}
module PlutusLedgerApi.Common.PlutusLedgerLanguage where

import PlutusPrelude

import Codec.Serialise.Class (Serialise)
import Language.Haskell.TH.Syntax (Lift)
import NoThunks.Class (NoThunks)
import Prettyprinter

data PlutusLedgerLanguage =
      PlutusV1 -- ^ introduced in Alonzo HF
    | PlutusV2 -- ^ introduced in Vasil HF
    | PlutusV3 -- ^ introduced in Chang HF
   deriving stock (Eq, Ord, Show, Generic, Enum, Bounded, Lift)
   deriving anyclass (NFData, NoThunks, Serialise)

instance Pretty PlutusLedgerLanguage where
    pretty = viaShow

