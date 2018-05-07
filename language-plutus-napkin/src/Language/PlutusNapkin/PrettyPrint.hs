module Language.PlutusNapkin.PrettyPrint ( prettyPrint
                                         ) where

import qualified Data.ByteString.Lazy             as BSL
import qualified Data.IntMap                      as IM
import           Language.PlutusNapkin.Identifier
import           Language.PlutusNapkin.Type

prettyPrint :: (IdentifierState, Term a) -> Maybe BSL.ByteString
prettyPrint (is, Var _ (Name _ i)) = IM.lookup i (fst is)
prettyPrint _                      = Nothing -- FIXME this is bad
