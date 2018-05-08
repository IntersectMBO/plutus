module Language.PlutusCore.PrettyPrint ( prettyPrint
                                         ) where

import qualified Data.ByteString.Lazy             as BSL
import qualified Data.IntMap                      as IM
import           Language.PlutusCore.Identifier
import           Language.PlutusCore.Type

prettyPrint :: (IdentifierState, Term a) -> Maybe BSL.ByteString
prettyPrint (is, Var _ (Name _ (Unique i))) = IM.lookup i (fst is)
prettyPrint _                               = Nothing -- FIXME this is bad
