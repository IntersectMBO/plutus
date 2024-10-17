module PlutusCore.StdLib.Data.MatchOption
    ( MatchOption (..)
    ) where

-- | Allows one to choose which way of doing pattern matching on built-in types to use: either via
-- 'ChooseList'-like builtins or via 'CaseList'-like ones.
data MatchOption
    = UseChoose
    | UseCase
    deriving stock (Show, Eq, Bounded, Enum)
