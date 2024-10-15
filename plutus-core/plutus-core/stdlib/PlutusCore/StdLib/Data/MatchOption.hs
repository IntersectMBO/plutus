module PlutusCore.StdLib.Data.MatchOption
    ( MatchOption (..)
    ) where

data MatchOption
    = UseChoose
    | UseCase
    deriving stock (Show, Eq, Bounded, Enum)
