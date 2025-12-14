module PlutusCore.StdLib.Data.MatchOption
  ( MatchOption (..)
  ) where

{-| Allows one to choose which way of doing pattern matching on built-in types to use: currently
only 'ChooseList'-like builtins are supported. -}
data MatchOption
  = UseChoose
  deriving stock (Show, Eq, Bounded, Enum)
