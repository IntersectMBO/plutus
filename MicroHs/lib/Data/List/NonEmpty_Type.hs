module Data.List.NonEmpty_Type(module Data.List.NonEmpty_Type) where
import Prelude qualified ()

infixr 5 :|

data NonEmpty a = a :| [a]
