-- Copyright 2023 Lennart Augustsson
-- See LICENSE file for full license.
module Data.Constraint(module Data.Constraint) where
import Prelude qualified ()
import Primitives
import Text.Show

-- A very, very minimal version of the constraints package

type Dict :: Constraint -> Type
data Dict c = c => Dict

instance Show (Dict c) where
  showsPrec _ Dict = showString "Dict"

withDict :: forall c r . Dict c -> (c => r) -> r
withDict Dict r = r
