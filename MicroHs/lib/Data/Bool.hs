-- Copyright 2023 Lennart Augustsson
-- See LICENSE file for full license.
module Data.Bool(
  module Data.Bool,
  module Data.Bool_Type
  ) where
import qualified Prelude()              -- do not import Prelude
import Primitives
import Data.Bool_Type
import Data.Bounded
import Data.Eq
import Data.Ord
import Text.Show

instance Eq Bool where
  False == x  =  not x
  True  == x  =  x

instance Ord Bool where
  False <= _ = True
  True  <= x = x

instance Show Bool where
  showsPrec _ False = showString "False"
  showsPrec _ True  = showString "True"

instance Bounded Bool where
  minBound = False
  maxBound = True

infixr 2 ||
(||) :: Bool -> Bool -> Bool
(||) False y = y
(||) True  _ = True

infixr 3 &&
(&&) :: Bool -> Bool -> Bool
(&&) False _ = False
(&&) True  y = y

not :: Bool -> Bool
not False = True
not True  = False

otherwise :: Bool
otherwise = True

bool :: forall a . a -> a -> Bool -> a
bool f _ False = f
bool _ t True  = t
