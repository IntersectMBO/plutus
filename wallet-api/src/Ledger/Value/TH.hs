{-# LANGUAGE DeriveAnyClass     #-}
{-# LANGUAGE DeriveGeneric      #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE TemplateHaskell    #-}
module Ledger.Value.TH(
      Value(..)
      -- * Constants
    , zero
      -- * Num operations
    , plus
    , minus
    , multiply
    , divide
    , negate
    , geq
    , gt
    , leq
    , lt
    , eq
      -- * Etc.
    , isZero
    , size
    ) where

import           Codec.Serialise.Class        (Serialise)
import           Data.Aeson                   (FromJSON, ToJSON)
import           Data.Swagger.Internal.Schema (ToSchema)
import           GHC.Generics                 (Generic)
import           Language.PlutusTx.Lift       (makeLift)
import qualified Language.PlutusTx.Prelude    as P
import           Language.Haskell.TH          (Q, TExp)
import           Prelude                      hiding (negate)

-- | Cryptocurrency value
--
newtype Value = Value { getValue :: Int }
    deriving (Eq, Ord, Show, Enum)
    deriving stock (Generic)
    deriving anyclass (ToSchema, ToJSON, FromJSON)
    deriving newtype (Serialise)

makeLift ''Value

-- Num operations

plus :: Q (TExp (Value -> Value -> Value))
plus = [|| \(Value a) (Value b) -> Value ($$(P.plus) a b)||]

minus :: Q (TExp (Value -> Value -> Value))
minus = [|| \(Value a) (Value b) -> Value ($$(P.minus) a b)||]

multiply :: Q (TExp (Value -> Value -> Value))
multiply = [|| \(Value a) (Value b) -> Value ($$(P.multiply) a b)||]

divide :: Q (TExp (Value -> Value -> Value))
divide = [|| \(Value a) (Value b) -> Value ($$(P.divide) a b)||]

zero :: Q (TExp Value)
zero = [|| Value 0 ||]

negate :: Q (TExp (Value -> Value))
negate = [|| \(Value i) -> Value ($$(P.multiply) (-1) i) ||]

isZero :: Q (TExp (Value -> Bool))
isZero = [|| \(Value i) -> $$(P.eq) i 0 ||]

geq :: Q (TExp (Value -> Value -> Bool))
geq = [|| \(Value i) (Value j) -> $$(P.geq) i j ||]

gt :: Q (TExp (Value -> Value -> Bool))
gt = [|| \(Value i) (Value j) -> $$(P.gt) i j ||]

leq :: Q (TExp (Value -> Value -> Bool))
leq = [|| \(Value i) (Value j) -> $$(P.leq) i j ||]

lt :: Q (TExp (Value -> Value -> Bool))
lt = [|| \(Value i) (Value j) -> $$(P.lt) i j ||]

eq :: Q (TExp (Value -> Value -> Bool))
eq = [|| \(Value i) (Value j) -> $$(P.eq) i j ||]

size :: Q (TExp (Value -> Int))
size = [|| \(Value i) -> i ||]
