{-# LANGUAGE DeriveAnyClass     #-}
{-# LANGUAGE DeriveGeneric      #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE TemplateHaskell    #-}
module Ledger.Ada.TH(
      Ada(..)
    -- * Constructor
    , fromValue
    , fromInt
    , toValue
    , toInt
    , adaValueOf
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
    ) where

import           Codec.Serialise.Class        (Serialise)
import           Data.Aeson                   (FromJSON, ToJSON)
import           Data.Swagger.Internal.Schema (ToSchema)
import           GHC.Generics                 (Generic)
import           Language.PlutusTx.Lift       (makeLift)
import qualified Language.PlutusTx.Prelude    as P
import           Language.Haskell.TH          (Q, TExp)
import           Prelude                      hiding (negate)

import           Ledger.Value.TH              (Value(..))

-- | ADA (special currency)
--
newtype Ada = Ada { getAda :: Int }
    deriving (Eq, Ord, Show, Enum)
    deriving stock (Generic)
    deriving anyclass (ToSchema, ToJSON, FromJSON)
    deriving newtype (Num, Integral, Real, Serialise)

makeLift ''Ada

toValue :: Q (TExp (Ada -> Value))
toValue = [||  \(Ada i) -> Value i ||]

fromValue :: Q (TExp (Value -> Ada))
fromValue = [||  \(Value i) -> Ada i ||]

toInt :: Q (TExp (Ada -> Int))
toInt = [|| \(Ada i) -> i ||]

fromInt :: Q (TExp (Int -> Ada))
fromInt = [|| Ada ||]

-- | A 'Value' with the given amount of Ada.
--
--   @adaValueOf == toValue . fromInt@
--
adaValueOf :: Q (TExp (Int -> Value))
adaValueOf = [|| \i -> Value i ||]

plus :: Q (TExp (Ada -> Ada -> Ada))
plus = [|| \(Ada a) (Ada b) -> Ada ($$(P.plus) a b)||]

minus :: Q (TExp (Ada -> Ada -> Ada))
minus = [|| \(Ada a) (Ada b) -> Ada ($$(P.minus) a b)||]

multiply :: Q (TExp (Ada -> Ada -> Ada))
multiply = [|| \(Ada a) (Ada b) -> Ada ($$(P.multiply) a b)||]

divide :: Q (TExp (Ada -> Ada -> Ada))
divide = [|| \(Ada a) (Ada b) -> Ada ($$(P.divide) a b)||]

zero :: Q (TExp Ada)
zero = [|| Ada 0 ||]

negate :: Q (TExp (Ada -> Ada))
negate = [|| \(Ada i) -> Ada ($$(P.multiply) (-1) i) ||]

isZero :: Q (TExp (Ada -> Bool))
isZero = [|| \(Ada i) -> $$(P.eq) i 0 ||]

geq :: Q (TExp (Ada -> Ada -> Bool))
geq = [|| \(Ada i) (Ada j) -> $$(P.geq) i j ||]

gt :: Q (TExp (Ada -> Ada -> Bool))
gt = [|| \(Ada i) (Ada j) -> $$(P.gt) i j ||]

leq :: Q (TExp (Ada -> Ada -> Bool))
leq = [|| \(Ada i) (Ada j) -> $$(P.leq) i j ||]

lt :: Q (TExp (Ada -> Ada -> Bool))
lt = [|| \(Ada i) (Ada j) -> $$(P.lt) i j ||]

eq :: Q (TExp (Ada -> Ada -> Bool))
eq = [|| \(Ada i) (Ada j) -> $$(P.eq) i j ||]
