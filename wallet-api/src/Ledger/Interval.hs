{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE DerivingStrategies   #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE DeriveGeneric        #-}
{-# LANGUAGE TemplateHaskell      #-}
{-# LANGUAGE DeriveAnyClass       #-}
{-# LANGUAGE MonoLocalBinds       #-}
-- | A type for intervals and associated functions.
module Ledger.Interval(
      Slot(..)
    , Interval(..)
    , SlotRange
    , interval
    , from
    , to
    , singleton
    , empty
    , always
    , member
    , width
    , contains
    , before
    , after
    ) where

import           Codec.Serialise.Class                    (Serialise)
import           Data.Aeson                               (FromJSON, ToJSON)
import           Data.Swagger.Internal.Schema             (ToSchema)
import           GHC.Generics                             (Generic)
import           Language.Haskell.TH

import           Language.PlutusTx.Lift                   (makeLift)
import           Language.PlutusTx.Prelude

-- | Slot number
newtype Slot = Slot { getSlot :: Int }
    deriving (Eq, Ord, Show, Enum)
    deriving stock (Generic)
    deriving anyclass (ToSchema, FromJSON, ToJSON)
    deriving newtype (Num, Real, Integral, Serialise)

makeLift ''Slot

-- | An interval of @a@s. The interval is closed below and open above, meaning 
--   that @Interval (Just (10 :: Int)) (Just 11)@ contains a single value @11@.
--   The interval is unbounded on either side: @Interval Nothing (Just 12)@ 
--   contains all numbers smaller than @12@.
--   
data Interval a = Interval { ivFrom :: Maybe a, ivTo :: Maybe a }
    deriving (Eq, Ord, Show)
    deriving stock (Generic)
    deriving anyclass (ToSchema, FromJSON, ToJSON, Serialise)

makeLift ''Interval

type SlotRange = Interval Slot

{- note [Definition of Interval]

The purpose of this module is to provide an interval data type that 
can be used in on-chain and off-chain code alike. Its two main uses in the 
'wallet-api' module are the validity range of transactions, and the ranges of
funds and slot numbers for wallet triggers.

To ensure that 'Interval' can be used in on-chain code, the functions in this 
module do not use type classes or functions from the Haskell Prelude. The types 
of the query functions exported from here are specialised to
'Interval Slot'. 

-}


-- | A 'SlotRange' that covers every slot.
always :: Q (TExp SlotRange)
always = [|| Interval Nothing Nothing ||]

-- | @from a@ is an 'Interval' that includes all values that are
--  greater than or equal to @a@.
from :: Q (TExp (a -> Interval a))
from = [|| \s -> Interval (Just s) Nothing ||]

-- | @to a@ is an 'Interval' that includes all values that are
--  smaller than @a@.
to :: Q (TExp (a -> Interval a))
to = [|| \s -> Interval Nothing (Just s) ||]

-- | @interval a b@ includes all values that are greater than or equal
--   to @a@ and smaller than @b@. Therefore it includes @a@ but not it
--   does not include @b@.
interval :: Q (TExp (a -> a -> Interval a))
interval = [|| \s s' -> Interval (Just s) (Just s') ||]

-- | A 'SlotRange' that covers only a single slot.
singleton :: Q (TExp (Slot -> SlotRange))
singleton = [|| \(Slot s) -> Interval (Just (Slot s)) (Just (Slot ($$plus s 1))) ||]

-- | Check if a 'SlotRange' is empty
empty :: Q (TExp (SlotRange -> Bool))
empty = [|| 
    \(Interval f t) -> 
        case f of 
            Nothing -> False
            Just (Slot f') -> case t of
                Nothing -> False
                Just (Slot t') -> $$geq f' t'
    ||]

-- | Check if 'Slot' is contained in a 'SlotRange'.
member :: Q (TExp (Slot -> SlotRange -> Bool))
member = [|| 
    \(Slot s) (Interval f t) -> 
        let lw = case f of { Nothing -> True; Just (Slot f') -> $$leq f' s; }
            hg = case t of { Nothing -> True; Just (Slot t') -> $$gt t' s; }
        in
            if lw then hg else False
    ||]

-- | Number of 'Slot's covered by the interval. @width (from x) == Nothing@
width :: Q (TExp (SlotRange -> Maybe Int))
width = [|| 
    \(Interval f t) -> 
        case f of 
            Nothing -> Nothing
            Just (Slot f') -> case t of
                Nothing -> Nothing
                Just (Slot t') -> Just ($$minus t' f')  ||]

-- | @a `contains` b@ is true if the 'SlotRange' @b@ is entirely contained in 
--   @a@. That is, @a `contains` b@ if for every slot @s@, if @member s b@ then
--   @member s a@.
contains :: Q (TExp (SlotRange -> SlotRange -> Bool))
contains = [|| 
    \(Interval af at) (Interval bf bt) ->
        let lw = case af of
                Nothing -> True
                Just (Slot af') -> case bf of
                    Nothing -> False
                    Just (Slot bf') -> $$leq af' bf'
            hg = case at of
                Nothing -> True
                Just (Slot at') -> case bt of
                    Nothing -> False
                    Just (Slot bt') -> $$geq at' bt'
        in
            if lw then hg else False
    ||]

-- | Check if a 'Slot' is earlier than the beginning of a 'SlotRange'
before :: Q (TExp (Slot -> SlotRange -> Bool))
before = [||
    \(Slot h) (Interval f _) -> case f of { Nothing -> False; Just (Slot h') -> $$gt h' h; }
    ||]

-- | Check if a 'Slot' is later than the end of a 'SlotRange'
after :: Q (TExp (Slot -> SlotRange -> Bool))
after = [||
    \(Slot h) (Interval _ t) -> case t of { Nothing -> False; Just (Slot t') -> $$geq h t'; }
    ||]
