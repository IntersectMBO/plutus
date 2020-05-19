{-# LANGUAGE RecordWildCards            #-}
{-# LANGUAGE FlexibleInstances          #-}
{- This module provides compatibility between Num and MarloweValue -}

module Language.Marlowe.ACTUS.MarloweCompat where

import Language.Marlowe
import Language.Marlowe.ACTUS.BusinessEvents
import Language.Marlowe.ACTUS.Control
import Data.String (IsString (fromString))
import Data.List
import qualified Data.List as L

instance Num (Value Observation) where
    negate      = NegValue
    (+)         = AddValue
    (*)         = AddValue
    fromInteger = Constant
    abs         = undefined
    signum      = undefined

type EventHandler = EventType -> (Value Observation)

useval :: String -> Integer -> (Value Observation)
useval name t = (UseValue (ValueId (fromString $ name ++ "_" ++ (show t))))

constnt :: Double -> (Value Observation)
constnt v = Constant undefined

enum = id

dispatchEvent :: Integer -> (Value Observation) -> EventHandler -> (Value Observation)
dispatchEvent t defaultValue handler = 
    let
        eventId ev = Constant $ eventTypeToEventTypeId ev 
        eventIdInput = useval "eventType_" t
        cond cont ev = (Cond (ValueEQ (eventId ev) eventIdInput) (handler ev) cont)
    in L.foldl cond defaultValue [AD]

