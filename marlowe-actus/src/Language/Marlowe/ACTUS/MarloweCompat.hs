{-# LANGUAGE RecordWildCards            #-}
{- This module provides compatibility between Num and MarloweValue -}

module Language.Marlowe.ACTUS.MarloweCompat where

import           Language.Marlowe
import           Language.Marlowe.ACTUS.BusinessEvents
import           Language.Marlowe.ACTUS.ContractState
import           Data.String                    ( IsString(fromString) )
import qualified Data.List                     as L

type EventHandler = EventType -> (Value Observation)

type EventHandlerSTF = EventType -> ContractStateMarlowe -> ContractStateMarlowe

type ContractStateMarlowe
    = ContractStatePoly (Value Observation) (Value Observation)

useval :: String -> Integer -> (Value Observation)
useval name t = (UseValue (ValueId (fromString $ name ++ "_" ++ (show t))))

letval :: String -> Integer -> (Value Observation) -> Contract -> Contract
letval name t val cont =
    (Let (ValueId (fromString $ name ++ "_" ++ (show t))) val cont)

constnt :: Double -> (Value Observation)
constnt v = Constant $ round $ v * marloweFixedPoint

constntMaybe :: Maybe Double -> Maybe (Value Observation)
constntMaybe = fmap (\v' -> Constant $ round $ v' * marloweFixedPoint)

enum :: forall a . a -> a
enum = id

dispatchEvent
    :: Integer -> (Value Observation) -> EventHandler -> (Value Observation)
dispatchEvent t defaultValue handler =
    let
        eventId ev = Constant $ eventTypeToEventTypeId ev
        eventIdInput = useval "eventType_" t
        cond cont ev =
            (Cond (ValueEQ (eventId ev) eventIdInput) (handler ev) cont)
    in
        L.foldl cond defaultValue [AD, IED, MD]

dispatchStateTransition :: Integer -> Contract -> EventHandlerSTF -> Contract
dispatchStateTransition t continue handler =
    let inputState = ContractStatePoly { tmd   = (useval "tmd" (t - 1))
                                       , nt    = (useval "nt" (t - 1))
                                       , ipnr  = (useval "ipnr" (t - 1))
                                       , ipac  = (useval "ipac" (t - 1))
                                       , feac  = (useval "feac" (t - 1))
                                       , fac   = (useval "fac" (t - 1))
                                       , nsc   = (useval "nsc" (t - 1))
                                       , isc   = (useval "isc" (t - 1))
                                       , sd    = (useval "sd" (t - 1))
                                       , prnxt = (useval "prnxt" (t - 1))
                                       , ipcb  = (useval "ipcb" (t - 1))
                                       , prf   = undefined
                                       }
        handler_tmd ev = tmd $ handler ev inputState
        handler_nt ev = nt $ handler ev inputState
        handler_ipnr ev = ipnr $ handler ev inputState
        handler_ipac ev = ipac $ handler ev inputState
        handler_feac ev = feac $ handler ev inputState
        handler_fac ev = fac $ handler ev inputState
        handler_nsc ev = nsc $ handler ev inputState
        handler_isc ev = isc $ handler ev inputState
        handler_sd ev = sd $ handler ev inputState
        handler_prnxt ev = prnxt $ handler ev inputState
        handler_ipcb ev = ipcb $ handler ev inputState
    in  letval "tmd" t (dispatchEvent t (tmd inputState) handler_tmd)
            $ letval "nt"   t (dispatchEvent t (nt inputState) handler_nt)
            $ letval "ipnr" t (dispatchEvent t (ipnr inputState) handler_ipnr)
            $ letval "ipac" t (dispatchEvent t (ipac inputState) handler_ipac)
            $ letval "feac" t (dispatchEvent t (feac inputState) handler_feac)
            $ letval "fac"  t (dispatchEvent t (fac inputState) handler_fac)
            $ letval "nsc"  t (dispatchEvent t (nsc inputState) handler_nsc)
            $ letval "isc"  t (dispatchEvent t (isc inputState) handler_isc)
            $ letval "sd"   t (dispatchEvent t (sd inputState) handler_sd)
            $ letval "prnxt"
                     t
                     (dispatchEvent t (prnxt inputState) handler_prnxt)
            $ letval "ipcb" t (dispatchEvent t (ipcb inputState) handler_ipcb)
            continue

