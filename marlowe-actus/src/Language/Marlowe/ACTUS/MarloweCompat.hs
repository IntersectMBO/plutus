{-# LANGUAGE RecordWildCards #-}

{- This module provides compatibility to Marlowe DSL -}

module Language.Marlowe.ACTUS.MarloweCompat where

import           Language.Marlowe                                  (Contract (Let), Observation,
                                                                    Value (Constant, UseValue), ValueId (ValueId))

import           Data.String                                       (IsString (fromString))
import           Data.Time                                         (Day, UTCTime (UTCTime))
import           Data.Time.Clock.System                            (SystemTime (MkSystemTime), utcToSystemTime)
import           Language.Marlowe.ACTUS.Definitions.BusinessEvents (EventType)
import           Language.Marlowe.ACTUS.Definitions.ContractState  (ContractState, ContractStatePoly (..))
import           Language.Marlowe.ACTUS.Ops                        (marloweFixedPoint)

type EventHandlerSTF = EventType -> ContractStateMarlowe -> ContractStateMarlowe
type ContractStateMarlowe = ContractStatePoly (Value Observation) (Value Observation)

useval :: String -> Integer -> Value Observation
useval name t = UseValue $ ValueId $ fromString $ name ++ "_" ++ show t

letval :: String -> Integer -> Value Observation -> Contract -> Contract
letval name t = Let $ ValueId $ fromString $ name ++ "_" ++ show t

toMarloweFixedPoint :: Double -> Integer
toMarloweFixedPoint = round <$> (fromIntegral marloweFixedPoint *)

constnt :: Double -> Value Observation
constnt = Constant . toMarloweFixedPoint

enum :: a -> a
enum = id

stateTransitionMarlowe :: EventType -> Integer -> Contract -> EventHandlerSTF -> Contract
stateTransitionMarlowe ev t continue handler =
  let inputState =
        ContractStatePoly
          { tmd = useval "tmd" $ t - 1,
            nt = useval "nt" $ t - 1,
            ipnr = useval "ipnr" $ t - 1,
            ipac = useval "ipac" $ t - 1,
            feac = useval "feac" $ t - 1,
            nsc = useval "nsc" $ t - 1,
            isc = useval "isc" $ t - 1,
            sd = useval "sd" $ t - 1,
            prnxt = useval "prnxt" $ t - 1,
            ipcb = useval "ipcb" $ t - 1,
            prf = undefined
          }
      h = handler ev inputState
   in letval "tmd" t (tmd h) $
      letval "nt" t (nt h) $
      letval "ipnr" t (ipnr h) $
      letval "ipac" t (ipac h) $
      letval "feac" t (feac h) $
      letval "nsc" t (nsc h) $
      letval "isc" t (isc h) $
      letval "sd" t (sd h) $
      letval "prnxt" t (prnxt h) $
      letval "ipcb" t (ipcb h) continue

stateInitialisation :: ContractState -> Contract -> Contract
stateInitialisation ContractStatePoly {..} continue =
  letval "tmd" 0 (marloweDate tmd) $
  letval "nt" 0 (constnt nt) $
  letval "ipnr" 0 (constnt ipnr) $
  letval "ipac" 0 (constnt ipac) $
  letval "feac" 0 (constnt feac) $
  letval "nsc" 0 (constnt nsc) $
  letval "isc" 0 (constnt isc) $
  letval "sd" 0 (marloweDate sd) $
  letval "prnxt" 0 (constnt prnxt) $
  letval "ipcb" 0 (constnt ipcb) continue

cardanoEpochStart :: Integer
cardanoEpochStart = 100

dayToSlotNumber :: Day -> Integer
dayToSlotNumber d =
  let (MkSystemTime secs _) = utcToSystemTime (UTCTime d 0)
   in fromIntegral secs - cardanoEpochStart

marloweDate :: Day -> Value Observation
marloweDate = Constant . fromInteger . dayToSlotNumber
