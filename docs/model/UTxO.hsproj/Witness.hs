{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE PackageImports, RecordWildCards #-}
{-# LANGUAGE StandaloneDeriving, GADTs, TypeSynonymInstances, FlexibleInstances #-}

-- |
-- Module      : Witness
-- Copyright   : [2018] IOHK
-- License     : MIT
--
-- Maintainer  : Manuel M T Chakravarty <manuel.chakravarty@iohk.io>
-- Stability   : experimental
--
-- Definition of script witnesses, including common witness functions

module Witness (

  -- ** Scripts
  Script, script, scriptHash,
  revealPreimageValidator, lockWithPublicKeyValidator, lockWithMultiSigValidator, 
  lockWithPublicKeyHashValidator, revealCollisionValidator, revealFixedPointValidator,
  lockUntilValidator,

  -- ** Witnesses
  Height, Witness, witness, witnessHash,
  revealPreimage, lockWithPublicKey, lockWithMultiSig, lockWithPublicKeyHash, 
  revealCollision, revealFixedPoint, lockUntil,
  
  -- ** Witness validation
  validate
) where
  
import "cryptonite" 
       Crypto.Hash
import "cryptonite" 
       Crypto.PubKey.ECC.ECDSA
import qualified
       Data.ByteArray             as BA
import qualified 
       Data.ByteString.Char8      as BS
import Language.Haskell.TH
import Language.Haskell.TH.Syntax

import Types


instance BA.ByteArrayAccess String where
  length        = BA.length . BS.pack
  withByteArray = BA.withByteArray . BS.pack


-- Scripts
-- -------

data Script t = Script { scriptText :: String, scriptValue :: t }

script :: Q (TExp t) -> Q (TExp (Script t))
script scriptQ
  = do
    { scriptString <- (pprint . unType) <$> scriptQ
    ; [|| Script scriptString $$scriptQ ||]
    }
    
scriptHash :: Script t -> Digest SHA256
scriptHash Script{..} = hash (hash . BS.pack $ scriptText :: Digest SHA256)
                        -- FIXME: we should serialise properly


-- Common scripts
-- --------------

-- |This validator checks that the given preimage has the SHA256 hash embedded in the script.
--
revealPreimageValidator :: BA.ByteArrayAccess v => v -> Q (TExp (Script (State -> v -> Bool)))
revealPreimageValidator preimage
  = script [|| \state preimage -> show (hash preimage :: Digest SHA256) == digest ||]
  where
    digest = show (hash preimage :: Digest SHA256)

-- |This validator checks that the transaction signature matches the given public key.
--
lockWithPublicKeyValidator :: PublicKey -> Q (TExp (Script (State -> Signature -> Bool)))
lockWithPublicKeyValidator pubkey 
  = script [|| \state sig -> verify SHA256 (read pubkeyString) sig (stateTxHash state) ||]
  where
    pubkeyString = show pubkey    -- FIXME: we can't TH lift keys directly

-- |This validator checks that the specified number of transaction signatures are distinct and each match
-- one of the given public keys.
--
lockWithMultiSigValidator :: [PublicKey] -> Int -> Q (TExp (Script (State -> [Signature] -> Bool)))
lockWithMultiSigValidator pubkeys requiredSigCount
  = script [|| \state sigs ->
                 let pubkeys = map read pubkeyStrings
                     disjoint []     = True
                     disjoint (x:xs) = x `notElem` xs && disjoint xs
                 in
                   length sigs == requiredSigCount
                   && disjoint sigs
                   && all (\sig -> any (\pubkey -> verify SHA256 pubkey sig (stateTxHash state)) pubkeys) sigs ||]
  where
    pubkeyStrings = map show pubkeys    -- FIXME: we can't TH lift keys directly

-- |This validator checks that the transaction signature matches the public key with the given hash.
--
lockWithPublicKeyHashValidator :: PublicKey -> Q (TExp (Script (State -> (PublicKey, Signature) -> Bool)))
lockWithPublicKeyHashValidator pubKey 
  = script [|| \state (pubKey, sig) -> 
                 show (hash (show pubKey) :: Digest SHA256) == digest 
                 && verify SHA256 pubKey sig (stateTxHash state) ||]
  where
    digest = show (hash (show pubKey) :: Digest SHA256)    -- hash of public key
    
-- |This validator checks that the given two values produce a SHA1 collision.
--
revealCollisionValidator :: (BA.ByteArrayAccess v, Eq v) 
                         => Q (TExp (Script (State -> (v, v) -> Bool)))
revealCollisionValidator 
  = script [|| \state (value1, value2) -> 
                 value1 /= value2 
                 && hash value1 == (hash value2 :: Digest SHA1) ||]

-- |This validator checks that the value is a SHA256 fixed point.
--
revealFixedPointValidator :: BA.ByteArrayAccess v => Q (TExp (Script (State -> v -> Bool)))
revealFixedPointValidator 
  = script [|| \state value -> 
                 digestFromByteString value == Just (hash value :: Digest SHA256) ||]

-- |This validator checks that the transaction signature matches the given public key
-- and isn't added to the ledger before the ledger reaches the specified height.
--
lockUntilValidator :: PublicKey -> Height -> Q (TExp (Script (State -> Signature -> Bool)))
lockUntilValidator pubkey minHeight
  = script [|| \state sig -> 
                 stateHeight state >= minHeight 
                 && verify SHA256 (read pubkeyString) sig (stateTxHash state) ||]
  where
    pubkeyString = show pubkey    -- FIXME: we can't TH lift keys directly



-- Witness types
-- -------------

data Witness where
  Witness ::
    { validator :: Script (State -> proof -> Bool)
    , redeemer  :: Script (State -> proof)
    } -> Witness
    
witness :: Q (TExp (Script (State -> proof -> Bool)))
        -> Q (TExp (Script (State -> proof)))
        -> Q (TExp Witness)
witness validatorQ redeemerQ = [|| Witness $$validatorQ $$redeemerQ ||]

-- |The hash of the witness' validator.
--
witnessHash :: Witness -> Digest SHA256
witnessHash Witness{..} = scriptHash validator

instance Show (Script t) where
  show = scriptText
  
deriving instance Show Witness
    
instance BA.ByteArrayAccess Witness where
  length        = BA.length . BS.pack . show            -- FIXME: we should serialise properly
  withByteArray = BA.withByteArray . BS.pack  . show    -- FIXME: we should serialise properly


-- Common witnesses    
-- ----------------

revealPreimage :: (BA.ByteArrayAccess v, Lift v) => v -> Q (TExp Witness)
revealPreimage preimage = witness (revealPreimageValidator preimage) (script [|| const preimage ||])

lockWithPublicKey :: PublicKey -> Signature -> Q (TExp Witness)
lockWithPublicKey pubKey sig
  = witness (lockWithPublicKeyValidator pubKey) 
            (script [|| const $ read sigString ||])
  where
    sigString = show sig       -- FIXME: we can't TH lift signatures directly

lockWithMultiSig :: [PublicKey] -> Int -> [Signature] -> Q (TExp Witness)
lockWithMultiSig pubkeys requiredSigCount sigs
  = witness (lockWithMultiSigValidator pubkeys requiredSigCount)
            (script [|| const $ (map read sigStrings) ||])
  where
    sigStrings = map show sigs

lockWithPublicKeyHash :: PublicKey -> Signature -> Q (TExp Witness)
lockWithPublicKeyHash pubKey sig
  = witness (lockWithPublicKeyHashValidator pubKey) 
            (script [|| const $ (read pubKeyString, read sigString) ||])
  where
    pubKeyString = show pubKey    -- FIXME: we can't TH lift keys directly
    sigString    = show sig       -- FIXME: we can't TH lift signatures directly
    
revealCollision :: (BA.ByteArrayAccess v, Eq v, Lift v) => v -> v -> Q (TExp Witness) 
revealCollision value1 value2 = witness revealCollisionValidator (script [|| const (value1, value2) ||])

revealFixedPoint :: (BA.ByteArrayAccess v, Lift v) => v -> Q (TExp Witness)
revealFixedPoint value = witness revealFixedPointValidator (script [|| const value ||])

lockUntil :: PublicKey -> Signature -> Height -> Q (TExp Witness)
lockUntil pubKey sig minHeight
  = witness (lockUntilValidator pubKey minHeight) 
            (script [|| const $ read sigString ||])
  where
    sigString = show sig       -- FIXME: we can't TH lift signatures directly



-- Witness validation
-- ------------------

-- |Validate a witness whose validator must have the given hash under succeeds with
-- the given transaction height.
--
validate :: Digest SHA256 -> State -> Witness -> Bool
validate validatorHash state Witness{..} 
  | validatorHash /= scriptHash validator
  = False
  | otherwise
  = (scriptValue validator) state (scriptValue redeemer state)

