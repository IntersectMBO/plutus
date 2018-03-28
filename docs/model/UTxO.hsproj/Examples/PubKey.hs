{-# LANGUAGE PackageImports, TemplateHaskell #-}

module Examples.PubKey
where
  
import Crypto.PubKey.ECC.Generate
import Crypto.PubKey.ECC.Types
import "cryptonite" 
       Crypto.Random

import Data.Map   (Map)
import qualified
       Data.Map   as Map
import Data.Set   (Set)
import qualified
       Data.Set   as Set

import Ledger
import UTxO
import Witness


pubKeyLedger = [t2, t1]
  where
    t1 = Tx [] 
            [TxOut (vhash wit1) 1000] 1000 0
    t2 = Tx [txIn (hashTx t1) 0 wit1]
            [TxOut (vhash wit2) 800, TxOut (vhash wit1) 200] 0 0
    
    vhash = witnessHash
    wit1  = $$(lockWithPublicKey _pubKey _sig)
    wit2  = $$(revealPreimage "2")

    curve = getCurveByName SEC_p112r1
    drg   = drgNewSeed (seedFromInteger 42)
    ((pubKey, privKey), _)     = withDRG drg $ do
              generate curve