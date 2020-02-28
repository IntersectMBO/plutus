{-# LANGUAGE DataKinds          #-}
{-# LANGUAGE EmptyCase          #-}
{-# LANGUAGE FlexibleInstances  #-}
{-# LANGUAGE GADTs              #-}
{-# LANGUAGE PolyKinds          #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeFamilies       #-}

module Cardano.Protocol.Puppet.Type where

import Network.TypedProtocol.Core

data Puppet state block where
  StIdle :: Puppet state block
  StBusy :: Puppet state block
  StDone :: Puppet state block

instance Protocol (Puppet state block) where
  data Message (Puppet state block) from to where
    MsgRequestState :: Message (Puppet state block) 'StIdle 'StBusy
    MsgReplyState :: state -> Message (Puppet state block) 'StBusy 'StIdle
    MsgValidate :: Message (Puppet state block) 'StIdle 'StBusy
    MsgValidated :: block -> Message (Puppet state block) 'StBusy 'StIdle
    MsgDone :: Message (Puppet state block) 'StIdle 'StDone

  data ClientHasAgency st where
    TokIdle :: ClientHasAgency 'StIdle

  data ServerHasAgency st where
    TokBusy :: ServerHasAgency 'StBusy

  data NobodyHasAgency st where
    TokDone :: NobodyHasAgency 'StDone

  exclusionLemma_ClientAndServerHaveAgency TokIdle tok = case tok of {}

  exclusionLemma_NobodyAndClientHaveAgency TokDone tok = case tok of {}

  exclusionLemma_NobodyAndServerHaveAgency TokDone tok = case tok of {}

deriving instance (Eq state, Eq block) =>
                   Eq (Message (Puppet state block) from to)

deriving instance (Show state, Show block) =>
                   Show (Message (Puppet state block) from to)

instance Show (ClientHasAgency (st :: Puppet state block)) where
  show TokIdle = "TokIdle"

instance Show (ServerHasAgency (st :: Puppet state block)) where
  show TokBusy = "TokBusy"
