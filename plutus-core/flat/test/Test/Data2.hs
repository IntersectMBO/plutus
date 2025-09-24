{-# LANGUAGE DefaultSignatures         #-}
{-# LANGUAGE DeriveDataTypeable        #-}
{-# LANGUAGE DeriveGeneric             #-}
{-# LANGUAGE EmptyDataDecls            #-}
{-# LANGUAGE FlexibleContexts          #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE GADTs                     #-}
{-# LANGUAGE MultiParamTypeClasses     #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE ScopedTypeVariables       #-}
{-# LANGUAGE TemplateHaskell           #-}
{-# LANGUAGE TypeFamilies              #-}
module Test.Data2 where

import Data.Data
import Data.Typeable
import GHC.Generics

-- A definition with the same name of a definition in Test.Data, used to test for name clashes.a
data List a = Cons2 a (List a)
            | Nil2
  deriving (Eq, Ord, Read, Show, Data, Generic ,Generic1)

