-- editorconfig-checker-disable-file
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE NoImplicitPrelude #-}

module Plugin.Lib where

import PlutusTx.Prelude

import PlutusTx.Builtins qualified as Builtins

-- This is here for the Plugin spec, but we're testing using things from a different module
andExternal :: Bool -> Bool -> Bool
andExternal a b = if a then b else False

data MyExternalRecord = MyExternalRecord {myExternal :: Integer}

evenDirect :: Integer -> Bool
evenDirect n = if Builtins.equalsInteger n 0 then True else oddDirect (Builtins.subtractInteger n 1)
{-# INLINEABLE evenDirect #-}

oddDirect :: Integer -> Bool
oddDirect n = if Builtins.equalsInteger n 0 then False else evenDirect (Builtins.subtractInteger n 1)
{-# INLINEABLE oddDirect #-}

-- GHC will lift out the error call to the top level, which is unsafe unless we bind it lazily.
-- This is in Lib so we get the fully optimized unfolding with awkward top-level binds and everything.
joinError :: Bool -> Bool -> ()
joinError x y = if andExternal x y then Builtins.error () else ()
