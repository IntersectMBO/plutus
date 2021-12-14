{-# OPTIONS_HADDOCK hide #-}
module Foundation.System.Bindings.PosixDef
    ( CErrno
    , CFd
    , CMemProtFlags
    , CMemMappingFlags
    , CMemAdvice
    , CMemSyncFlags
    , CSysconfName
    , COpenFlags
    , COff(..)
    , CMode(..)
    ) where

import Basement.Compat.C.Types

type CErrno = CInt
type CFd = CInt
type CMemProtFlags = CInt
type CMemMappingFlags = CInt
type CMemAdvice = CInt
type CMemSyncFlags = CInt
type CSysconfName = CInt
type COpenFlags = CInt
