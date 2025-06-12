module System.IO_Handle(BFILE, Handle(..), HandleState(..)) where
import Data.Bool
import Data.Eq
import Data.IORef
import Prelude qualified ()
import Primitives

-- A handle is a ForeignPtr to a C BFILE transducer.
-- It needs to be a ForeignPtr so it can have a finalizer
-- that closes the underlying BFILE when the Handle is gc():ed.

data BFILE  -- tag used for C pointers to BFILE structs

data Handle = Handle (ForeignPtr BFILE) (IORef HandleState) [Char]

data HandleState = HRead | HWrite | HReadWrite | HSemiClosed | HClosed
  deriving (Eq)
