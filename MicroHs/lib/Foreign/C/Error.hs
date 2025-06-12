-----------------------------------------------------------------------------
-- |
-- Module      :  GHC.Internal.Foreign.C.Error
-- Copyright   :  (c) The FFI task force 2001
-- License     :  BSD-style (see the file libraries/base/LICENSE)
--
-- Maintainer  :  ffi@haskell.org
-- Stability   :  provisional
-- Portability :  portable
--
-- C-specific Marshalling support: Handling of C \"errno\" error codes.
--
-----------------------------------------------------------------------------

module Foreign.C.Error (
  -- * Haskell representations of @errno@ values

  Errno(..),

  eAGAIN, eINTR, eWOULDBLOCK,
{-
  -- ** Common @errno@ symbols
  -- | Different operating systems and\/or C libraries often support
  -- different values of @errno@.  This module defines the common values,
  -- but due to the open definition of 'Errno' users may add definitions
  -- which are not predefined.
  eOK, e2BIG, eACCES, eADDRINUSE, eADDRNOTAVAIL, eADV, eAFNOSUPPORT, eAGAIN,
  eALREADY, eBADF, eBADMSG, eBADRPC, eBUSY, eCHILD, eCOMM, eCONNABORTED,
  eCONNREFUSED, eCONNRESET, eDEADLK, eDESTADDRREQ, eDIRTY, eDOM, eDQUOT,
  eEXIST, eFAULT, eFBIG, eFTYPE, eHOSTDOWN, eHOSTUNREACH, eIDRM, eILSEQ,
  eINPROGRESS, eINTR, eINVAL, eIO, eISCONN, eISDIR, eLOOP, eMFILE, eMLINK,
  eMSGSIZE, eMULTIHOP, eNAMETOOLONG, eNETDOWN, eNETRESET, eNETUNREACH,
  eNFILE, eNOBUFS, eNODATA, eNODEV, eNOENT, eNOEXEC, eNOLCK, eNOLINK,
  eNOMEM, eNOMSG, eNONET, eNOPROTOOPT, eNOSPC, eNOSR, eNOSTR, eNOSYS,
  eNOTBLK, eNOTCONN, eNOTDIR, eNOTEMPTY, eNOTSOCK, eNOTSUP, eNOTTY, eNXIO,
  eOPNOTSUPP, ePERM, ePFNOSUPPORT, ePIPE, ePROCLIM, ePROCUNAVAIL,
  ePROGMISMATCH, ePROGUNAVAIL, ePROTO, ePROTONOSUPPORT, ePROTOTYPE,
  eRANGE, eREMCHG, eREMOTE, eROFS, eRPCMISMATCH, eRREMOTE, eSHUTDOWN,
  eSOCKTNOSUPPORT, eSPIPE, eSRCH, eSRMNT, eSTALE, eTIME, eTIMEDOUT,
  eTOOMANYREFS, eTXTBSY, eUSERS, eWOULDBLOCK, eXDEV,
-}
  -- ** 'Errno' functions
  isValidErrno,

  -- access to the current thread's "errno" value
  --
  getErrno,
  resetErrno,

  -- conversion of an "errno" value into IO error
  --
  errnoToIOError,

  -- throw current "errno" value
  --
  throwErrno,

  -- ** Guards for IO operations that may fail

  throwErrnoIf,
  throwErrnoIf_,
  throwErrnoIfRetry,
  throwErrnoIfRetry_,
  throwErrnoIfMinus1,
  throwErrnoIfMinus1_,
  throwErrnoIfMinus1Retry,
  throwErrnoIfMinus1Retry_,
  throwErrnoIfNull,
  throwErrnoIfNullRetry,

  throwErrnoIfRetryMayBlock,
  throwErrnoIfRetryMayBlock_,
  throwErrnoIfMinus1RetryMayBlock,
  throwErrnoIfMinus1RetryMayBlock_,
  throwErrnoIfNullRetryMayBlock,

  throwErrnoPath,
  throwErrnoPathIf,
  throwErrnoPathIf_,
  throwErrnoPathIfNull,
  throwErrnoPathIfMinus1,
  throwErrnoPathIfMinus1_,
) where
import qualified Prelude(); import MiniPrelude

import Foreign.Ptr
import Foreign.Marshal.Alloc
import Foreign.C.Types
import Foreign.C.String
import Foreign.Storable
import Data.Functor(void)
import Data.Maybe
import System.IO(Handle)
import System.IO.Error
import System.IO.Unsafe(unsafePerformIO)

{-
import GHC.Internal.IO
import GHC.Internal.IO.Exception
import GHC.Internal.IO.Handle.Types
import GHC.Internal.Num
import GHC.Internal.Base
-}

newtype Errno = Errno Int

instance Eq Errno where
  errno1@(Errno no1) == errno2@(Errno no2)
    | isValidErrno errno1 && isValidErrno errno2 = no1 == no2
    | otherwise                                  = False

{-
eOK, e2BIG, eACCES, eADDRINUSE, eADDRNOTAVAIL, eADV, eAFNOSUPPORT, eAGAIN,
  eALREADY, eBADF, eBADMSG, eBADRPC, eBUSY, eCHILD, eCOMM, eCONNABORTED,
  eCONNREFUSED, eCONNRESET, eDEADLK, eDESTADDRREQ, eDIRTY, eDOM, eDQUOT,
  eEXIST, eFAULT, eFBIG, eFTYPE, eHOSTDOWN, eHOSTUNREACH, eIDRM, eILSEQ,
  eINPROGRESS, eINTR, eINVAL, eIO, eISCONN, eISDIR, eLOOP, eMFILE, eMLINK,
  eMSGSIZE, eMULTIHOP, eNAMETOOLONG, eNETDOWN, eNETRESET, eNETUNREACH,
  eNFILE, eNOBUFS, eNODATA, eNODEV, eNOENT, eNOEXEC, eNOLCK, eNOLINK,
  eNOMEM, eNOMSG, eNONET, eNOPROTOOPT, eNOSPC, eNOSR, eNOSTR, eNOSYS,
  eNOTBLK, eNOTCONN, eNOTDIR, eNOTEMPTY, eNOTSOCK, eNOTSUP, eNOTTY, eNXIO,
  eOPNOTSUPP, ePERM, ePFNOSUPPORT, ePIPE, ePROCLIM, ePROCUNAVAIL,
  ePROGMISMATCH, ePROGUNAVAIL, ePROTO, ePROTONOSUPPORT, ePROTOTYPE,
  eRANGE, eREMCHG, eREMOTE, eROFS, eRPCMISMATCH, eRREMOTE, eSHUTDOWN,
  eSOCKTNOSUPPORT, eSPIPE, eSRCH, eSRMNT, eSTALE, eTIME, eTIMEDOUT,
  eTOOMANYREFS, eTXTBSY, eUSERS, eWOULDBLOCK, eXDEV                    :: Errno

eOK             = Errno 0
e2BIG           = Errno (CONST_E2BIG)
eACCES          = Errno (CONST_EACCES)
eADDRINUSE      = Errno (CONST_EADDRINUSE)
eADDRNOTAVAIL   = Errno (CONST_EADDRNOTAVAIL)
eADV            = Errno (CONST_EADV)
eAFNOSUPPORT    = Errno (CONST_EAFNOSUPPORT)
eAGAIN          = Errno (CONST_EAGAIN)
eALREADY        = Errno (CONST_EALREADY)
eBADF           = Errno (CONST_EBADF)
eBADMSG         = Errno (CONST_EBADMSG)
eBADRPC         = Errno (CONST_EBADRPC)
eBUSY           = Errno (CONST_EBUSY)
eCHILD          = Errno (CONST_ECHILD)
eCOMM           = Errno (CONST_ECOMM)
eCONNABORTED    = Errno (CONST_ECONNABORTED)
eCONNREFUSED    = Errno (CONST_ECONNREFUSED)
eCONNRESET      = Errno (CONST_ECONNRESET)
eDEADLK         = Errno (CONST_EDEADLK)
eDESTADDRREQ    = Errno (CONST_EDESTADDRREQ)
eDIRTY          = Errno (CONST_EDIRTY)
eDOM            = Errno (CONST_EDOM)
eDQUOT          = Errno (CONST_EDQUOT)
eEXIST          = Errno (CONST_EEXIST)
eFAULT          = Errno (CONST_EFAULT)
eFBIG           = Errno (CONST_EFBIG)
eFTYPE          = Errno (CONST_EFTYPE)
eHOSTDOWN       = Errno (CONST_EHOSTDOWN)
eHOSTUNREACH    = Errno (CONST_EHOSTUNREACH)
eIDRM           = Errno (CONST_EIDRM)
eILSEQ          = Errno (CONST_EILSEQ)
eINPROGRESS     = Errno (CONST_EINPROGRESS)
eINTR           = Errno (CONST_EINTR)
eINVAL          = Errno (CONST_EINVAL)
eIO             = Errno (CONST_EIO)
eISCONN         = Errno (CONST_EISCONN)
eISDIR          = Errno (CONST_EISDIR)
eLOOP           = Errno (CONST_ELOOP)
eMFILE          = Errno (CONST_EMFILE)
eMLINK          = Errno (CONST_EMLINK)
eMSGSIZE        = Errno (CONST_EMSGSIZE)
eMULTIHOP       = Errno (CONST_EMULTIHOP)
eNAMETOOLONG    = Errno (CONST_ENAMETOOLONG)
eNETDOWN        = Errno (CONST_ENETDOWN)
eNETRESET       = Errno (CONST_ENETRESET)
eNETUNREACH     = Errno (CONST_ENETUNREACH)
eNFILE          = Errno (CONST_ENFILE)
eNOBUFS         = Errno (CONST_ENOBUFS)
eNODATA         = Errno (CONST_ENODATA)
eNODEV          = Errno (CONST_ENODEV)
eNOENT          = Errno (CONST_ENOENT)
eNOEXEC         = Errno (CONST_ENOEXEC)
eNOLCK          = Errno (CONST_ENOLCK)
eNOLINK         = Errno (CONST_ENOLINK)
eNOMEM          = Errno (CONST_ENOMEM)
eNOMSG          = Errno (CONST_ENOMSG)
eNONET          = Errno (CONST_ENONET)
eNOPROTOOPT     = Errno (CONST_ENOPROTOOPT)
eNOSPC          = Errno (CONST_ENOSPC)
eNOSR           = Errno (CONST_ENOSR)
eNOSTR          = Errno (CONST_ENOSTR)
eNOSYS          = Errno (CONST_ENOSYS)
eNOTBLK         = Errno (CONST_ENOTBLK)
eNOTCONN        = Errno (CONST_ENOTCONN)
eNOTDIR         = Errno (CONST_ENOTDIR)
eNOTEMPTY       = Errno (CONST_ENOTEMPTY)
eNOTSOCK        = Errno (CONST_ENOTSOCK)
eNOTSUP         = Errno (CONST_ENOTSUP)
-- ^ @since base-4.7.0.0
eNOTTY          = Errno (CONST_ENOTTY)
eNXIO           = Errno (CONST_ENXIO)
eOPNOTSUPP      = Errno (CONST_EOPNOTSUPP)
ePERM           = Errno (CONST_EPERM)
ePFNOSUPPORT    = Errno (CONST_EPFNOSUPPORT)
ePIPE           = Errno (CONST_EPIPE)
ePROCLIM        = Errno (CONST_EPROCLIM)
ePROCUNAVAIL    = Errno (CONST_EPROCUNAVAIL)
ePROGMISMATCH   = Errno (CONST_EPROGMISMATCH)
ePROGUNAVAIL    = Errno (CONST_EPROGUNAVAIL)
ePROTO          = Errno (CONST_EPROTO)
ePROTONOSUPPORT = Errno (CONST_EPROTONOSUPPORT)
ePROTOTYPE      = Errno (CONST_EPROTOTYPE)
eRANGE          = Errno (CONST_ERANGE)
eREMCHG         = Errno (CONST_EREMCHG)
eREMOTE         = Errno (CONST_EREMOTE)
eROFS           = Errno (CONST_EROFS)
eRPCMISMATCH    = Errno (CONST_ERPCMISMATCH)
eRREMOTE        = Errno (CONST_ERREMOTE)
eSHUTDOWN       = Errno (CONST_ESHUTDOWN)
eSOCKTNOSUPPORT = Errno (CONST_ESOCKTNOSUPPORT)
eSPIPE          = Errno (CONST_ESPIPE)
eSRCH           = Errno (CONST_ESRCH)
eSRMNT          = Errno (CONST_ESRMNT)
eSTALE          = Errno (CONST_ESTALE)
eTIME           = Errno (CONST_ETIME)
eTIMEDOUT       = Errno (CONST_ETIMEDOUT)
eTOOMANYREFS    = Errno (CONST_ETOOMANYREFS)
eTXTBSY         = Errno (CONST_ETXTBSY)
eUSERS          = Errno (CONST_EUSERS)
eWOULDBLOCK     = Errno (CONST_EWOULDBLOCK)
eXDEV           = Errno (CONST_EXDEV)
-}

eINTR :: Errno
eAGAIN      = Errno cAGAIN;      foreign import capi "value EAGAIN"      cAGAIN      :: Int
eINTR       = Errno cINTR;       foreign import capi "value EINTR"       cINTR       :: Int
eWOULDBLOCK = Errno cWOULDBLOCK; foreign import capi "value EWOULDBLOCK" cWOULDBLOCK :: Int

isValidErrno               :: Errno -> Bool
isValidErrno (Errno errno)  = errno /= -1

foreign import ccall unsafe "sys/errno.h &errno" c_errno_ptr :: IO (Ptr Int)

getErrno :: IO Errno
getErrno = do
  p <- c_errno_ptr
  e <- peek p
  return (Errno e)

resetErrno :: IO ()
resetErrno = do
  p <- c_errno_ptr
  poke p 0
  return ()

throwErrno :: String -> IO a
throwErrno loc = do
  errno <- getErrno
  ioError (errnoToIOError loc errno Nothing Nothing)

throwErrnoIf    :: (a -> Bool)  -- ^ predicate to apply to the result value
                                -- of the 'IO' operation
                -> String       -- ^ textual description of the location
                -> IO a         -- ^ the 'IO' operation to be executed
                -> IO a
throwErrnoIf pred loc f  =
  do
    res <- f
    if pred res then throwErrno loc else return res

throwErrnoIf_   :: (a -> Bool) -> String -> IO a -> IO ()
throwErrnoIf_ pred loc f  = void $ throwErrnoIf pred loc f

throwErrnoIfRetry            :: (a -> Bool) -> String -> IO a -> IO a
throwErrnoIfRetry pred loc f  =
  do
    res <- f
    if pred res
      then do
        err <- getErrno
        if err == eINTR
          then throwErrnoIfRetry pred loc f
          else throwErrno loc
      else return res

throwErrnoIfRetryMayBlock
                :: (a -> Bool)  -- ^ predicate to apply to the result value
                                -- of the 'IO' operation
                -> String       -- ^ textual description of the location
                -> IO a         -- ^ the 'IO' operation to be executed
                -> IO b         -- ^ action to execute before retrying if
                                -- an immediate retry would block
                -> IO a
throwErrnoIfRetryMayBlock pred loc f on_block  =
  do
    res <- f
    if pred res
      then do
        err <- getErrno
        if err == eINTR
          then throwErrnoIfRetryMayBlock pred loc f on_block
          else if err == eWOULDBLOCK || err == eAGAIN
                 then do _ <- on_block
                         throwErrnoIfRetryMayBlock pred loc f on_block
                 else throwErrno loc
      else return res

throwErrnoIfRetry_            :: (a -> Bool) -> String -> IO a -> IO ()
throwErrnoIfRetry_ pred loc f  = void $ throwErrnoIfRetry pred loc f

throwErrnoIfRetryMayBlock_ :: (a -> Bool) -> String -> IO a -> IO b -> IO ()
throwErrnoIfRetryMayBlock_ pred loc f on_block
  = void $ throwErrnoIfRetryMayBlock pred loc f on_block

throwErrnoIfMinus1 :: (Eq a, Num a) => String -> IO a -> IO a
throwErrnoIfMinus1  = throwErrnoIf (== (-1))

throwErrnoIfMinus1_ :: (Eq a, Num a) => String -> IO a -> IO ()
throwErrnoIfMinus1_  = throwErrnoIf_ (== (-1))

throwErrnoIfMinus1Retry :: (Eq a, Num a) => String -> IO a -> IO a
throwErrnoIfMinus1Retry  = throwErrnoIfRetry (== (-1))

throwErrnoIfMinus1Retry_ :: (Eq a, Num a) => String -> IO a -> IO ()
throwErrnoIfMinus1Retry_  = throwErrnoIfRetry_ (== (-1))

throwErrnoIfMinus1RetryMayBlock :: (Eq a, Num a)
                                => String -> IO a -> IO b -> IO a
throwErrnoIfMinus1RetryMayBlock  = throwErrnoIfRetryMayBlock (== (-1))

throwErrnoIfMinus1RetryMayBlock_ :: (Eq a, Num a)
                                 => String -> IO a -> IO b -> IO ()
throwErrnoIfMinus1RetryMayBlock_  = throwErrnoIfRetryMayBlock_ (== (-1))

throwErrnoIfNull :: String -> IO (Ptr a) -> IO (Ptr a)
throwErrnoIfNull  = throwErrnoIf (== nullPtr)

throwErrnoIfNullRetry :: String -> IO (Ptr a) -> IO (Ptr a)
throwErrnoIfNullRetry  = throwErrnoIfRetry (== nullPtr)

throwErrnoIfNullRetryMayBlock :: String -> IO (Ptr a) -> IO b -> IO (Ptr a)
throwErrnoIfNullRetryMayBlock  = throwErrnoIfRetryMayBlock (== nullPtr)

throwErrnoPath :: String -> FilePath -> IO a
throwErrnoPath loc path =
  do
    errno <- getErrno
    ioError (errnoToIOError loc errno Nothing (Just path))

throwErrnoPathIf :: (a -> Bool) -> String -> FilePath -> IO a -> IO a
throwErrnoPathIf pred loc path f =
  do
    res <- f
    if pred res then throwErrnoPath loc path else return res

throwErrnoPathIf_ :: (a -> Bool) -> String -> FilePath -> IO a -> IO ()
throwErrnoPathIf_ pred loc path f  = void $ throwErrnoPathIf pred loc path f

throwErrnoPathIfNull :: String -> FilePath -> IO (Ptr a) -> IO (Ptr a)
throwErrnoPathIfNull  = throwErrnoPathIf (== nullPtr)

throwErrnoPathIfMinus1 :: (Eq a, Num a) => String -> FilePath -> IO a -> IO a
throwErrnoPathIfMinus1 = throwErrnoPathIf (== (-1))

throwErrnoPathIfMinus1_ :: (Eq a, Num a) => String -> FilePath -> IO a -> IO ()
throwErrnoPathIfMinus1_  = throwErrnoPathIf_ (== (-1))


foreign import ccall "string.h strerror_r"
    c_strerror_r :: Int -> CString -> CSize -> IO Int

errnoToString :: Errno -> IO String
errnoToString (Errno errno) =
    allocaBytes 512 $ \ ptr -> do
        ret <- c_strerror_r errno ptr (CSize 512)
        if ret /= 0
          then return "errnoToString failed"
          else peekCString ptr
  where len = 512::Int

errnoToIOError  :: String       -- ^ the location where the error occurred
                -> Errno        -- ^ the error number
                -> Maybe Handle -- ^ optional handle associated with the error
                -> Maybe String -- ^ optional filename associated with the error
                -> IOError
errnoToIOError loc errno@(Errno errno') maybeHdl maybeName = unsafePerformIO $ do
    str <- errnoToString errno
    return (IOError maybeHdl errType loc str (Just errno') maybeName)
  where
    errType = OtherError
{-
    errType =
        | errno == eOK             = OtherError
        | errno == e2BIG           = ResourceExhausted
        | errno == eACCES          = PermissionDenied
        | errno == eADDRINUSE      = ResourceBusy
        | errno == eADDRNOTAVAIL   = UnsupportedOperation
        | errno == eADV            = OtherError
        | errno == eAFNOSUPPORT    = UnsupportedOperation
        | errno == eAGAIN          = ResourceExhausted
        | errno == eALREADY        = AlreadyExists
        | errno == eBADF           = InvalidArgument
        | errno == eBADMSG         = InappropriateType
        | errno == eBADRPC         = OtherError
        | errno == eBUSY           = ResourceBusy
        | errno == eCHILD          = NoSuchThing
        | errno == eCOMM           = ResourceVanished
        | errno == eCONNABORTED    = OtherError
        | errno == eCONNREFUSED    = NoSuchThing
        | errno == eCONNRESET      = ResourceVanished
        | errno == eDEADLK         = ResourceBusy
        | errno == eDESTADDRREQ    = InvalidArgument
        | errno == eDIRTY          = UnsatisfiedConstraints
        | errno == eDOM            = InvalidArgument
        | errno == eDQUOT          = PermissionDenied
        | errno == eEXIST          = AlreadyExists
        | errno == eFAULT          = OtherError
        | errno == eFBIG           = PermissionDenied
        | errno == eFTYPE          = InappropriateType
        | errno == eHOSTDOWN       = NoSuchThing
        | errno == eHOSTUNREACH    = NoSuchThing
        | errno == eIDRM           = ResourceVanished
        | errno == eILSEQ          = InvalidArgument
        | errno == eINPROGRESS     = AlreadyExists
        | errno == eINTR           = Interrupted
        | errno == eINVAL          = InvalidArgument
        | errno == eIO             = HardwareFault
        | errno == eISCONN         = AlreadyExists
        | errno == eISDIR          = InappropriateType
        | errno == eLOOP           = InvalidArgument
        | errno == eMFILE          = ResourceExhausted
        | errno == eMLINK          = ResourceExhausted
        | errno == eMSGSIZE        = ResourceExhausted
        | errno == eMULTIHOP       = UnsupportedOperation
        | errno == eNAMETOOLONG    = InvalidArgument
        | errno == eNETDOWN        = ResourceVanished
        | errno == eNETRESET       = ResourceVanished
        | errno == eNETUNREACH     = NoSuchThing
        | errno == eNFILE          = ResourceExhausted
        | errno == eNOBUFS         = ResourceExhausted
        | errno == eNODATA         = NoSuchThing
        | errno == eNODEV          = UnsupportedOperation
        | errno == eNOENT          = NoSuchThing
        | errno == eNOEXEC         = InvalidArgument
        | errno == eNOLCK          = ResourceExhausted
        | errno == eNOLINK         = ResourceVanished
        | errno == eNOMEM          = ResourceExhausted
        | errno == eNOMSG          = NoSuchThing
        | errno == eNONET          = NoSuchThing
        | errno == eNOPROTOOPT     = UnsupportedOperation
        | errno == eNOSPC          = ResourceExhausted
        | errno == eNOSR           = ResourceExhausted
        | errno == eNOSTR          = InvalidArgument
        | errno == eNOSYS          = UnsupportedOperation
        | errno == eNOTBLK         = InvalidArgument
        | errno == eNOTCONN        = InvalidArgument
        | errno == eNOTDIR         = InappropriateType
        | errno == eNOTEMPTY       = UnsatisfiedConstraints
        | errno == eNOTSOCK        = InvalidArgument
        | errno == eNOTTY          = IllegalOperation
        | errno == eNXIO           = NoSuchThing
        | errno == eOPNOTSUPP      = UnsupportedOperation
        | errno == ePERM           = PermissionDenied
        | errno == ePFNOSUPPORT    = UnsupportedOperation
        | errno == ePIPE           = ResourceVanished
        | errno == ePROCLIM        = PermissionDenied
        | errno == ePROCUNAVAIL    = UnsupportedOperation
        | errno == ePROGMISMATCH   = ProtocolError
        | errno == ePROGUNAVAIL    = UnsupportedOperation
        | errno == ePROTO          = ProtocolError
        | errno == ePROTONOSUPPORT = ProtocolError
        | errno == ePROTOTYPE      = ProtocolError
        | errno == eRANGE          = UnsupportedOperation
        | errno == eREMCHG         = ResourceVanished
        | errno == eREMOTE         = IllegalOperation
        | errno == eROFS           = PermissionDenied
        | errno == eRPCMISMATCH    = ProtocolError
        | errno == eRREMOTE        = IllegalOperation
        | errno == eSHUTDOWN       = IllegalOperation
        | errno == eSOCKTNOSUPPORT = UnsupportedOperation
        | errno == eSPIPE          = UnsupportedOperation
        | errno == eSRCH           = NoSuchThing
        | errno == eSRMNT          = UnsatisfiedConstraints
        | errno == eSTALE          = ResourceVanished
        | errno == eTIME           = TimeExpired
        | errno == eTIMEDOUT       = TimeExpired
        | errno == eTOOMANYREFS    = ResourceExhausted
        | errno == eTXTBSY         = ResourceBusy
        | errno == eUSERS          = ResourceExhausted
        | errno == eWOULDBLOCK     = OtherError
        | errno == eXDEV           = UnsupportedOperation
        | otherwise                = OtherError
-}
