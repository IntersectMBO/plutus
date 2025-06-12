module System.IO.Error (
    IOException(..),

    -- * I\/O errors
    IOError,
    IOErrorType(..),

    userError,

    mkIOError,

    annotateIOError,

    -- ** Classifying I\/O errors
    isAlreadyExistsError,
    isDoesNotExistError,
    isAlreadyInUseError,
    isFullError,
    isEOFError,
    isIllegalOperation,
    isPermissionError,
    isUserError,
    isResourceVanishedError,

    -- ** Attributes of I\/O errors
    ioeGetErrorType,
    ioeGetLocation,
    ioeGetErrorString,
    ioeGetHandle,
    ioeGetFileName,

    ioeSetErrorType,
    ioeSetErrorString,
    ioeSetLocation,
    ioeSetHandle,
    ioeSetFileName,

    -- * Types of I\/O error
    IOErrorType,                -- abstract

    alreadyExistsErrorType,
    doesNotExistErrorType,
    alreadyInUseErrorType,
    fullErrorType,
    eofErrorType,
    illegalOperationErrorType,
    permissionErrorType,
    userErrorType,
    resourceVanishedErrorType,

    -- ** 'IOErrorType' predicates
    isAlreadyExistsErrorType,
    isDoesNotExistErrorType,
    isAlreadyInUseErrorType,
    isFullErrorType,
    isEOFErrorType,
    isIllegalOperationErrorType,
    isPermissionErrorType,
    isUserErrorType,
    isResourceVanishedErrorType,

    -- * Throwing and catching I\/O errors

    ioError,

    catchIOError,
    tryIOError,

    modifyIOError,
  ) where
import Control.Exception.Internal
import Control.Monad
import Data.Bool
import Data.Char_Type
import Data.Either
import Data.Eq
import Data.Function
import Data.Functor
import Data.Int
import Data.List
import Data.Maybe
import Data.Records
import Data.String
import {-# SOURCE #-} Data.Typeable
import Prelude qualified ()
import Primitives (IO)
import System.IO.Internal
import Text.Show


ioException     :: IOException -> IO a
ioException err = throw err

ioError         :: IOError -> IO a
ioError         =  ioException

type IOError = IOException

data IOException
 = IOError {
     ioe_handle      :: Maybe Handle,   -- ^ the handle used by the action flagging
                                     --   the error.
     ioe_type        :: IOErrorType,    -- ^ what it was.
     ioe_location    :: String,         -- ^ location.
     ioe_description :: String,      -- ^ error type specific information.
     ioe_errno       :: Maybe Int,      -- ^ errno leading to this error, if any.
     ioe_filename    :: Maybe FilePath  -- ^ filename the error is related to
                                     --   (some libraries may assume different encodings
                                     --   when constructing this field from e.g. 'ByteString'
                                     --   or other types)
   }
  deriving (Typeable)

instance Exception IOException

instance Eq IOException where
  (IOError h1 e1 loc1 str1 en1 fn1) == (IOError h2 e2 loc2 str2 en2 fn2) =
    e1==e2 && str1==str2 && h1==h2 && loc1==loc2 && en1==en2 && fn1==fn2

-- | An abstract type that contains a value for each variant of 'IOError'.
data IOErrorType
  -- Haskell 2010:
  = AlreadyExists
  | NoSuchThing
  | ResourceBusy
  | ResourceExhausted
  | EOF
  | IllegalOperation
  | PermissionDenied
  | UserError
  -- GHC only:
  | UnsatisfiedConstraints
  | SystemError
  | ProtocolError
  | OtherError
  | InvalidArgument
  | InappropriateType
  | HardwareFault
  | UnsupportedOperation
  | TimeExpired
  | ResourceVanished
  | Interrupted
  deriving (Eq)

instance Show IOErrorType where
  showsPrec _ e =
    showString $
    case e of
      AlreadyExists          -> "already exists"
      NoSuchThing            -> "does not exist"
      ResourceBusy           -> "resource busy"
      ResourceExhausted      -> "resource exhausted"
      EOF                    -> "end of file"
      IllegalOperation       -> "illegal operation"
      PermissionDenied       -> "permission denied"
      UserError              -> "user error"
      HardwareFault          -> "hardware fault"
      InappropriateType      -> "inappropriate type"
      Interrupted            -> "interrupted"
      InvalidArgument        -> "invalid argument"
      OtherError             -> "failed"
      ProtocolError          -> "protocol error"
      ResourceVanished       -> "resource vanished"
      SystemError            -> "system error"
      TimeExpired            -> "timeout"
      UnsatisfiedConstraints -> "unsatisfied constraints" -- ultra-precise!
      UnsupportedOperation   -> "unsupported operation"

userError       :: String  -> IOError
userError str   =  IOError Nothing UserError "" str Nothing Nothing

instance Show IOException where
    showsPrec p (IOError hdl iot loc s _ fn) =
      (case fn of
         Nothing -> case hdl of
                        Nothing -> id
                        Just h  -> showsPrec p h . showString ": "
         Just name -> showString name . showString ": ") .
      (case loc of
         "" -> id
         _  -> showString loc . showString ": ") .
      showsPrec p iot .
      (case s of
         "" -> id
         _  -> showString " (" . showString s . showString ")")

-----------

tryIOError     :: IO a -> IO (Either IOError a)
tryIOError f   =  catch (Right <$> f)
                        (return . Left)

mkIOError :: IOErrorType -> String -> Maybe Handle -> Maybe FilePath -> IOError
mkIOError t location maybe_hdl maybe_filename =
               IOError{ ioe_type = t,
                        ioe_location = location,
                        ioe_description = "",
                        ioe_errno = Nothing,
                        ioe_handle = maybe_hdl,
                        ioe_filename = maybe_filename
                        }

isAlreadyExistsError :: IOError -> Bool
isAlreadyExistsError = isAlreadyExistsErrorType    . ioeGetErrorType

isDoesNotExistError :: IOError -> Bool
isDoesNotExistError  = isDoesNotExistErrorType     . ioeGetErrorType

isAlreadyInUseError :: IOError -> Bool
isAlreadyInUseError  = isAlreadyInUseErrorType     . ioeGetErrorType

isFullError         :: IOError -> Bool
isFullError          = isFullErrorType             . ioeGetErrorType

isEOFError          :: IOError -> Bool
isEOFError           = isEOFErrorType              . ioeGetErrorType

isIllegalOperation  :: IOError -> Bool
isIllegalOperation   = isIllegalOperationErrorType . ioeGetErrorType

isPermissionError   :: IOError -> Bool
isPermissionError    = isPermissionErrorType       . ioeGetErrorType

isUserError         :: IOError -> Bool
isUserError          = isUserErrorType             . ioeGetErrorType

isResourceVanishedError :: IOError -> Bool
isResourceVanishedError = isResourceVanishedErrorType . ioeGetErrorType

alreadyExistsErrorType   :: IOErrorType
alreadyExistsErrorType    = AlreadyExists

doesNotExistErrorType    :: IOErrorType
doesNotExistErrorType     = NoSuchThing

alreadyInUseErrorType    :: IOErrorType
alreadyInUseErrorType     = ResourceBusy

fullErrorType            :: IOErrorType
fullErrorType             = ResourceExhausted

eofErrorType             :: IOErrorType
eofErrorType              = EOF

illegalOperationErrorType :: IOErrorType
illegalOperationErrorType = IllegalOperation

permissionErrorType      :: IOErrorType
permissionErrorType       = PermissionDenied

userErrorType            :: IOErrorType
userErrorType             = UserError

resourceVanishedErrorType :: IOErrorType
resourceVanishedErrorType = ResourceVanished

isAlreadyExistsErrorType :: IOErrorType -> Bool
isAlreadyExistsErrorType AlreadyExists = True
isAlreadyExistsErrorType _             = False

isDoesNotExistErrorType :: IOErrorType -> Bool
isDoesNotExistErrorType NoSuchThing = True
isDoesNotExistErrorType _           = False

isAlreadyInUseErrorType :: IOErrorType -> Bool
isAlreadyInUseErrorType ResourceBusy = True
isAlreadyInUseErrorType _            = False

isFullErrorType :: IOErrorType -> Bool
isFullErrorType ResourceExhausted = True
isFullErrorType _                 = False

isEOFErrorType :: IOErrorType -> Bool
isEOFErrorType EOF = True
isEOFErrorType _   = False

isIllegalOperationErrorType :: IOErrorType -> Bool
isIllegalOperationErrorType IllegalOperation = True
isIllegalOperationErrorType _                = False

isPermissionErrorType :: IOErrorType -> Bool
isPermissionErrorType PermissionDenied = True
isPermissionErrorType _                = False

isUserErrorType :: IOErrorType -> Bool
isUserErrorType UserError = True
isUserErrorType _         = False

isResourceVanishedErrorType :: IOErrorType -> Bool
isResourceVanishedErrorType ResourceVanished = True
isResourceVanishedErrorType _                = False

ioeGetErrorType       :: IOError -> IOErrorType
ioeGetErrorString     :: IOError -> String
ioeGetLocation        :: IOError -> String
ioeGetHandle          :: IOError -> Maybe Handle
ioeGetFileName        :: IOError -> Maybe FilePath

ioeGetErrorType ioe = ioe_type ioe

ioeGetErrorString ioe
   | isUserErrorType (ioe_type ioe) = ioe_description ioe
   | otherwise                      = show (ioe_type ioe)

ioeGetLocation ioe = ioe_location ioe

ioeGetHandle ioe = ioe_handle ioe

ioeGetFileName ioe = ioe_filename ioe

ioeSetErrorType   :: IOError -> IOErrorType -> IOError
ioeSetErrorString :: IOError -> String      -> IOError
ioeSetLocation    :: IOError -> String      -> IOError
ioeSetHandle      :: IOError -> Handle      -> IOError
ioeSetFileName    :: IOError -> FilePath    -> IOError

ioeSetErrorType   ioe errtype  = ioe{ ioe_type = errtype }
ioeSetErrorString ioe str      = ioe{ ioe_description = str }
ioeSetLocation    ioe str      = ioe{ ioe_location = str }
ioeSetHandle      ioe hdl      = ioe{ ioe_handle = Just hdl }
ioeSetFileName    ioe filename = ioe{ ioe_filename = Just filename }

modifyIOError :: (IOError -> IOError) -> IO a -> IO a
modifyIOError f io = catch io (ioError . f)

annotateIOError :: IOError
              -> String
              -> Maybe Handle
              -> Maybe FilePath
              -> IOError
annotateIOError ioe loc hdl path =
  ioe{ ioe_handle = hdl `mplus` ioe_handle ioe,
       ioe_location = loc, ioe_filename = path `mplus` ioe_filename ioe }

catchIOError :: IO a -> (IOError -> IO a) -> IO a
catchIOError = catch
