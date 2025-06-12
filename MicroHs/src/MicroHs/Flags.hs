module MicroHs.Flags(
  Flags(..), verbosityGT, defaultFlags,
  DumpFlag(..), dumpIf,
  wantGMP) where
import MHSPrelude
import Prelude qualified ()

data Flags = Flags {
  verbose    :: Int,        -- verbosity level
  runIt      :: Bool,       -- run instead of compile
  mhsdir     :: FilePath,   -- where MHS files live
  paths      :: [FilePath], -- module search path
  output     :: String,     -- output file
  loading    :: Bool,       -- show loading message
  speed      :: Bool,       -- show lines/s
  readCache  :: Bool,       -- read and use cache
  writeCache :: Bool,       -- generate cache
  useTicks   :: Bool,       -- emit ticks
  doCPP      :: Bool,       -- run ccphs on input files
  cppArgs    :: [String],   -- flags for CPP
  cArgs      :: [String],   -- arguments for C compiler
  compress   :: Bool,       -- compress generated combinators
  buildPkg   :: Maybe FilePath, -- build a package
  listPkg    :: Maybe FilePath, -- list package contents
  pkgPath    :: [FilePath], -- package search path
  installPkg :: Bool,       -- install a package
  target     :: String,     -- Compile target defined in target.conf
  dumpFlags  :: [DumpFlag], -- For debugging,
  useStdin   :: Bool        -- Use stdin in interactive system
  }
  deriving (Show)

verbosityGT :: Flags -> Int -> Bool
verbosityGT flags v = verbose flags > v

defaultFlags :: FilePath -> Flags
defaultFlags dir = Flags {
  verbose    = 0,
  runIt      = False,
  mhsdir     = dir,
  paths      = ["."] ++ gmp ++ [dir ++ "/lib"],
  output     = "out.comb",
  loading    = False,
  speed      = False,
  readCache  = False,
  writeCache = False,
  useTicks   = False,
  doCPP      = False,
  cppArgs    = [],
  cArgs      = [],
  compress   = False,
  buildPkg   = Nothing,
  listPkg    = Nothing,
  pkgPath    = [],
  installPkg = False,
  target     = "default",
  dumpFlags  = [],
  useStdin   = False
  }
  -- This is a hack so that the in-place mhs picks up GMP.
  where gmp | dir == "." && wantGMP = ["lib/gmp"]
            | otherwise             = []

data DumpFlag = Dparse | Dderive | Dtypecheck | Ddesugar | Dtoplevel | Dcombinator | Dall
  deriving (Eq, Show, Enum, Bounded)

dumpIf :: Monad m => Flags -> DumpFlag -> m () -> m ()
dumpIf flags df act | df `elem` dfs || Dall `elem` dfs = act
                    | otherwise = return ()
  where dfs = dumpFlags flags
