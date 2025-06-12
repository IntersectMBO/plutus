-- Copyright 2023 Lennart Augustsson
-- See LICENSE file for full license.
module MicroHs.Compile(
  compileCacheTop,
  compileMany,
  maybeSaveCache,
  getCached,
  validateCache,
  Cache, emptyCache, deleteFromCache,
  moduleToFile,
  packageDir, packageSuffix, packageTxtSuffix,
  mhsVersion,
  getMhsDir,
  openFilePath,
  ) where
import Data.Char
import Data.List
import Data.Maybe
import Data.Version
import MHSPrelude
import MicroHs.Abstract
import MicroHs.Builtin
import MicroHs.CompileCache
import MicroHs.Desugar
import MicroHs.Exp
import MicroHs.Expr
import MicroHs.Flags
import MicroHs.Ident
import MicroHs.IdentMap qualified as M
import MicroHs.List
import MicroHs.Package
import MicroHs.Parse
import MicroHs.StateIO
import MicroHs.SymTab
import MicroHs.TypeCheck
import Paths_MicroHs (getDataDir, version)
import Prelude qualified ()
import System.Directory
import System.Environment
import System.FilePath
import System.IO
import System.IO.MD5
import System.IO.Serialize
import System.IO.TimeMilli
import System.Process

mhsVersion :: String
mhsVersion = showVersion version

mhsCacheName :: FilePath
mhsCacheName = ".mhscache"

type Time = Int

type CM a = StateIO Cache a

-----------------

-- Compile the module with the given name, starting with the given cache.
-- Return the "compiled module" and the resulting cache.
compileCacheTop :: Flags -> IdentModule -> Cache -> IO ((IdentModule, [(Ident, Exp)]), Symbols, Cache)
compileCacheTop flags mn ch = do
  res@((_, ds), _, _) <- compile flags mn ch
  dumpIf flags Dcombinator $
    putStrLn $ "combinators:\n" ++ showLDefs ds
  return res

compileMany :: Flags -> [IdentModule] -> Cache -> IO Cache
compileMany flags mns ach = snd <$> runStateIO (mapM_ (compileModuleCached flags ImpNormal) mns) ach

getCached :: Flags -> IO Cache
getCached flags | not (readCache flags) = return emptyCache
getCached flags = do
  mcash <- loadCached mhsCacheName
  case mcash of
    Nothing ->
      return emptyCache
    Just cash -> do
      when (loading flags || verbosityGT flags 0) $
        putStrLn $ "Loading saved cache " ++ show mhsCacheName
      validateCache flags cash

maybeSaveCache :: Flags -> Cache -> IO ()
maybeSaveCache flags cash =
  when (writeCache flags) $ do
    when (verbosityGT flags 0) $
      putStrLn $ "Saving cache " ++ show mhsCacheName
    saveCache mhsCacheName cash

compile :: Flags -> IdentModule -> Cache -> IO ((IdentModule, [LDef]), Symbols, Cache)
compile flags nm ach = do
  let comp = do
--XXX        modify $ addBoot $ mkIdent "Control.Exception.Internal"      -- the compiler generates references to this module
        r <- compileModuleCached flags ImpNormal nm
        let loadBoots = do
              bs <- gets getBoots
              case bs of
                [] -> return ()
                bmn:_ -> do
                  when (verbosityGT flags 0) $
                    liftIO $ putStrLn $ "compiling used boot module " ++ showIdent bmn
                  _ <- compileModuleCached flags ImpNormal bmn
                  loadBoots
        loadBoots
        loadDependencies flags
        return r
  ((cm, syms, t), ch) <- runStateIO comp ach
  when (verbosityGT flags 0) $
    putStrLn $ "total import time     " ++ padLeft 6 (show t) ++ "ms"
  return ((tModuleName cm, concatMap tBindingsOf $ cachedModules ch), syms, ch)

-- Compile a module with the given name.
-- If the module has already been compiled, return the cached result.
-- If the module has not been compiled, first try to find a source file.
-- If there is no source file, try loading a package.
compileModuleCached :: Flags -> ImpType -> IdentModule -> CM (TModule [LDef], Symbols, Time)
compileModuleCached flags impt mn = do
  cash <- get
  case lookupCache mn cash of
    Nothing ->
      case impt of
        ImpBoot -> compileBootModule flags mn
        ImpNormal -> do
          when (verbosityGT flags 1) $ do
            ms <- gets getWorking
            putStrLnInd $ "[from " ++ head (map showIdent ms ++ ["-"]) ++ "]"
            putStrInd $ "importing " ++ showIdent mn
          mres <- liftIO (readModulePath flags "hs" mn)
          case mres of
            Nothing -> do
              (fn, res) <- findPkgModule flags mn
              liftIO $ when (verbosityGT flags 1) $ do
                when (verbosityGT flags 2) $
                  putStrLn $ " (" ++ show fn ++ ")"
                putStrLn ""
              return res
            Just (pathfn, file) -> do
              liftIO $ when (verbosityGT flags 1) $ do
                when (verbosityGT flags 2) $
                  putStrLn $ " (" ++ show pathfn ++ ")"
                putStrLn ""
              modify $ addWorking mn
              compileModule flags ImpNormal mn pathfn file
    Just tm -> do
      when (verbosityGT flags 1) $
        putStrLnInd $ "importing cached " ++ showIdent mn
      return (tm, noSymbols, 0)

putStrLnInd :: String -> CM ()
putStrLnInd msg = do
  ms <- gets getWorking
  liftIO $ putStrLn $ map (const ' ') ms ++ msg

putStrInd :: String -> CM ()
putStrInd msg = do
  ms <- gets getWorking
  liftIO $ putStr $ map (const ' ') ms ++ msg

noSymbols :: Symbols
noSymbols = (stEmpty, stEmpty)

compileBootModule :: Flags -> IdentModule -> CM (TModule [LDef], Symbols, Time)
compileBootModule flags mn = do
  when (verbosityGT flags 0) $
    putStrLnInd $ "importing boot " ++ showIdent mn
  mres <- liftIO (readModulePath flags ".hs-boot" mn)
  case mres of
    Nothing -> error $ "boot module not found: " ++ showIdent mn
    Just (pathfn, file) -> do
      modify $ addBoot mn
      compileModule flags ImpBoot mn pathfn file

compileModule :: Flags -> ImpType -> IdentModule -> FilePath -> String -> CM (TModule [LDef], Symbols, Time)
compileModule flags impt mn pathfn file = do
  t1 <- liftIO getTimeMilli
  mchksum <- liftIO (md5File pathfn)  -- XXX there is a small gap between reading and computing the checksum.
  let chksum :: MD5CheckSum
      chksum = fromMaybe undefined mchksum
  when (verbosityGT flags 4) $
    liftIO $ putStrLn $ "parsing: " ++ pathfn
  let pmdl = parseDie pTop pathfn file
  dumpIf flags Dparse $
    liftIO $ putStrLn $ "parsed:\n" ++ show pmdl
  let mdl@(EModule mnn _ defs) = addPreludeImport pmdl

  -- liftIO $ putStrLn $ showEModule mdl
  -- liftIO $ putStrLn $ showEDefs defs
  -- TODO: skip test when mn is a file name
  when (isNothing (getFileName mn) && mn /= mnn) $
    error $ "module name does not agree with file name: " ++ showIdent mn ++ " " ++ showIdent mnn
  let
    specs = [ s | Import s <- defs ]
    imported = [ (boot, m) | ImportSpec boot _ m _ _ <- specs ]
  t2 <- liftIO getTimeMilli
  (impMdls, _, tImps) <- unzip3 <$> mapM (uncurry $ compileModuleCached flags) imported

  t3 <- liftIO getTimeMilli
  glob <- gets getCacheTables
  let
    (tmdl, glob', syms) = typeCheck flags glob impt (zip specs impMdls) mdl
  modify $ setCacheTables glob'
  dumpIf flags Dtypecheck $
    liftIO $ putStrLn $ "type checked:\n" ++ showTModule showEDefs tmdl ++ "-----\n"
  let
    dmdl = desugar flags tmdl

  t4 <- liftIO getTimeMilli
  let
    cmdl = setBindings dmdl [ (i, e) | (i, e) <- tBindingsOf dmdl ]
  () <- return $ rnf cmdl  -- This makes execution slower, but speeds up GC
  t5 <- liftIO getTimeMilli

  let tParse = t2 - t1
      tTCDesug = t4 - t3
      tAbstract = t5 - t4
      tThis = tParse + tTCDesug + tAbstract
      tImp = sum tImps

  dumpIf flags Ddesugar $
    liftIO $ putStrLn $ "desugared:\n" ++ showTModule showLDefs dmdl
  when (verbosityGT flags 0) $
    putStrLnInd $ "importing done " ++ showIdent mn ++ ", " ++ show tThis ++
            "ms (" ++ show tParse ++ " + " ++ show tTCDesug ++ " + " ++ show tAbstract ++ ")"
  when (loading flags && mn /= mkIdent "Interactive" && not (verbosityGT flags 0)) $
    liftIO $ putStrLn $ "loaded " ++ showIdent mn ++ " (" ++ pathfn ++ ")"

  case impt of
    ImpNormal -> modify $ workToDone (cmdl, map snd imported, chksum)
    ImpBoot   -> return ()

  return (cmdl, syms, tThis + tImp)

addPreludeImport :: EModule -> EModule
addPreludeImport (EModule mn es ds) =
  EModule mn es ds
  -- where ds' = ps' ++ nps
  --       (ps, nps) = partition isImportPrelude ds
  --       isImportPrelude (Import (ImportSpec _ _ i _ _)) = i == idPrelude
  --       isImportPrelude _ = False
  --       idPrelude = mkIdent "Prelude"
  --       iblt = Import $ ImportSpec ImpNormal True builtinMdlQ (Just builtinMdl) Nothing
  --       ps' =
  --         case ps of
  --           [] -> [Import $ ImportSpec ImpNormal False idPrelude Nothing Nothing,      -- no Prelude imports, so add 'import Prelude'
  --                  iblt]                                                               -- and 'import Mhs.Builtin as B@'
  --           [Import (ImportSpec ImpNormal True _ Nothing (Just (False, [])))] -> []    -- exactly 'import qualified Prelude()', so import nothing
  --           _ -> iblt : ps                                                             -- keep the given Prelude imports, add Builtin

-------------------------------------------

validateCache :: Flags -> Cache -> IO Cache
validateCache flags acash = execStateIO (mapM_ (validate . fst) fdeps) acash
  where
    fdeps = getImportDeps acash                           -- forwards dependencies
    deps = invertGraph fdeps                              -- backwards dependencies
    invalidate :: IdentModule -> CM ()
    invalidate mn = do
      b <- gets $ isJust . lookupCache mn
      when b $ do
        -- It's still in the cache, so invalidate it, and all modules that import it
        when (verbosityGT flags 1) $
          liftIO $ putStrLn $ "invalidate cached " ++ show mn
        modify (deleteFromCache mn)
        mapM_ invalidate $ fromMaybe [] $ M.lookup mn deps
    validate :: IdentModule -> CM ()
    validate mn = do
      cash <- get
      case lookupCacheChksum mn cash of
        Nothing -> return () -- no longer in the cache, so just ignore.
        Just chksum -> do
          mhdl <- liftIO $ findModulePath flags ".hs" mn
          case mhdl of
            Nothing ->
              -- Cannot find module, so invalidate it
              invalidate mn
            Just (_, h) -> do
              cs <- liftIO $ md5Handle h
              liftIO $ hClose h
              when (cs /= chksum) $
                -- bad checksum, invalidate module
                invalidate mn

-- Take a graph in adjencency list form and reverse all the arrow.
-- Used to invert the import graph.
invertGraph :: [(IdentModule, [IdentModule])] -> M.Map [IdentModule]
invertGraph = foldr ins M.empty
  where
    ins :: (IdentModule, [IdentModule]) -> M.Map [IdentModule] -> M.Map [IdentModule]
    ins (m, ms) g = foldr (\ n -> M.insertWith (++) n [m]) g ms

------------------

-- Is the module name actually a file name?
getFileName :: IdentModule -> Maybe String
getFileName m | ".hs" `isSuffixOf` s = Just s
              | otherwise = Nothing
  where s = unIdent m

readModulePath :: Flags -> String -> IdentModule -> IO (Maybe (FilePath, String))
readModulePath flags suf mn = do
  case getFileName mn of
    Just fn -> do
      mh <- openFileM fn ReadMode
      case mh of
        Nothing -> errorMessage (getSLoc mn) $ "File not found: " ++ show fn
        Just h  -> readRest fn =<< hGetContents h
    _ -> do
      mh <- findModulePath flags suf mn
      case mh of
        Nothing -> do
          mhc <- findModulePath flags (suf ++ "c") mn  -- look for hsc file
          case mhc of
            Nothing -> do
              mhl <- findModulePath flags ("l" ++ suf) mn  -- look for lhs file
              case mhl of
                Nothing -> do
                  return Nothing
                Just (fn, h) -> readRest fn . unlit =<< hGetContents h
            Just (_fn, _h) -> undefined  -- hsc2hs no implemented yet
        Just (fn, h) -> readRest fn =<< hGetContents h
  where readRest :: FilePath -> String -> IO (Maybe (FilePath, String))
        readRest fn file = do
          hasCPP <- hasLangCPP fn
          file' <-
            if hasCPP || doCPP flags then do
              runCPPString flags fn file
            else
              return file
          return (Just (fn, file'))

-- Check if the file contains {-# LANGUAGE ... CPP ... #-}
-- XXX This is pretty hacky and not really correct.
hasLangCPP :: FilePath -> IO Bool
hasLangCPP fn = do
  let scanFor _ []                          = False
      scanFor s ('{':'-':'#':cs)            = scanFor' s cs
      scanFor _ ('m':'o':'d':'u':'l':'e':_) = False
      scanFor s (_:cs)                      = scanFor s cs
      scanFor' _ [] = False
      scanFor' s ('#':'-':'}':cs) = scanFor s cs
      scanFor' s (' ':cs) | s `isPrefixOf` cs = True
      scanFor' s (_:cs) = scanFor' s cs
  scanFor "cpp" . map toLower <$> readFile fn

moduleToFile :: IdentModule -> FilePath
moduleToFile mn = map (\ c -> if c == '.' then pathSeparator else c) (unIdent mn)

findModulePath :: Flags -> String -> IdentModule -> IO (Maybe (FilePath, Handle))
findModulePath flags suf mn = do
  let
    fn = moduleToFile mn <.> suf
  openFilePath (paths flags) fn

openFilePath :: [FilePath] -> FilePath -> IO (Maybe (FilePath, Handle))
openFilePath adirs fileName =
  case adirs of
    [] -> return Nothing
    dir:dirs -> do
      let
        path = dir </> fileName
      mh <- openFileM path ReadMode
      case mh of
        Nothing  -> openFilePath dirs fileName -- If opening failed, try the next directory
        Just hdl -> return (Just (path, hdl))

runCPPString :: Flags -> FilePath -> String -> IO String
runCPPString flags fn ifile = do
  (fni, hi) <- openTmpFile "mhsin.hs"
  hClose hi
  writeFile fni $ "#line 1 \"" ++ fn ++ "\"\n" ++ ifile
  (fno, ho) <- openTmpFile "mhsout.hs"
  runCPP flags fni fno
  ofile <- hGetContents ho
  removeFile fni
  removeFile fno
  return ofile

mhsDefines :: [String]
mhsDefines =
  [ "-D__MHS__"                                 -- We are MHS
  ]

runCPP :: Flags -> FilePath -> FilePath -> IO ()
runCPP flags infile outfile = do
  mcpphs <- lookupEnv "MHSCPPHS"
  datadir <- getMhsDir
  let cpphs = fromMaybe "cpphs" mcpphs
      mhsIncludes = ["-I" ++ datadir </> "src/runtime"]
      args = mhsDefines ++ mhsIncludes ++ map quote (cppArgs flags)
      cmd = cpphs ++ " --strip " ++ unwords args ++ " " ++ infile ++ " -O" ++ outfile
      quote s = "'" ++ s ++ "'"
  when (verbosityGT flags 1) $
    putStrLn $ "Run cpphs: " ++ show cmd
  callCommand cmd

packageDir :: String
packageDir = "packages"
packageSuffix :: String
packageSuffix = ".pkg"
packageTxtSuffix :: String
packageTxtSuffix = ".txt"

-- Find the module mn in the package path, and return it's contents.
findPkgModule :: Flags -> IdentModule -> CM (FilePath, (TModule [LDef], Symbols, Time))
findPkgModule flags mn = do
  t0 <- liftIO getTimeMilli
  let fn = moduleToFile mn <.> packageTxtSuffix
  mres <- liftIO $ openFilePath (pkgPath flags) fn
  case mres of
    Just (pfn, hdl) -> do
      -- liftIO $ putStrLn $ "findPkgModule " ++ pfn
      pkg <- liftIO $ hGetContents hdl  -- this closes the handle
      let dir = take (length pfn - length fn) pfn  -- directory where the file was found
      loadPkg flags (dir ++ packageDir </> pkg)
      cash <- get
      case lookupCache mn cash of
        Nothing -> error $ "package does not contain module " ++ pkg ++ " " ++ showIdent mn
        Just t -> do
          t1 <- liftIO getTimeMilli
          return (pfn, (t, noSymbols, t1 - t0))
    Nothing ->
      errorMessage (getSLoc mn) $
        "Module not found: " ++ show mn ++
        "\nsearch path=" ++ show (paths flags) ++
        "\npackage path=" ++ show (pkgPath flags)

loadPkg :: Flags -> FilePath -> CM ()
loadPkg flags fn = do
  when (loading flags || verbosityGT flags 0) $
    liftIO $ putStrLn $ "Loading package " ++ fn
  pkg <- liftIO $ readSerialized fn
  when (pkgCompiler pkg /= mhsVersion) $
    error $ "Package compile version mismatch: file=" ++ fn ++ ", package=" ++ pkgCompiler pkg ++ ", compiler=" ++ mhsVersion
  modify $ addPackage fn pkg

-- XXX add function to find&load package from package name

-- Load all packages that we depend on, but that are not already loaded.
loadDependencies :: Flags -> CM ()
loadDependencies flags = do
  loadedPkgs <- gets getPkgs
  let deps = concatMap pkgDepends loadedPkgs
      loaded = map pkgName loadedPkgs
      deps' = [ pv | pv@(p, _v) <- deps, p `notElem` loaded ]
  if null deps' then
    return ()
   else do
    mapM_ (loadDeps flags) deps'
    loadDependencies flags  -- loadDeps can add new dependencies

loadDeps :: Flags -> (IdentPackage, Version) -> CM ()
loadDeps flags (pid, pver) = do
  mres <- liftIO $ openFilePath (pkgPath flags) (packageDir </> unIdent pid ++ "-" ++ showVersion pver <.> packageSuffix)
  case mres of
    Nothing -> error $ "Cannot find package " ++ showIdent pid
    Just (pfn, hdl) -> do
      liftIO $ hClose hdl
      loadPkg flags pfn

getMhsDir :: IO FilePath
getMhsDir = maybe getDataDir return =<< lookupEnv "MHSDIR"

-- Deal with literate Haskell
unlit :: String -> String
unlit = unlines . un True . lines
  where
    un _ [] = []
    un _ (l:ls) | all isSpace l = un True ls
    un _ ("\\begin{code}":ls) = "" : code ls
    un spc (l@('#':'!':_) : ls) = l : un spc ls
    un spc (('>':l):ls) | spc = (' ':l) : un True ls
                        | otherwise = error "unlit: missing blank before >"
    un _ (_:ls) = un False ls
    -- We allow non-blank to follow directly after >
    code ("\\end{code}":ls) = "" : un False ls
    code (l : ls)           = l : code ls
    code []                 = error "unlit: missing \\end{code}"
