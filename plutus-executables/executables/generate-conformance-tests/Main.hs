module Main (main) where

import Evaluation.Builtins.Conformance
  ( CheckMode (..)
  , OutputFormat (..)
  , PropertyId (..)
  , checkModeName
  , formatName
  , propertyIdPath
  , propertyIdText
  )
import Evaluation.Builtins.Conformance.Suites (allSuites)
import Paths_plutus_executables (version)
import PlutusExecutables.Conformance.Info
  ( InfoDetails (..)
  , removeInfo
  , writeInfo
  )

import Control.Exception (SomeException, catch, throwIO)
import Control.Monad (forM, forM_, when)
import Data.List (intersperse, isInfixOf, nub)
import Data.Version (showVersion)
import Options.Applicative
import Options.Applicative.Help.Pretty (Doc, hardline, pretty)
import System.Directory (doesDirectoryExist, doesPathExist, listDirectory, removePathForcibly)
import System.FilePath ((</>))
import System.IO (hPutStrLn, stderr)
import System.Random (randomIO)
import Test.QuickCheck.Random (mkQCGen)

data Options = Options
  { outputDirectory :: FilePath
  , numberOfFiles :: Int
  , randomSeed :: Maybe Int
  , outputFormat :: OutputFormat
  , namePatterns :: [String]
  , listTests :: Bool
  , cleanOutput :: Bool
  , forceOutput :: Bool
  , checkMode :: CheckMode
  }

options :: Parser Options
options =
  Options
    <$> strOption
      ( long "output-dir"
          <> short 'o'
          <> metavar "DIR"
          <> value "conformance-property-tests"
          <> showDefault
          <> help "Root directory for generated conformance cases"
      )
    <*> option
      ( do
          n <- auto
          if n > 0 then pure n else readerError "the number of cases must be positive"
      )
      ( long "num-files"
          <> short 'n'
          <> metavar "N"
          <> value 200
          <> showDefault
          <> help
            "Number of numbered cases per property; equality cases emit an -A/-B pair, each with expected results and a budget"
      )
    <*> optional
      ( option
          auto
          ( long "seed"
              <> short 's'
              <> metavar "INT"
              <> help "QuickCheck seed for reproducible inputs (default: a fresh random seed, recorded in info.json)"
          )
      )
    <*> option
      ( eitherReader $ \arg -> case arg of
          "flat" -> Right Flat
          "uplc" -> Right Uplc
          "both" -> Right Both
          _ -> Left "format must be flat, uplc, or both"
      )
      ( long "format"
          <> metavar "flat|uplc|both"
          <> value Flat
          <> showDefaultWith (const "flat")
          <> help "Output encoding; writes matching .flat.expected and/or .uplc.expected files"
      )
    <*> many
      ( strOption
          ( long "match"
              <> short 'm'
              <> metavar "TEXT"
              <> help
                "Match a case-sensitive substring of TYPE/MODULE/[GROUP/]PROPERTY; repeat to match any substring (default: all properties)"
          )
      )
    <*> switch
      ( long "list"
          <> help "List matching property paths without generating inputs or writing files"
      )
    <*> switch
      ( long "clean"
          <> help
            "Remove existing cases before generating: those of the selected properties, or, with no --match, all of the directories this tool writes"
      )
    <*> switch
      ( long "force"
          <> help "Write into a non-empty output directory anyway"
      )
    <*> flag
      FastCheck
      FullCheck
      ( long "full-check"
          <> help
            "During generation, typecheck each case's terms before checking it against its property, as the normal tests do; much slower than the default check, which does not typecheck"
      )

{-| Refuse to generate into a directory that already contains anything unless
the user asked for it: cases are only overwritten by name, so unrelated or
stale files would silently remain alongside the new ones. -}
checkOutputDirectory :: Options -> IO ()
checkOutputDirectory opts = do
  let dir = outputDirectory opts
  exists <- doesPathExist dir
  isDirectory <- doesDirectoryExist dir
  when (exists && not isDirectory) $
    ioError . userError $
      "output path " <> show dir <> " exists and is not a directory"
  when (isDirectory && not (forceOutput opts)) $ do
    entries <- listDirectory dir
    when (not (null entries)) $
      ioError . userError $
        "output directory "
          <> show dir
          <> " is not empty; use --force to write into it anyway"

{-| The top-level directories this tool writes: the first path segment of every
property. Cleaning removes only these, never other things in the output
directory. -}
ownedDirectories :: [FilePath]
ownedDirectories =
  nub [directory | PropertyId (directory : _) _ <- concatMap fst allSuites]

-- | Does the directory exist and contain anything at all?
hasAnyEntries :: FilePath -> IO Bool
hasAnyEntries dir = do
  exists <- doesDirectoryExist dir
  if exists then not . null <$> listDirectory dir else pure False

-- | Is there anything in the output directory that this tool did not write?
hasUnrelatedEntries :: FilePath -> IO Bool
hasUnrelatedEntries dir = do
  exists <- doesDirectoryExist dir
  if exists
    then any (`notElem` ("info.json" : ownedDirectories)) <$> listDirectory dir
    else pure False

-- | Footer shown by @--help@, one entry per line.
footerLines :: [String]
footerLines =
  [ "Example: generate-conformance-tests --output-dir cases --num-files 100 --seed 42 --format both --match multiScalarMul"
  , "Output: DIR/{integer,bitwise,bls12_381}/MODULE/[GROUP/]PROPERTY/CASE/"
  , "Existing cases with the same names are overwritten; use --clean to remove old ones first."
  ]

{-| The footer as a document with hard line breaks, which 'footer' would
otherwise reflow as a single paragraph. -}
helpFooterDoc :: Doc
helpFooterDoc = mconcat (intersperse hardline (map pretty footerLines))

main :: IO ()
main = do
  opts <-
    execParser $
      info
        (options <**> helper)
        ( fullDesc
            <> progDesc "Generate UPLC conformance cases from the builtin properties"
            <> footerDoc (Just helpFooterDoc)
        )
  let include identifier =
        null (namePatterns opts)
          || any (`isInfixOf` propertyIdText identifier) (namePatterns opts)
  if listTests opts
    then mapM_ (putStrLn . propertyIdText) $ filter include $ concatMap fst allSuites
    else do
      let outputDir = outputDirectory opts
      checkOutputDirectory opts
      startedEmpty <- not <$> hasAnyEntries outputDir
      seedValue <- maybe randomIO pure (randomSeed opts)
      let seed = mkQCGen seedValue
      -- An info file from an earlier run would no longer describe this tree.
      removeInfo outputDir
      when (cleanOutput opts) $
        if null (namePatterns opts)
          then forM_ ownedDirectories $ \directory ->
            removePathForcibly (outputDir </> directory)
          else forM_ (filter include $ concatMap fst allSuites) $ \propertyId ->
            removePathForcibly (outputDir </> propertyIdPath propertyId)
      ( do
          reports <-
            concat
              <$> forM
                allSuites
                ( \(_, generate) ->
                    generate (outputFormat opts) (checkMode opts) include outputDir (numberOfFiles opts) seed
                )
          unrelated <- hasUnrelatedEntries outputDir
          -- The directory holds exactly this run's cases if nothing was filtered
          -- out, it was empty or cleaned beforehand, and nothing else is in it.
          let completeTree =
                null (namePatterns opts)
                  && (cleanOutput opts || startedEmpty)
                  && not unrelated
          infoPath <-
            writeInfo
              outputDir
              InfoDetails
                { infoTool = "generate-conformance-tests"
                , infoVersion = showVersion version
                , infoFormat = formatName (outputFormat opts)
                , infoNumFiles = numberOfFiles opts
                , infoSeed = seedValue
                , infoMatch = namePatterns opts
                , infoClean = cleanOutput opts
                , infoCheck = checkModeName (checkMode opts)
                , infoCompleteTree = completeTree
                }
              reports
          putStrLn ("Wrote " <> infoPath)
        )
        `catch` \(err :: SomeException) -> do
          hPutStrLn stderr ""
          hPutStrLn stderr "Generation failed: the generated test cases are incomplete."
          hPutStrLn
            stderr
            "Files written before the failure have been left in place, and no info.json was written."
          hPutStrLn stderr "Use --force (or --clean) to write into the same directory again."
          throwIO err
