-- A few function copied from the filepath package
module System.FilePath(
    FilePath,
--    splitSearchPath,
    pathSeparator,
--    takeExtension,
    dropExtension,
    (<.>),
    splitFileName,
    takeDirectory,
    (</>),
  ) where
import qualified Prelude(); import MHSPrelude
import Data.List

infixr 7 <.>
infixr 5 </>

(</>) :: FilePath -> FilePath -> FilePath
(</>) = combine

{-
hasLeadingPathSeparator :: FilePath -> Bool
hasLeadingPathSeparator ('/':_) = True
hasLeadingPathSeparator _ = False

hasTrailingPathSeparator :: FilePath -> Bool
hasTrailingPathSeparator = hasLeadingPathSeparator . reverse
-}

joinPath :: [FilePath] -> FilePath
joinPath = foldr combine ""

combine :: FilePath -> FilePath -> FilePath
combine a b {-x | hasLeadingPathSeparator b = b
            | otherwise -} = combineAlways a b

combineAlways :: FilePath -> FilePath -> FilePath
combineAlways a b {-x | null a = b
                  | null b = a
                  | hasTrailingPathSeparator a = a ++ b
                  | otherwise -} = a ++ pathSeparator : b

pathSeparator :: Char
pathSeparator = '/'

isPathSeparator :: Char -> Bool
isPathSeparator = (pathSeparator ==)

---------
{-
splitSearchPath :: String -> [FilePath]
splitSearchPath = f
  where
    f xs = case break (':' ==) xs of
             (pre, []    ) -> g pre
             (pre, _:post) -> g pre ++ f post

    g "" = ["."]
    g x = [x]
-}
---------

splitFileName :: FilePath -> (String, String)
splitFileName x = (if null dir then "./" else dir, name)
    where
        (dir, name) = splitFileName_ x

splitFileName_ :: FilePath -> (String, String)
splitFileName_ = breakEnd isPathSeparator

dropFileName :: FilePath -> FilePath
dropFileName = fst . splitFileName

{-
replaceBaseName :: FilePath -> String -> FilePath
replaceBaseName pth nam = combineAlways a (nam <.> ext)
    where
        (a,b) = splitFileName_ pth
        ext = takeExtension b
-}

takeDirectory :: FilePath -> FilePath
takeDirectory = dropTrailingPathSeparator . dropFileName

dropTrailingPathSeparator :: FilePath -> FilePath
dropTrailingPathSeparator = dropWhileEnd isPathSeparator

---------

extSeparator :: Char
extSeparator = '.'

isExtSeparator :: Char -> Bool
isExtSeparator = (extSeparator ==)

{-
splitExtension :: FilePath -> (String, String)
splitExtension x = case nameDot of
                       "" -> (x,"")
                       _  -> (dir ++ init nameDot, extSeparator : ext)
    where
        (dir, file) = splitFileName_ x
        (nameDot, ext) = breakEnd isExtSeparator file

takeExtension :: FilePath -> String
takeExtension = snd . splitExtension
-}

dropExtension :: FilePath -> FilePath
--dropExtension = fst . splitExtension
dropExtension = reverse . drop 1 . dropWhile (not . isExtSeparator) . reverse

(<.>) :: FilePath -> String -> FilePath
(<.>) = addExtension

addExtension :: FilePath -> String -> FilePath
addExtension file "" = file
addExtension file xs@(x:_) = res
    where
        res = if isExtSeparator x then file ++ xs
              else file ++ extSeparator : xs
