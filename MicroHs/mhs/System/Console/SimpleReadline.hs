-- Copyright 2023 Lennart Augustsson
-- See LICENSE file for full license.
--
-- Simple readline with line editing and history.
-- Only assumes the terminal is capable of (sane) backspace.
module System.Console.SimpleReadline(
  getInputLine,
  getInputLineHist,
  getInputLineHistComp,
  ) where
import Control.Monad
import Data.Char
import MiniPrelude
import Prelude qualified ()
import System.IO

foreign import ccall "GETRAW" c_getRaw :: IO Int


-- Get an input line with editing.
-- Return Nothing if the input is ^D, otherwise the typed string.
getInputLine :: String -> IO (Maybe String)
getInputLine prompt = do
  (_, r) <- loop (\ _ -> return []) emptyHist "" ""
  return r

getInputLineHist :: FilePath -> String -> IO (Maybe String)
getInputLineHist = getInputLineHistComp (\ _ -> return [])

type CompleteFn = (String, String) -> IO [String]

-- Get an input line with editing.
-- Return Nothing if the input is ^D, otherwise the typed string.
-- The FilePath gives the name of a file that stores the history.
getInputLineHistComp :: CompleteFn -> FilePath -> String -> IO (Maybe String)
getInputLineHistComp comp hfn prompt = do
  mhdl <- openFileM hfn ReadMode
  hist <-
    case mhdl of
      Nothing -> return []
      Just hdl -> do
        file <- hGetContents hdl
        let h = lines file
        seq (length h) (return h)   -- force file to be read
  putStr prompt
  (hist', r) <- loop comp (fromLines hist) "" ""
--  putStrLn $ "done: " ++ hfn ++ "\n" ++ unlines hist'
  writeFile hfn $ unlines hist'
  return r   -- XXX no type error

getRaw :: IO Char
getRaw = do
  i <- c_getRaw
  when (i < 0) $
    error "getRaw failed"
  return (chr i)

-- The history.
-- before: the inputs before the current input
-- after: the inputs after the current input, including the current input (if non-empty)
-- original: the original input before using the history, if the history was already used
data Hist = Hist {- before -} [String] {- after -} [String] {- original -} (Maybe String)

emptyHist :: Hist
emptyHist = Hist [] [] Nothing

fromLines :: [String] -> Hist
fromLines hist = Hist (reverse hist) [] Nothing

toLines :: Hist -> [String]
toLines (Hist before after _) = reverse before ++ after

loop :: CompleteFn -> Hist -> String -> String -> IO ([String], Maybe String)
loop comp hist before after = do
  hFlush stdout
  i <- getRaw
  loop' comp hist before after i

loop' :: CompleteFn -> Hist -> String -> String -> Char -> IO ([String], Maybe String)
loop' comp hist before after cmd = do
  let
    cur = reverse before ++ after
    back n = putStr (replicate n '\b')
    bsSpBs n = concat $ replicate n "\b \b"

    ins c = do
      putChar c
      putStr after
      back (length after)
    add c = do
      ins c
      loop comp hist (c:before) after
    backward =
      case before of
        [] -> noop
        c:cs -> do
          back 1
          loop comp hist cs (c:after)
    forward =
      case after of
        [] -> noop
        c:cs -> do
          putChar c
          loop comp hist (c:before) cs
    bol = do
      back (length before)
      loop comp hist [] cur
    eol = do
      putStr after
      loop comp hist (reverse after ++ before) []
    bs = do
      case before of
        [] -> noop
        _:cs -> do
          back 1
          putStr after
          putChar ' '
          back (length after + 1)
          loop comp hist cs after
    del = do
      case after of
        [] -> noop
        _:cs -> do
          putStr cs
          putChar ' '
          back (length cs + 1)
          loop comp hist before cs
    send =
      ret (Just cur)
    ret ms = do
      putChar '\n'
      hFlush stdout
      let
        o = toLines hist
        l =
          case ms of
            Nothing -> []
            Just [] -> []
            Just s  | not (null o) && s == last o -> []
                    | otherwise -> [s]
        h = o ++ l
      return (h, ms)
    erase = do
      eraseLine
      loop comp hist [] []
    noop = loop comp hist before after
    kill = do
      putStr after
      putStr $ bsSpBs $ length after
      loop comp hist before []

    next =
      case hist of
        Hist _ [] Nothing      -> noop
        Hist p [] (Just orig)  -> setLine (Hist p [] Nothing) orig
        Hist _ [_] Nothing     -> noop
        Hist p [l] (Just orig) -> setLine (Hist (l:p) [] Nothing) orig
        Hist p (c:l:n) orig    -> setLine (Hist (c:p) (l:n) orig) l
    previous =
      case hist of
        Hist [] _ _           -> noop
        Hist (l:p) [] Nothing -> setLine (Hist p [l] (Just cur)) l
        Hist (l:p) n orig     -> setLine (Hist p (l:n) orig) l
    setLine h s = do
      eraseLine
      putStr s
      loop comp h (reverse s) ""

    eraseLine = do
      putStr after
      putStr $ bsSpBs $ length before + length after

    complete = do
      alts <- comp (before, after)
      case alts of
        []  -> loop comp hist before after
        [s] -> do mapM_ ins s; loop comp hist (reverse s ++ before) after
        ss  -> tabLoop ss

    tabLoop (s:ss) = do
      mapM_ ins s           -- show first alternative
      hFlush stdout
      c <- getRaw
      if c /= '\t' then
        loop' comp hist (reverse s ++ before) after c
       else do
        let n = length s
        back n                    -- back up this alternative
        putStr after              -- put back old text
        putStr $ replicate n ' '  -- erase extra
        back (n + length after)   -- put cursor back
        tabLoop (ss ++ [s])       -- try next alternative

    exec i =
      case i of
        '\^D' ->                     -- CTL-D, EOF
          if null before && null after then
            ret Nothing
          else
            del
        '\^B'  -> backward           -- CTL-B, backwards
        '\^F'  -> forward            -- CTL-F, forwards
        '\^A'  -> bol                -- CTL-A, beginning of line
        '\^E'  -> eol                -- CTL-E, end of line
        '\b'   -> bs                 -- BS, backspace
        '\DEL' -> bs                 -- DEL, backspace
        '\r'   -> send               -- CR, return
        '\n'   -> send               -- LF, return
        '\^N'  -> next               -- CTL-N, next line
        '\^P'  -> previous           -- CTL-P, previous line
        '\^U'  -> erase              -- CTL-U, erase line
        '\^K'  -> kill               -- CTL-K, kill to eol
        '\t'   -> complete           -- TAB, complete word
        '\ESC' -> do                 -- ESC
          b <- getRaw
          if b /= '[' then
            noop
           else do
            c <- getRaw
            case c of
              'A' -> previous
              'B' -> next
              'C' -> forward
              'D' -> backward
              _   -> noop
        _ -> if i >= ' ' && i < '\DEL' then add i else noop

  exec cmd
