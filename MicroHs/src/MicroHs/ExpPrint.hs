module MicroHs.ExpPrint(toStringCMdl, toStringP, encodeString, combVersion) where
import qualified Prelude(); import MHSPrelude
import Data.Char(ord, chr)
import qualified MicroHs.IdentMap as M
import Data.Maybe
import MicroHs.Desugar(LDef)
import MicroHs.EncodeData(encList)
import MicroHs.Exp
import MicroHs.Expr(Lit(..), showLit, errorMessage, HasLoc(..))
import MicroHs.Ident(Ident, showIdent, mkIdent, showSLoc)
import MicroHs.List(groupSort)
import MicroHs.State
import MicroHs.TypeCheck(isInstId)

-- Version number of combinator file.
-- Must match version in eval.c.
combVersion :: String
combVersion = "v8.0\n"

-- Rename (to a numbers) top level definitions and remove unused ones.
-- Also check for duplicated instances.
toStringCMdl :: (Ident, [LDef]) -> (Int, String)
toStringCMdl (mainName, ds) =
  let
    dMap = M.fromList ds
    -- Shake the tree bottom-up, serializing nodes as we see them.
    -- This is much faster than (say) computing the sccs and walking that.
    dfs :: Ident -> State (Int, M.Map Exp, String -> String) ()
    dfs n = do
      (i, seen, r) <- get
      case M.lookup n seen of
        Just _ -> return ()
        Nothing -> do
          -- Put placeholder for n in seen.
          put (i, M.insert n (Var n) seen, r)
          -- Walk n's children
          let e = findIdentIn n dMap
          mapM_ dfs $ freeVars e
          -- Now that n's children are done, compute its actual entry.
          (i', seen', r') <- get
          put (i'+1, M.insert n (ref i') seen', def r' (i', e))
    (_,(ndefs, defs, res)) = runState (dfs mainName) (0, M.empty, toStringP emain)
    ref i = Var $ mkIdent $ "_" ++ show i
    findIdentIn n m = fromMaybe (errorMessage (getSLoc n) $ "No definition found for: " ++ showIdent n) $
                      M.lookup n m
    findIdent n = findIdentIn n defs
    emain = findIdent mainName
    substv aexp =
      case aexp of
        Var n -> findIdent n
        App f a -> App (substv f) (substv a)
        e -> e
    def :: (String -> String) -> (Int, Exp) -> (String -> String)
    def r (i, e) =
      ("A " ++) . toStringP (substv e) . ((":" ++ show i ++  " @\n") ++) . r . ("@" ++)
  in
    case dupInstances ds of
      (n1 : n2 : _) : _ -> errorMessage (getSLoc n1) $ "Duplicate instance " ++ unmangleInst (showIdent n1) ++ " at " ++ showSLoc (getSLoc n2)
      _ -> (ndefs, combVersion ++ show ndefs ++ "\n" ++ res " }")

dupInstances :: [LDef] -> [[Ident]]
dupInstances = filter ((> 1) . length) . groupSort . filter isInstId . map fst

-- XXX not nice
unmangleInst :: String -> String
unmangleInst = map (\ c -> if c == '@' then ' ' else c) . drop 5

-- Avoid quadratic concatenation by using difference lists,
-- turning concatenation into function composition.
toStringP :: Exp -> (String -> String)
toStringP ae =
  case ae of
    Var x   -> (showIdent x ++) . (' ' :)
    Lit (LStr s) ->
      -- Encode very short string directly as combinators.
      if length s > 1 then
        toStringP (App (Lit (LPrim "fromUTF8")) (Lit (LBStr (utf8encode s))))
      else
        toStringP (encodeString s)
    Lit (LBStr s) -> (quoteString s ++) . (' ' :)
    Lit (LInteger _) -> undefined
    Lit (LRat _) -> undefined
    Lit (LTick s) -> ('!':) . (quoteString s ++) . (' ' :)
    Lit l -> (showLit l ++) . (' ' :)
    Lam x e -> (("(\\" ++ showIdent x ++ " ") ++) . toStringP e . (")" ++)
    -- App f a -> ("(" ++) . toStringP f . (" " ++) . toStringP a . (")" ++)
    App f a -> toStringP f . toStringP a . ("@" ++)

-- Strings are encoded in a slightly unusal way.
-- It ensure that (most) printable ASCII only take
-- up 1 byte, and outside this range, only 2 bytes.
-- The input should be in the range 0x00-0xff.
-- '\x00'..'\x1f'  "^\x20".."^\x3f"
-- '\x20'..'\x7e'  '\x20'..'\x7e', except '^','\\','|','"'
-- '"'             "\\\""
-- '^'             "\^"
-- '|'             "\|"
-- '\\'            "\\\\"
-- '\x7f'          "\?"
-- '\x80'..'\x9f'  "^\x40".."^\x5f"
-- '\xa0'..'\xfe'  "|\x20".."|\x7e"
-- '\xff'          "\_'
quoteString :: String -> String
quoteString s =
  let
    achar c
      | c < '\0' || c > '\xff' = error "quoteString"
      | c < '\x20'             = ['^', chr (ord c + 0x20)]
      | c == '"' || c == '^' || c == '|' || c == '\\' = ['\\', c]
      | c < '\x7f'             = [c]
      | c == '\x7f'            = "\\?"
      | c < '\xa0'             = ['^', chr (ord c - 0x80 + 0x40)]
      | c < '\xff'             = ['|', chr (ord c - 0x80)]
      | otherwise              = "\\_"
  in  '"' : concatMap (\c -> achar (chr (ord c `rem` 256))) s ++ ['"']

encodeString :: String -> Exp
encodeString = encList . map (Lit . LInt . ord)

utf8encode :: String -> String
utf8encode = concatMap utf8Char

utf8Char :: Char -> [Char]
utf8Char c | c <= chr 0x7f = [c]
           | otherwise =
  let i = ord c
  in  if i < 0x800 then
        let (i1, i2) = quotRem i 0x40
        in  [chr (i1 + 0xc0), chr (i2 + 0x80)]
      else if i < 0x10000 then
        let (i12, i3) = quotRem i   0x40
            (i1,  i2) = quotRem i12 0x40
        in  [chr (i1 + 0xe0), chr (i2 + 0x80), chr (i3 + 0x80)]
      else if i < 0x110000 then
        let (i123, i4) = quotRem i    0x40
            (i12,  i3) = quotRem i123 0x40
            (i1,   i2) = quotRem i12  0x40
        in  [chr (i1 + 0xf0), chr (i2 + 0x80), chr (i3 + 0x80), chr (i4 + 0x80)]
      else
        error "utf8Char: bad Char"
