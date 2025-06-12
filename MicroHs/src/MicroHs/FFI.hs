module MicroHs.FFI(makeFFI) where
import Data.Function
import Data.List
import MHSPrelude
import MicroHs.Desugar (LDef)
import MicroHs.Exp
import MicroHs.Expr
import MicroHs.Flags
import MicroHs.Ident
import MicroHs.Names
import Prelude qualified ()

makeFFI :: Flags -> [LDef] -> String
makeFFI _ ds =
  let ffiImports = [ (parseImpEnt i f, t) | (i, d) <- ds, Lit (LForImp f (CType t)) <- [get d] ]
                 where get (App _ a) = a   -- if there is no IO type, we have (App primPerform (LForImp ...))
                       get a         = a
      wrappers = [ t | (ImpWrapper, t) <- ffiImports]
      dynamics = [ t | (ImpDynamic, t) <- ffiImports]
      imps     = uniqName $ filter ((`notElem` runtimeFFI) . impName) ffiImports
      includes = "mhsffi.h" : nub [ inc | (ImpStatic _ (Just inc) _ _, _) <- imps ]
  in
    if not (null wrappers) || not (null dynamics) then error "Unimplemented FFI feature" else
    unlines $
      map (\ fn -> "#include \"" ++ fn ++ "\"") includes ++
      map mkHdr imps ++
      ["static struct ffi_entry table[] = {"] ++
      map mkEntry imps ++
      ["{ 0,0 }",
       "};",
       "struct ffi_entry *xffi_table = table;"
      ]

uniqName :: [(ImpEnt, EType)] -> [(ImpEnt, EType)]
uniqName = map head . groupBy ((==) `on` impName) . sortBy (compare `on` impName)

data ImpEnt = ImpStatic Ident (Maybe String) Imp String | ImpDynamic | ImpWrapper
--  deriving (Show)

impName :: (ImpEnt, EType) -> String
impName (ImpStatic i _ Value _, _) = unIdent' i
impName (ImpStatic _ _ _ s, _)     = s
impName _                          = undefined

data Imp = Ptr | Value | Func
--  deriving (Show)

-- "[static] [name.h] [&] [name]"
-- "dynamic"
-- "wrapper"
parseImpEnt :: Ident -> String -> ImpEnt
parseImpEnt i s =
  case words s of
    ["dynamic"]  -> ImpDynamic
    ["wrapper"]  -> ImpWrapper
    "static" : r -> rest r
    r            -> rest r
 where rest (inc : r) | ".h" `isSuffixOf` inc = rest' (ImpStatic i (Just inc)) r
       rest r                                 = rest' (ImpStatic i Nothing)    r
       rest' c ("&"     : r) = rest'' (c Ptr) r
       rest' c ['&'     : r] = rest'' (c Ptr) [r]
       rest' c ("value" : r) = rest'' (c Value) [unwords r]
       rest' c r             = rest'' (c Func) r
       rest'' c [n] = c n
       rest'' _ _   = errorMessage loc $ "bad foreign import " ++ show s
       loc = getSLoc i

mkEntry :: (ImpEnt, EType) -> String
mkEntry (ImpStatic _ _ Func  f, t) = "{ \"" ++ f ++ "\", " ++ show (arity t) ++ ", mhs_" ++ f ++ "},"
mkEntry (ImpStatic _ _ Ptr   f, _) = "{ \"&" ++ f ++ "\", 0, mhs_addr_" ++ f ++ "},"
mkEntry (ImpStatic i _ Value _, _) = "{ \"" ++ f ++ "\", 0, mhs_" ++ f ++ "}," where f = unIdent' i
mkEntry _ = undefined

mkMhsFun :: String -> String -> String
mkMhsFun fn body = "from_t mhs_" ++ fn ++ "(int s) { " ++ body ++ "; }"

checkIO :: EType -> EType
checkIO iot =
  case dropApp identIO iot of
    Nothing -> iot -- errorMessage (getSLoc iot) $ "foreign return type must be IO: " ++ showEType iot
    Just t  -> t

dropApp :: Ident -> EType -> Maybe EType
dropApp i (EApp (EVar i') t) | i == i' = Just t
dropApp _ _ = Nothing

isUnit :: EType -> Bool
isUnit (EVar unit) = unit == identUnit
isUnit _           = False

mkRet :: EType -> Int -> String -> String
mkRet t n call = "mhs_from_" ++ cTypeName t ++ "(s, " ++ show n ++ ", " ++ call ++ ")"

mkArg :: EType -> Int -> String
mkArg t i = "mhs_to_" ++ cTypeName t ++ "(s, " ++ show i ++ ")"

mkHdr :: (ImpEnt, EType) -> String
mkHdr (ImpStatic _ _ Ptr fn, iot) =
  let r = checkIO iot
      (s, _) =
        case dropApp identPtr r of
          Just t  -> ("", t)
          Nothing ->
            case dropApp identFunPtr r of
              Just t  -> ("(HsFunPtr)", t)
              Nothing -> errorMessage (getSLoc r) "foreign & must be Ptr/FunPtr"
      body = mkRet r 0 (s ++ "&" ++ fn)
  in  mkMhsFun ("addr_" ++ fn) body
mkHdr (ImpStatic _ _ Func fn, t) =
  let (as, ior) = getArrows t
      r = checkIO ior
      n = length as
      call = fn ++ "(" ++ intercalate ", " (zipWith mkArg as [0..]) ++ ")"
      fcall =
        if isUnit r then
          call ++ "; return mhs_from_Unit(s, " ++ show n ++ ")"
        else
          "return " ++ mkRet r n call
  in  mkMhsFun fn fcall
mkHdr (ImpStatic i _ Value val, iot) =
  let r = checkIO iot
      body = mkRet r 0 val
  in  mkMhsFun (unIdent' i) body
mkHdr _ = undefined

arity :: EType -> Int
arity = length . fst . getArrows

unIdent' :: Ident -> String
unIdent' = unIdent . unQualIdent

cTypeName :: EType -> String
cTypeName (EApp (EVar ptr) _t) | ptr == identPtr = "Ptr"
                               | ptr == identFunPtr = "FunPtr"
cTypeName (EVar i) | Just c <- lookup (unIdent i) cTypes = c
cTypeName t = errorMessage (getSLoc t) $ "Not a valid C type: " ++ showEType t

cTypes :: [(String, String)]
cTypes =
  -- These are temporary
  [ ("Primitives.FloatW", "FloatW")
  , ("Primitives.Int",    "Int")
  , ("Primitives.Word",   "Word")
  , ("Data.Word.Word8",   "Word8")
  , ("()",                "Unit")
  , ("System.IO.Handle",  "Ptr")
  ] ++ map (\ t -> ("Foreign.C.Types." ++ t, t))
  [ "CChar",
    "CSChar",
    "CUChar",
    "CShort",
    "CUShort",
    "CInt",
    "CUInt",
    "CLong",
    "CULong",
    "CPtrdiff",
    "CSize",
    "CSSize",
    "CLLong",
    "CULLong",
    "CTime"
  ]

-- These are already in the runtime
runtimeFFI :: [String]
runtimeFFI = [
  "GETRAW", "GETTIMEMILLI", "acos", "add_FILE", "add_utf8", "asin", "atan", "atan2", "calloc", "closeb",
  "cos", "exp", "flushb", "fopen", "free", "getb", "getenv", "iswindows", "log", "malloc",
  "md5Array", "md5BFILE", "md5String", "memcpy", "memmove",
  "putb", "sin", "sqrt", "system", "tan", "tmpname", "ungetb", "unlink",
  "readb", "writeb",
  "peekPtr", "pokePtr", "pokeWord", "peekWord",
  "add_lz77_compressor", "add_lz77_decompressor",
  "add_rle_compressor", "add_rle_decompressor",
  "add_bwt_compressor", "add_bwt_decompressor",
  "peek_uint8", "poke_uint8", "peek_uint16", "poke_uint16", "peek_uint32", "poke_uint32", "peek_uint64", "poke_uint64",
  "peek_int8", "poke_int8", "peek_int16", "poke_int16", "peek_int32", "poke_int32", "peek_int64", "poke_int64",
  "peek_ushort", "poke_ushort", "peek_short", "poke_short",
  "peek_uint", "poke_uint", "peek_int", "poke_int",
  "peek_ulong", "poke_ulong", "peek_long", "poke_long",
  "peek_ullong", "poke_ullong", "peek_llong", "poke_llong",
  "peek_size_t", "poke_size_t",
  "peek_flt", "poke_flt",
  "sizeof_int", "sizeof_long", "sizeof_llong", "sizeof_size_t",
  "opendir", "closedir", "readdir", "c_d_name", "chdir", "mkdir", "getcwd",
  "getcpu",
  "get_buf", "openb_rd_buf", "openb_wr_buf",
  "new_mpz", "mpz_abs", "mpz_add", "mpz_and", "mpz_cmp", "mpz_get_d",
  "mpz_get_si", "mpz_get_ui", "mpz_init_set_si", "mpz_init_set_ui", "mpz_ior",
  "mpz_mul", "mpz_mul_2exp", "mpz_neg", "mpz_popcount", "mpz_sub", "mpz_fdiv_q_2exp",
  "mpz_tdiv_qr", "mpz_tstbit", "mpz_xor",
  "want_gmp"
  ]
