-- Copyright 2023 Lennart Augustsson
-- See LICENSE file for full license.
{-# OPTIONS_GHC -Wno-unused-imports #-}
module MicroHs.Translate(
  translate, translateAndRun
  ) where

import Data.ByteString.Internal (ByteString)
import Data.Maybe
import Data.String
import Debug.Trace
import MHSPrelude
import Prelude qualified ()
import PrimTable
import Unsafe.Coerce

import MicroHs.Desugar (LDef, encodeInteger)
import MicroHs.Exp
import MicroHs.ExpPrint (encodeString)
import MicroHs.Expr
import MicroHs.Ident
import MicroHs.IdentMap qualified as M

translateAndRun :: (Ident, [LDef]) -> IO ()
translateAndRun defs = trace "BBBBBBBBBB" $ do
  let prog = unsafeCoerce (translate defs)
  prog

translate :: (Ident, [LDef]) -> AnyType
translate (mainName, ds) = trace "AAAAAAAAAAAAAAAAAAAAABB" $
  let
    look n = fromMaybe (error $ "translate: not found " ++ showIdent n) $ M.lookup n mp
    mp = M.fromList [(n, trans look d) | (n, d) <- ds ]
  in look mainName

trans :: (Ident -> AnyType) -> Exp -> AnyType
trans r ae = trace "AAAAAAAAAAAAAA" $ trace (show ae) $
  case ae of
    Var n             -> r n
    App f a           -> unsafeCoerce (trans r f) (trans r a)
    Lit (LInt i)      -> unsafeCoerce i
    Lit (LDouble i)   -> unsafeCoerce i
    Lit (LStr s)      -> trans r (encodeString s)
    Lit (LBStr s)     -> unsafeCoerce (Data.String.fromString s :: ByteString)
    Lit (LPrim p)     -> fromMaybe (error $ "trans: no primop " ++ show p) $ lookup p primTable
    Lit (LInteger i)  -> trans r (encodeInteger i)
    Lit (LForImp s _) -> trans r (App (Lit (LPrim "dynsym")) (Lit (LStr s)))
    _                 -> error $ "trans: impossible: " ++ show ae

-- Use linear search in this table.
-- 99% of the hits are among the combinators.
primTable :: [(String, AnyType)]
primTable = [
  ("B", _primitive "B"),
  ("O", _primitive "O"),
  ("K", _primitive "K"),
  ("C'", _primitive "C'"),
  ("C", _primitive "C"),
  ("A", _primitive "A"),
  ("S'", _primitive "S'"),
  ("P", _primitive "P"),
  ("I", _primitive "I"),
  ("S", _primitive "S"),
  ("U", _primitive "U"),
  ("Y", _primitive "Y"),
  ("B'", _primitive "B'"),
  ("Z", _primitive "Z"),
--  ("J", _primitive "J"),
  ("R", _primitive "R"),
  ("K2", _primitive "K2"),
  ("K3", _primitive "K3"),
  ("K4", _primitive "K4"),
  ("C'B", _primitive "C'B"),
  ("+", _primitive "+"),
  ("-", _primitive "-"),
  ("*", _primitive "*"),
  ("quot", _primitive "quot"),
  ("rem", _primitive "rem"),
  ("uquot", _primitive "uquot"),
  ("urem", _primitive "urem"),
  ("neg", _primitive "neg"),
  ("and", _primitive "and"),
  ("or", _primitive "or"),
  ("xor", _primitive "xor"),
  ("inv", _primitive "inv"),
  ("shl", _primitive "shl"),
  ("shr", _primitive "shr"),
  ("ashr", _primitive "ashr"),
  ("subtract", _primitive "subtract"),
  ("popcount", _primitive "popcount"),
  ("clz", _primitive "clz"),
  ("ctz", _primitive "ctz"),
  ("==", _primitive "=="),
  ("/=", _primitive "/="),
  ("<", _primitive "<"),
  ("<=", _primitive "<="),
  (">", _primitive ">"),
  (">=", _primitive ">="),
  ("u<", _primitive "u<"),
  ("u<=", _primitive "u<="),
  ("u>", _primitive "u>"),
  ("u>=", _primitive "u>="),
  ("ord", _primitive "ord"),
  ("chr", _primitive "chr"),
  ("f+", _primitive "f+"),
  ("f-", _primitive "f-"),
  ("f*", _primitive "f*"),
  ("f/", _primitive "f/"),
  ("f==", _primitive "f=="),
  ("f/=", _primitive "f/="),
  ("f<", _primitive "f<"),
  ("f<=", _primitive "f<="),
  ("f>", _primitive "f>"),
  ("f>=", _primitive "f>="),
  ("fneg", _primitive "fneg"),
  ("fshow", _primitive "fshow"),
  ("fread", _primitive "fread"),
  ("itof", _primitive "itof"),
  ("seq", _primitive "seq"),
  ("sequal", _primitive "sequal"),
  ("equal", _primitive "equal"),
  ("scmp", _primitive "scmp"),
  ("icmp", _primitive "icmp"),
  ("ucmp", _primitive "ucmp"),
  ("rnf", _primitive "rnf"),
  ("IO.>>=", _primitive "IO.>>="),
  ("IO.>>", _primitive "IO.>>"),
  ("IO.return", _primitive "IO.return"),
  ("IO.print", _primitive "IO.print"),
  ("IO.serialize", _primitive "IO.serialize"),
  ("IO.deserialize", _primitive "IO.deserialize"),
  ("IO.stdin", _primitive "IO.stdin"),
  ("IO.stdout", _primitive "IO.stdout"),
  ("IO.stderr", _primitive "IO.stderr"),
  ("IO.getArgRef", _primitive "IO.getArgRef"),
  ("IO.performIO", _primitive "IO.performIO"),
  ("IO.gc", _primitive "IO.gc"),
  ("IO.stats", _primitive "IO.stats"),
  ("raise", _primitive "raise"),
  ("catch", _primitive "catch"),
  ("dynsym", _primitive "dynsym"),
  ("newCAStringLen", _primitive "newCAStringLen"),
  ("packCString", _primitive "packCString"),
  ("packCStringLen", _primitive "packCStringLen"),
  ("toInt", _primitive "toInt"),
  ("toPtr", _primitive "toPtr"),
  ("toDbl", _primitive "toDbl"),
  ("toFunPtr", _primitive "toFunPtr"),
  ("A.alloc", _primitive "A.alloc"),
  ("A.copy", _primitive "A.copy"),
  ("A.size", _primitive "A.size"),
  ("A.read", _primitive "A.read"),
  ("A.write", _primitive "A.write"),
  ("A.==", _primitive "A.=="),
  ("bs++", _primitive "bs++"),
  ("bs++.", _primitive "bs++."),
  ("bs==", _primitive "bs=="),
  ("bs/=", _primitive "bs/="),
  ("bs<", _primitive "bs<"),
  ("bs<=", _primitive "bs<="),
  ("bs>", _primitive "bs>"),
  ("bs>=", _primitive "bs>="),
  ("bscmp", _primitive "bscmp"),
  ("bspack", _primitive "bspack"),
  ("bsunpack", _primitive "bsunpack"),
  ("bsreplicate", _primitive "bsreplicate"),
  ("bslength", _primitive "bslength"),
  ("bssubstr", _primitive "bssubstr"),
  ("bsindex", _primitive "bsindex"),
  ("fromUTF8", _primitive "fromUTF8"),
  ("toUTF8", _primitive "toUTF8"),
  ("headUTF8", _primitive "headUTF8"),
  ("tailUTF8", _primitive "tailUTF8"),
  ("fp+", _primitive "fp+"),
  ("fp2p", _primitive "fp2p"),
  ("fpnew", _primitive "fpnew"),
  ("fpfin", _primitive "fpfin"),
  ("fp2bs", _primitive "fp2bs"),
  ("bs2fp", _primitive "bs2fp"),
  ("IO.fork", _primitive "IO.fork"),
  ("IO.thid", _primitive "IO.thid"),
  ("thnum", _primitive "thnum"),
  ("IO.throwto", _primitive "IO.throwto"),
  ("IO.yield", _primitive "IO.yield"),
  ("IO.newmvar", _primitive "IO.newmvar"),
  ("IO.takemvar", _primitive "IO.takemvar"),
  ("IO.putmvar", _primitive "IO.putmvar"),
  ("IO.readmvar", _primitive "IO.readmvar"),
  ("IO.trytakemvar", _primitive "IO.trytakemvar"),
  ("IO.tryputmvar", _primitive "IO.tryputmvar"),
  ("IO.tryreadmvar", _primitive "IO.tryreadmvar"),
  ("IO.threaddelay", _primitive "IO.threaddelay"),
  ("IO.threadstatus", _primitive "IO.threadstatus"),
  ("isint", _primitive "isint")
  ]
