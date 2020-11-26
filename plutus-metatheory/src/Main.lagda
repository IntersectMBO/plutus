\begin{code}
module Main where
open import Agda.Builtin.IO
import IO.Primitive as IO using (return;_>>=_)
open import Agda.Builtin.Unit
open import Agda.Builtin.String
open import Function
open import Data.Sum
open import Data.String
open import Agda.Builtin.TrustMe
open import Relation.Binary.PropositionalEquality
open import Agda.Builtin.Nat
open import Data.Nat
open import Agda.Builtin.Int
open import Data.Integer
open import Data.Product renaming (_,_ to _,,_)
open import Data.Bool
open import Data.Fin
open import Data.Vec hiding (_>>=_;_++_)
open import Data.List hiding (_++_)

open import Type
open import Builtin
open import Builtin.Constant.Type hiding (ByteString)
open import Builtin.Constant.Term Ctx⋆ Kind * _⊢⋆_ con
open import Builtin.Signature
open import Check
open import Scoped.Extrication
open import Type.BetaNBE
open import Type.BetaNormal
open import Untyped as U
import Untyped.Reduction as U
import Scoped as S
import Scoped.Reduction as S
open import Raw
open import Scoped
open import Utils
open import Untyped
open import Scoped.CK
open import Algorithmic
open import Algorithmic.Reduction
open import Algorithmic.CK
open import Algorithmic.CEKV
open import Scoped.Erasure


-- There's a long prelude here that could go in a different file but
-- currently it's only used here

-- Text Stuff

postulate
  putStrLn : String → IO ⊤

{-# FOREIGN GHC import qualified Data.Text as T #-}
{-# FOREIGN GHC import qualified Data.Text.IO as TextIO #-}
{-# COMPILE GHC putStrLn = TextIO.putStrLn #-}

-- IO Stuff

instance
  IOMonad : Monad IO
  IOMonad = record { return = IO.return; _>>=_ = IO._>>=_ }

-- Bytestring stuff

postulate
  ByteString : Set
  getContents : IO ByteString
  readFile : String → IO ByteString

{-# FOREIGN GHC import qualified Data.ByteString.Lazy as BSL #-}
{-# COMPILE GHC ByteString = type BSL.ByteString #-}
{-# COMPILE GHC readFile = \ s -> BSL.readFile (T.unpack s) #-}
{-# COMPILE GHC getContents = BSL.getContents #-}

-- System.Exit stuff

postulate
  exitFailure : IO ⊤
  exitSuccess : IO ⊤

{-# FOREIGN GHC import System.Exit #-}
{-# COMPILE GHC exitSuccess = exitSuccess #-}
{-# COMPILE GHC exitFailure = exitFailure #-}

-- System.Environment stuff

postulate
  getArgs : IO (List String)

{-# FOREIGN GHC import System.Environment #-}
{-# COMPILE GHC getArgs = (fmap . fmap) T.pack $ getArgs #-}

-- Misc stuff

{-# FOREIGN GHC import Data.Either #-}
{-# FOREIGN GHC import Control.Monad.Trans.Except #-}

postulate
  TermN : Set -- term with names
  Term : Set  -- DeBruijn term
  TypeN : Set
  Type : Set
  ProgramN : Set
  Program : Set
  convTm : Term → RawTm
  convTy : Type → RawTy
  unconvTy : RawTy → Type
  unconvTm : RawTm → Term
  convP : Program → RawTm
  ParseError : Set
  parse : ByteString → Either ParseError ProgramN
  parseTm : ByteString → Either ParseError TermN
  parseTy : ByteString → Either ParseError TypeN
  showTerm : RawTm → String
  deBruijnify : ProgramN → Either FreeVariableError Program
  deBruijnifyTm : TermN → Maybe Term
  deBruijnifyTy : TypeN → Maybe Type

{-# FOREIGN GHC import Language.PlutusCore.Name #-}
{-# FOREIGN GHC import Language.PlutusCore.Lexer #-}
{-# FOREIGN GHC import Language.PlutusCore.Parser #-}
{-# FOREIGN GHC import Language.PlutusCore.Pretty #-}
{-# FOREIGN GHC import Language.PlutusCore.DeBruijn #-}
{-# FOREIGN GHC import Raw #-}
{-# COMPILE GHC convP = convP #-}
{-# COMPILE GHC convTm = conv #-}
{-# COMPILE GHC convTy = convT #-}
{-# COMPILE GHC unconvTy = unconvT 0 #-}
{-# COMPILE GHC unconvTm = unconv 0 #-}
{-# FOREIGN GHC import Data.Bifunctor #-}

{-# COMPILE GHC ParseError = type ParseError () #-}
{-# COMPILE GHC parse = first (() <$) . runQuote . runExceptT . parseProgram  #-}
{-# COMPILE GHC parseTm = first (() <$) . runQuote. runExceptT . parseTerm  #-}
{-# COMPILE GHC parseTy = first (() <$) . runQuote . runExceptT . parseType  #-}
{-# COMPILE GHC deBruijnify = second (() <$) . runExcept . deBruijnProgram #-}
{-# COMPILE GHC deBruijnifyTm = either (\_ -> Nothing) Just . runExcept . deBruijnTerm . (() <$) #-}
{-# COMPILE GHC deBruijnifyTy = either (\_ -> Nothing) Just . runExcept . deBruijnTy . (() <$) #-}
{-# FOREIGN GHC import Language.PlutusCore #-}
{-# COMPILE GHC ProgramN = type Language.PlutusCore.Program TyName Name DefaultUni DefaultFun Language.PlutusCore.Lexer.AlexPosn #-}
{-# COMPILE GHC Program = type Language.PlutusCore.Program NamedTyDeBruijn NamedDeBruijn DefaultUni DefaultFun () #-}
{-# COMPILE GHC TermN = type Language.PlutusCore.Term TyName Name DefaultUni DefaultFun Language.PlutusCore.Lexer.AlexPosn #-}
{-# COMPILE GHC Term = type Language.PlutusCore.Term NamedTyDeBruijn NamedDeBruijn DefaultUni DefaultFun () #-}
{-# COMPILE GHC TypeN = type Language.PlutusCore.Type TyName DefaultUni Language.PlutusCore.Lexer.AlexPosn #-}
{-# COMPILE GHC Type = type Language.PlutusCore.Type NamedTyDeBruijn DefaultUni () #-}

{-# COMPILE GHC showTerm = T.pack . show #-}

postulate
  prettyPrintTm : RawTm → String
  prettyPrintTy : RawTy → String

{-# FOREIGN GHC {-# LANGUAGE TypeApplications #-} #-}
{-# COMPILE GHC prettyPrintTm = display @T.Text . unconv 0 #-}
{-# COMPILE GHC prettyPrintTy = display @T.Text . unconvT 0 #-}

data EvalMode : Set where
  U TL L TCK CK TCEK : EvalMode

{-# COMPILE GHC EvalMode = data EvalMode (U | TL | L | TCK | CK | TCEK) #-}

-- the Error's returned by `plc-agda` and the haskell interface to `metatheory`.

data ERROR : Set where
  typeError : String → ERROR
  parseError : ParseError → ERROR
  scopeError : ScopeError → ERROR
  runtimeError : RuntimeError → ERROR


uglyTypeError : TypeError → String
uglyTypeError (kindMismatch K K' x) = "kindMismatch"
uglyTypeError (notStar K x) = "notStar"
uglyTypeError (notFunKind K x) = "NotFunKind"
uglyTypeError (notPat K x) = "notPat"
uglyTypeError UnknownType = "UnknownType"
uglyTypeError (notPi A x) = "notPi"
uglyTypeError (notMu A x) = "notMu"
uglyTypeError (notFunType A x) = "notFunType"
uglyTypeError (typeMismatch A A' x) =
  prettyPrintTy (extricateScopeTy (extricateNf⋆ A))
  ++
  " doesn't match "
  ++
  prettyPrintTy (extricateScopeTy (extricateNf⋆ A'))
uglyTypeError builtinError = "builtinError"

-- the haskell version of Error is defined in Raw
{-# FOREIGN GHC import Raw #-}

{-# COMPILE GHC ERROR = data ERROR (TypeError | ParseError | ScopeError | RuntimeError) #-}


parsePLC : ByteString → Either ERROR (ScopedTm Z)
parsePLC plc = do
  namedprog ← withE parseError $ parse plc
  prog ← withE (ERROR.scopeError ∘ freeVariableError) $ deBruijnify namedprog
  withE scopeError $ scopeCheckTm {0}{Z} (shifter Z (convP prog))
  -- ^ FIXME: this should have an interface that guarantees that the
  -- shifter is run


typeCheckPLC : ScopedTm Z → Either TypeError (Σ (∅ ⊢Nf⋆ *) (∅ ⊢_))
typeCheckPLC t = inferType _ t


maxsteps = 10000000000

open import Data.String

reportError : ERROR → String
reportError (parseError _) = "parseError"
reportError (typeError s) = "typeError: " ++ s
reportError (scopeError _) = "scopeError"
reportError (runtimeError _) = "gasError"


executePLC : EvalMode → ScopedTm Z → Either ERROR String
executePLC U t = inj₁ (runtimeError gasError)
executePLC TL t = do
  (A ,, t) ← withE (λ e → typeError (uglyTypeError e)) $ typeCheckPLC t
  just t' ← withE runtimeError $ Algorithmic.Reduction.progressor maxsteps t
    where nothing → inj₂ "ERROR"
  return (prettyPrintTm (unshifter Z (extricateScope (extricate t'))))

executePLC L t with S.run t maxsteps
... | t' ,, p ,, inj₁ (just v) = inj₂ (prettyPrintTm (unshifter Z (extricateScope t')))
... | t' ,, p ,, inj₁ nothing  = inj₁ (runtimeError gasError)
... | t' ,, p ,, inj₂ e        = inj₂ "ERROR"
executePLC CK t = do
  □ {t = t} v ← withE runtimeError $ Scoped.CK.stepper maxsteps (ε ▻ t)
    where ◆  → inj₂ "ERROR"
          _  → inj₁ (runtimeError gasError)
  return (prettyPrintTm (unshifter Z (extricateScope t)))
executePLC TCK t = do
  (A ,, t) ← withE (λ e → typeError (uglyTypeError e)) $ typeCheckPLC t
  □ {t = t} v ← withE runtimeError $ Algorithmic.CK.stepper maxsteps (ε ▻ t)
    where ◆ _  → inj₂ "ERROR"
          _    → inj₁ (runtimeError gasError)
  return (prettyPrintTm (unshifter Z (extricateScope (extricate t))))
executePLC TCEKV t = do
  (A ,, t) ← withE (λ e → typeError (uglyTypeError e)) $ typeCheckPLC t
  □ V ← withE runtimeError $ Algorithmic.CEKV.stepper maxsteps (ε ; [] ▻ t)
    where ◆ _  → inj₂ "ERROR"
          _    → inj₁ (runtimeError gasError)
  return (prettyPrintTm (unshifter Z (extricateScope (extricate (Algorithmic.CEKV.discharge V)))))

evalByteString : EvalMode → ByteString → Either ERROR String
evalByteString m b = do
{-
  -- some debugging code
  namedprog ← withE parseError $ parse b
  prog ← withE (ERROR.scopeError ∘ freeVariableError) $ deBruijnify namedprog
  let shiftedprog = shifter Z (convP prog)
  scopedprog ← withE scopeError $ scopeCheckTm {0}{Z} shiftedprog
  let extricatedprog = extricateScope scopedprog
  let unshiftedprog = unshifter Z extricatedprog
  return ("orginal: " ++ rawPrinter (convP prog) ++ "\n" ++
          "shifted: " ++ rawPrinter shiftedprog ++ "\n" ++
          "instrinsically scoped: " ++ Scoped.ugly scopedprog ++ "\n" ++
          "extricated: " ++ rawPrinter extricatedprog ++ "\n" ++
          "unshifted: " ++ rawPrinter unshiftedprog ++ "\n" ++
          "unconved: " ++ prettyPrintTm unshiftedprog ++ "\n")
-}
  t ← parsePLC b
  executePLC m t

typeCheckByteString : ByteString → Either ERROR String
typeCheckByteString b = do
  t ← parsePLC b
  (A ,, _) ← withE (λ e → typeError (uglyTypeError e) ) $ typeCheckPLC t
{-
  -- some debugging code
  let extricatedtype = extricateScopeTy (extricateNf⋆ A)
  let unshiftedtype = unshifterTy Z extricatedtype
  return ("original: " ++ "???" ++ "\n" ++
          "extricated: " ++ rawTyPrinter extricatedtype ++ "\n" ++
          "unshifted: " ++ rawTyPrinter unshiftedtype ++ "\n" ++
          "unconved: " ++ prettyPrintTy unshiftedtype ++ "\n")
-}
  return (prettyPrintTy (unshifterTy Z (extricateScopeTy (extricateNf⋆ A))))

junk : ∀{n} → Vec String n
junk {zero}      = []
junk {Nat.suc n} = Data.Integer.show (pos n) ∷ junk

alphaTm : ByteString → ByteString → Bool
alphaTm plc1 plc2 with parseTm plc1 | parseTm plc2
alphaTm plc1 plc2 | inj₂ plc1' | inj₂ plc2' with deBruijnifyTm plc1' | deBruijnifyTm plc2'
alphaTm plc1 plc2 | inj₂ plc1' | inj₂ plc2' | just plc1'' | just plc2'' = decRTm (convTm plc1'') (convTm plc2'')
alphaTm plc1 plc2 | inj₂ plc1' | inj₂ plc2' | _ | _ = Bool.false
alphaTm plc1 plc2 | _ | _ = Bool.false

{-# COMPILE GHC alphaTm as alphaTm #-}

blah : ByteString → ByteString → String
blah plc1 plc2 with parseTm plc1 | parseTm plc2
blah plc1 plc2 | inj₂ plc1' | inj₂ plc2' with deBruijnifyTm plc1' | deBruijnifyTm plc2'
blah plc1 plc2 | inj₂ plc1' | inj₂ plc2' | just plc1'' | just plc2'' = rawPrinter (convTm plc1'') ++ " || " ++ rawPrinter (convTm plc2'')
blah plc1 plc2 | inj₂ plc1' | inj₂ plc2' | _ | _ = "deBruijnifying failed"
blah plc1 plc2 | _ | _ = "parsing failed"

{-# COMPILE GHC blah as blah #-}

printTy : ByteString → String
printTy b with parseTy b
... | inj₁ _ = "parseTy error"
... | inj₂ A  with deBruijnifyTy A
... | nothing = "deBruinjifyTy error"
... | just A' = rawTyPrinter (convTy A')

{-# COMPILE GHC printTy as printTy #-}

alphaTy : ByteString → ByteString → Bool
alphaTy plc1 plc2 with parseTy plc1 | parseTy plc2
alphaTy plc1 plc2 | inj₂ plc1' | inj₂ plc2' with deBruijnifyTy plc1' | deBruijnifyTy plc2'
alphaTy plc1 plc2 | inj₂ plc1' | inj₂ plc2' | just plc1'' | just plc2'' = decRTy (convTy plc1'') (convTy plc2'')
alphaTy plc1 plc2 | inj₂ plc1' | inj₂ plc2' | _ | _ = Bool.false
alphaTy plc1 plc2 | _ | _ = Bool.false

{-# COMPILE GHC alphaTy as alphaTy #-}

-- Opt stuff

{-# FOREIGN GHC import Opts #-}

data Input : Set where
  FileInput : String → Input
  StdInput : Input

{-# COMPILE GHC Input = data Input (FileInput | StdInput) #-}

data EvalOptions : Set where
  EvalOpts : Input → EvalMode → EvalOptions

{-# COMPILE GHC EvalOptions = data EvalOptions (EvalOpts) #-}

data TCOptions : Set where
  TCOpts : Input → TCOptions

{-# COMPILE GHC TCOptions = data TCOptions (TCOpts) #-}

data Command : Set where
  Evaluate  : EvalOptions → Command
  TypeCheck : TCOptions → Command

{-# COMPILE GHC Command = data Command (Evaluate | TypeCheck) #-}

postulate execP : IO Command

{-# COMPILE GHC execP = execP #-}

evalInput : EvalMode → Input → IO (Either ERROR String)
evalInput m (FileInput fn) = fmap (evalByteString m) (readFile fn)
evalInput m StdInput       = fmap (evalByteString m) getContents

tcInput : Input → IO (Either ERROR String)
tcInput (FileInput fn) = fmap typeCheckByteString (readFile fn)
tcInput StdInput       = fmap typeCheckByteString getContents


main' : Command → IO ⊤
main' (Evaluate (EvalOpts i m)) = do
  inj₂ s ← evalInput m i
    where
    inj₁ e → putStrLn (reportError e) >> exitFailure
  putStrLn s >> exitSuccess
main' (TypeCheck (TCOpts i))    = do
  inj₂ s ← tcInput i
    where
    inj₁ e → putStrLn (reportError e) >> exitFailure
  putStrLn s >> exitSuccess

main : IO ⊤
main = execP >>= main'

liftSum : {A : Set} → Either ERROR A → Maybe A
liftSum (inj₂ a) = just a
liftSum (inj₁ e) = nothing


-- a Haskell interface to the kindchecker:
checkKindX : Type → Kind → Either ERROR ⊤
checkKindX ty k = do
  ty        ← withE scopeError (scopeCheckTy (shifterTy Z (convTy ty)))
  (k' ,, _) ← withE (λ e → typeError (uglyTypeError e)) (inferKind ∅ ty)
  _         ← withE ((λ e → typeError (uglyTypeError e)) ∘ kindMismatch _ _) (meqKind k k')
  return tt

{-# COMPILE GHC checkKindX as checkKindAgda #-}


-- a Haskell interface to kind inference:

inferKind∅ : Type → Either ERROR Kind
inferKind∅ ty = do
  ty       ← withE scopeError (scopeCheckTy (shifterTy Z (convTy ty)))
  (k ,, _) ← withE (λ e → typeError (uglyTypeError e)) (inferKind ∅ ty)
  return k

{-# COMPILE GHC inferKind∅ as inferKindAgda #-}

open import Type.BetaNormal

-- a Haskell interface to the type normalizer:
normalizeType : Type → Either ERROR Type
normalizeType ty = do
  ty'    ← withE scopeError (scopeCheckTy (shifterTy Z (convTy ty)))
  _ ,, n ← withE (λ e → typeError (uglyTypeError e)) (inferKind ∅ ty')
  return (unconvTy (unshifterTy Z (extricateScopeTy (extricateNf⋆ n))))

{-# COMPILE GHC normalizeType as normalizeTypeAgda #-}

-- Haskell interface to type checker:
inferType∅ : Term → Either ERROR Type
inferType∅ t = do
  t' ← withE scopeError (scopeCheckTm {0}{Z} (shifter Z (convTm t)))
  ty ,, _ ← withE (λ e → typeError (uglyTypeError e)) (inferType ∅ t')
  return (unconvTy (unshifterTy Z (extricateScopeTy (extricateNf⋆ ty))))

{-# COMPILE GHC inferType∅ as inferTypeAgda #-}


-- FIXME: we have a checkType function now...
checkType∅ : Type → Term → Either ERROR ⊤
checkType∅ ty t = do
  ty' ← withE scopeError (scopeCheckTy (shifterTy Z (convTy ty)))
  tyN ← withE (λ e → typeError (uglyTypeError e)) (checkKind ∅ ty' *)
  t'  ← withE scopeError (scopeCheckTm {0}{Z} (shifter Z (convTm t)))
  withE (λ e → typeError (uglyTypeError e)) (checkType ∅ t' tyN)
{-
  tyN' ,, tmC ← withE (λ e → typeError (uglyTypeError e)) (inferType ∅ t')
  refl      ← withE ((λ e → typeError (uglyTypeError e)) ∘ kindMismatch _ _) (meqKind k *)
  refl      ← withE ((λ e → typeError (uglyTypeError e)) ∘ typeMismatch _ _) (meqNfTy tyN tyN')
-}
  return _

-- Haskell interface to type normalizer (for terms)
-- the type checker/inferer could also return such a term
normalizeTypeTerm : Term → Either ERROR Term
normalizeTypeTerm t = do
  tDB ← withE scopeError (scopeCheckTm {0}{Z} (shifter Z (convTm t)))
  _ ,, tC ← withE (λ e → typeError (uglyTypeError e)) (inferType ∅ tDB)
  return (unconvTm (unshifter Z (extricateScope (extricate tC))))

{-# COMPILE GHC normalizeTypeTerm as normalizeTypeTermAgda #-}


{-# COMPILE GHC checkType∅ as checkTypeAgda #-}

-- Haskell interface to (typechecked and proven correct) reduction

import Algorithmic.Evaluation as L

runL : Term → Either ERROR Term
runL t = do
  tDB ← withE scopeError (scopeCheckTm {0}{Z} (shifter Z (convTm t)))
  _ ,, tC ← withE (λ e → typeError (uglyTypeError e)) (inferType ∅ tDB)
  t ← withE runtimeError $ L.stepper tC maxsteps
  return (unconvTm (unshifter Z (extricateScope (extricate t))))

{-# COMPILE GHC runL as runLAgda #-}

-- Haskell interface to (untypechecked CK)
runCK : Term → Either ERROR Term
runCK t = do
  tDB ← withE scopeError $ scopeCheckTm {0}{Z} (shifter Z (convTm t))
  □ V ← withE runtimeError $ Scoped.CK.stepper maxsteps (ε ▻ tDB)
    where (_ ▻ _) → inj₁ (runtimeError gasError)
          (_ ◅ _) → inj₁ (runtimeError gasError)
          ◆ → return (unconvTm (unshifter Z (extricateScope {0}{Z} (error missing)))) -- NOTE: we could use the typechecker to get the correct type
  return (unconvTm (unshifter Z (extricateScope (Scoped.CK.discharge V))))

{-# COMPILE GHC runCK as runCKAgda #-}

-- Haskell interface to (typechecked) CK
runTCK : Term → Either ERROR Term
runTCK t = do
  tDB ← withE scopeError (scopeCheckTm {0}{Z} (shifter Z (convTm t)))
  _ ,, tC ← withE (λ e → typeError (uglyTypeError e)) (inferType ∅ tDB)
  □ V ← withE runtimeError $ Algorithmic.CK.stepper maxsteps (ε ▻ tC)
    where (_ ▻ _) → inj₁ (runtimeError gasError)
          (_ ◅ _) → inj₁ (runtimeError gasError)
          ◆ A → return (unconvTm (unshifter Z (extricateScope {0}{Z} (error missing)))) -- NOTE: we could use the typechecker to get the correct type
  return (unconvTm (unshifter Z (extricateScope (extricate (Algorithmic.CK.discharge V)))))

{-# COMPILE GHC runTCK as runTCKAgda #-}

-- Haskell interface to (typechecked) CEKV
runTCEKV : Term → Either ERROR Term
runTCEKV t = do
  tDB ← withE scopeError (scopeCheckTm {0}{Z} (shifter Z (convTm t)))
  _ ,, tC ← withE (λ e → typeError (uglyTypeError e)) (inferType ∅ tDB)
  □ V ← withE runtimeError $ Algorithmic.CEKV.stepper maxsteps (ε ; [] ▻ tC)
    where (_ ; _ ▻ _) → inj₁ (runtimeError gasError)
          (_ ◅ _) → inj₁ (runtimeError gasError)
          ◆ A → return (unconvTm (unshifter Z (extricateScope {0}{Z} (error missing)))) -- NOTE: we could use the typechecker to get the correct type
  return (unconvTm (unshifter Z (extricateScope (extricate (Algorithmic.CEKV.discharge V)))))

{-# COMPILE GHC runTCEKV as runTCEKVAgda #-}
\end{code}
