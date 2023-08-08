\begin{code}
module Main where
open import Agda.Builtin.IO using (IO)
import IO.Primitive as IO using (return;_>>=_)
open import Agda.Builtin.Unit using (⊤;tt)
open import Function using (_$_;_∘_)
open import Data.String using (String;_++_)
open import Agda.Builtin.Nat
open import Agda.Builtin.Int using (pos)
open import Data.Integer.Show using (show)
open import Data.Product using (Σ) renaming (_,_ to _,,_)
open import Data.Bool using (Bool)
open import Data.Vec using (Vec;[];_∷_)
open import Data.List using (List)
open import Data.Empty using (⊥)

open import Type using (Ctx⋆;∅;_,⋆_)
open import Check using (TypeError;inferType;inferKind;meqKind;checkKind;checkType)
open TypeError -- Bring all TypeError constructors in scope.

open import Scoped.Extrication using (extricateNf⋆;extricate)
open import Type.BetaNormal using (_⊢Nf⋆_)
import Untyped as U using (Untyped;_⊢;scopeCheckU0;extricateU0;decUTm)

open import Untyped.CEK as U using (stepper;Stack;ε;Env;[];State)
open U.State

open import Raw using (RawTm;RawTy;rawPrinter;rawTyPrinter;decRTy;decRTm)
open import Scoped using (FreeVariableError;ScopeError;freeVariableError;extricateScopeTy;ScopedTm;Weirdℕ;scopeCheckTm;shifter;unshifter;extricateScope;unshifterTy;scopeCheckTy;shifterTy)
open Weirdℕ -- Bring Weirdℕ constructors in scope
open import Utils using (Either;inj₁;inj₂;withE;Kind;*;Maybe;nothing;just;Monad;RuntimeError)
open RuntimeError
open Monad {{...}}

open import Algorithmic using (_⊢_;∅;error)

open import Algorithmic.CK using (stepper;State;Stack;ε)
open Algorithmic.CK.State

open import Algorithmic.CEK using (stepper;State;Stack;ε;Env;[])
open Algorithmic.CEK.State

open import Algorithmic.Erasure using (erase)
import Algorithmic.Evaluation as L using(stepper)



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

-- Parsing stuff

postulate
  FilePath : Set

{-# COMPILE GHC FilePath = type FilePath #-}

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

-- Input Options stuff
{-# FOREIGN GHC import PlutusCore.Executable.Common  #-}
{-# FOREIGN GHC import PlutusCore.Executable.Parsers #-}
{-# FOREIGN GHC import Opts #-}

postulate
   Format : Set
   Input : Set

{-# COMPILE GHC Format = type Format #-}
{-# COMPILE GHC Input = type Input #-}

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
  parse : Format → Input → IO ProgramN
  parseTm : String → Either ParseError TermN
  parseTy : String → Either ParseError TypeN
  showTerm : RawTm → String
  deBruijnify : ProgramN → Either FreeVariableError Program
  deBruijnifyTm : TermN → Either FreeVariableError Term
  deBruijnifyTy : TypeN → Either FreeVariableError Type

  ProgramNU : Set
  ProgramU : Set
  TermNU : Set
  TermU : Set
  deBruijnifyU : ProgramNU → Either FreeVariableError ProgramU
  deBruijnifyTmU : TermNU → Either FreeVariableError TermU
  parseU : Format → Input → IO ProgramNU
  parseTmU : String → Either ParseError TermNU
  convPU : ProgramU → U.Untyped
  convTmU : TermU → U.Untyped
  unconvTmU : U.Untyped → TermU


{-# FOREIGN GHC import PlutusCore.Name #-}
{-# FOREIGN GHC import PlutusCore.Parser #-}
{-# FOREIGN GHC import PlutusCore.Pretty #-}
{-# FOREIGN GHC import PlutusCore.DeBruijn #-}
{-# FOREIGN GHC import PlutusCore.Error #-}
{-# FOREIGN GHC import PlutusCore.Quote #-}
{-# FOREIGN GHC import qualified UntypedPlutusCore as U #-}
{-# FOREIGN GHC import qualified UntypedPlutusCore.Parser as U #-}

{-# FOREIGN GHC import Raw #-}
{-# COMPILE GHC convP = convP #-}
{-# COMPILE GHC convPU = U.convP #-}
{-# COMPILE GHC convTm = conv #-}
{-# COMPILE GHC convTy = convT #-}
{-# COMPILE GHC unconvTy = unconvT 0 #-}
{-# COMPILE GHC unconvTm = unconv 0 #-}
{-# FOREIGN GHC import Data.Bifunctor #-}
{-# FOREIGN GHC import Data.Functor #-}
{-# COMPILE GHC ParseError = type PlutusCore.Error.ParserErrorBundle #-}

{-# COMPILE GHC parse = getProgram #-}
{-# COMPILE GHC parseU = getProgram #-}
{-# COMPILE GHC parseTm = runQuoteT . parseTerm #-}
{-# COMPILE GHC parseTy = runQuoteT . parseType #-}
{-# COMPILE GHC parseTmU = runQuoteT . U.parseTerm #-}
{-# COMPILE GHC deBruijnify = \ (Program ann ver tm) -> second (void . Program ann ver) . runExcept $ deBruijnTerm tm #-}
{-# COMPILE GHC deBruijnifyTm = second void . runExcept . deBruijnTerm #-}
{-# COMPILE GHC deBruijnifyTy = second void . runExcept . deBruijnTy #-}
{-# FOREIGN GHC import PlutusCore #-}
{-# COMPILE GHC ProgramN = type PlutusCore.Program TyName Name DefaultUni DefaultFun PlutusCore.SrcSpan #-}
{-# COMPILE GHC Program = type PlutusCore.Program NamedTyDeBruijn NamedDeBruijn DefaultUni DefaultFun () #-}
{-# COMPILE GHC TermN = type PlutusCore.Term TyName Name DefaultUni DefaultFun PlutusCore.SrcSpan #-}
{-# COMPILE GHC Term = type PlutusCore.Term NamedTyDeBruijn NamedDeBruijn DefaultUni DefaultFun () #-}
{-# COMPILE GHC TypeN = type PlutusCore.Type TyName DefaultUni PlutusCore.SrcSpan #-}
{-# COMPILE GHC Type = type PlutusCore.Type NamedTyDeBruijn DefaultUni () #-}
{-# COMPILE GHC showTerm = T.pack . show #-}

{-# COMPILE GHC ProgramNU = type U.Program Name DefaultUni DefaultFun PlutusCore.SrcSpan #-}
{-# COMPILE GHC ProgramU = type U.Program NamedDeBruijn DefaultUni DefaultFun () #-}
{-# COMPILE GHC TermNU = type U.Term Name DefaultUni DefaultFun PlutusCore.SrcSpan #-}
{-# COMPILE GHC TermU = type U.Term NamedDeBruijn DefaultUni DefaultFun () #-}
{-# COMPILE GHC deBruijnifyU = \ (U.Program ann ver tm) -> second (void . U.Program ann ver) . runExcept $ U.deBruijnTerm tm #-}
{-# COMPILE GHC deBruijnifyTmU = second void . runExcept . U.deBruijnTerm #-}
{-# COMPILE GHC convTmU = U.conv #-}
{-# COMPILE GHC unconvTmU = U.uconv 0 #-}

postulate
  prettyPrintTm : RawTm → String
  prettyPrintTy : RawTy → String

  prettyPrintUTm : U.Untyped → String

{-# FOREIGN GHC {-# LANGUAGE TypeApplications #-} #-}
{-# COMPILE GHC prettyPrintTm = display @T.Text . unconv 0 #-}
{-# COMPILE GHC prettyPrintTy = display @T.Text . unconvT 0 #-}

{-# FOREIGN GHC import qualified Untyped as U #-}
{-# COMPILE GHC prettyPrintUTm = display @T.Text . U.uconv 0 #-}


data EvalMode : Set where
  U TL TCK TCEK : EvalMode

{-# COMPILE GHC EvalMode = data EvalMode (U | TL | TCK | TCEK) #-}

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

{-# COMPILE GHC ERROR = data ERROR (TypeError | ParseError | ScopeError | RuntimeError) #-}

parsePLC : ProgramN → Either ERROR (ScopedTm Z)
parsePLC namedprog = do
  prog ← withE (ERROR.scopeError ∘ freeVariableError) $ deBruijnify namedprog
  withE scopeError $ scopeCheckTm {0}{Z} (shifter Z (convP prog))
  -- ^ FIXME: this should have an interface that guarantees that the
  -- shifter is run

parseUPLC : ProgramNU → Either ERROR (⊥ U.⊢)
parseUPLC namedprog = do
  prog ← withE (ERROR.scopeError ∘ freeVariableError) $ deBruijnifyU namedprog
  withE scopeError $ U.scopeCheckU0 (convPU prog)

typeCheckPLC : ScopedTm Z → Either TypeError (Σ (∅ ⊢Nf⋆ *) (∅ ⊢_))
typeCheckPLC t = inferType _ t


maxsteps = 10000000000

reportError : ERROR → String
reportError (parseError _) = "parseError"
reportError (typeError s) = "typeError: " ++ s
reportError (scopeError _) = "scopeError"
reportError (runtimeError gasError)         = "gasError"
reportError (runtimeError userError)        = "userError"
reportError (runtimeError runtimeTypeError) = "runtimeTypeError"


{- check if the term is an error term, and in that case
  return an ERROR.
  This is used when evaluation of the reduction semantics has ended
-}
checkError : ∀{A} → ∅ ⊢ A → Either ERROR (∅ ⊢ A )
checkError (error _) = inj₁ (runtimeError userError)
checkError t         = return t

executePLC : EvalMode → ScopedTm Z → Either ERROR String
executePLC U t = do
  (A ,, t) ← withE (λ e → typeError (uglyTypeError e)) $ typeCheckPLC t
  □ V ← withE runtimeError $ U.stepper maxsteps (ε ; [] ▻ erase t)
    where ◆  → inj₁ (runtimeError userError)
          _    → inj₁ (runtimeError gasError)
{-
just t' ← withE runtimeError $ U.stepper maxsteps (ε ; [] ▻ erase t)
    where nothing → inj₁ (runtimeError userError)
    -}
  return $ prettyPrintUTm (U.extricateU0 (U.discharge V))
executePLC TL t = do
  (A ,, t) ← withE (λ e → typeError (uglyTypeError e)) $ typeCheckPLC t
  t' ← (withE runtimeError $ L.stepper t maxsteps) >>= checkError
  return (prettyPrintTm (unshifter Z (extricateScope (extricate t'))))
executePLC TCK t = do
  (A ,, t) ← withE (λ e → typeError (uglyTypeError e)) $ typeCheckPLC t
  □ {t = t} v ← withE runtimeError $ Algorithmic.CK.stepper maxsteps (ε ▻ t)
    where ◆ _  → inj₁ (runtimeError userError)
          _    → inj₁ (runtimeError gasError)
  return (prettyPrintTm (unshifter Z (extricateScope (extricate t))))
executePLC TCEK t = do
  (A ,, t) ← withE (λ e → typeError (uglyTypeError e)) $ typeCheckPLC t
  □ V ← withE runtimeError $ Algorithmic.CEK.stepper maxsteps (ε ; [] ▻ t)
    where ◆ _  → inj₁ (runtimeError userError)
          _    → inj₁ (runtimeError gasError)
  return (prettyPrintTm (unshifter Z (extricateScope (extricate (Algorithmic.CEK.discharge V)))))

executeUPLC : ⊥ U.⊢ → Either ERROR String
executeUPLC t = do
  □ V ← withE runtimeError $ U.stepper maxsteps (ε ; [] ▻ t)
    where ◆  → inj₁ (runtimeError userError)
          _    → inj₁ (runtimeError gasError)
  return $ prettyPrintUTm (U.extricateU0 (U.discharge V))

evalProgramNU : ProgramNU → Either ERROR String
evalProgramNU namedprog = do
  t ← parseUPLC namedprog
  executeUPLC t

evalProgramN : EvalMode → ProgramN → Either ERROR String
evalProgramN m namedprog = do
{-
  -- some debugging code
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
  t ← parsePLC namedprog
  executePLC m t

typeCheckProgramN : ProgramN → Either ERROR String
typeCheckProgramN namedprog = do
  t ← parsePLC namedprog
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

blah : String → String → String
blah plc1 plc2 with parseTm plc1 | parseTm plc2
blah plc1 plc2 | inj₂ plc1' | inj₂ plc2' with deBruijnifyTm plc1' | deBruijnifyTm plc2'
blah plc1 plc2 | inj₂ plc1' | inj₂ plc2' | inj₂ plc1'' | inj₂ plc2'' = rawPrinter (convTm plc1'') ++ " || " ++ rawPrinter (convTm plc2'')
blah plc1 plc2 | inj₂ plc1' | inj₂ plc2' | _ | _ = "deBruijnifying failed"
blah plc1 plc2 | _ | _ = "parsing failed"

{-# COMPILE GHC blah as blah #-}

printTy : String → String
printTy b with parseTy b
... | inj₁ _ = "parseTy error"
... | inj₂ A  with deBruijnifyTy A
... | inj₁ _ = "deBruinjifyTy error"
... | inj₂ A' = rawTyPrinter (convTy A')

{-# COMPILE GHC printTy as printTy #-}

alphaTy : String → String → Bool
alphaTy plc1 plc2 with parseTy plc1 | parseTy plc2
alphaTy plc1 plc2 | inj₂ plc1' | inj₂ plc2' with deBruijnifyTy plc1' | deBruijnifyTy plc2'
alphaTy plc1 plc2 | inj₂ plc1' | inj₂ plc2' | inj₂ plc1'' | inj₂ plc2'' = decRTy (convTy plc1'') (convTy plc2'')
alphaTy plc1 plc2 | inj₂ plc1' | inj₂ plc2' | _ | _ = Bool.false
alphaTy plc1 plc2 | _ | _ = Bool.false

{-# COMPILE GHC alphaTy as alphaTy #-}

alphaTm : String → String → Bool
alphaTm plc1 plc2 with parseTm plc1 | parseTm plc2
alphaTm plc1 plc2 | inj₂ plc1' | inj₂ plc2' with deBruijnifyTm plc1' | deBruijnifyTm plc2'
alphaTm plc1 plc2 | inj₂ plc1' | inj₂ plc2' | inj₂ plc1'' | inj₂ plc2'' = decRTm (convTm plc1'') (convTm plc2'')
alphaTm plc1 plc2 | inj₂ plc1' | inj₂ plc2' | _ | _ = Bool.false
alphaTm plc1 plc2 | _ | _ = Bool.false

{-# COMPILE GHC alphaTm as alphaTm #-}

alphaU : String → String → Bool
alphaU plc1 plc2 with parseTmU plc1 | parseTmU plc2
alphaU plc1 plc2 | inj₂ plc1' | inj₂ plc2' with deBruijnifyTmU plc1' | deBruijnifyTmU plc2'
alphaU plc1 plc2 | inj₂ plc1' | inj₂ plc2' | inj₂ plc1'' | inj₂ plc2'' = U.decUTm (convTmU plc1'') (convTmU plc2'')
alphaU plc1 plc2 | inj₂ plc1' | inj₂ plc2' | _ | _ = Bool.false
alphaU plc1 plc2 | _ | _ = Bool.false

{-# COMPILE GHC alphaU as alphaU #-}

-- More Opt Stuff

data EvalOptions : Set where
  EvalOpts : Input → Format → EvalMode → EvalOptions

{-# COMPILE GHC EvalOptions = data EvalOptions (EvalOpts) #-}

data TypecheckOptions : Set where
  TCOpts : Input → Format → TypecheckOptions

{-# COMPILE GHC TypecheckOptions = data TypecheckOptions (TCOpts) #-}

data Command : Set where
  Eval  : EvalOptions → Command
  Typecheck : TypecheckOptions → Command

{-# COMPILE GHC Command = data Command (Eval | Typecheck) #-}

postulate execP : IO Command

{-# COMPILE GHC execP = execP #-}

evalInput : EvalMode → Format → Input → IO (Either ERROR String)
evalInput U fmt inp = fmap evalProgramNU (parseU fmt inp)
evalInput m fmt inp = fmap (evalProgramN m) (parse fmt inp)

tcInput : Format → Input → IO (Either ERROR String)
tcInput fmt inp = fmap typeCheckProgramN (parse fmt inp)

main' : Command → IO ⊤
main' (Eval (EvalOpts inp fmt m)) = do
  inj₂ s ← evalInput m fmt inp
    where
    inj₁ e → putStrLn (reportError e) >> exitFailure
  putStrLn s >> exitSuccess
main' (Typecheck (TCOpts inp fmt))    = do
  inj₂ s ← tcInput fmt inp
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
  _         ← withE ((λ e → ERROR.typeError (uglyTypeError e)) ∘ kindMismatch _ _) (meqKind k k')
  return tt

{-# COMPILE GHC checkKindX as checkKindAgda #-}


-- a Haskell interface to kind inference:

inferKind∅ : Type → Either ERROR Kind
inferKind∅ ty = do
  ty       ← withE scopeError (scopeCheckTy (shifterTy Z (convTy ty)))
  (k ,, _) ← withE (λ e → typeError (uglyTypeError e)) (inferKind ∅ ty)
  return k

{-# COMPILE GHC inferKind∅ as inferKindAgda #-}

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

runTL : Term → Either ERROR Term
runTL t = do
  tDB ← withE scopeError (scopeCheckTm {0}{Z} (shifter Z (convTm t)))
  _ ,, tC ← withE (λ e → typeError (uglyTypeError e)) (inferType ∅ tDB)
  t ← withE runtimeError $ L.stepper tC maxsteps
  return (unconvTm (unshifter Z (extricateScope (extricate t))))

{-# COMPILE GHC runTL as runTLAgda #-}

-- note the interfaces to evaluation below catch userErrors and replace them with error terms

-- Haskell interface to (typechecked) CK
runTCK : Term → Either ERROR Term
runTCK t = do
  tDB ← withE scopeError (scopeCheckTm {0}{Z} (shifter Z (convTm t)))
  ty ,, tC ← withE (λ e → typeError (uglyTypeError e)) (inferType ∅ tDB)
  □ V ← withE runtimeError $ Algorithmic.CK.stepper maxsteps (ε ▻ tC)
    where (_ ▻ _) → inj₁ (runtimeError gasError)
          (_ ◅ _) → inj₁ (runtimeError gasError)
          ◆ A → return (unconvTm (unshifter Z (extricateScope {0}{Z} (extricate (error ty)))))
  return (unconvTm (unshifter Z (extricateScope (extricate (Algorithmic.CK.discharge V)))))

{-# COMPILE GHC runTCK as runTCKAgda #-}

-- Haskell interface to (typechecked) CEK
runTCEK : Term → Either ERROR Term
runTCEK t = do
  tDB ← withE scopeError (scopeCheckTm {0}{Z} (shifter Z (convTm t)))
  ty ,, tC ← withE (λ e → typeError (uglyTypeError e)) (inferType ∅ tDB)
  □ V ← withE runtimeError $ Algorithmic.CEK.stepper maxsteps (ε ; [] ▻ tC)
    where (_ ; _ ▻ _) → inj₁ (runtimeError gasError)
          (_ ◅ _) → inj₁ (runtimeError gasError)
          ◆ A → return (unconvTm (unshifter Z (extricateScope {0}{Z} (extricate (error ty)))))
  return (unconvTm (unshifter Z (extricateScope (extricate (Algorithmic.CEK.discharge V)))))

{-# COMPILE GHC runTCEK as runTCEKAgda #-}

postulate showU : TermU -> String

{-# COMPILE GHC showU = T.pack . show #-}

-- Note that according to the specification ◆ should reduce to an error term,
-- but here the untyped PLC term evaluator
-- matches the behaviour of the Haskell implementation:
-- an error is thrown with ◆.
runU : TermU → Either ERROR TermU
runU t = do
  tDB ← withE scopeError $ U.scopeCheckU0 (convTmU t)
  □ V ← withE runtimeError $ U.stepper maxsteps (ε ; [] ▻ tDB)
    where
    ◆ → inj₁ (runtimeError userError) -- ◆ returns a `userError` runtimeError.
    _ → inj₁ (runtimeError gasError)
  return (unconvTmU (U.extricateU0 (U.discharge V)))

{-# COMPILE GHC runU as runUAgda #-}
\end{code}
