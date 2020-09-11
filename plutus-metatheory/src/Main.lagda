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
open import Builtin.Constant.Type
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
open import Algorithmic.CK
open import Algorithmic.CEKC
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
  getContents : IO ByteString
  readFile : String → IO ByteString

{-# FOREIGN GHC import qualified Data.ByteString.Lazy as BSL #-}
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
  TermN : Set
  Term : Set
  TypeN : Set
  Type : Set
  ProgramN : Set
  Program : Set
  convTm : Term → RawTm
  convTy : Type → RawTy
  unconvTy : RawTy → Type
  unconvTm : RawTm → Term
  convP : Program → RawTm
  parse : ByteString → Either Error ProgramN
  parseTm : ByteString → Maybe TermN
  parseTy : ByteString → Maybe TypeN
  showTerm : RawTm → String
  deBruijnify : ProgramN → Either Error Program
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
{-# COMPILE GHC unconvTy = \ ty -> AlexPn 0 0 0 <$ (unconvT 0 ty) #-}
{-# COMPILE GHC unconvTm = \ tm -> AlexPn 0 0 0 <$ (unconv 0 tm) #-}
{-# FOREIGN GHC import Data.Bifunctor #-}
{-# COMPILE GHC parse = first (const ParseError) . parse  #-}
{-# COMPILE GHC parseTm = either (\_ -> Nothing) Just . parseTm  #-}
{-# COMPILE GHC parseTy = either (\_ -> Nothing) Just . parseTy  #-}
{-# COMPILE GHC deBruijnify = first (const ScopeError) . runExcept . deBruijnProgram #-}
{-# COMPILE GHC deBruijnifyTm = either (\_ -> Nothing) Just . runExcept . deBruijnTerm #-}
{-# COMPILE GHC deBruijnifyTy = either (\_ -> Nothing) Just . runExcept . deBruijnTy #-}
{-# FOREIGN GHC import Language.PlutusCore #-}
{-# COMPILE GHC ProgramN = type Language.PlutusCore.Program TyName Name DefaultUni Language.PlutusCore.Lexer.AlexPosn #-}
{-# COMPILE GHC Program = type Language.PlutusCore.Program TyDeBruijn DeBruijn DefaultUni Language.PlutusCore.Lexer.AlexPosn #-}
{-# COMPILE GHC TermN = type Language.PlutusCore.Term TyName Name DefaultUni Language.PlutusCore.Lexer.AlexPosn #-}
{-# COMPILE GHC Term = type Language.PlutusCore.Term TyDeBruijn DeBruijn DefaultUni Language.PlutusCore.Lexer.AlexPosn #-}
{-# COMPILE GHC TypeN = type Language.PlutusCore.Type TyName DefaultUni Language.PlutusCore.Lexer.AlexPosn #-}
{-# COMPILE GHC Type = type Language.PlutusCore.Type TyDeBruijn DefaultUni Language.PlutusCore.Lexer.AlexPosn #-}
{-# COMPILE GHC showTerm = T.pack . show #-}

postulate
  prettyPrintTm : RawTm → String
  prettyPrintTy : RawTy → String

{-# FOREIGN GHC {-# LANGUAGE TypeApplications #-} #-}
{-# COMPILE GHC prettyPrintTm = display @T.Text . unconv 0 #-}
{-# COMPILE GHC prettyPrintTy = display @T.Text . unconvT 0 #-}

data EvalMode : Set where
  U L TCK CK TCEKC TCEKV : EvalMode

{-# COMPILE GHC EvalMode = data EvalMode (U | L | TCK | CK | TCEKC | TCEKV) #-}

parsePLC : ByteString → Either Error (ScopedTm Z)
parsePLC plc = do
  namedprog ← parse plc
  prog ← deBruijnify namedprog
  scopeCheckTm {0}{Z} (shifter Z (convP prog))
  -- ^ TODO: this should have an interface that guarantees that the
  -- shifter is run

typeCheckPLC : ScopedTm Z → Either Error (Σ (∅ ⊢Nf⋆ *) (∅ ⊢_))
typeCheckPLC t = inferType _ t

maxsteps = 10000000000

executePLC : EvalMode → ScopedTm Z → Either Error String
executePLC U t = inj₁ gasError
executePLC L t with S.run t maxsteps
... | t' ,, p ,, inj₁ (just v) = inj₂ (prettyPrintTm (unshifter Z (extricateScope t')))
... | t' ,, p ,, inj₁ nothing  = inj₁ gasError
... | t' ,, p ,, inj₂ e        = inj₂ "ERROR"
executePLC CK t = do
  □ {t = t} v ← Scoped.CK.stepper maxsteps (ε ▻ t)
    where ◆  → inj₂ "ERROR"
          _  → inj₁ gasError
  return (prettyPrintTm (unshifter Z (extricateScope t)))
executePLC TCK t = do
  (A ,, t) ← typeCheckPLC t
  □ {t = t} v ← Algorithmic.CK.stepper maxsteps (ε ▻ t)
    where ◆ _  → inj₂ "ERROR"
          _    → inj₁ gasError
  return (prettyPrintTm (unshifter Z (extricateScope (extricate t))))
executePLC TCEKC t = do
  (A ,, t) ← typeCheckPLC t
  □ (_ ,, _ ,, V ,, ρ) ← Algorithmic.CEKC.stepper maxsteps (ε ; [] ▻ t)
    where ◆ _  → inj₂ "ERROR"
          _    → inj₁ gasError
  return (prettyPrintTm (unshifter Z (extricateScope (extricate (proj₁ (Algorithmic.CEKC.discharge V ρ))))))
executePLC TCEKV t = do
  (A ,, t) ← typeCheckPLC t
  □ V ← Algorithmic.CEKV.stepper maxsteps (ε ; [] ▻ t)
    where ◆ _  → inj₂ "ERROR"
          _    → inj₁ gasError
  return (prettyPrintTm (unshifter Z (extricateScope (extricate (Algorithmic.CEKV.discharge V)))))

evalByteString : EvalMode → ByteString → Either Error String
evalByteString m b = do
{-
namedprog ← parse b
  prog ← deBruijnify namedprog
  let shiftedprog = shifter Z (convP prog)
  scopedprog ← scopeCheckTm {0}{Z} shiftedprog
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

typeCheckByteString : ByteString → Either Error String
typeCheckByteString b = do
  t ← parsePLC b
  (A ,, _) ← typeCheckPLC t
{-  
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
alphaTm plc1 plc2 | just plc1' | just plc2' with deBruijnifyTm plc1' | deBruijnifyTm plc2'
alphaTm plc1 plc2 | just plc1' | just plc2' | just plc1'' | just plc2'' = decRTm (convTm plc1'') (convTm plc2'')
alphaTm plc1 plc2 | just plc1' | just plc2' | _ | _ = Bool.false
alphaTm plc1 plc2 | _ | _ = Bool.false

{-# COMPILE GHC alphaTm as alphaTm #-}

blah : ByteString → ByteString → String
blah plc1 plc2 with parseTm plc1 | parseTm plc2
blah plc1 plc2 | just plc1' | just plc2' with deBruijnifyTm plc1' | deBruijnifyTm plc2'
blah plc1 plc2 | just plc1' | just plc2' | just plc1'' | just plc2'' = rawPrinter (convTm plc1'') ++ " || " ++ rawPrinter (convTm plc2'')
blah plc1 plc2 | just plc1' | just plc2' | _ | _ = "deBruijnifying failed"
blah plc1 plc2 | _ | _ = "parsing failed"

{-# COMPILE GHC blah as blah #-}

printTy : ByteString → String
printTy b with parseTy b
... | nothing = "parseTy error"
... | just A  with deBruijnifyTy A
... | nothing = "deBruinjifyTy error"
... | just A' = rawTyPrinter (convTy A')

{-# COMPILE GHC printTy as printTy #-}

alphaTy : ByteString → ByteString → Bool
alphaTy plc1 plc2 with parseTy plc1 | parseTy plc2
alphaTy plc1 plc2 | just plc1' | just plc2' with deBruijnifyTy plc1' | deBruijnifyTy plc2'
alphaTy plc1 plc2 | just plc1' | just plc2' | just plc1'' | just plc2'' = decRTy (convTy plc1'') (convTy plc2'')
alphaTy plc1 plc2 | just plc1' | just plc2' | _ | _ = Bool.false
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

evalInput : EvalMode → Input → IO (Either Error String)
evalInput m (FileInput fn) = fmap (evalByteString m) (readFile fn)
evalInput m StdInput       = fmap (evalByteString m) getContents

tcInput : Input → IO (Either Error String)
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

liftSum : {A : Set} → Either Error A → Maybe A
liftSum (inj₂ a) = just a
liftSum (inj₁ e) = nothing

-- a Haskell interface to the kindchecker:
checkKind : Type → Kind → Maybe ⊤
checkKind ty k = do
  ty        ← liftSum (scopeCheckTy (shifterTy Z (convTy ty)))
  (k' ,, _) ← liftSum (inferKind ∅ ty)
  _         ← liftSum (meqKind k k')
  return tt

{-# COMPILE GHC checkKind as checkKindAgda #-}


-- a Haskell interface to kind inference:
inferKind∅ : Type → Maybe Kind
inferKind∅ ty = do
  ty       ← liftSum (scopeCheckTy (shifterTy Z (convTy ty)))
  (k ,, _) ← liftSum (inferKind ∅ ty)
  return k

{-# COMPILE GHC inferKind∅ as inferKindAgda #-}

open import Type.BetaNormal

-- a Haskell interface to the type normalizer:
normalizeType : Type → Maybe Type
normalizeType ty = do
  ty'    ← liftSum (scopeCheckTy (shifterTy Z (convTy ty)))
  _ ,, n ← liftSum (inferKind ∅ ty')
  return (unconvTy (unshifterTy Z (extricateScopeTy (extricateNf⋆ n))))

{-# COMPILE GHC normalizeType as normalizeTypeAgda #-}

-- Haskell interface to type checker:
inferType∅ : Term → Maybe Type
inferType∅ t = do
  t' ← liftSum (scopeCheckTm {0}{Z} (shifter Z (convTm t)))
  ty ,, _ ← liftSum (inferType ∅ t')
  return (unconvTy (unshifterTy Z (extricateScopeTy (extricateNf⋆ ty))))

{-# COMPILE GHC inferType∅ as inferTypeAgda #-}

checkType : Type → Term → Maybe ⊤
checkType ty t = do
  ty'       ← liftSum (scopeCheckTy (shifterTy Z (convTy ty)))
  k ,, tyN  ← liftSum (inferKind ∅ ty')
  t'        ← liftSum (scopeCheckTm {0}{Z} (shifter Z (convTm t)))
  tyN' ,, tmC ← liftSum (inferType ∅ t')
  refl      ← liftSum (meqKind k *)
  refl      ← liftSum (meqNfTy tyN tyN')
  return _
  
{-# COMPILE GHC checkType as checkTypeAgda #-}

-- Haskell interface to (typechecked and proven correct) reduction

import Algorithmic.Evaluation as L

runL : Term → Maybe Term
runL t = do
  tDB ← liftSum (scopeCheckTm {0}{Z} (shifter Z (convTm t)))
  _ ,, tC ← liftSum (inferType ∅ tDB)
  case (L.stepper tC maxsteps)
       (λ _ → nothing)
       λ{ (error _) → nothing -- FIXME
        ; tV → just (unconvTm (unshifter Z (extricateScope (extricate tV))))}

{-# COMPILE GHC runL as runLAgda #-}

-- Haskell interface to (untypechecked CK)
runCK : Term → Maybe Term
runCK t = do
  tDB ← liftSum (scopeCheckTm {0}{Z} (shifter Z (convTm t)))
  case (Scoped.CK.stepper maxsteps (ε ▻ tDB))
       (λ _ → nothing)
       λ{ (_ ▻ _) → nothing
        ; (_ ◅ _) → nothing
        ; (□ {t = tV} _) → just (unconvTm (unshifter Z (extricateScope tV)))
        ; ◆ → nothing} -- FIXME

{-# COMPILE GHC runCK as runCKAgda #-}

-- Haskell interface to (typechecked) CK
runTCK : Term → Maybe Term
runTCK t = do
  tDB ← liftSum (scopeCheckTm {0}{Z} (shifter Z (convTm t)))
  _ ,, tC ← liftSum (inferType ∅ tDB)
  case (Algorithmic.CK.stepper maxsteps (ε ▻ tC))
       (λ _ → nothing)
       λ{ (_ ▻ _) → nothing
        ; (_ ◅ _) → nothing
        ; (□ {t = tV} _) → just (unconvTm (unshifter Z (extricateScope (extricate tV))))
        ; (◆ _) → nothing}
  
{-# COMPILE GHC runTCK as runTCKAgda #-}

-- Haskell interface to (typechecked) CEKV
runTCEKV : Term → Maybe Term
runTCEKV t = do
  tDB ← liftSum (scopeCheckTm {0}{Z} (shifter Z (convTm t)))
  _ ,, tC ← liftSum (inferType ∅ tDB)
  case (Algorithmic.CEKV.stepper maxsteps (ε ; [] ▻ tC))
       (λ _ → nothing)
       λ{ (_ ; _ ▻ _) → nothing
        ; (_ ◅ _) → nothing
        ; (□ V) → just (unconvTm (unshifter Z (extricateScope (extricate (Algorithmic.CEKV.discharge V)))))
        ; (◆ _) → nothing}
  
{-# COMPILE GHC runTCEKV as runTCEKVAgda #-}

-- Haskell interface to (typechecked) CEKC
runTCEKC : Term → Maybe Term
runTCEKC t = do
  tDB ← liftSum (scopeCheckTm {0}{Z} (shifter Z (convTm t)))
  _ ,, tC ← liftSum (inferType ∅ tDB)
  case (Algorithmic.CEKC.stepper maxsteps (ε ; [] ▻ tC))
       (λ _ → nothing)
       λ{ (_ ; _ ▻ _) → nothing
        ; (_ ; _ ◅ _) → nothing
        ; (□ (_ ,, _ ,, V ,, ρ)) → just (unconvTm (unshifter Z (extricateScope (extricate (proj₁ (Algorithmic.CEKC.discharge V ρ))))))
        ; (◆ _) → nothing}
  
{-# COMPILE GHC runTCEKC as runTCEKCAgda #-}
\end{code}
