\begin{code}
module Main where
open import Agda.Builtin.IO
open import Agda.Builtin.Unit
open import Agda.Builtin.String
open Agda.Builtin.IO
open import Function
open import Data.Sum
open import Data.String
open import Agda.Builtin.TrustMe
open import Relation.Binary.PropositionalEquality
open import Agda.Builtin.Nat
open import Data.Nat
open import Agda.Builtin.Int
open import Data.Integer
import Data.Maybe as M
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
open import Check hiding (_>>=_; return)
open import Scoped.Extrication
open import Type.BetaNBE
open import Untyped as U
import Untyped.Reduction as U
import Scoped as S
import Scoped.Reduction as S
open import Raw
open import Scoped
open import Utils
open import Untyped
open import Scoped.CK
open import Algorithmic.CK
open import Scoped.Erasure


postulate
  putStrLn : String → IO ⊤

{-# FOREIGN GHC import qualified Data.Text.IO as Text #-}
{-# FOREIGN GHC import qualified Data.Text as T #-}
{-# COMPILE GHC putStrLn = Text.putStrLn #-}

postulate
  return : ∀ {a} {A : Set a} → A → IO A
  _>>=_  : ∀ {a b} {A : Set a} {B : Set b} → IO A → (A → IO B) → IO B

{-# COMPILE GHC return = \_ _ -> return    #-}
{-# COMPILE GHC _>>=_  = \_ _ _ _ -> (>>=) #-}

_>>_  : ∀ {a b} {A : Set a} {B : Set b} → IO A → IO B → IO B
x >> y = x >>= λ _ → y

postulate
  imap : ∀{A B : Set} → (A → B) → IO A → IO B
  mmap : ∀{A B : Set} → (A → B) → Maybe A → Maybe B
  mbind : ∀{A B : Set} → (A → Maybe B) → Maybe A → Maybe B
  TermN : Set
  Term : Set
  TypeN : Set
  Type : Set
  ProgramN : Set
  Program : Set
  convTm : Term → RawTm
  convTy : Type → RawTy
  convP : Program → RawTm
  readFile : String → IO ByteString
  parse : ByteString → Maybe ProgramN
  parseTm : ByteString → Maybe TermN
  parseTy : ByteString → Maybe TypeN
  showTerm : RawTm → String
  getContents : IO ByteString
  exitFailure : IO ⊤
  exitSuccess : IO ⊤
  deBruijnify : ProgramN → Maybe Program
  deBruijnifyTm : TermN → Maybe Term
  deBruijnifyTy : TypeN → Maybe Type

{-# FOREIGN GHC import Language.PlutusCore.Name #-}
{-# FOREIGN GHC import Language.PlutusCore.Lexer #-}
{-# FOREIGN GHC import Language.PlutusCore.Parser #-}
{-# FOREIGN GHC import Language.PlutusCore.Pretty #-}
{-# FOREIGN GHC import Language.PlutusCore.DeBruijn #-}
{-# FOREIGN GHC import Data.Either #-}
{-# FOREIGN GHC import System.Exit #-}
{-# COMPILE GHC exitSuccess = exitSuccess #-}
{-# COMPILE GHC exitFailure = exitFailure #-}
{-# FOREIGN GHC import Control.Monad.Trans.Except #-}
{-# FOREIGN GHC import Raw #-}
{-# COMPILE GHC convP = convP #-}
{-# COMPILE GHC convTm = conv #-}
{-# COMPILE GHC convTy = convT #-}
{-# FOREIGN GHC import qualified Data.ByteString.Lazy as BSL #-}
{-# COMPILE GHC getContents = BSL.getContents #-}
{-# COMPILE GHC imap = \_ _ -> fmap #-}
{-# COMPILE GHC mmap = \_ _ -> fmap #-}
{-# COMPILE GHC mbind = \_ _ f a -> f =<< a #-}
{-# FOREIGN GHC import Data.Either #-}
{-# COMPILE GHC parse = either (\_ -> Nothing) Just . parse  #-}
{-# COMPILE GHC parseTm = either (\_ -> Nothing) Just . parseTm  #-}
{-# COMPILE GHC parseTy = either (\_ -> Nothing) Just . parseTy  #-}
{-# COMPILE GHC deBruijnify = either (\_ -> Nothing) Just . runExcept . deBruijnProgram #-}
{-# COMPILE GHC deBruijnifyTm = either (\_ -> Nothing) Just . runExcept . deBruijnTerm #-}
{-# COMPILE GHC deBruijnifyTy = either (\_ -> Nothing) Just . runExcept . deBruijnTy #-}
{-# FOREIGN GHC import Language.PlutusCore #-}
{-# COMPILE GHC ProgramN = type Language.PlutusCore.Program TyName Name DefaultUni Language.PlutusCore.Lexer.AlexPosn #-}
{-# COMPILE GHC Program = type Language.PlutusCore.Program TyDeBruijn DeBruijn DefaultUni Language.PlutusCore.Lexer.AlexPosn #-}
{-# COMPILE GHC TermN = type Language.PlutusCore.Term TyName Name DefaultUni Language.PlutusCore.Lexer.AlexPosn #-}
{-# COMPILE GHC Term = type Language.PlutusCore.Term TyDeBruijn DeBruijn DefaultUni Language.PlutusCore.Lexer.AlexPosn #-}
{-# COMPILE GHC TypeN = type Language.PlutusCore.Type TyName DefaultUni Language.PlutusCore.Lexer.AlexPosn #-}
{-# COMPILE GHC Type = type Language.PlutusCore.Type TyDeBruijn DefaultUni Language.PlutusCore.Lexer.AlexPosn #-}
{-# COMPILE GHC readFile = \ s -> BSL.readFile (T.unpack s) #-}
{-# COMPILE GHC showTerm = T.pack . show #-}


mapper : {A B : Set} → (A → B) → Maybe A → Maybe B
mapper f nothing = nothing
mapper f (just a) = just (f a)

{-
utestPLC : ByteString → Maybe String
utestPLC plc = mmap (U.ugly ∘ (λ (t : 0 ⊢) → proj₁ (U.run t 100)) ∘ eraseTm) (mbind {! deBruijnifyTm!} {! mmap convP (parse plc)!})
-}

postulate
  prettyPrintTm : RawTm → String
  prettyPrintTy : RawTy → String

{-# COMPILE GHC prettyPrintTm = prettyText . unconv (-1) (-1) #-}
{-# COMPILE GHC prettyPrintTy = prettyText . unconvT (-1) #-}

data EvalMode : Set where
  U L TCK CK : EvalMode

-- extrinsically typed evaluation
evalPLC : EvalMode → ByteString → String ⊎ String
evalPLC m plc with parse plc
evalPLC m plc | nothing = inj₂ "parse error"
evalPLC m plc | just nt with deBruijnify nt
evalPLC m plc | just nt | nothing = inj₂ "(Haskell) Scope Error"
evalPLC m plc | just nt | just t with scopeCheckTm {0}{Z} (shifter 0 Z (convP t))
evalPLC m plc | just nt | just t | nothing = inj₂ $ "(Agda) Scope Error"
  ++ "\n" ++ rawPrinter (shifter 0 Z (convP t))
evalPLC L plc | just nt | just t | just t' with S.run t' 10000000000
evalPLC L plc | just nt | just t | just t' | t'' ,, p ,, inj₁ (just v) =
  inj₁ (prettyPrintTm (extricateScope t''))
evalPLC L plc | just nt | just t | just t' | t'' ,, p ,, inj₁ nothing  =
  inj₂ "out of fuel"
evalPLC L plc | just nt | just t | just t' | t'' ,, p ,, inj₂ e        =
  inj₂ "computed to error"
evalPLC CK plc | just nt | just t | just t' with Scoped.CK.stepper 1000000000 (ε ▻ t')
evalPLC CK plc | just nt | just t | just t' | just (□ {t = t''}  V) =
   inj₁ (prettyPrintTm (extricateScope t''))
evalPLC CK plc | just nt | just t | just t' | just _ =
  inj₂ ("this shouldn't happen")
evalPLC CK plc | just nt | just t | just t' | nothing = inj₂ "out of fuel"
evalPLC TCK plc | just nt | just t | just t' with inferType _ t'
... | inj₂ e = inj₂ "typechecking error"
... | inj₁ (A ,, t'') with Algorithmic.CK.stepper 1000000000 (ε ▻ t'')
... | M.just (□ {t = t'''} V)  =
  inj₁ (prettyPrintTm (extricateScope (extricate t''')))
... | M.just _  = inj₂ "this shouldn't happen"
... | M.nothing = inj₂ "out of fuel"
evalPLC U plc | just nt | just t | just t' with U.run (eraseTm t') 10000000
evalPLC U plc | just nt | just t | just t' | t'' ,, p ,, inj₁ (just v) =
  inj₁ (U.ugly t'')
evalPLC U plc | just nt | just t | just t' | t'' ,, p ,, inj₁ nothing =
  inj₂ "out of fuel"
evalPLC U plc | just nt | just t | just t' | t'' ,, p ,, inj₂ e =
  inj₂ "computed to error"
junk : ∀{n} → Vec String n
junk {zero}      = []
junk {Nat.suc n} = Data.Integer.show (pos n) ∷ junk

tcPLC : ByteString → String ⊎ String
tcPLC plc with parse plc
... | nothing = inj₂ "Parse Error"
... | just nt with deBruijnify nt
... | nothing = inj₂ "(Haskell) Scope Error"
... | just t with scopeCheckTm {0}{Z} (shifter 0 Z (convP t))
... | nothing = inj₂ "(Agda) scope error"
... | just t' with inferType _ t'
... | inj₁ (A ,, t'') =
  inj₁ (prettyPrintTy (extricateScopeTy (extricateNf⋆ A)))
... | inj₂ typeError = inj₂ "typeError"
... | inj₂ kindEqError = inj₂ "kindEqError"
... | inj₂ notTypeError = inj₂ "notTypeError"
... | inj₂ notFunction = inj₂ "notFunction"
... | inj₂ notPiError = inj₂ "notPiError"
... | inj₂ notPat = inj₂ "notPat"
... | inj₂ (nameError x x') = inj₂ (x Data.String.++ " != " Data.String.++ x')
... | inj₂ (typeEqError n n') = inj₂ (
  prettyPrintTy (extricateScopeTy (extricateNf⋆ n))
  Data.String.++
  "\n != \n"
  Data.String.++
  prettyPrintTy (extricateScopeTy (extricateNf⋆ n')))
... | inj₂ typeVarEqError = inj₂ "typeVarEqError"
... | inj₂ tyConError     = inj₂ "tyConError"
... | inj₂ builtinError   = inj₂ "builtinError"
... | inj₂ unwrapError    = inj₂ "unwrapError"

alphaTm : ByteString → ByteString → Bool
alphaTm plc1 plc2 with parseTm plc1 | parseTm plc2
alphaTm plc1 plc2 | just plc1' | just plc2' with deBruijnifyTm plc1' | deBruijnifyTm plc2'
alphaTm plc1 plc2 | just plc1' | just plc2' | just plc1'' | just plc2'' = decRTm (convTm plc1'') (convTm plc2'')
alphaTm plc1 plc2 | just plc1' | just plc2' | _ | _ = Bool.false
alphaTm plc1 plc2 | _ | _ = Bool.false

{-# COMPILE GHC alphaTm as alphaTm #-}
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

{-# FOREIGN GHC import System.Environment #-}

postulate getArgs : IO (List String)

{-# COMPILE GHC getArgs = (fmap . fmap) T.pack $ getArgs #-}

{-# FOREIGN GHC import Opts #-}

data Input : Set where
  FileInput : String → Input
  StdInput : Input

{-# COMPILE GHC Input = data Input (FileInput | StdInput) #-}

data EvalOptions : Set where
  EvalOpts : Input → EvalMode → EvalOptions

data TCOptions : Set where
  TCOpts : Input → TCOptions

data Command : Set where
  Evaluate  : EvalOptions → Command
  TypeCheck : TCOptions → Command

postulate execP : IO Command

{-# COMPILE GHC EvalOptions = data EvalOptions (EvalOpts) #-}
{-# COMPILE GHC TCOptions = data TCOptions (TCOpts) #-}
{-# COMPILE GHC Command = data Command (Evaluate | TypeCheck) #-}
{-# COMPILE GHC EvalMode = data EvalMode (U | L | TCK | CK ) #-}
{-# COMPILE GHC execP = execP #-}

evalInput : EvalMode → Input → IO (String ⊎ String)
evalInput m (FileInput fn) = imap (evalPLC m) (readFile fn)
evalInput m StdInput       = imap (evalPLC m) getContents

tcInput : Input → IO (String ⊎ String)
tcInput (FileInput fn) = imap tcPLC (readFile fn)
tcInput StdInput       = imap tcPLC getContents

main' : Command → IO ⊤
main' (Evaluate (EvalOpts i m)) =
  evalInput m i
  >>=
  Data.Sum.[ (λ s → putStrLn s >> exitSuccess)
           , (λ e → putStrLn e >> exitFailure)
           ]
main' (TypeCheck (TCOpts i))    =
  (tcInput i)
  >>=
  Data.Sum.[ (λ s → putStrLn s >> exitSuccess)
           , (λ e → putStrLn e >> exitFailure)
           ]

main : IO ⊤
main = execP >>= main'
\end{code}
