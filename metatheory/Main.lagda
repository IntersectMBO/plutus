\begin{code}
module Main where
open import Agda.Builtin.IO
open import Agda.Builtin.Unit
open import Agda.Builtin.String

postulate
  putStrLn : String → IO ⊤

{-# FOREIGN GHC import qualified Data.Text.IO as Text #-}
{-# FOREIGN GHC import qualified Data.Text as T #-}
{-# COMPILE GHC putStrLn = Text.putStrLn #-}

open import Type
open import Builtin
open import Builtin.Constant.Type
open import Builtin.Constant.Term Ctx⋆ Kind * _⊢⋆_ con
open import Builtin.Signature

open import Agda.Builtin.TrustMe
open import Relation.Binary.PropositionalEquality
open import Agda.Builtin.Nat
open import Data.Nat
open import Agda.Builtin.Int
open import Data.Integer
import Data.Maybe as M
open import Data.Product renaming (_,_ to _,,_)
open import Data.Bool

open import Check hiding (_>>=_; return)
open import Scoped.Extrication
open import Type.BetaNBE


open Agda.Builtin.IO
open import Data.String
postulate
  return : ∀ {a} {A : Set a} → A → IO A
  _>>=_  : ∀ {a b} {A : Set a} {B : Set b} → IO A → (A → IO B) → IO B

{-# COMPILE GHC return = \_ _ -> return    #-}
{-# COMPILE GHC _>>=_  = \_ _ _ _ -> (>>=) #-}

_>>_  : ∀ {a b} {A : Set a} {B : Set b} → IO A → IO B → IO B
x >> y = x >>= λ _ → y

open import Raw
open import Scoped
open import Utils

postulate
  imap : ∀{A B : Set} → (A → B) → IO A → IO B
  mmap : ∀{A B : Set} → (A → B) → Maybe A → Maybe B
  mbind : ∀{A B : Set} → (A → Maybe B) → Maybe A → Maybe B
  ProgramN : Set
  Program : Set
  convP : Program → RawTm
  readFile : String → IO ByteString
  parse : ByteString → Maybe ProgramN
  showTerm : RawTm → String
  getContents : IO ByteString
  exitFailure : IO ⊤
  exitSuccess : IO ⊤
  deBruijnify : ProgramN → Maybe Program
  
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
{-# FOREIGN GHC import qualified Data.ByteString.Lazy as BSL #-}
{-# COMPILE GHC getContents = BSL.getContents #-}
{-# COMPILE GHC imap = \_ _ -> fmap #-}
{-# COMPILE GHC mmap = \_ _ -> fmap #-}
{-# COMPILE GHC mbind = \_ _ f a -> f =<< a #-}
{-# FOREIGN GHC import Data.Either #-}
{-# COMPILE GHC parse = either (\_ -> Nothing) Just . parse  #-}
{-# COMPILE GHC deBruijnify = either (\_ -> Nothing) Just . runExcept . deBruijnProgram #-}
{-# FOREIGN GHC import Language.PlutusCore #-}
{-# COMPILE GHC ProgramN = type Language.PlutusCore.Program TyName Name Language.PlutusCore.Lexer.AlexPosn #-}
{-# COMPILE GHC Program = type Language.PlutusCore.Program TyDeBruijn DeBruijn Language.PlutusCore.Lexer.AlexPosn #-}
{-# COMPILE GHC readFile = \ s -> BSL.readFile (T.unpack s) #-}
{-# COMPILE GHC showTerm = T.pack . show #-}
open import Function

open import Untyped as U
import Untyped.Reduction as U
import Scoped as S
import Scoped.Reduction as S

open import Data.Sum

mapper : {A B : Set} → (A → B) → Maybe A → Maybe B
mapper f nothing = nothing
mapper f (just a) = just (f a)

open import Untyped

-- untyped evaluation
--utestPLC : ByteString → Maybe String
--utestplc plc = mmap (U.ugly ∘ (λ (t : 0 ⊢) → proj₁ (U.run t 100)) ∘ erase⊢) (mbind (deBruijnifyTm nil) (mmap convP (parse plc)))

open import Data.Fin

postulate
  prettyPrintTm : RawTm → String
  prettyPrintTy : RawTy → String

{-# COMPILE GHC prettyPrintTm = prettyText . unconv #-}
{-# COMPILE GHC prettyPrintTy = prettyText . unconvT #-}

open import Data.Vec hiding (_>>=_;_++_)

open import Scoped.CK
open import Algorithmic.CK

data EvalMode : Set where
  TCK CK L : EvalMode

-- extrinsically typed evaluation
evalPLC : EvalMode → ByteString → String ⊎ String
evalPLC m plc with parse plc
evalPLC m plc | nothing = inj₂ "parse error"
evalPLC m plc | just nt with deBruijnify nt
evalPLC m plc | just nt | nothing = inj₂ "(Haskell) Scope Error"
evalPLC m plc | just nt | just t with scopeCheckTm {0}{Z} (shifter 0 Z (convP t))
evalPLC m plc | just nt | just t | nothing = inj₂ $ "(Agda) Scope Error"
  ++ "\n" ++ rawPrinter (shifter 0 Z (convP t))
evalPLC L plc | just nt | just t | just t' with S.run (saturate t') 1000000
evalPLC L plc | just nt | just t | just t' | t'' ,, _ ,, inj₁ (just _) =
  inj₁ (prettyPrintTm (unshifter Z (extricateScope (unsaturate t''))))
evalPLC L plc | just nt | just t | just t' | t'' ,, p ,, inj₁ nothing =
  inj₂ "out of fuel"
evalPLC L plc | just nt | just t | just t' | t'' ,, p ,, inj₂ e = inj₂
  ("runtime error" Data.String.++
  prettyPrintTm (unshifter Z (extricateScope (unsaturate t''))))
evalPLC CK plc | just nt | just t | just t' with Scoped.CK.stepper 1000000000 _ (ε ▻ saturate t')
evalPLC CK plc | just nt | just t | just t' | n ,, i ,, _ ,, just (□ {t = t''}  V) =
  inj₁ (prettyPrintTm (unshifter Z (extricateScope (unsaturate t''))))
evalPLC CK plc | just nt | just t | just t' | _ ,, _ ,, _ ,,  just _ =
  inj₂ ("this shouldn't happen")
evalPLC CK plc | just nt | just t | just t' | _ ,, _ ,, _ ,,  nothing = inj₂ "out of fuel"
evalPLC TCK plc | just nt | just t | just t' with inferType _ t'
... | inj₂ e = inj₂ "typechecking error"
... | inj₁ (A ,, t'') with Algorithmic.CK.stepper 1000000000 _ (ε ▻ t'')
... | _ ,, _ ,, _ ,, _ ,, M.just (□ {t = t'''} V)  =
  inj₁ (prettyPrintTm (unshifter Z (extricateScope (extricate t'''))))
... | _ ,, _ ,, _ ,, _ ,, M.just _  = inj₂ "this shouldn't happen"
... | _ ,, _ ,, _ ,, _ ,, M.nothing = inj₂ "out of fuel"


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
  inj₁ (prettyPrintTy (unshifterTy Z (extricateScopeTy (extricateNf⋆ A))))
... | inj₂ typeError = inj₂ "typeError"
... | inj₂ kindEqError = inj₂ "kindEqError"
... | inj₂ notTypeError = inj₂ "notTypeError"
... | inj₂ notFunction = inj₂ "notFunction"
... | inj₂ notPiError = inj₂ "notPiError"
... | inj₂ notPat = inj₂ "notPat"
... | inj₂ (nameError x x') = inj₂ (x Data.String.++ " != " Data.String.++ x')
... | inj₂ (typeEqError n n') = inj₂ (
  prettyPrintTy (unshifterTy Z (extricateScopeTy (extricateNf⋆ n)))
  Data.String.++
  "\n != \n"
  Data.String.++
  prettyPrintTy (unshifterTy Z (extricateScopeTy (extricateNf⋆ n'))))
  
... | inj₂ typeVarEqError = inj₂ "typeVarEqError"
... | inj₂ tyConError     = inj₂ "tyConError"
... | inj₂ builtinError   = inj₂ "builtinError"
... | inj₂ unwrapError    = inj₂ "unwrapError"



{-# FOREIGN GHC import System.Environment #-}

open import Data.List

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
{-# COMPILE GHC EvalMode = data EvalMode (TCK | CK | L ) #-}
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
