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

open import Data.Product renaming (_,_ to _,,_)
open import Data.Bool

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
  Program : Set
  convP : Program → RawTm
  readFile : String → IO ByteString
  parse : ByteString → Maybe Program
  showTerm : RawTm → String
  getContents : IO ByteString
  
{-# FOREIGN GHC import Language.PlutusCore.Name #-}
{-# FOREIGN GHC import Language.PlutusCore.Lexer #-}
{-# FOREIGN GHC import Language.PlutusCore.Parser #-}
{-# FOREIGN GHC import Language.PlutusCore.Pretty #-}
{-# FOREIGN GHC import Data.Either #-}

{-# FOREIGN GHC import Raw #-}
{-# COMPILE GHC convP = convP #-}
{-# FOREIGN GHC import qualified Data.ByteString.Lazy as BSL #-}
{-# COMPILE GHC getContents = BSL.getContents #-}
{-# COMPILE GHC imap = \_ _ -> fmap #-}
{-# COMPILE GHC mmap = \_ _ -> fmap #-}
{-# COMPILE GHC mbind = \_ _ f a -> f =<< a #-}
{-# FOREIGN GHC import Data.Either #-}
{-# COMPILE GHC parse = either (\_ -> Nothing) Just . parse #-}
{-# FOREIGN GHC import Language.PlutusCore #-}
{-# COMPILE GHC Program = type Language.PlutusCore.Program TyName Name Language.PlutusCore.Lexer.AlexPosn #-}
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
--utestPLC plc = mmap (U.ugly ∘ (λ (t : 0 ⊢) → proj₁ (U.run t 100)) ∘ erase⊢) (mbind (deBruijnifyTm nil) (mmap convP (parse plc)))

open import Data.Fin

postulate
  prettyPrintTm : RawTm → String
  prettyPrintTy : RawTy → String

{-# COMPILE GHC prettyPrintTm = prettyText . unconv #-}
{-# COMPILE GHC prettyPrintTy = prettyText . unconvT #-}

open import Data.Vec hiding (_>>=_)

open import Scoped.CK

data EvalMode : Set where
  CK L : EvalMode

-- extrinsically typed evaluation
evalPLC : EvalMode → ByteString → String
evalPLC m plc with parse plc
evalPLC m plc | just t with deBruijnifyTm nil (convP t)
evalPLC L plc | just t | just t' with S.run (saturate t') 1000000
evalPLC L plc | just t | just t' | t'' ,, _ ,, inj₁ (just _) =
  prettyPrintTm (deDeBruijnify [] nil (unsaturate t''))
evalPLC L plc | just t | just t' | t'' ,, p ,, inj₁ nothing = "out of fuel"
evalPLC L plc | just t | just t' | t'' ,, p ,, inj₂ e =
  "runtime error" Data.String.++
  prettyPrintTm (deDeBruijnify [] nil (unsaturate t''))
evalPLC CK plc | just t | just t' with stepper 1000000000 _ (ε ▻ saturate t')
evalPLC CK plc | just t | just t' | n ,, i ,, _ ,, just (□ {t = t''}  V) =
  prettyPrintTm (deDeBruijnify [] nil (unsaturate t''))
evalPLC CK plc | just t | just t' | _ ,, _ ,, _ ,,  just _ =
  "this shouldn't happen"
evalPLC CK plc | just t | just t' | _ ,, _ ,, _ ,,  nothing = "out of fuel"
evalPLC m plc | just t | nothing = "scope error"
evalPLC m plc | nothing = "parse error"

open import Check hiding (_>>=_)
open import Scoped.Extrication
open import Type.BetaNBE

junk : ∀{n} → Vec String n
junk {zero}      = []
junk {Nat.suc n} = Data.Integer.show (pos n) ∷ junk

tcPLC : ByteString → String
tcPLC plc with parse plc
... | nothing = "parse error"
... | just t with deBruijnifyTm nil (convP t)
... | nothing = "scope error"
... | just t' with inferType _ t'
... | inj₁ (A ,, t'') = prettyPrintTy (deDeBruijnify⋆ [] (extricateNf⋆ A))
... | inj₂ typeError = "typeError"
... | inj₂ kindEqError = "kindEqError"
... | inj₂ notTypeError = "notTypeError"
... | inj₂ notFunction = "notFunction"
... | inj₂ notPiError = "notPiError"
... | inj₂ notPat = "notPat"
... | inj₂ (nameError x x') = x Data.String.++ " != " Data.String.++ x'
... | inj₂ (typeEqError n n') =
  prettyPrintTy (deDeBruijnify⋆ junk (extricateNf⋆ n))
  Data.String.++
  "\n != \n"
  Data.String.++
  prettyPrintTy (deDeBruijnify⋆ junk (extricateNf⋆ n'))
  
... | inj₂ typeVarEqError = "typeVarEqError"
... | inj₂ tyConError     = "tyConError"
... | inj₂ builtinError   = "builtinError"
... | inj₂ unwrapError    = "unwrapError"



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
{-# COMPILE GHC EvalMode = data EvalMode (CK | L) #-}
{-# COMPILE GHC execP = execP #-}

evalInput : EvalMode → Input → IO String
evalInput m (FileInput fn) = imap (evalPLC m) (readFile fn)
evalInput m StdInput       = imap (evalPLC m) getContents 

tcInput : Input → IO String
tcInput (FileInput fn) = imap tcPLC (readFile fn)
tcInput StdInput       = imap tcPLC getContents

main' : Command → IO ⊤
main' (Evaluate (EvalOpts i m)) = evalInput m i >>= putStrLn
main' (TypeCheck (TCOpts i))    = tcInput i >>= putStrLn

main : IO ⊤
main = execP >>= main'
\end{code}
