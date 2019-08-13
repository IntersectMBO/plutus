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

{-# FOREIGN GHC import Language.PlutusCore.Name #-}
{-# FOREIGN GHC import Language.PlutusCore.Lexer #-}
{-# FOREIGN GHC import Language.PlutusCore.Parser #-}
{-# FOREIGN GHC import Language.PlutusCore.Pretty #-}
{-# FOREIGN GHC import Data.Either #-}

{-# FOREIGN GHC import Raw #-}
{-# COMPILE GHC convP = convP #-}
{-# FOREIGN GHC import qualified Data.ByteString.Lazy as BSL #-}
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

postulate prettyPrint : RawTm → String

{-# COMPILE GHC prettyPrint = prettyText . unconv #-}

open import Data.Vec hiding (_>>=_)

open import Scoped.CK

tvars : ∀{n} → Vec String n
tvars {zero}      = []
tvars {Nat.suc n} =
  ("tvar" Data.String.++ Data.Integer.show (pos n)) ∷ tvars {n}

-- this is not very useful but I am expecting that it won't be used
vars : ∀{n}{i : Weirdℕ n} → WeirdVec String i
vars {i = Z} = nil
vars {i = S i} = consS "varS" (vars {i = i})
vars {i = T i} = consT "varT" (vars {i = i})

-- extrinsically typed evaluation
stestPLC : Bool → ByteString → String
stestPLC b plc with parse plc
stestPLC b plc | just t with deBruijnifyTm nil (convP t)
stestPLC Bool.false plc | just t | just t' with S.run (saturate t') 1000000
stestPLC Bool.false plc | just t | just t' | t'' ,, _ ,, inj₁ (just _) =
  prettyPrint (deDeBruijnify [] nil (unsaturate t''))
stestPLC Bool.false plc | just t | just t' | t'' ,, p ,, inj₁ nothing = "out of fuel"
stestPLC Bool.false plc | just t | just t' | t'' ,, p ,, inj₂ e =
  "runtime error" Data.String.++
  prettyPrint (deDeBruijnify [] nil (unsaturate t''))
stestPLC Bool.true plc | just t | just t' with stepper 1000000000 _ (ε ▻ saturate t')
stestPLC Bool.true plc | just t | just t' | n ,, i ,, _ ,, just (□ {t = t''}  V) =
  prettyPrint (deDeBruijnify tvars vars (unsaturate t''))
stestPLC Bool.true plc | just t | just t' | _ ,, _ ,, _ ,,  just _ =
  "this shouldn't happen"
stestPLC Bool.true plc | just t | just t' | _ ,, _ ,, _ ,,  nothing = "out of fuel"
stestPLC b plc | just t | nothing = "scope error"
stestPLC b plc | nothing = "parse error"

testFile : Bool → String → IO String
testFile b fn = do
  t ← readFile fn
  return (stestPLC b t)

{-# FOREIGN GHC import System.Environment #-}

open import Data.List

postulate getArgs : IO (List String)

{-# COMPILE GHC getArgs = (fmap . fmap) T.pack $ getArgs #-}

{-# FOREIGN GHC import Opts #-}

data Config : Set where
  Conf : String → Bool → Config

postulate execP : IO Config

{-# COMPILE GHC Config = data Config (Conf) #-}
{-# COMPILE GHC execP = execP #-}

main' : Config → IO ⊤
main' (Conf filename b) = testFile b filename >>= putStrLn

main : IO ⊤
main = execP >>= main'
\end{code}
