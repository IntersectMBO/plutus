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
open import Builtin.Constant.Term Ctx⋆ Kind * # _⊢⋆_ con size⋆
open import Builtin.Signature
open import Declarative.Term
open import Declarative.Evaluation
open import Declarative.Term.Reduction

--open import Declarative.Examples

open import Agda.Builtin.TrustMe
open import Relation.Binary.PropositionalEquality
open import Agda.Builtin.Nat
open import Data.Nat
open import Agda.Builtin.Int
open import Data.Integer

open import Data.Product renaming (_,_ to _,,_)
{-
lemma : length empty ≡ 0
lemma = primTrustMe

postulate
  str1 : ByteString
  str2 : ByteString

  printByteString : ByteString -> String

{-# FOREIGN GHC import qualified Data.ByteString.Lazy.Char8 as BS #-}
{-# COMPILE GHC str1 = BS.pack "Hello, " #-}
{-# COMPILE GHC str2 = BS.pack "world"   #-}
{-# COMPILE GHC printByteString = T.pack . BS.unpack #-}
{-# FOREIGN GHC import qualified Crypto.Hash #-}

lemma1 : length str1 ≡ 7
lemma1 = primTrustMe 
lemma2 : length str2 ≡ 7
lemma2 = primTrustMe

constr1 : ∀{Γ} → Γ ⊢ con bytestring (size⋆ 16)
constr1 = con (bytestring 16 str1 (subst (λ x → x Data.Nat.≤ 16) (sym lemma1) (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))))))

constr2 : ∀{Γ} → Γ ⊢ con bytestring (size⋆ 16)
constr2 = con (bytestring 16 str2 (subst (λ x → x Data.Nat.≤ 16) (sym lemma2) (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))))))

{-
conE : ∀{Γ} → Γ ⊢ con bytestring (size⋆ 8)
conE = con (bytestring 8 empty {!!})

appendE : ∀{Γ} → Γ ⊢ con bytestring (size⋆ 8)
appendE = builtin concatenate (λ { Z → size⋆ 8 ; (S ())}) (conE ,, conE ,, tt)
-}
append12 : ∀{Γ} → Γ ⊢ con bytestring (size⋆ 16)
append12 = builtin concatenate (λ { Z → size⋆ 16 ; (S ())}) (constr1 ,, constr2 ,, tt)

con1 : ∀{Γ} → Γ ⊢ con integer (size⋆ 8)
con1 = con (integer 8 (pos 1) (-≤+ ,, (+≤+ (s≤s (s≤s z≤n)))))

con2 : ∀{Γ} → Γ ⊢ con integer (size⋆ 8)
con2 = con (integer 8 (pos 2) (-≤+ ,, (+≤+ (s≤s (s≤s (s≤s z≤n))))))

builtin2plus2 : ∅ ⊢ con integer (size⋆ 8)
builtin2plus2 = builtin
  addInteger
  (λ { Z → size⋆ 8 ; (S x) → ` x})
  (con2 ,, con2 ,, tt)

inc8 : ∅ ⊢ con integer (size⋆ 8) ⇒ con integer (size⋆ 8)
inc8 = ƛ (builtin
  addInteger
  (λ { Z → size⋆ 8 ; (S x) → ` x})
  (con1 ,, ` Z ,, tt))

builtininc2 : ∅ ⊢ con integer (size⋆ 8)
builtininc2 = inc8 · con2

inc : ∅ ⊢ Π (con integer (` Z) ⇒ con integer (` Z))
inc = Λ (ƛ (builtin addInteger ` ((builtin resizeInteger (λ { Z → ` Z ; (S Z) → size⋆ 8 ; (S (S ()))}) (builtin sizeOfInteger ` (` Z ,, tt) ,, (con1 ,, tt))) ,, (` Z) ,, tt)))

builtininc2' : ∅ ⊢ con integer (size⋆ 8)
builtininc2' = (inc ·⋆ size⋆ 8) · con2

print : ∀{A : ∅ ⊢⋆ #}{b} → (x : ∅ ⊢ con b A) → Value x → String
print .(con (integer s i x)) (V-con (integer s i x)) = show i
print .(con (bytestring s b x)) (V-con (bytestring s b x)) = printByteString b
print .(con (size s)) (V-con (TermCon.size s)) = show (pos s)

help : ∀{A : ∅ ⊢⋆ *} → (M : ∅ ⊢ A) → Steps M → String
help {con x₁ A} M (steps x (done n v)) = print n v
help {_} M (steps x (done n v)) = "it worked"
help M (steps x out-of-gas) = "out of gas..."
help M error = "something went wrong"
-}
open import test.AddInteger
open import test.IntegerLiteral
open import test.IntegerOverflow -- can't be used
open import test.Negation -- TODO
open import test.StringLiteral

open Agda.Builtin.IO
open import Data.String
postulate
  return : ∀ {a} {A : Set a} → A → IO A
  _>>=_  : ∀ {a b} {A : Set a} {B : Set b} → IO A → (A → IO B) → IO B

{-# COMPILE GHC return = \_ _ -> return    #-}
{-# COMPILE GHC _>>=_  = \_ _ _ _ -> (>>=) #-}

_>>_  : ∀ {a b} {A : Set a} {B : Set b} → IO A → IO B → IO B
x >> y = x >>= λ _ → y

{-
test : ∀{A : ∅ ⊢⋆ *}
  → ∅ ⊢ A → (name : String) → (expected : String) → IO ⊤
test t name expected = do
  putStrLn ("test:" ++ name)
  putStrLn ("expected output: " ++ expected)
  s ← return (help _ (eval (gas 100) t))
  putStrLn ("actual output:   " ++ s)
  putStrLn ""
-}

{-
main : IO ⊤
main = do
  test (addI · con2 · con2) "AddInteger" "4"
  test intLit "IntegerLiteral" "102341"
  test stringLit "StringLiteral" "4321758fabce1aa4780193f"
  test negate "Negation" "it worked"
-}

open import Raw
open import Scoped
open import Data.Maybe

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
{-# FOREIGN GHC import Data.Either #-}

{-# FOREIGN GHC import Raw #-}
{-# COMPILE GHC convP = convP #-}
{-# FOREIGN GHC import qualified Data.ByteString.Lazy as BSL #-}
{-# COMPILE GHC imap = \_ _ -> fmap #-}
{-# COMPILE GHC mmap = \_ _ -> fmap #-}
{-# COMPILE GHC mbind = \_ _ f a -> f =<< a #-}
{-# FOREIGN GHC import Data.Either #-}
{-# COMPILE GHC parse = either (\_ -> Nothing) Just . parse #-}
{-# FOREIGN GHC import Language.PlutusCore.Type #-}
{-# COMPILE GHC Program = type Language.PlutusCore.Type.Program TyName Name Language.PlutusCore.Lexer.AlexPosn #-}
{-# COMPILE GHC readFile = \ s -> BSL.readFile (T.unpack s) #-}
{-# COMPILE GHC showTerm = T.pack . show #-}
open import Function

open import Untyped.Term as U
import Untyped.Reduction as U
import Scoped as S
import Scoped.Reduction as S


-- untyped evaluation
utestPLC : ByteString → Maybe String
utestPLC plc = mmap (U.ugly ∘ (λ (t : 0 ⊢) → proj₁ (U.run t 100)) ∘ erase⊢) (mbind (deBruijnifyTm nil) (mmap convP (parse plc)))

-- extrinsically typed evaluation
stestPLC : ByteString → Maybe String
stestPLC plc = mmap (S.ugly ∘ (λ (t : ScopedTm Z) → proj₁ (S.run t 100)) ∘ saturate) (mbind (deBruijnifyTm nil) (mmap convP (parse plc)))

testFile : String → IO String
testFile fn = do
  t ← readFile fn
  return (maybe id "blerk" (stestPLC t))

{-# FOREIGN GHC import System.Environment #-}

open import Data.List

postulate getArgs : IO (List String)

{-# COMPILE GHC getArgs = (fmap . fmap) T.pack $ getArgs #-}

main : IO ⊤
main = do
  (arg ∷ args) ← getArgs
    where [] → return _
  putStrLn arg
  testFile arg >>= putStrLn

{-
  -- plutus/language-plutus-core/type-errors
  putStrLn "errorKind.plc:"
  testFile "../plutus/language-plutus-core/test/type-errors/errorKind.plc" >>= putStrLn
  
  putStrLn "instType.plc:"
  testFile "../plutus/language-plutus-core/test/type-errors/instType.plc" >>= putStrLn

  putStrLn "applyType.plc:"
  testFile "../plutus/language-plutus-core/test/type-errors/applyType.plc" >>= putStrLn
{- uses ifix  
  putStrLn "unwrapType.plc:"
  testFile "../plutus/language-plutus-core/test/type-errors/unwrapType.plc" >>= putStrLn
-}

  -- plutus/language-plutus-core/types
  -- these test are intended to check type inference

  putStrLn "addInteger.plc:"
  testFile "../plutus/language-plutus-core/test/types/addInteger.plc" >>= putStrLn

  putStrLn "case.plc:"
  testFile "../plutus/language-plutus-core/test/types/case.plc" >>= putStrLn

  putStrLn "correctType.plc:"
  testFile "../plutus/language-plutus-core/test/types/correctType.plc" >>= putStrLn

{- uses ifix
  putStrLn "example.plc:"
  testFile "../plutus/language-plutus-core/test/types/example.plc" >>= putStrLn
-}
  
  putStrLn "negation.plc:"
  testFile "../plutus/language-plutus-core/test/types/negation.plc" >>= putStrLn
  

  putStrLn "not.plc:"
  testFile "../plutus/language-plutus-core/test/types/not.plc" >>= putStrLn
  
{- uses ifix
  putStrLn "recursiveWrap.plc:"
  testFile "../plutus/language-plutus-core/test/types/recursiveWrap.plc" >>= putStrLn
-}

  putStrLn "reduce.plc:"
  testFile "../plutus/language-plutus-core/test/types/reduce.plc" >>= putStrLn
  
{- uses ifix  
  putStrLn "tail.plc:"
  testFile "../plutus/language-plutus-core/test/types/tail.plc" >>= putStrLn
-}
  
  putStrLn "verifyIdentity.plc:"
  testFile "../plutus/language-plutus-core/test/types/verifyIdentity.plc" >>= putStrLn

  -- plutus/language-plutus-core/normalize-types
  putStrLn "addIntegerCorrect.plc:"
  testFile "../plutus/language-plutus-core/test/normalize-types/addIntegerCorrect.plc"
    >>= putStrLn

  putStrLn "ntm.plc:"
  testFile "../plutus/language-plutus-core/test/normalize-types/ntm.plc" >>= putStrLn


  -- plutus/language-plutus-core/test/Evaluation/Golden
  putStrLn "verifySignature.plc:"
  testFile "../plutus/language-plutus-core/test/Evaluation/Golden/verifySignature.plc"
    >>= putStrLn

  putStrLn "verifySignatureError.plc:"
  testFile
    "../plutus/language-plutus-core/test/Evaluation/Golden/verifySignatureError.plc"
    >>= putStrLn

  -- plutus/language-plutus-core/test/data
  putStrLn "integerLiteral.plc:"
  testFile "../plutus/language-plutus-core/test/data/integerLiteral.plc" >>= putStrLn

  putStrLn "negation.plc:"
  testFile "../plutus/language-plutus-core/test/data/negation.plc" >>= putStrLn

  putStrLn "stringLiteral.plc:"
  testFile "../plutus/language-plutus-core/test/data/stringLiteral.plc" >>= putStrLn

  -- the overflow is a parse error
  putStrLn "integerOverflow.plc:"
  testFile "../plutus/language-plutus-core/test/data/integerOverflow.plc" >>= putStrLn

  putStrLn "addInteger.plc:"
  testFile "../plutus/language-plutus-core/test/data/addInteger.plc" >>= putStrLn

  -- plutus/language-plutus-core/test/scopes
  putStrLn "negation.plc:"
  testFile "../plutus/language-plutus-core/test/scopes/negation.plc" >>= putStrLn

  putStrLn "negation.plc:"
  testFile "../plutus/language-plutus-core/test/scopes/negation.plc" >>= putStrLn

  putStrLn "apply.plc:"
  testFile "../plutus/language-plutus-core/test/scopes/apply.plc" >>= putStrLn

  putStrLn "lambda2.plc:"
  testFile "../plutus/language-plutus-core/test/scopes/lambda2.plc" >>= putStrLn

  putStrLn "lambda.plc:"
  testFile "../plutus/language-plutus-core/test/scopes/lambda.plc" >>= putStrLn
-}
\end{code}
