\begin{code}
module TermIndexedBySyntacticType.Main where
open import Agda.Builtin.IO
open import Agda.Builtin.Unit
open import Agda.Builtin.String

postulate
  putStrLn : String → IO ⊤

{-# FOREIGN GHC import qualified Data.Text.IO as Text #-}
{-# COMPILE GHC putStrLn = Text.putStrLn #-}

open import Builtin.Constant.Term
open import Builtin.Constant.Type
open import Builtin.Signature
open import Type
open import TermIndexedBySyntacticType.Term
open import TermIndexedBySyntacticType.Evaluation

open import TermIndexedBySyntacticType.Examples

main : IO ⊤
-- main with eval (gas 100) Builtins.builtininc2'
-- this blows the stack
main with eval (gas 100) Church.TwoPlusTwo
main | steps x (done _ _) = putStrLn "it worked!"
main | steps x out-of-gas = putStrLn "out of gas..."
main | error              = putStrLn "something went wrong..."
\end{code}
