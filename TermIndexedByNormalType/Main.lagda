\begin{code}
module TermIndexedByNormalType.Main where
open import Agda.Builtin.IO
open import Agda.Builtin.Unit
open import Agda.Builtin.String

open import Type
open import Type.BetaNormal
open import TermIndexedByNormalType.Term
open import TermIndexedByNormalType.Evaluation
open import Builtin.Constant.Type
open import Builtin.Constant.Term

postulate
  putStrLn : String → IO ⊤

{-# FOREIGN GHC import qualified Data.Text.IO as Text #-}
{-# COMPILE GHC putStrLn = Text.putStrLn #-}

open import TermIndexedByNormalType.Examples

main : IO ⊤
main with eval (gas 100) TwoPlusTwo'
main | steps x (done _ _) = putStrLn "it worked!"
main | steps x out-of-gas = putStrLn "out of gas..."
\end{code}
