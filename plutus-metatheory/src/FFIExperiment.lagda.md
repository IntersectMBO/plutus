---
title: FFIExperiment
layout: page
---
```
module FFIExperiment where
```

## Imports

```
import Data.Bool.Base using (Bool; true; false; T; _∧_; _∨_; not)
open import Data.Nat using (ℕ; zero; suc)
open import Relation.Nullary using (Dec; yes; no; ¬_)
import Relation.Nullary.Decidable using (⌊_⌋; True; toWitness; fromWitness)
import Relation.Nullary.Negation using (¬?)
import Relation.Nullary.Product using (_×-dec_)
import Relation.Nullary.Sum using (_⊎-dec_)
import Relation.Binary using (Decidable)
open import Untyped
open import Utils as U using (Maybe;nothing;just;Either;inj₁;inj₂;Monad;DATA;List;[];_∷_)
open import RawU using (Untyped)
open import Data.String using (String;_++_)
open import Agda.Builtin.IO using (IO)
open import Agda.Builtin.Unit using (⊤;tt)
open import Function.Base using (id; _∘_ ; _∘′_; const; flip)
open Monad {{...}}
import IO.Primitive as IO using (return;_>>=_)
import Data.List as L
```

## Compiler certification component
```

postulate
  something : {X : Set} → List (X ⊢) → Dec (X ⊢)
  serializeProof : {X : Set} → Dec (X ⊢) → String

parseASTs : {X : Set} → List Untyped → Maybe (List (Maybe X ⊢))
parseASTs [] = nothing
parseASTs (x ∷ xs) with toWellScoped x 
...                | inj₁ _ = nothing
...                | inj₂ t with parseASTs xs
...                         | nothing = nothing
...                         | just ts = just (t ∷ ts)

postulate
  putStrLn : String → IO ⊤

{-# FOREIGN GHC import qualified Data.Text.IO as TextIO #-}
{-# COMPILE GHC putStrLn = TextIO.putStrLn #-}

postulate
  exitFailure : IO ⊤
  exitSuccess : IO ⊤

{-# FOREIGN GHC import System.Exit #-}
{-# COMPILE GHC exitSuccess = exitSuccess #-}
{-# COMPILE GHC exitFailure = exitFailure #-}

instance
  IOMonad : Monad IO
  IOMonad = record { return = IO.return; _>>=_ = IO._>>=_ }

postulate
  showUntyped : Untyped → String
{-# FOREIGN GHC import qualified Data.Text as Text #-}
{-# COMPILE GHC showUntyped = Text.pack . show #-}

-- TODO: this just prints the ASTs to test if the translation works
runCertifier : List Untyped → IO ⊤
runCertifier x =
  let result = L.foldr (λ t acc -> showUntyped t ++ "\n" ++ acc) "" (U.toList x) 
   in putStrLn result
-- TODO: this currently doesn't compile because it doesn't know the concrete type of X I think
-- runCertifier us with parseASTs us
-- ...             | nothing = putStrLn "Parse error" >> exitFailure
-- ...             | just asts =
--                     let result = (serializeProof ∘ something) asts
--                      in putStrLn "TODO"
{-# COMPILE GHC runCertifier as runCertifier #-}
