# Costs


This module contains the basic definitions and structures for modelling costs.

```

module Cost where 

```

## Imports

```
open import Function using (_∘_)
open import Data.Bool using (if_then_else_)
open import Data.Fin using (Fin;zero;suc)
open import Data.Integer using (+_)
open import Data.Nat using (ℕ;zero;suc;_+_;_*_;_∸_;_⊔_;_⊓_;_<ᵇ_;_≡ᵇ_)
open import Data.Nat.DivMod using (_/_)
open import Data.Nat.Properties using (+-assoc;+-identityʳ)
open import Data.Nat.Show using () renaming (show to showℕ)
open import Data.Integer using (ℤ;∣_∣)
open import Data.Float using (Float;fromℕ;_÷_;_≤ᵇ_) renaming (show to show𝔽;_*_ to _*f_)
import Data.List as L

open import Data.Maybe using (Maybe;just;nothing;maybe′;fromMaybe) renaming (map to mapMaybe; _>>=_ to _>>=m_ )
open import Data.Product using () renaming (_,_ to _,,_)
open import Data.String using (String;_++_;padLeft;padRight;length)
open import Data.Vec using (Vec;replicate;[];_∷_;sum;foldr) 
                     renaming (lookup to lookupVec)
open import Algebra using (IsMonoid)
open import Relation.Nullary using (yes;no)
open import Relation.Binary.PropositionalEquality using (_≡_;refl;isEquivalence;cong₂)
open import Text.Printf using (printf)

open import Utils using (_×_;_,_;_∷_;[];DATA;List;map;ByteString)
open DATA

open import Relation.Binary using (StrictTotalOrder)
open import Data.Char using (_≈ᵇ_)
open import Data.String.Properties using (<-strictTotalOrder-≈)
open import Data.Tree.AVL.Map <-strictTotalOrder-≈ as AVL 
          using (Map;empty;unionWith;singleton) 
          renaming (lookup to lookupAVL)
open import Builtin using (Builtin;showBuiltin;builtinList;lengthBS;arity)
open Builtin.Builtin
open import Builtin.Signature using (_⊢♯)
open _⊢♯
open import RawU using (TmCon) 
open TmCon
open import Builtin.Constant.AtomicType using (AtomicTyCon)
open AtomicTyCon

open import Cost.Base 
open import Cost.Model
```

## Interface with Haskell Machine Parameters

```
{-# FOREIGN GHC import Data.SatInt (fromSatInt) #-}
{-# FOREIGN GHC import Data.Functor.Identity (Identity, runIdentity) #-}
{-# FOREIGN GHC import PlutusCore.Evaluation.Machine.ExBudget (ExBudget(..))  #-}
{-# FOREIGN GHC import PlutusCore.Evaluation.Machine.ExMemory (ExCPU(..), ExMemory(..)) #-}
{-# FOREIGN GHC import PlutusCore.Evaluation.Machine.ExBudgetingDefaults (defaultCekMachineCosts) #-}
{-# FOREIGN GHC import UntypedPlutusCore.Evaluation.Machine.Cek.CekMachineCosts (CekMachineCostsBase(..)) #-}

postulate HCekMachineCosts : Set 
postulate HExBudget : Set 

{-# COMPILE GHC HCekMachineCosts = type CekMachineCostsBase Identity #-}
{-# COMPILE GHC HExBudget = type ExBudget #-}

postulate getCekStartupCost : HCekMachineCosts →  HExBudget
postulate getCekVarCost     : HCekMachineCosts →  HExBudget
postulate getCekConstCost   : HCekMachineCosts →  HExBudget
postulate getCekLamCost     : HCekMachineCosts →  HExBudget
postulate getCekDelayCost   : HCekMachineCosts →  HExBudget
postulate getCekForceCost   : HCekMachineCosts →  HExBudget
postulate getCekApplyCost   : HCekMachineCosts →  HExBudget
postulate getCekBuiltinCost : HCekMachineCosts →  HExBudget
postulate getCekConstrCost  : HCekMachineCosts →  HExBudget
postulate getCekCaseCost    : HCekMachineCosts →  HExBudget

{-# COMPILE GHC getCekStartupCost = runIdentity . cekStartupCost  #-}
{-# COMPILE GHC getCekVarCost     = runIdentity . cekVarCost      #-}
{-# COMPILE GHC getCekConstCost   = runIdentity . cekConstCost    #-}
{-# COMPILE GHC getCekLamCost     = runIdentity . cekLamCost      #-}
{-# COMPILE GHC getCekDelayCost   = runIdentity . cekDelayCost    #-}
{-# COMPILE GHC getCekForceCost   = runIdentity . cekForceCost    #-}
{-# COMPILE GHC getCekApplyCost   = runIdentity . cekApplyCost    #-}
{-# COMPILE GHC getCekBuiltinCost = runIdentity . cekBuiltinCost  #-}
{-# COMPILE GHC getCekConstrCost  = runIdentity . cekConstrCost   #-}
{-# COMPILE GHC getCekCaseCost    = runIdentity . cekCaseCost     #-}

postulate getCPUCost : HExBudget → CostingNat
postulate getMemoryCost : HExBudget → CostingNat

{-# COMPILE GHC getCPUCost = fromSatInt . (\(ExCPU x) -> x) . exBudgetCPU  #-}
{-# COMPILE GHC getMemoryCost = fromSatInt . (\(ExMemory x) -> x) . exBudgetMemory  #-}

postulate defaultHCekMachineCosts : HCekMachineCosts

{-# COMPILE GHC defaultHCekMachineCosts = defaultCekMachineCosts #-}
``` 

## Execution Budget

An execution budget consist of two costs: CPU and memory costs.

```
record ExBudget : Set where
  constructor mkExBudget 
  field
    ExCPU : CostingNat -- CPU usage
    ExMem : CostingNat -- Memory usage

open ExBudget

fromHExBudget : HExBudget → ExBudget 
fromHExBudget hb = mkExBudget (getCPUCost hb) (getMemoryCost hb)
```

The type for execution budget should be a Monoid.
We show that this is the case for `ExBudget`.

```
-- unit of the monoid
ε€ : ExBudget 
ε€ = mkExBudget 0 0 

-- binary operation
_∙€_ : ExBudget → ExBudget → ExBudget 
(mkExBudget xCPU xMem) ∙€ (mkExBudget yCPU yMem) = mkExBudget (xCPU + yCPU) (xMem + yMem)

-- Note: working with `Monoid` instances would imply working in Set₁, so we avoid it
-- and just state that `ExBudget` is a Monoid

isMonoidExBudget : IsMonoid _≡_ _∙€_ ε€
isMonoidExBudget = record { 
       isSemigroup = record { 
           isMagma = record { isEquivalence = isEquivalence ; ∙-cong = λ {refl refl → refl }} 
           ; assoc = λ x y z → cong₂ mkExBudget (+-assoc (ExCPU x) (ExCPU y) (ExCPU z)) 
                                                (+-assoc (ExMem x) (ExMem y) (ExMem z)) } 
     ; identity = (λ x → refl) ,, λ x → cong₂ mkExBudget (+-identityʳ (ExCPU x)) (+-identityʳ (ExMem x)) }
``` 

## Memory usage of type constants

For each type constant we calculate its size, as a measure of memory usage.

First we bring some functions from Haskell world.

```
postulate ℕtoWords : ℤ → CostingNat 
postulate g1ElementCost : CostingNat
postulate g2ElementCost : CostingNat
postulate mlResultElementCost : CostingNat 

{-# FOREIGN GHC {-# LANGUAGE MagicHash #-} #-}
{-# FOREIGN GHC import GHC.Exts (Int (I#)) #-}
{-# FOREIGN GHC import GHC.Integer  #-}
{-# FOREIGN GHC import GHC.Integer.Logarithms  #-}
{-# FOREIGN GHC import GHC.Prim #-}
{-# FOREIGN GHC import PlutusCore.Crypto.BLS12_381.G1 as BLS12_381.G1 #-}
{-# FOREIGN GHC import PlutusCore.Crypto.BLS12_381.G2 as BLS12_381.G2 #-}
{-# FOREIGN GHC import PlutusCore.Crypto.BLS12_381.Pairing as BLS12_381.Pairing #-}

{-# COMPILE GHC ℕtoWords = \i -> fromIntegral $ I# (integerLog2# (abs i) `quotInt#` integerToInt 64) + 1 #-}
{-# COMPILE GHC g1ElementCost = toInteger (BLS12_381.G1.memSizeBytes `div` 8) #-}
{-# COMPILE GHC g2ElementCost = toInteger (BLS12_381.G2.memSizeBytes `div` 8) #-}
{-# COMPILE GHC mlResultElementCost = toInteger (BLS12_381.Pairing.mlResultMemSizeBytes `div` 8) #-}
```

For each constant we return the corresponding size.

```
byteStringSize : ByteString → CostingNat 
byteStringSize x = let n = ∣ lengthBS x ∣ in ((n ∸ 1) / 8) + 1

-- cost of a Data node
dataNodeMem : CostingNat 
dataNodeMem = 4

sizeData : DATA → CostingNat 
sizeDataList : List DATA → CostingNat 
sizeDataDataList : List (DATA × DATA) → CostingNat

sizeData (ConstrDATA _ xs) = dataNodeMem + sizeDataList xs
sizeData (MapDATA []) = dataNodeMem
sizeData (MapDATA xs) = dataNodeMem + sizeDataDataList xs
sizeData (ListDATA xs) = dataNodeMem + sizeDataList xs
sizeData (iDATA x) = dataNodeMem +  ℕtoWords x
sizeData (bDATA x) = dataNodeMem + byteStringSize x 

-- The following tow functions are stupid but
-- they make the termination checker happy
sizeDataDataList [] = 0
sizeDataDataList ((x , y) ∷ xs) = sizeData x + sizeData y + sizeDataDataList xs

sizeDataList [] = 0
sizeDataList (x ∷ xs) = sizeData x + sizeDataList xs

-- This the main sizing function for constants
defaultConstantMeasure : TmCon → CostingNat
defaultConstantMeasure (tmCon (atomic aInteger) x) = ℕtoWords x
defaultConstantMeasure (tmCon (atomic aBytestring) x) = byteStringSize x
defaultConstantMeasure (tmCon (atomic aString) x) = length x -- each Char costs 1
defaultConstantMeasure (tmCon (atomic aUnit) x) = 1
defaultConstantMeasure (tmCon (atomic aBool) x) = 1
defaultConstantMeasure (tmCon (atomic aData) d) = sizeData d
defaultConstantMeasure (tmCon (atomic aBls12-381-g1-element) x) = g1ElementCost
defaultConstantMeasure (tmCon (atomic aBls12-381-g2-element) x) = g2ElementCost
defaultConstantMeasure (tmCon (atomic aBls12-381-mlresult) x) = mlResultElementCost
defaultConstantMeasure (tmCon (list t) []) = 0
defaultConstantMeasure (tmCon (list t) (x ∷ xs)) = 
       defaultConstantMeasure (tmCon t x) 
     + defaultConstantMeasure (tmCon (list t) xs)
defaultConstantMeasure (tmCon (pair t u) (x , y)) = 
      1 + defaultConstantMeasure (tmCon t x) 
        + defaultConstantMeasure (tmCon u y)
```

## Cost of executing a builtin

To calculate the cost of a builtin we obtain the corresponding builtin model, 
and run the cpu and memory model using the vector of argument sizes.

```
builtinCost : (b : Builtin) → BuiltinModel (arity b) → Vec CostingNat (arity b) → ExBudget
builtinCost b bc cs = mkExBudget (runModel (costingCPU bc) cs) (runModel (costingMem bc) cs)
``` 


## Default Machine Parameters

The machine parameters for `ExBudget` for a given Cost Model

```
CostModel = HCekMachineCosts × ModelAssignment

cekMachineCostFunction : HCekMachineCosts → StepKind → ExBudget
cekMachineCostFunction mc BConst = fromHExBudget (getCekConstCost mc)
cekMachineCostFunction mc BVar = fromHExBudget (getCekVarCost mc)
cekMachineCostFunction mc BLamAbs = fromHExBudget (getCekLamCost mc)
cekMachineCostFunction mc BApply = fromHExBudget (getCekApplyCost mc)
cekMachineCostFunction mc BDelay = fromHExBudget (getCekDelayCost mc)
cekMachineCostFunction mc BForce = fromHExBudget (getCekForceCost mc)
cekMachineCostFunction mc BBuiltin = fromHExBudget (getCekBuiltinCost mc)
cekMachineCostFunction mc BConstr = fromHExBudget (getCekConstCost mc)
cekMachineCostFunction mc BCase = fromHExBudget (getCekCaseCost mc)

exBudgetCategoryCost' : CostModel → ExBudgetCategory → ExBudget 
exBudgetCategoryCost' (cekMc , _) (BStep x) = cekMachineCostFunction cekMc x
exBudgetCategoryCost' (_ , ma) (BBuiltinApp b cs) = builtinCost b (ma b) cs
exBudgetCategoryCost' (cekMc , _) BStartup = fromHExBudget (getCekStartupCost cekMc)

machineParameters : CostModel → MachineParameters ExBudget
machineParameters costmodel = record {
    cekMachineCost = exBudgetCategoryCost' costmodel
  ; ε = ε€
  ; _∙_ = _∙€_
  ; costMonoid = isMonoidExBudget
  ; constantMeasure = defaultConstantMeasure 
 } 

exBudgetCategoryCost : ModelAssignment → ExBudgetCategory → ExBudget 
exBudgetCategoryCost ma = exBudgetCategoryCost' (defaultHCekMachineCosts , ma)

defaultMachineParameters : ModelAssignment → MachineParameters ExBudget
defaultMachineParameters assignModel = record {
    cekMachineCost = exBudgetCategoryCost assignModel
  ; ε = ε€
  ; _∙_ = _∙€_
  ; costMonoid = isMonoidExBudget
  ; constantMeasure = defaultConstantMeasure 
 } 

countingReport : ExBudget → String 
countingReport (mkExBudget cpu mem) = 
      "\nCPU budget:    " ++ showℕ cpu 
   ++ "\nMemory budget: " ++ showℕ mem
```
 ## Tallying budget 

These functions define a type for Budgets that can record detailed cost information
about nodes and builtins.

We need a map from `ExBudgetCategory` into `ExBudget`. 
It's not the most efficient, but the simplest thing to do is to 
transform `ExBudgetCategory` into a string, and use that as keys.

```
mkKeyFromExBudgetCategory : ExBudgetCategory → String 
mkKeyFromExBudgetCategory (BStep x) = "0" ++ showStepKind x
mkKeyFromExBudgetCategory (BBuiltinApp x _) = "1"++ showBuiltin x
mkKeyFromExBudgetCategory BStartup = "2"

TallyingBudget : Set 
TallyingBudget = Map ExBudget × ExBudget

lookup : Map ExBudget → ExBudgetCategory → ExBudget
lookup m k with lookupAVL (mkKeyFromExBudgetCategory k) m 
... | just x = x
... | nothing = ε€
```

As required, `TallyingBudget` is a monoid. 

```
--unit of TallyingBudget 
εT : TallyingBudget
εT = empty , ε€

-- adding TallyingBudgets
_∙T_ : TallyingBudget → TallyingBudget → TallyingBudget
(m , x) ∙T (n , y) = unionWith u m n , (x ∙€ y)
   where u : ExBudget → Maybe (ExBudget) → ExBudget
         u x (just y) = x ∙€ y
         u x nothing = x

-- TODO : Prove these postulates.
postulate TallyingBudget-assoc : Algebra.Associative _≡_ _∙T_
postulate Tallying-budget-identityʳ : Algebra.RightIdentity _≡_ εT _∙T_

isMonoidTallyingBudget : IsMonoid _≡_ _∙T_ εT
isMonoidTallyingBudget = record { 
       isSemigroup = record { 
           isMagma = record { isEquivalence = isEquivalence 
                            ; ∙-cong = λ {refl refl → refl }} 
           ; assoc = TallyingBudget-assoc } 
     ; identity = (λ x → refl) ,, Tallying-budget-identityʳ }


tallyingCekMachineCost' : CostModel → ExBudgetCategory → TallyingBudget
tallyingCekMachineCost' cm k = 
      let spent = exBudgetCategoryCost' cm k 
      in singleton (mkKeyFromExBudgetCategory k) spent , spent

tallyingMachineParameters' : CostModel → MachineParameters TallyingBudget
tallyingMachineParameters' cm = record { 
        cekMachineCost = tallyingCekMachineCost' cm
      ; ε = εT
      ; _∙_ = _∙T_
      ; costMonoid = isMonoidTallyingBudget
      ; constantMeasure = defaultConstantMeasure
      } 

tallyingCekMachineCost : ModelAssignment → ExBudgetCategory → TallyingBudget
tallyingCekMachineCost am k = 
      let spent = exBudgetCategoryCost am k 
      in singleton (mkKeyFromExBudgetCategory k) spent , spent

tallyingMachineParameters : ModelAssignment → MachineParameters TallyingBudget
tallyingMachineParameters am = record { 
        cekMachineCost = tallyingCekMachineCost am
      ; ε = εT
      ; _∙_ = _∙T_
      ; costMonoid = isMonoidTallyingBudget
      ; constantMeasure = defaultConstantMeasure
      } 

tallyingReport : TallyingBudget → String
tallyingReport (mp , budget) =  
       countingReport budget
    ++ "\n"
    ++ "\n"
    ++ printStepReport mp
    ++ "\n"
    ++ "startup    " ++ budgetToString (lookup mp BStartup) ++ "\n"
    ++ "compute    " ++ budgetToString totalComputeCost ++ "\n"
    -- ++ "AST nodes  " ++ ++ "\n"
    ++ "\n\n"
    ++ printBuiltinReport mp 
    ++ "\n" 
    ++ "Total builtin costs:   " ++ budgetToString totalBuiltinCosts ++ "\n"
     -- We would like to be able to print the following  number as "%4.2f" 
     -- but Agda's printf currently doesn't support it.
    ++ printf "Time spent executing builtins:  %f%%\n" (fromℕ 100 *f (getCPU totalBuiltinCosts) ÷ (getCPU budget)) ++ "\n"
    ++ "\n"
    ++ "Total budget spent:    " ++ budgetToString budget ++ "\n"
    ++  "Predicted execution time: " ++ formatTimePicoseconds (getCPU budget)
  where 
    totalComputeCost totalBuiltinCosts : ExBudget 
    totalComputeCost = L.foldr (λ x acc → (lookup mp (BStep x)) ∙€ acc) ε€ stepKindList
    totalBuiltinCosts = L.foldr _∙€_ ε€ (L.map (lookup mp ∘ (λ b → BBuiltinApp b (replicate 0))) builtinList)

    getCPU : ExBudget → Float
    getCPU n = fromℕ (ExCPU n)   

    budgetToString : ExBudget → String 
    budgetToString (mkExBudget cpu mem) = padLeft ' ' 15 (showℕ cpu) ++ "  " 
                                       ++ padLeft ' ' 15 (showℕ mem)

    printStepCost : StepKind → ExBudget → String
    printStepCost sk budget = padRight ' ' 10 (showStepKind sk) ++ " " 
                           ++ padLeft ' ' 20 (budgetToString budget) ++ "\n"

    printStepReport : Map ExBudget → String 
    printStepReport mp = L.foldr (λ s xs → printStepCost s (lookup mp (BStep s)) ++ xs)
                               "" 
                               stepKindList

    printBuiltinCost : Builtin → ExBudget → String 
    printBuiltinCost b (mkExBudget 0 0) = "" 
    printBuiltinCost b budget = padRight ' ' 22 (showBuiltin b) ++ " " 
                             ++ budgetToString budget ++ "\n"

    printBuiltinReport : Map ExBudget → String 
    printBuiltinReport mp = 
        L.foldr (λ b xs → printBuiltinCost b (lookup mp (BBuiltinApp b (replicate 0))) ++ xs) 
              "" 
              builtinList     
    
    formatTimePicoseconds : Float → String
    formatTimePicoseconds t = if 1e12 ≤ᵇ t then (printf "%f s" (t ÷ 1e12)) else
                              if 1e9 ≤ᵇ t then  (printf "%f ms" (t ÷ 1e9)) else
                              if 1e6 ≤ᵇ t then  (printf "%f μs" (t ÷ 1e6)) else
                              if 1e3 ≤ᵇ t then  (printf "%f ns" (t ÷ 1e3)) else
                              printf "%f ps" t
 ```
