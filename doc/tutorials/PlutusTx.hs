-- BLOCK1
-- Necessary language extensions for the Plutus Tx compiler to work.
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE NoImplicitPrelude   #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell     #-}
module PlutusTx where

import qualified Language.PlutusCore.Universe as PLC
-- Main Plutus Tx module.
import           Language.PlutusTx
-- Additional support for lifting.
import           Language.PlutusTx.Lift
-- Builtin functions.
import           Language.PlutusTx.Builtins
-- The Plutus Tx Prelude, discussed further below.
import           Language.PlutusTx.Prelude

-- Setup for doctest examples.

-- $setup
-- >>> import Tutorial.PlutusTx
-- >>> import Language.PlutusTx
-- >>> import Language.PlutusCore
-- >>> import Language.PlutusCore.Evaluation.Machine.Ck
-- >>> import Data.Text.Prettyprint.Doc

-- BLOCK2
integerOne :: CompiledCode PLC.DefaultUni Integer
{- 'compile' turns the 'TExpQ Integer' into a
  'TExpQ (CompiledCode PLC.DefaultUni Integer)' and the splice
  inserts it into the program. -}
integerOne = $$(compile
    {- The quote has type 'TExpQ Integer'.
      We always use unbounded integers in Plutus Core, so we have to pin
      down this numeric literal to an ``Integer`` rather than an ``Int``. -}
    [|| (1 :: Integer) ||])

{- |
>>> pretty $ getPlc integerOne
(program 1.0.0
  (con 1)
)
-}
-- BLOCK3
integerIdentity :: CompiledCode PLC.DefaultUni (Integer -> Integer)
integerIdentity = $$(compile [|| \(x:: Integer) -> x ||])

{- |
>>> pretty $ getPlc integerIdentity
(program 1.0.0
  (lam ds (con integer) ds)
)
-}
-- BLOCK4
{- Functions which will be used in Plutus Tx programs should be marked
  with GHC’s 'INLINABLE' pragma. This is usually necessary for
  non-local functions to be usable in Plutus Tx blocks, as it instructs
  GHC to keep the information that the Plutus Tx compiler needs. While
  you may be able to get away with omitting it, it is good practice to
  always include it. -}
{-# INLINABLE plusOne #-}
plusOne :: Integer -> Integer
{- 'addInteger' comes from 'Language.PlutusTx.Builtins', and is
  mapped to the builtin integer addition function in Plutus Core. -}
plusOne x = x `addInteger` 1

{-# INLINABLE myProgram #-}
myProgram :: Integer
myProgram =
    let
        -- Local functions do not need to be marked as 'INLINABLE'.
        plusOneLocal :: Integer -> Integer
        plusOneLocal x = x `addInteger` 1

        localTwo = plusOneLocal 1
        externalTwo = plusOne 1
    in localTwo `addInteger` externalTwo

functions :: CompiledCode PLC.DefaultUni Integer
functions = $$(compile [|| myProgram ||])

{- We’ve used the CK evaluator for Plutus Core to evaluate the program
  and check that the result was what we expected. -}
{- |
>>> pretty $ unsafeEvaluateCk $ toTerm $ getPlc functions
(con 4)
-}
-- BLOCK5
matchMaybe :: CompiledCode PLC.DefaultUni (Maybe Integer -> Integer)
matchMaybe = $$(compile [|| \(x:: Maybe Integer) -> case x of
    Just n  -> n
    Nothing -> 0
  ||])
-- BLOCK6
-- | Either a specific end date, or "never".
data EndDate = Fixed Integer | Never

-- | Check whether a given time is past the end date.
pastEnd :: CompiledCode PLC.DefaultUni (EndDate -> Integer -> Bool)
pastEnd = $$(compile [|| \(end::EndDate) (current::Integer) -> case end of
    Fixed n -> n `lessThanEqInteger` current
    Never   -> False
  ||])
-- BLOCK7
-- | Check whether a given time is past the end date.
pastEnd' :: CompiledCode PLC.DefaultUni (EndDate -> Integer -> Bool)
pastEnd' = $$(compile [|| \(end::EndDate) (current::Integer) -> case end of
    Fixed n -> n < current
    Never   -> False
  ||])
-- BLOCK8
addOne :: CompiledCode PLC.DefaultUni (Integer -> Integer)
addOne = $$(compile [|| \(x:: Integer) -> x `addInteger` 1 ||])
-- BLOCK9
addOneToN :: Integer -> CompiledCode PLC.DefaultUni Integer
addOneToN n =
    addOne
    -- 'applyCode' applies one 'CompiledCode' to another.
    `applyCode`
    -- 'liftCode' lifts the argument 'n' into a
    -- 'CompiledCode PLC.DefaultUni Integer'.
    liftCode n

{- |
>>> pretty $ getPlc addOne
(program 1.0.0
  [
    (lam
      addInteger
      (fun (con integer) (fun (con integer) (con integer)))
      (lam ds (con integer) [ [ addInteger ds ] (con 1) ])
    )
    (lam
      arg
      (con integer)
      (lam arg (con integer) [ [ (builtin addInteger) arg ] arg ])
    )
  ]
)
>>> let program = getPlc $ addOneToN 4
>>> pretty program
(program 1.0.0
  [
    [
      (lam
        addInteger
        (fun (con integer) (fun (con integer) (con integer)))
        (lam ds (con integer) [ [ addInteger ds ] (con 1) ])
      )
      (lam
        arg
        (con integer)
        (lam arg (con integer) [ [ (builtin addInteger) arg ] arg ])
      )
    ]
    (con 4)
  ]
)
>>> pretty $ unsafeEvaluateCk $ toTerm program
(con 5)
-}
-- BLOCK10
-- 'makeLift' generates instances of 'Lift' automatically.
makeLift ''EndDate

pastEndAt :: EndDate -> Integer -> CompiledCode PLC.DefaultUni Bool
pastEndAt end current =
    pastEnd
    `applyCode`
    liftCode end
    `applyCode`
    liftCode current

{- |
>>> let program = getPlc $ pastEndAt Never 5
>>> pretty $ unsafeEvaluateCk $ toTerm program
(abs
  out_Bool (type) (lam case_True out_Bool (lam case_False out_Bool case_False))
)
-}
-- BLOCK11
