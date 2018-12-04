#line 6 "haskell"
{-# LANGUAGE TemplateHaskell     #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Tutorial where
import Language.PlutusTx
import Language.PlutusTx.Lift
import Language.PlutusCore
import Language.PlutusCore.Pretty
import Language.PlutusCore.Quote
import Language.PlutusCore.Evaluation.CkMachine
#line 32 "haskell"
-- |
-- >>> prettyPlcDef $ getAst integerOne
-- (program 1.0.0
--   (con 8 ! 1)
-- )
integerOne :: PlcCode
-- We don't like unbounded integers in Plutus Core, so we have to pin
-- down that numeric literal to an `Int` not an `Integer`.
integerOne = $$(plutus [|| (1 :: Int) ||])
#line 57 "haskell"
-- |
-- >>> prettyPlcDef $ getAst integerIdentity
-- (program 1.0.0
--   (lam ds [(con integer) (con 8)] ds)
-- )
integerIdentity :: PlcCode
integerIdentity = $$(plutus [|| \(x:: Int) -> x ||])
#line 74 "haskell"
plusOne :: Int -> Int
plusOne x = x + 1

functions :: PlcCode
functions = $$(plutus [||
    let
        plusOneLocal :: Int -> Int
        plusOneLocal x = x + 1
        -- This won't work.
        -- nonLocalDoesntWork = plusOne 1
        localWorks = plusOneLocal 1
        -- You can of course bind this to a name, but for the purposes
        -- of this tutorial we won't since TH requires it to be in
        -- another module.
        thWorks = $$([|| \(x::Int) -> x + 1 ||]) 1
    in localWorks + thWorks
    ||])
#line 103 "haskell"
matchMaybe :: PlcCode
matchMaybe = $$(plutus [|| \(x:: Maybe Int) -> case x of
    Just n -> n
    Nothing -> 0
   ||])
#line 117 "haskell"
data EndDate = Fixed Int | Never

shouldEnd :: PlcCode
shouldEnd = $$(plutus [|| \(end::EndDate) (current::Int) -> case end of
    Fixed n -> n <= current
    Never -> False
   ||])
#line 152 "haskell"
-- TODO: show PIR here too

-- |
-- >>> prettyPlcDef $ addOneToN 4
-- (program 1.0.0
--   [
--     [
--       (lam
--         addInteger
--         (fun [(con integer) (con 8)] (fun [(con integer) (con 8)] [(con integer) (con 8)]))
--         (lam ds [(con integer) (con 8)] [ [ addInteger ds ] (con 8 ! 1) ])
--       )
--       { (builtin addInteger) (con 8) }
--     ]
--     (con 8 ! 4)
--   ]
-- )

-- >>> prettyPlcDef $ runCk program
-- (con 8 ! 5)
addOneToN :: Int -> Program TyName Name ()
addOneToN n =
    let addOne = $$(plutus [|| \(x:: Int) -> x + 1 ||])
    in (getAst addOne) `applyProgram` unsafeLiftPlcProgram n
#line 195 "haskell"
makeLift ''EndDate

-- |
-- >>> let program = shouldEndAt Never 5
-- >>> prettyPlcDef $ runCk program
-- (abs
--   out_Bool (type) (lam case_True out_Bool (lam case_False out_Bool case_False))
-- )
shouldEndAt :: EndDate -> Int -> Program TyName Name ()
shouldEndAt end current =
    (getAst shouldEnd)
    `applyProgram`
    unsafeLiftPlcProgram end
    `applyProgram`
    unsafeLiftPlcProgram current
