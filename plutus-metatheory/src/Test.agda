module Test where

open import VerifiedCompilation
open import Untyped
open import RawU
open import Builtin
open import Data.Unit
open import Data.Nat
open import Data.Integer
open import Utils

-- this doesn't work for some reason ...
-- fromNat : ℕ → ℤ
-- fromNat = ℤ.pos
-- {-# BUILTIN FROMNAT fromNat #-}

a : Untyped
a = ULambda (UVar 0)

-- a = fromNat 1

-- x =
--     (UApp
--      (UApp
--       (UApp (ULambda (UApp (UVar 0) (UVar 0)))
--        (ULambda
--         (ULambda
--          (ULambda
--           (UApp (UApp (UForce (UVar 0)) (UVar 1))
--            (ULambda
--             (ULambda
--              (UApp
--               (UApp (ULambda (UApp (UApp (UVar 5) (UVar 5)) (UVar 0)))
--                (UApp (UApp (UBuiltin multiplyInteger) (UVar 3)) (UVar 1)))
--               (UVar 0)))))))))
--       (UCon (tagCon integer 1)))
--      (UApp
--       (UApp (ULambda (UApp (UVar 0) (UVar 0)))
--        (ULambda
--         (ULambda
--          (UApp
--           (ULambda
--            (UApp
--             (UApp
--              (UApp (UApp (UForce (UBuiltin ifThenElse)) (UVar 0))
--               (ULambda
--                (UApp
--                 (ULambda
--                  (UDelay
--                   (ULambda (ULambda (UApp (UApp (UVar 0) (UVar 5)) (UVar 2))))))
--                 (UApp (ULambda (UApp (UApp (UVar 4) (UVar 4)) (UVar 0)))
--                  (UApp (UApp (UBuiltin addInteger) (UVar 2))
--                   (UCon (tagCon integer 1)))))))
--              (ULambda (UDelay (ULambda (ULambda (UVar 1))))))
--             (UCon (tagCon unit ⊤))))
--           (UApp (UApp (UBuiltin lessThanEqualsInteger) (UVar 0))
--            (UCon (tagCon integer 2)))))))
--       (UCon (tagCon integer 1))))