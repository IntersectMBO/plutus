{-# LANGUAGE TemplateHaskell #-}

module PlutusTx.NatRatio.TH (nr) where

import           Language.Haskell.TH.Quote  (QuasiQuoter (QuasiQuoter))
import           Language.Haskell.TH.Syntax (Dec, Exp (AppE, ConE, LitE, UInfixE, VarE), Lit (IntegerL), Pat, Q, Type)
import           PlutusTx.NatRatio.Internal (NatRatio (NatRatio))
import           PlutusTx.Ratio             ((%))
import           Prelude
import           Text.Read                  (readMaybe)

{- | Quasi-quoter for 'NatRatio' literals.

 Used as follows:

 > [nr| (10, 100) |]
-}
nr :: QuasiQuoter
nr = QuasiQuoter nrExp errorPat errorType errorDeclaration

-- Helpers

nrExp :: String -> Q Exp
nrExp s = case readMaybe s of
  Nothing -> fail $ "Input should be of the form (n, m), but got: " <> s
  Just (n :: Integer, m :: Integer) -> case signum m of
    (-1) -> fail "Cannot use a negative literal for a NatRatio denominator."
    0 -> fail "A NatRatio cannot have denominator 0."
    _ -> case signum n of
      (-1) -> fail "Cannot use a negative literal for a NatRatio numerator."
      _ ->
        pure
          . AppE (ConE 'NatRatio)
          . UInfixE (LitE . IntegerL $ n) (VarE '(%))
          . LitE
          . IntegerL
          $ m

errorPat :: String -> Q Pat
errorPat _ = fail "Cannot use 'nr' in a pattern context."

errorType :: String -> Q Type
errorType _ = fail "Cannot use 'nr' in a type context."

errorDeclaration :: String -> Q [Dec]
errorDeclaration _ = fail "Cannot use 'nr' in a declaration context."
