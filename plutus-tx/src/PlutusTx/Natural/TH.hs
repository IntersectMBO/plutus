{-# LANGUAGE TemplateHaskell #-}

module PlutusTx.Natural.TH (nat) where

import           Language.Haskell.TH.Quote  (QuasiQuoter (QuasiQuoter))
import           Language.Haskell.TH.Syntax (Dec, Exp (AppE, ConE, LitE), Lit (IntegerL), Pat (ConP, LitP), Q, Type)
import           PlutusTx.Natural.Internal  (Natural (Natural))
import           Prelude
import           Text.Read                  (readMaybe)

{- | Quasi-quoter for 'Natural' literals.

 Used as follows:

 > [nat| 1234 |]

 > case foo of
 >    [nat| 0 |] -> ...
 >    [nat| 1 |] -> ...
-}
nat :: QuasiQuoter
nat = QuasiQuoter natExp natPat errorType errorDeclaration

-- Helpers

natExp :: String -> Q Exp
natExp s = case readMaybe s of
  Nothing -> fail $ "Not a valid Natural: " <> s
  Just (i :: Integer) -> case signum i of
    (-1) -> fail "Cannot use a negative literal for a Natural."
    _    -> pure . AppE (ConE 'Natural) . LitE . IntegerL $ i

natPat :: String -> Q Pat
natPat s = case readMaybe s of
  Nothing -> fail $ "Not a valid Natural: " <> s
  Just (i :: Integer) -> case signum i of
    (-1) -> fail "Cannot use a negative literal for a Natural."
    _    -> pure . ConP 'Natural $ [LitP . IntegerL $ i]

errorType :: String -> Q Type
errorType _ = fail "Cannot use 'nat' in a type context."

errorDeclaration :: String -> Q [Dec]
errorDeclaration _ = fail "Cannot use 'nat' in a declaration context."
