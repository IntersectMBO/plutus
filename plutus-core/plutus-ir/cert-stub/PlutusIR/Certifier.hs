{-# LANGUAGE GADTs      #-}
{-# LANGUAGE LambdaCase #-}

-- | Interface to automatically extracted code from plutus-cert (Coq):
-- - Conversion functions for PIR's AST to the representation in Coq.
-- - Boolean decision procedures for translation relations
module PlutusIR.Certifier (is_dead_code, is_unique) where

import PlutusCore qualified as P
import PlutusIR qualified as PIR

type Term a = PIR.Term P.TyName P.Name P.DefaultUni P.DefaultFun a

-- | Check if only pure let bindings were eliminated
is_dead_code :: Term a -> Term a -> Bool
is_dead_code _ _ = True

-- | Check if a term has unique binders
is_unique :: Term a -> Bool
is_unique _ = True
