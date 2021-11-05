-- | TH operators for booleans that implement short-circuit as quasi-quoter expressions.
module PlutusTx.Bool.TH(
  and_if,
  or_if
) where

import Prelude

import Language.Haskell.Meta.Parse qualified as P
import Language.Haskell.TH
import Language.Haskell.TH.Quote

-- | QQ for list of @and@-expressions written with if-then-else.
-- It implements short circuit.
--
-- > [and_if| expr1, expr2, expr3, ... |]
--
-- where @exprN@ is valid haskell expression. It is expanded to:
--
-- > if expr1
-- >   then if expr2
-- >     then if expr3
-- >       then True
-- >       else False
-- >     else False
-- >   else False
and_if :: QuasiQuoter
and_if = listExpr "and_if" $ foldr (\e res -> CondE e res false) true

-- | QQ for list of @or@-expressions written with if-then-else.
-- It implements short circuit.
--
-- > [or_if| expr1, expr2, expr3, ... |]
--
-- where @exprN@ is valid haskell expression. It is expanded to:
--
-- > if expr1
-- >   then True
-- >   else if expr2
-- >     then True
-- >     else if expr3
-- >       then True
-- >       else False
or_if :: QuasiQuoter
or_if = listExpr "or_if" $ foldr (\e res -> CondE e true res) false

listExpr :: String -> ([Exp] -> Exp) -> QuasiQuoter
listExpr name f = qqExprExp $ \s -> do
  case P.parseExp $ mconcat ["[", s, "]"] of
    Right (ListE args) -> pure $ f args
    _                  -> fail $ mconcat [ "Not a list of comma separated ", name
                                        , "-expressions, failed to parse. "
                                        , "Use [|", name, "| expr1, expr2, expr3 |]"]

qqExprExp :: (String -> Q Exp) -> QuasiQuoter
qqExprExp f = QuasiQuoter
  { quoteExp = f
  , quotePat = undefined
  , quoteDec = undefined
  , quoteType = undefined
  }

true, false :: Exp
true = ConE $ mkName "True"
false = ConE $ mkName "False"

