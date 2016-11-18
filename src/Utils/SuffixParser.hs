{-# OPTIONS -Wall #-}

module Utils.SuffixParser where

import Text.Parsec






infixl 9 >>=?

-- | The combinator '(>>=?)' makes it possible to easily define suffix parsers.
-- The idea here being that @X >>=? Y@ corresponds to roughly a grammar like
--
-- @
--    <S> ::= <X> | <X> <Y>
-- @
--
-- where the combined item is itself a distinct sort of thing. A good example
-- is a function type. Consider the miniature grammar:
--
-- @
--    <type> ::= <function> | <parentype> | <tycon>
--    <parentype> ::= "(" <type> ")"
--    <tycon> ::= "Int" | "Bool"
--    <function> ::= (<parentype> | <tycon>) "->" <type>
-- @
--
-- The disjunction in @<type>@ is an issue for parse, leading to redundant
-- parsing, because a string that begins with a @<tycon>@, say, can be both
-- merely a @<tycon>@, eg the type @Int@ or it could be a function type, eg
-- @Int -> Bool@. This grammar will try the alternatives, and sometimes make
-- partial progress but then have to backtrack. Later alternatives will then
-- reparse the string, sometimes making the same parses, but now as part of a
-- different alternative. This is wasteful.
--
-- Instead, we can use '(>>=?)' to factor out the shared prefix and the
-- residual optional suffix, as with the grammar
--
-- @
--    <type> ::= <parentype> <functionSuffix>?
--             | <tycon> <functionSuffix>?
--    <parentype> ::= "(" <type> ")"
--    <functionSuffix> ::= "->" <type>
-- @

(>>=?) :: Parsec String u a -> (a -> Parsec String u a) -> Parsec String u a
p >>=? f =
  do x <- p
     option x (f x)




(<|>?) :: (a -> Parsec String u a)
       -> (a -> Parsec String u a)
       -> (a -> Parsec String u a)
p <|>? q = \x -> p x <|> q x