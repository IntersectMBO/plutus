{-# LANGUAGE OverloadedStrings #-}

module Prettyprinter.Custom
  ( brackets'
  , braces'
  , parens'
  , sexp
  , (<?>)
  , vcatHard
  ) where

import Prettyprinter

{-| An area bracketed by two delimiters. When on multiple lines the delimiters are not
indented but the content is. -}
section' :: Doc a -> Doc a -> Doc a -> Doc a
-- The subtlety here is that the nest call surrounds the first delimiter and the content, but not
-- the final one. This is because of how nest behaves, where it doesn't indent until it hits
-- the first line break. So we need to include the first delimiter so that the main content gets
-- indented, but not the final delimiter.
section' c1 c2 d = group $ nest 2 (c1 <> d) <> c2

{-| An area bracketed by two delimiters. When on one line, there are spaces between the delimiters
and the content, when on multiple lines the delimiters are not indented but the content is. -}
section :: Doc a -> Doc a -> Doc a -> Doc a
section c1 c2 = section' (c1 <> line) (line <> c2)

{-| This prints a document enclosed by brackets, possibly indenting the output on
a new line if it does not fit. -}
brackets' :: Doc a -> Doc a
brackets' = section "[" "]"

{-| This prints a document enclosed by braces, possibly indenting the output on
a new line if it does not fit. -}
braces' :: Doc a -> Doc a
braces' = section "{" "}"

{-| This prints a document enclosed by parentheses, aligning the opening and
closing parentheses. -}
parens' :: Doc a -> Doc a
parens' = section "(" ")"

-- | Print a "sexp", i.e. something like "(keyword arg1 ... argN)".
sexp :: Doc a -> [Doc a] -> Doc a
sexp a es =
  -- This is a bit funny, because we want the keyword to "stick" to the opening parenthesis
  -- when it's split over multiple lines. So we include it in the "initial" segment. But then
  -- we also have to have a space after that rather than no space. So we start with "(keyword"
  -- and a line-or-space, but end with a line-or-nothing and ")".
  -- However if @es@ is empty, then we don't want to insert a space right before @)@, so in that
  -- case we use line-or-nothing as well.
  section' ("(" <> a <> if null es then line' else line) (line' <> ")") (sep es)

{-| Lay out a sequence of documents vertically with forced lines between documents. Useful
for prettyprinting layout-sensitive things like let-bindings. -}
vcatHard :: [Doc ann] -> Doc ann
vcatHard = concatWith (\x y -> x <> hardline <> y)

{-| Separate two documents `p` and `q` and increase indentation if `q` has to be put on a new
line. Useful to e.g. pretty-print function application like `fun <?> sep arguments`. -}
(<?>) :: Doc ann -> Doc ann -> Doc ann
p <?> q = align . nest 2 $ sep [p, q]

infixr 6 <?>
