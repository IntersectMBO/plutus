{-# LANGUAGE OverloadedStrings #-}

module Data.Text.Prettyprint.Doc.Custom ( brackets'
                                        , braces'
                                        , vsep'
                                        , parens'
                                        , (</>)
                                        , (<//>)
                                        ) where

import           Data.Text.Prettyprint.Doc

infixr 5 </>
infixr 5 <//>

-- | This operator prints @a@ and then prints @b@ indented on a new line
(<//>) :: Doc a -- ^ @a@
       -> Doc a -- ^ @b@
       -> Doc a
(<//>) d d' = d <> hardline <> indent 2 d'

-- | This prints both documents on the same line separated by a space if they
-- can fit, and behaves like '<//>' otherwise.
(</>) :: Doc a -> Doc a -> Doc a
(</>) d d' = group (flatAlt (d <//> d') (d <+> d'))

vsepSquish :: [Doc a] -> Doc a
vsepSquish = group . concatWith (\x y -> x <> line' <> y)

-- | This is the same as 'vsep', but it 'group's the output, so that documents
-- are printed on the same line when possible.
vsep' :: [Doc a] -> Doc a
vsep' = group . vsep

section :: Doc a -> Doc a -> Doc a -> Doc a
section c1 c2 d = group (flatAlt (c1 <> hardline <> indent 2 d <> hardline <> c2) (c1 <+> d <+> c2))

-- | This prints a document enclosed by brackets, possibly indenting the output on
-- a new line if it does not fit.
brackets' :: Doc a -> Doc a
brackets' = section "[" "]"

-- | This prints a document enclosed by braces, possibly indenting the output on
-- a new line if it does not fit.
braces' :: Doc a -> Doc a
braces' = section "{" "}"

-- | This prints a document enclosed by parentheses, aligning the opening and
-- closing parentheses.
parens' :: Doc a -> Doc a
parens' d = vsepSquish ["(" <> d, ")"]
