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

(<//>) :: Doc a -> Doc a -> Doc a
(<//>) d d' = d <> hardline <> indent 2 d'

(</>) :: Doc a -> Doc a -> Doc a
(</>) d d' = group (flatAlt (d <//> d') (d <+> d'))

vsepSquish :: [Doc a] -> Doc a
vsepSquish = group . concatWith (\x y -> x <> line' <> y)

vsep' :: [Doc a] -> Doc a
vsep' = group . vsep

section :: Doc a -> Doc a -> Doc a -> Doc a
section c1 c2 d = group (flatAlt (c1 <> hardline <> indent 2 d <> hardline <> c2) (c1 <+> d <+> c2))

brackets' :: Doc a -> Doc a
brackets' = section "[" "]"

braces' :: Doc a -> Doc a
braces' = section "{" "}"

parens' :: Doc a -> Doc a
parens' = vsepSquish . (\d -> ["(" <> d, ")"])
