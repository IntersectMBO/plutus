-- This code is copied from https://github.com/f-o-a-m/purescript-optparse/blob/master/src/Text/PrettyPrint/Leijen.purs
-- as it wasn't available for download at the time of writing

-- This is port of https://github.com/ekmett/ansi-wl-pprint to ps without any ansi stuff as it's 
-- used by optparser, later we shuold use [prettyprinter](https://hackage.haskell.org/package/prettyprinter) once
-- [this](https://github.com/pcapriotti/optparse-applicative/issues/273) is fixed.
-- Also see [this](https://github.com/ekmett/ansi-wl-pprint/issues/18)
module Text.PrettyPrint.Leijen where

import Prelude hiding ((<$>))

import Data.Array as Array
import Data.Foldable (foldr, intercalate)
import Data.Generic.Rep (class Generic)
import Data.Generic.Rep.Show (genericShow)
import Data.Int as Int
import Data.List as List
import Data.List.Lazy as LL
import Data.Maybe (Maybe(..))
import Data.Monoid (class Monoid, mempty)
import Data.String (split)
import Data.String.CodeUnits (fromCharArray)
import Data.String as String
import Partial.Unsafe (unsafeCrashWith)
-----------------------------------------------------------
-- list, tupled and semiBraces pretty print a list of
-- documents either horizontally or vertically aligned.
-----------------------------------------------------------

-- | The document @(list xs)@ comma separates the documents @xs@ and
-- encloses them in square brackets. The documents are rendered
-- horizontally if that fits the page. Otherwise they are aligned
-- vertically. All comma separators are put in front of the elements.
list :: Array Doc -> Doc
list            = encloseSep lbracket rbracket comma

-- | The document @(tupled xs)@ comma separates the documents @xs@ and
-- encloses them in parenthesis. The documents are rendered
-- horizontally if that fits the page. Otherwise they are aligned
-- vertically. All comma separators are put in front of the elements.
tupled :: Array Doc -> Doc
tupled          = encloseSep lparen   rparen  comma

-- | The document @(semiBraces xs)@ separates the documents @xs@ with
-- semicolons and encloses them in braces. The documents are rendered
-- horizontally if that fits the page. Otherwise they are aligned
-- vertically. All semicolons are put in front of the elements.
semiBraces :: Array Doc -> Doc
semiBraces      = encloseSep lbrace   rbrace  semi

-- | The document @(encloseSep l r sep xs)@ concatenates the documents
-- @xs@ separated by @sep@ and encloses the resulting document by @l@
-- and @r@. The documents are rendered horizontally if that fits the
-- page. Otherwise they are aligned vertically. All separators are put
-- in front of the elements. For example, the combinator 'list' can be
-- defined with @encloseSep@:
--
-- > list xs = encloseSep lbracket rbracket comma xs
-- > test    = text "list" <+> (list (map int [10,200,3000]))
--
-- Which is layed out with a page width of 20 as:
--
-- @
-- list [10,200,3000]
-- @
--
-- But when the page width is 15, it is layed out as:
--
-- @
-- list [10
--      ,200
--      ,3000]
-- @
encloseSep :: Doc -> Doc -> Doc -> Array Doc -> Doc
encloseSep left right sep' ds = case ds of
  []  -> left <> right
  [d] -> left <> d <> right
  _   -> align (cat (LL.toUnfoldable $ LL.zipWith (<>) (left LL.: LL.repeat sep') (LL.fromFoldable ds)) <> right)

-----------------------------------------------------------
-- punctuate p [d1,d2,...,dn] => [d1 <> p,d2 <> p, ... ,dn]
-----------------------------------------------------------

-- | @(punctuate p xs)@ concatenates all documents in @xs@ with
-- document @p@ except for the last document.
--
-- > someText = map text ["words","in","a","tuple"]
-- > test     = parens (align (cat (punctuate comma someText)))
--
-- This is layed out on a page width of 20 as:
--
-- @
-- (words,in,a,tuple)
-- @
--
-- But when the page width is 15, it is layed out as:
--
-- @
-- (words,
--  in,
--  a,
--  tuple)
-- @
--
-- (If you want put the commas in front of their elements instead of
-- at the end, you should use 'tupled' or, in general, 'encloseSep'.)
punctuate :: Doc -> Array Doc -> Array Doc
punctuate p arr  = let lastIdx = Array.length arr - 1
  in Array.mapWithIndex (\idx d -> if lastIdx == idx then d else d <> p) arr


-----------------------------------------------------------
-- high-level combinators
-----------------------------------------------------------

-- | The document @(sep xs)@ concatenates all documents @xs@ either
-- horizontally with @(\<+\>)@, if it fits the page, or vertically with
-- @(\<$\>)@.
--
-- > sep xs  = group (vsep xs)
sep :: Array Doc -> Doc
sep             = group <<< vsep

foldr1 :: forall a. Monoid a => (a -> a -> a) -> Array a -> a
foldr1 f = Array.unsnoc >>> case _ of
  Nothing -> mempty
  Just { init, last } -> foldr f last init
-- | The document @(fillSep xs)@ concatenates documents @xs@
-- horizontally with @(\<+\>)@ as long as its fits the page, than
-- inserts a @line@ and continues doing that for all documents in
-- @xs@.
--
-- > fillSep xs  = foldr (</>) empty xs
fillSep :: Array Doc -> Doc
fillSep         = foldr1 (</>)

-- | The document @(hsep xs)@ concatenates all documents @xs@
-- horizontally with @(\<+\>)@.
hsep :: Array Doc -> Doc
hsep            = foldr1 (<+>)

-- | The document @(vsep xs)@ concatenates all documents @xs@
-- vertically with @(\<$\>)@. If a 'group' undoes the line breaks
-- inserted by @vsep@, all documents are separated with a space.
--
-- > someText = map text (words ("text to lay out"))
-- >
-- > test     = text "some" <+> vsep someText
--
-- This is layed out as:
--
-- @
-- some text
-- to
-- lay
-- out
-- @
--
-- The 'align' combinator can be used to align the documents under
-- their first element
--
-- > test     = text "some" <+> align (vsep someText)
--
-- Which is printed as:
--
-- @
-- some text
--      to
--      lay
--      out
-- @
vsep :: Array Doc -> Doc
vsep = foldr1 (<$>)

-- | The document @(cat xs)@ concatenates all documents @xs@ either
-- horizontally with @(\<\>)@, if it fits the page, or vertically with
-- @(\<$$\>)@.
--
-- > cat xs  = group (vcat xs)
cat :: Array Doc -> Doc
cat = group <<< vcat

-- | The document @(fillCat xs)@ concatenates documents @xs@
-- horizontally with @(\<\>)@ as long as its fits the page, than inserts
-- a @linebreak@ and continues doing that for all documents in @xs@.
--
-- > fillCat xs  = foldr1 (<//>) empty
fillCat :: Array Doc -> Doc
fillCat         = foldr1 (<//>)

-- | The document @(hcat xs)@ concatenates all documents @xs@
-- horizontally with @(\<\>)@.
hcat :: Array Doc -> Doc
hcat            = foldr1 (<>)

-- | The document @(vcat xs)@ concatenates all documents @xs@
-- vertically with @(\<$$\>)@. If a 'group' undoes the line breaks
-- inserted by @vcat@, all documents are directly concatenated.
vcat :: Array Doc -> Doc
vcat            = foldr1 (<$$>)

-- | The document @(x \<+\> y)@ concatenates document @x@ and @y@ with a
-- @space@ in between.  (infixr 6)
appendWithSpace :: Doc -> Doc -> Doc
appendWithSpace x y = x <> space <> y
infixr 6 appendWithSpace as <+>

-- | The document @(x \<\/\> y)@ concatenates document @x@ and @y@ with a
-- 'softline' in between. This effectively puts @x@ and @y@ either
-- next to each other (with a @space@ in between) or underneath each
-- other. (infixr 5)
appendWithSoftline :: Doc -> Doc -> Doc
appendWithSoftline x y = x <> softline <> y
infixr 5 appendWithSoftline as </>

-- | The document @(x \<\/\/\> y)@ concatenates document @x@ and @y@ with
-- a 'softbreak' in between. This effectively puts @x@ and @y@ either
-- right next to each other or underneath each other. (infixr 5)
appendWithSoftbreak :: Doc -> Doc -> Doc
appendWithSoftbreak x y = x <> softbreak <> y
infixr 5 appendWithSoftbreak as <//>

-- | The document @(x \<$\> y)@ concatenates document @x@ and @y@ with a
-- 'line' in between. (infixr 5)
appendWithLine :: Doc -> Doc -> Doc
appendWithLine x y = x <> line <> y
infixr 5 appendWithLine as <$>

-- | The document @(x \<$$\> y)@ concatenates document @x@ and @y@ with
-- a @linebreak@ in between. (infixr 5)
appendWithLinebreak :: Doc -> Doc -> Doc
appendWithLinebreak x y = x <> linebreak <> y
infixr 5 appendWithLinebreak as <$$>

-- | The document @softline@ behaves like 'space' if the resulting
-- output fits the page, otherwise it behaves like 'line'.
--
-- > softline = group line
softline :: Doc
softline        = group line

-- | The document @softbreak@ behaves like 'empty' if the resulting
-- output fits the page, otherwise it behaves like 'line'.
--
-- > softbreak  = group linebreak
softbreak :: Doc
softbreak       = group linebreak

-- | Document @(squotes x)@ encloses document @x@ with single quotes
-- \"'\".
squotes :: Doc -> Doc
squotes         = enclose squote squote

-- | Document @(dquotes x)@ encloses document @x@ with double quotes
-- '\"'.
dquotes :: Doc -> Doc
dquotes         = enclose dquote dquote

-- | Document @(braces x)@ encloses document @x@ in braces, \"{\" and
-- \"}\".
braces :: Doc -> Doc
braces          = enclose lbrace rbrace

-- | Document @(parens x)@ encloses document @x@ in parenthesis, \"(\"
-- and \")\".
parens :: Doc -> Doc
parens          = enclose lparen rparen

-- | Document @(angles x)@ encloses document @x@ in angles, \"\<\" and
-- \"\>\".
angles :: Doc -> Doc
angles          = enclose langle rangle

-- | Document @(brackets x)@ encloses document @x@ in square brackets,
-- \"[\" and \"]\".
brackets :: Doc -> Doc
brackets        = enclose lbracket rbracket

-- | The document @(enclose l r x)@ encloses document @x@ between
-- documents @l@ and @r@ using @(\<\>)@.
--
-- > enclose l r x   = l <> x <> r
enclose :: Doc -> Doc -> Doc -> Doc
enclose l r x   = l <> x <> r

-- | The document @lparen@ contains a left parenthesis, \"(\".
lparen :: Doc
lparen          = Char '('
-- | The document @rparen@ contains a right parenthesis, \")\".
rparen :: Doc
rparen          = Char ')'
-- | The document @langle@ contains a left angle, \"\<\".
langle :: Doc
langle          = Char '<'
-- | The document @rangle@ contains a right angle, \">\".
rangle :: Doc
rangle          = Char '>'
-- | The document @lbrace@ contains a left brace, \"{\".
lbrace :: Doc
lbrace          = Char '{'
-- | The document @rbrace@ contains a right brace, \"}\".
rbrace :: Doc
rbrace          = Char '}'
-- | The document @lbracket@ contains a left square bracket, \"[\".
lbracket :: Doc
lbracket        = Char '['
-- | The document @rbracket@ contains a right square bracket, \"]\".
rbracket :: Doc
rbracket        = Char ']'

-- | The document @squote@ contains a single quote, \"'\".
squote :: Doc
squote          = Char '\''
-- | The document @dquote@ contains a double quote, '\"'.
dquote :: Doc
dquote          = Char '"'
-- | The document @semi@ contains a semicolon, \";\".
semi :: Doc
semi            = Char ';'
-- | The document @colon@ contains a colon, \":\".
colon :: Doc
colon           = Char ':'
-- | The document @comma@ contains a comma, \",\".
comma :: Doc
comma           = Char ','
-- | The document @space@ contains a single space, \" \".
--
-- > x <+> y   = x <> space <> y
space :: Doc
space           = Char ' '
-- | The document @dot@ contains a single dot, \".\".
dot :: Doc
dot             = Char '.'
-- | The document @backslash@ contains a back slash, \"\\\".
backslash :: Doc
backslash       = Char '\\'
-- | The document @equals@ contains an equal sign, \"=\".
equals :: Doc
equals          = Char '='

-----------------------------------------------------------
-- Combinators for prelude types
-----------------------------------------------------------

-- string is like "text" but replaces '\n' by "line"

-- | The document @(string s)@ concatenates all characters in @s@
-- using @line@ for newline characters and @char@ for all other
-- characters. It is used instead of 'text' whenever the text contains
-- newline characters.
string :: String -> Doc
string = intercalate line <<< map text <<< split (String.Pattern "\n")

-- | The document @(bool b)@ shows the literal bool @b@ using 'text'.
bool :: Boolean -> Doc
bool b          = text (show b)

-- | The document @(int i)@ shows the literal integer @i@ using 'text'.
int :: Int -> Doc
int i           = text (show i)

-- | The document @(number f)@ shows the literal number @f@ using 'text'.
number :: Number -> Doc
number f         = text (show f)

-- -----------------------------------------------------------
-- -- overloading "pretty"
-- -----------------------------------------------------------

-- -- | The member @prettyList@ is only used to define the @instance Pretty
-- -- a => Pretty [a]@. In normal circumstances only the @pretty@ function
-- -- is used.
-- class Pretty a where
--   pretty        :: a -> Doc
--   prettyList    :: Array a -> Doc

-- instance Pretty a => Pretty [a] where
--   pretty        = prettyList

-- instance Pretty Doc where
--   pretty        = id

-- instance Pretty Unit where
--   pretty Unit     = text "Unit"

-- instance Pretty Boolean where
--   pretty b      = bool b

-- instance Pretty Char where
--   pretty c      = char c
--   prettyList s  = string s

-- instance Pretty Int where
--   pretty i      = int i

-- instance Pretty Integer where
--   pretty i      = integer i

-- instance Pretty Number where
--   pretty f      = number f

-- instance Pretty Double where
--   pretty d      = double d

-- --instance Pretty Rational where
-- --  pretty r      = rational r

-- instance (Pretty a,Pretty b) => Pretty (a,b) where
--   pretty (x,y)  = tupled [pretty x, pretty y]

-- instance (Pretty a,Pretty b,Pretty c) => Pretty (a,b,c) where
--   pretty (x,y,z)= tupled [pretty x, pretty y, pretty z]

-- instance Pretty a => Pretty (Maybe a) where
--   pretty Nothing        = empty
--   pretty (Just x)       = pretty x



-----------------------------------------------------------
-- semi primitive: fill and fillBreak
-----------------------------------------------------------

-- | The document @(fillBreak i x)@ first renders document @x@. It
-- than appends @space@s until the width is equal to @i@. If the
-- width of @x@ is already larger than @i@, the nesting level is
-- increased by @i@ and a @line@ is appended. When we redefine @ptype@
-- in the previous example to use @fillBreak@, we get a useful
-- variation of the previous output:
--
-- > ptype (name,tp)
-- >        = fillBreak 6 (text name) <+> text "::" <+> text tp
--
-- The output will now be:
--
-- @
-- let empty  :: Doc
--     nest   :: Int -> Doc -> Doc
--     linebreak
--            :: Doc
-- @
fillBreak :: Int -> Doc -> Doc
fillBreak f x   = width x (\w ->
                  if (w > f) then nest f linebreak
                             else text (spaces (f - w)))

-- | The document @(fill i x)@ renders document @x@. It than appends
-- @space@s until the width is equal to @i@. If the width of @x@ is
-- already larger, nothing is appended. This combinator is quite
-- useful in practice to output a list of bindings. The following
-- example demonstrates this.
--
-- > types  = [("empty","Doc")
-- >          ,("nest","Int -> Doc -> Doc")
-- >          ,("linebreak","Doc")]
-- >
-- > ptype (name,tp)
-- >        = fill 6 (text name) <+> text "::" <+> text tp
-- >
-- > test   = text "let" <+> align (vcat (map ptype types))
--
-- Which is layed out as:
--
-- @
-- let empty  :: Doc
--     nest   :: Int -> Doc -> Doc
--     linebreak :: Doc
-- @
fill :: Int -> Doc -> Doc
fill f d        = width d (\w ->
                  if (w >= f) then empty
                              else text (spaces (f - w)))

width :: Doc -> (Int -> Doc) -> Doc
width d f       = column (\k1 -> d <> column (\k2 -> f (k2 - k1)))

-----------------------------------------------------------
-- semi primitive: Alignment and indentation
-----------------------------------------------------------

-- | The document @(indent i x)@ indents document @x@ with @i@ spaces.
--
-- > test  = indent 4 (fillSep (map text
-- >         (words "the indent combinator indents these words !")))
--
-- Which lays out with a page width of 20 as:
--
-- @
--     the indent
--     combinator
--     indents these
--     words !
-- @
indent :: Int -> Doc -> Doc
indent i d      = hang i (text (spaces i) <> d)

-- | The hang combinator implements hanging indentation. The document
-- @(hang i x)@ renders document @x@ with a nesting level set to the
-- current column plus @i@. The following example uses hanging
-- indentation for some text:
--
-- > test  = hang 4 (fillSep (map text
-- >         (words "the hang combinator indents these words !")))
--
-- Which lays out on a page with a width of 20 characters as:
--
-- @
-- the hang combinator
--     indents these
--     words !
-- @
--
-- The @hang@ combinator is implemented as:
--
-- > hang i x  = align (nest i x)
hang :: Int -> Doc -> Doc
hang i d        = align (nest i d)

-- | The document @(align x)@ renders document @x@ with the nesting
-- level set to the current column. It is used for example to
-- implement 'hang'.
--
-- As an example, we will put a document right above another one,
-- regardless of the current nesting level:
--
-- > x $$ y  = align (x <$> y)
--
-- > test    = text "hi" <+> (text "nice" $$ text "world")
--
-- which will be layed out as:
--
-- @
-- hi nice
--    world
-- @
align :: Doc -> Doc
align d         = column (\k ->
                  nesting (\i -> nest (k - i) d))   --nesting might be negative :-)



-----------------------------------------------------------
-- Primitives
-----------------------------------------------------------

-- | The abstract data type @Doc@ represents pretty documents.
--
-- More specifically, a value of type @Doc@ represents a non-empty set of
-- possible renderings of a document.  The rendering functions select one of
-- these possibilities.
--
-- @Doc@ is an instance of the 'Show' class. @(show doc)@ pretty
-- prints document @doc@ with a page width of 80 characters and a
-- ribbon width of 32 characters.
--
-- > show (text "hello" <$> text "world")
--
-- Which would return the string \"hello\\nworld\", i.e.
--
-- @
-- hello
-- world
-- @
data Doc        = Fail
                | Empty
                | Char Char             -- invariant: char is not '\n'
                | Text Int String      -- invariant: text doesn't contain '\n'
                | Line
                | FlatAlt Doc Doc       -- Render the first doc, but when
                                        -- flattened, render the second.
                | Cat Doc Doc
                | Nest Int Doc
                | Union Doc Doc         -- invariant: first lines of first doc longer than the first lines of the second doc
                | Column  (Int -> Doc)
                | Columns (Maybe Int -> Doc)
                | Nesting (Int -> Doc)

-- | The data type @SimpleDoc@ represents rendered documents and is
-- used by the display functions.
--
-- Whereas values of the data type 'Doc' represent non-empty sets of possible
-- renderings of a document, values of the data type @SimpleDoc@ represent
-- single renderings of a document.
--
-- The @Int@ in @SText@ contains the length of the string. The @Int@
-- in @SLine@ contains the indentation for that line. The library
-- provides two default display functions 'displayS' and
-- 'displayIO'. You can provide your own display function by writing a
-- function from a @SimpleDoc@ to your own output format.
data SimpleDoc  = SFail
                | SEmpty
                | SChar Char SimpleDoc
                | SText Int String SimpleDoc
                | SLine Int SimpleDoc

derive instance simpleDocEq :: Eq SimpleDoc
derive instance simpleDocOrd :: Ord SimpleDoc
derive instance genericSimpleDoc :: Generic SimpleDoc _
instance showSimpleDoc :: Show SimpleDoc where show a = genericShow a

instance docSemigroup :: Semigroup Doc where
  append = beside
instance docMonoid :: Monoid Doc where
  mempty = empty

-- | The empty document is, indeed, empty. Although @empty@ has no
-- content, it does have a \'height\' of 1 and behaves exactly like
-- @(text \"\")@ (and is therefore not a unit of @\<$\>@).
empty :: Doc
empty           = Empty

-- | The document @(char c)@ contains the literal character @c@. The
-- character shouldn't be a newline (@'\n'@), the function 'line'
-- should be used for line breaks.
char :: Char -> Doc
char '\n'       = line
char c          = Char c

-- | The document @(text s)@ contains the literal string @s@. The
-- string shouldn't contain any newline (@'\n'@) characters. If the
-- string contains newline characters, the function 'string' should be
-- used.
text :: String -> Doc
text ""         = Empty
text s          = Text (String.length s) s

-- | The @line@ document advances to the next line and indents to the
-- current nesting level. Document @line@ behaves like @(text \" \")@
-- if the line break is undone by 'group'.
line :: Doc
line            = FlatAlt Line space

-- | The @linebreak@ document advances to the next line and indents to
-- the current nesting level. Document @linebreak@ behaves like
-- 'empty' if the line break is undone by 'group'.
linebreak :: Doc
linebreak       = FlatAlt Line empty

-- | A linebreak that will never be flattened; it is guaranteed to render
-- as a newline.
hardline :: Doc
hardline = Line

beside :: Doc -> Doc -> Doc
beside x y      = Cat x y

-- | The document @(nest i x)@ renders document @x@ with the current
-- indentation level increased by i (See also 'hang', 'align' and
-- 'indent').
--
-- > nest 2 (text "hello" <$> text "world") <$> text "!"
--
-- outputs as:
--
-- @
-- hello
--   world
-- !
-- @
nest :: Int -> Doc -> Doc
nest i x        = Nest i x

column :: (Int -> Doc) -> Doc
column f        = Column f

nesting :: (Int -> Doc) -> Doc
nesting f       = Nesting f

columns :: (Maybe Int -> Doc) -> Doc
columns f       = Columns f

-- | The @group@ combinator is used to specify alternative
-- layouts. The document @(group x)@ undoes all line breaks in
-- document @x@. The resulting line is added to the current line if
-- that fits the page. Otherwise, the document @x@ is rendered without
-- any changes.
group :: Doc -> Doc
group x         = Union (flatten x) x

-- | A document that is normally rendered as the first argument, but
-- when flattened, is rendered as the second document.
flatAlt :: Doc -> Doc -> Doc
flatAlt = FlatAlt

flatten :: Doc -> Doc
flatten (FlatAlt x y)    = y
flatten (Cat x y)        = Cat (flatten x) (flatten y)
flatten (Nest i x)       = Nest i (flatten x)
flatten  Line            = Fail
flatten (Union x y)      = flatten x
flatten (Column f)       = Column (flatten <<< f)
flatten (Columns f)      = Columns (flatten <<< f)
flatten (Nesting f)      = Nesting (flatten <<< f)
flatten other            = other                     --Empty,Char,Text


-----------------------------------------------------------
-- Renderers
-----------------------------------------------------------

-----------------------------------------------------------
-- renderPretty: the default pretty printing algorithm
-----------------------------------------------------------

-- list of indentation/document pairs; saves an indirection over [(Int,Doc)]
data Docs   = Nil
            | Cons Int Doc Docs

-- | This is the default pretty printer which is used by 'show',
-- 'putDoc' and 'hPutDoc'. @(renderPretty ribbonfrac width x)@ renders
-- document @x@ with a page width of @width@ and a ribbon width of
-- @(ribbonfrac * width)@ characters. The ribbon width is the maximal
-- amount of non-indentation characters on a line. The parameter
-- @ribbonfrac@ should be between @0.0@ and @1.0@. If it is lower or
-- higher, the ribbon width will be 0 or @width@ respectively.
renderPretty :: Number -> Int -> Doc -> SimpleDoc
renderPretty = renderFits fits1

-- | A slightly smarter rendering algorithm with more lookahead. It provides
-- provide earlier breaking on deeply nested structures
-- For example, consider this python-ish pseudocode:
-- @fun(fun(fun(fun(fun([abcdefg, abcdefg])))))@
-- If we put a softbreak (+ nesting 2) after each open parenthesis, and align
-- the elements of the list to match the opening brackets, this will render with
-- @renderPretty@ and a page width of 20 as:
-- @
-- fun(fun(fun(fun(fun([
--                     | abcdef,
--                     | abcdef,
--                     ]
--   )))))             |
-- @
-- Where the 20c. boundary has been marked with |.
-- Because @renderPretty@ only uses one-line lookahead, it sees that the first
-- line fits, and is stuck putting the second and third lines after the 20-c
-- mark. In contrast, @renderSmart@ will continue to check that the potential
-- document up to the end of the indentation level. Thus, it will format the
-- document as:
--
-- @
-- fun(                |
--   fun(              |
--     fun(            |
--       fun(          |
--         fun([       |
--               abcdef,
--               abcdef,
--             ]       |
--   )))))             |
-- @
-- Which fits within the 20c. boundary.
renderSmart :: Number -> Int -> Doc -> SimpleDoc
renderSmart = renderFits fitsR

renderFits :: (Int -> Int -> Int -> SimpleDoc -> Boolean)
           -> Number -> Int -> Doc -> SimpleDoc
renderFits fits rfrac w headNode
    -- I used to do a @SSGR [Reset]@ here, but if you do that it will result
    -- in any rendered @Doc@ containing at least some ANSI control codes. This
    -- may be undesirable if you want to render to non-ANSI devices by simply
    -- not making use of the ANSI color combinators I provide.
    --
    -- What I "really" want to do here is do an initial Reset iff there is some
    -- ANSI color within the Doc, but that's a bit fiddly. I'll fix it if someone
    -- complains!
    = best 0 0 (Cons 0 headNode Nil)
    where
      -- r :: the ribbon width in characters
      r  = max 0 (min w (Int.round (Int.toNumber w * rfrac)))

      -- best :: n = indentation of current line
      --         k = current column
      --        (ie. (k >= n) && (k - n == count of inserted characters)
      best n k Nil = SEmpty
      best n k (Cons i d ds)
        = case d of
            Fail          -> SFail
            Empty         -> best n k ds
            Char c        -> let k' = k+1 in SChar c (best n k' ds)
            Text l s      -> let k' = k+l in SText l s (best n k' ds)
            Line          -> SLine i (best i i ds)
            FlatAlt x _   -> best n k (Cons i x ds)
            Cat x y       -> best n k (Cons i x (Cons i y ds))
            Nest j x      -> let i' = i+j in best n k (Cons i' x ds)
            Union x y     -> nicest' n k i ds x y
            -- Union x y     -> nicest n k (best n k (Cons i x ds))
            --                             (best n k (Cons i y ds))
            Column f      -> best n k (Cons i (f k) ds)
            Columns f     -> best n k (Cons i (f (Just w)) ds)
            Nesting f     -> best n k (Cons i (f i) ds)

      --nicest':: r = ribbon width, w = page width,
      --          n = indentation of current line, k = current column
      --          i, d, x, y are from `(Cons i d (Union x y))`
      --          x' and y', the (simple) documents to chose from.
      --          precondition: first lines of x' are longer than the first lines of y'.
      -- nicest n k x y =
      --   let width' = min (w - k) (r - k + n)
      --   in if fits w (min n k) width' x then x else y
      nicest' n k i ds x y = 
        let
          x' = (best n k (Cons i x ds))
          width' = min (w - k) (r - k + n)
        in if fits w (min n k) width' x' then x' else let y' = best n k (Cons i y ds) in y'
      
-- @fits1@ does 1 line lookahead.
fits1 :: Int -> Int -> Int -> SimpleDoc -> Boolean
fits1 _ _ w x        | w < 0         = false
fits1 _ _ w SFail                    = false
fits1 _ _ w SEmpty                   = true
fits1 p m w (SChar c x)              = fits1 p m (w - 1) x
fits1 p m w (SText l s x)            = fits1 p m (w - l) x
fits1 _ _ w (SLine i x)              = true

-- @fitsR@ has a little more lookahead: assuming that nesting roughly
-- corresponds to syntactic depth, @fitsR@ checks that not only the current line
-- fits, but the entire syntactic structure being formatted at this level of
-- indentation fits. If we were to remove the second case for @SLine@, we would
-- check that not only the current structure fits, but also the rest of the
-- document, which would be slightly more intelligent but would have exponential
-- runtime (and is prohibitively expensive in practice).
-- p = pagewidth
-- m = minimum nesting level to fit in
-- w = the width in which to fit the first line
fitsR :: Int -> Int -> Int -> SimpleDoc -> Boolean
fitsR p m w x        | w < 0         = false
fitsR p m w SFail                    = false
fitsR p m w SEmpty                   = true
fitsR p m w (SChar c x)              = fitsR p m (w - 1) x
fitsR p m w (SText l s x)            = fitsR p m (w - l) x
fitsR p m w (SLine i x) | m < i      = fitsR p m (p - i) x
                        | otherwise  = true

-----------------------------------------------------------
-- renderCompact: renders documents without indentation
--  fast and fewer characters output, good for machines
-----------------------------------------------------------

-- | @(renderCompact x)@ renders document @x@ without adding any
-- indentation. Since no \'pretty\' printing is involved, this
-- renderer is very fast. The resulting output contains fewer
-- characters than a pretty printed version and can be used for output
-- that is read by other programs.
--
-- This rendering function does not add any colorisation information.
renderCompact :: Doc -> SimpleDoc
renderCompact
    = scan 0 <<< List.singleton
    where
      scan k List.Nil     = SEmpty
      scan k (d List.: ds) = case d of
                        Fail                    -> SFail
                        Empty                   -> scan k ds
                        Char c                  -> let k' = k+1 in SChar c (scan k' ds)
                        Text l s                -> let k' = k+l in SText l s (scan k' ds)
                        FlatAlt x _             -> scan k (x List.: ds)
                        Line                    -> SLine 0 (scan 0 ds)
                        Cat x y                 -> scan k (x List.: y List.: ds)
                        Nest j x                -> scan k (x List.: ds)
                        Union x y               -> scan k (y List.: ds)
                        Column f                -> scan k (f k List.: ds)
                        Columns f               -> scan k (f Nothing List.: ds)
                        Nesting f               -> scan k (f 0 List.:ds)



-----------------------------------------------------------
-- Displayers:  displayS and displayIO
-----------------------------------------------------------

-- | @(displayS simpleDoc)@ takes the output @simpleDoc@ from a
-- rendering function and transforms it to a 'ShowS' type (for use in
-- the 'Show' class).
--
-- > showWidth :: Int -> Doc -> String
-- > showWidth w x   = displayS (renderPretty 0.4 w x) ""
--
-- ANSI color information will be discarded by this function unless
-- you are running on a Unix-like operating system. This is due to
-- a technical limitation in Windows ANSI support.
displayS :: SimpleDoc -> String
displayS SFail              = unsafeCrashWith $ "@SFail@ can not appear uncaught in a rendered @SimpleDoc@"
displayS SEmpty             = ""
displayS (SChar c x)        = fromCharArray [c] <> displayS x
displayS (SText l s x)      = s <> displayS x
displayS (SLine i x)        = "\n" <> indentation i <> displayS x

instance docShow :: Show Doc where
  show = displayS <<< renderPretty 0.4 80

-----------------------------------------------------------
-- insert spaces
-- "indentation" used to insert tabs but tabs seem to cause
-- more trouble than they solve :-)
-----------------------------------------------------------
spaces :: Int -> String
spaces n        | n <= 0    = ""
                | otherwise = fromCharArray $ Array.replicate n ' '

indentation :: Int -> String
indentation n   = spaces n

--indentation n   | n >= 8    = '\t' : indentation (n-8)
--                | otherwise = spaces n

--  LocalWords:  PPrint combinators Wadler Wadler's encloseSep