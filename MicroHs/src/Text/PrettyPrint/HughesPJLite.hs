--  Based on the pretty-printer outlined in the paper
-- 'The Design of a Pretty-printing Library' by
-- John Hughes in Advanced Functional Programming, 1995.
-- With inspiration and code from the from the Hackage package pretty.
module Text.PrettyPrint.HughesPJLite(
  Doc,
  text, empty,
  (<>), (<+>), ($$), ($+$),
  hcat, hsep,
  vcat,
  sep, cat,
  fsep, fcat,
  nest, hang,
  punctuate,
  parens, brackets, braces,
  maybeParens,
  Style,
  render, renderStyle,
  ) where
import MHSPrelude hiding ((<>))
import Prelude qualified ()

infixl 6 <>, <+>
infixl 5 $$, $+$

data Doc
  = Empty                                            -- ^ An empty span, see 'empty'.
  | NilAbove Doc                                     -- ^ @text "" $$ x@.
  | TextBeside String Doc                            -- ^ @text s <> x@.
  | Nest Int Doc                                     -- ^ @nest k x@.
  | Union Doc Doc                                    -- ^ @ul `union` ur@.
  | NoDoc                                            -- ^ The empty set of documents.
  | Beside Doc Bool Doc                              -- ^ True <=> space between.
  | Above Doc Bool Doc                               -- ^ True <=> never overlap.

type RDoc = Doc

text :: String -> Doc
text s = TextBeside s Empty

empty :: Doc
empty = Empty

reduceDoc :: Doc -> RDoc
reduceDoc (Beside p g q) = beside p g (reduceDoc q)
reduceDoc (Above  p g q) = above  p g (reduceDoc q)
reduceDoc p              = p

hcat :: [Doc] -> Doc
hcat = snd . reduceHoriz . foldr (`Beside` False) empty

hsep :: [Doc] -> Doc
hsep = snd . reduceHoriz . foldr (`Beside` True)  empty

vcat :: [Doc] -> Doc
vcat = snd . reduceVert . foldr (`Above` False) empty

nest :: Int -> Doc -> Doc
nest k p = mkNest k (reduceDoc p)

-- | @hang d1 n d2 = sep [d1, nest n d2]@
hang :: Doc -> Int -> Doc -> Doc
hang d1 n d2 = sep [d1, nest n d2]

punctuate :: Doc -> [Doc] -> [Doc]
punctuate _ []     = []
punctuate p (x:xs) = go x xs
                   where go y []     = [y]
                         go y (z:zs) = (y <> p) : go z zs

maybeParens :: Bool -> Doc -> Doc
maybeParens False = id
maybeParens True  = parens

parens :: Doc -> Doc
parens p = text "(" <> p <> text ")"
braces :: Doc -> Doc
braces p = text "{" <> p <> text "}"
brackets :: Doc -> Doc
brackets p = text "[" <> p <> text "]"

-- mkNest checks for Nest's invariant that it doesn't have an Empty inside it
mkNest :: Int -> Doc -> Doc
mkNest k (Nest k1 p) = mkNest (k + k1) p
mkNest _ NoDoc       = NoDoc
mkNest _ Empty       = Empty
mkNest 0 p           = p
mkNest k p           = nest_ k p

-- mkUnion checks for an empty document
mkUnion :: Doc -> Doc -> Doc
mkUnion Empty _ = Empty
mkUnion p q     = p `union_` q

data IsEmpty = IsEmpty | NotEmpty

reduceHoriz :: Doc -> (IsEmpty, Doc)
reduceHoriz (Beside p g q) = eliminateEmpty Beside (snd (reduceHoriz p)) g (reduceHoriz q)
reduceHoriz doc            = (NotEmpty, doc)

reduceVert :: Doc -> (IsEmpty, Doc)
reduceVert (Above  p g q) = eliminateEmpty Above  (snd (reduceVert p)) g (reduceVert q)
reduceVert doc            = (NotEmpty, doc)

eliminateEmpty ::
  (Doc -> Bool -> Doc -> Doc) ->
  Doc -> Bool -> (IsEmpty, Doc) -> (IsEmpty, Doc)
eliminateEmpty _    Empty _ q          = q
eliminateEmpty cons p     g q          =
  (NotEmpty,
   case q of
     (NotEmpty, q') -> cons p g q'
     (IsEmpty, _)   -> p
  )

nilAbove_ :: RDoc -> RDoc
nilAbove_ = NilAbove

-- | Arg of a TextBeside is always an RDoc.
textBeside_ :: String -> RDoc -> RDoc
textBeside_  = TextBeside

nest_ :: Int -> RDoc -> RDoc
nest_ = Nest

union_ :: RDoc -> RDoc -> RDoc
union_ = Union

($$) :: Doc -> Doc -> Doc
p $$  q = above_ p False q

-- | Above, with no overlapping.
-- '$+$' is associative, with identity 'empty'.
($+$) :: Doc -> Doc -> Doc
p $+$ q = above_ p True q

above_ :: Doc -> Bool -> Doc -> Doc
above_ p _ Empty = p
above_ Empty _ q = q
above_ p g q     = Above p g q

above :: Doc -> Bool -> RDoc -> RDoc
above (Above p g1 q1) g2 q2 = above p g1 (above q1 g2 q2)
above p@Beside{}      g  q  = aboveNest (reduceDoc p) g 0 (reduceDoc q)
above p g q                 = aboveNest p             g 0 (reduceDoc q)

-- Specfication: aboveNest p g k q = p $g$ (nest k q)
aboveNest :: RDoc -> Bool -> Int -> RDoc -> RDoc
aboveNest _                   _ k _ | k `seq` False = undefined
aboveNest NoDoc               _ _ _ = NoDoc
aboveNest (p1 `Union` p2)     g k q = aboveNest p1 g k q `union_`
                                      aboveNest p2 g k q

aboveNest Empty               _ k q = mkNest k q
aboveNest (Nest k1 p)         g k q = nest_ k1 (aboveNest p g (k - k1) q)
                                  -- p can't be Empty, so no need for mkNest

aboveNest (NilAbove p)        g k q = nilAbove_ (aboveNest p g k q)
aboveNest (TextBeside s p)    g k q = TextBeside s rest
                                    where
                                      k1  = k - length s
                                      rest = case p of
                                                Empty -> nilAboveNest g k1 q
                                                _     -> aboveNest  p g k1 q

aboveNest Above{}             _ _ _ = error "aboveNest Above"
aboveNest Beside{}            _ _ _ = error "aboveNest Beside"

-- Specification: text s <> nilaboveNest g k q
--              = text s <> (text "" $g$ nest k q)
nilAboveNest :: Bool -> Int -> RDoc -> RDoc
nilAboveNest _ k _           | k `seq` False = undefined
nilAboveNest _ _ Empty       = Empty
                               -- Here's why the "text s <>" is in the spec!
nilAboveNest g k (Nest k1 q) = nilAboveNest g (k + k1) q
nilAboveNest g k q           | not g && k > 0      -- No newline if no overlap
                             = textBeside_ (replicate k ' ') q
                             | otherwise           -- Put them really above
                             = nilAbove_ (mkNest k q)

(<>) :: Doc -> Doc -> Doc
p <>  q = beside_ p False q

-- | Beside, separated by space, unless one of the arguments is 'empty'.
-- '<+>' is associative, with identity 'empty'.
(<+>) :: Doc -> Doc -> Doc
p <+> q = beside_ p True  q

beside_ :: Doc -> Bool -> Doc -> Doc
beside_ p _ Empty = p
beside_ Empty _ q = q
beside_ p g q     = Beside p g q

-- Specification: beside g p q = p <g> q
beside :: Doc -> Bool -> RDoc -> RDoc
beside NoDoc               _ _   = NoDoc
beside (p1 `Union` p2)     g q   = beside p1 g q `union_` beside p2 g q
beside Empty               _ q   = q
beside (Nest k p)          g q   = nest_ k $! beside p g q
beside p@(Beside p1 g1 q1) g2 q2
         | g1 == g2              = beside p1 g1 $! beside q1 g2 q2
         | otherwise             = beside (reduceDoc p) g2 q2
beside p@Above{}           g q   = let { d = reduceDoc p } in beside d g q
beside (NilAbove p)        g q   = nilAbove_ $! beside p g q
beside (TextBeside t p)    g q   = TextBeside t rest
                               where
                                  rest = case p of
                                           Empty -> nilBeside g q
                                           _     -> beside p g q

-- Specification: text "" <> nilBeside g p
--              = text "" <g> p
nilBeside :: Bool -> RDoc -> RDoc
nilBeside _ Empty         = Empty -- Hence the text "" in the spec
nilBeside g (Nest _ p)    = nilBeside g p
nilBeside g p | g         = textBeside_ " " p
              | otherwise = p

sep  :: [Doc] -> Doc
sep = sepX True   -- Separate with spaces

-- | Either 'hcat' or 'vcat'.
cat :: [Doc] -> Doc
cat = sepX False  -- Don't

sepX :: Bool -> [Doc] -> Doc
sepX _ []     = empty
sepX x (p:ps) = sep1 x (reduceDoc p) 0 ps


-- Specification: sep1 g k ys = sep (x : map (nest k) ys)
--                            = oneLiner (x <g> nest k (hsep ys))
--                              `union` x $$ nest k (vcat ys)
sep1 :: Bool -> RDoc -> Int -> [Doc] -> RDoc
sep1 _ _                   k _  | k `seq` False = undefined
sep1 _ NoDoc               _ _  = NoDoc
sep1 g (p `Union` q)       k ys = sep1 g p k ys `union_`
                                  aboveNest q False k (reduceDoc (vcat ys))

sep1 g Empty               k ys = mkNest k (sepX g ys)
sep1 g (Nest n p)          k ys = nest_ n (sep1 g p (k - n) ys)

sep1 _ (NilAbove p)        k ys = nilAbove_
                                  (aboveNest p False k (reduceDoc (vcat ys)))
sep1 g (TextBeside s p) k ys    = textBeside_ s (sepNB g p (k - length s) ys)
sep1 _ Above{}             _ _  = error "sep1 Above"
sep1 _ Beside{}            _ _  = error "sep1 Beside"

sepNB :: Bool -> Doc -> Int -> [Doc] -> Doc
sepNB g (Nest _ p) k ys
  = sepNB g p k ys
sepNB g Empty k ys
  = oneLiner (nilBeside g (reduceDoc rest)) `mkUnion`
    nilAboveNest False k (reduceDoc (vcat ys))
  where
    rest | g         = hsep ys
         | otherwise = hcat ys
sepNB g p k ys
  = sep1 g p k ys

oneLiner :: Doc -> Doc
oneLiner NoDoc            = NoDoc
oneLiner Empty            = Empty
oneLiner (NilAbove _)     = NoDoc
oneLiner (TextBeside s p) = textBeside_ s (oneLiner p)
oneLiner (Nest k p)       = nest_ k (oneLiner p)
oneLiner (p `Union` _)    = oneLiner p
oneLiner Above{}          = error "oneLiner Above"
oneLiner Beside{}         = error "oneLiner Beside"

-- ---------------------------------------------------------------------------
-- Rendering

-- | A rendering style. Allows us to specify constraints to choose among the
-- many different rendering options.
data Style = Style Int Rat
lineLength :: Style -> Int
lineLength (Style l _) = l
ribbonsPerLine :: Style -> Rat
ribbonsPerLine (Style _ r) = r

type Rat = (Int, Int)

style :: Style
style = Style 100 (3, 2)

-- | Render the @Doc@ to a String using the default @Style@ (see 'style').
render :: Doc -> String
render = renderStyle style

-- | Render the @Doc@ to a String using the given @Style@.
renderStyle :: Style -> Doc -> String
renderStyle s = fullRender (lineLength s) (ribbonsPerLine s) ""

-- | The general rendering interface. Please refer to the @Style@ and @Mode@
-- types for a description of rendering mode, line length and ribbons.
fullRender :: Int                     -- ^ Line length.
           -> Rat                     -- ^ Ribbons per line.
           -> String                  -- ^ What to do at the end.
           -> Doc                     -- ^ The document.
           -> String                  -- ^ Result.
fullRender lineLen (num, den) rest doc
  = display lineLen ribbonLen rest doc'
  where
    doc' = best bestLineLen ribbonLen (reduceDoc doc)

    ribbonLen   = (lineLen * den) `quot` num
    bestLineLen = lineLen

display :: Int -> Int -> String -> Doc -> String
display _page_width _ribbon_width end doc
  = let lay :: Int -> Doc -> String
        lay k (Nest k1 p)      = lay (k + k1) p
        lay _ Empty            = end
        lay k (NilAbove p)     = "\n" ++ lay k p
        lay k (TextBeside s p) = lay1 k s p
        lay _ _                = error "display lay"

        lay1 k s p        = let r = k + length s
                            in replicate k ' ' ++ (s ++ lay2 r p)

        lay2 :: Int -> Doc -> String
        lay2 k (NilAbove p)     = "\n" ++ lay k p
        lay2 k (TextBeside s p) = s ++ lay2 (k + length s) p
        lay2 k (Nest _ p)       = lay2 k p
        lay2 _ Empty            = end
        lay2 _ _                = error "display lay2"
    in  lay 0 doc

best :: Int   -- Line length.
     -> Int   -- Ribbon length.
     -> RDoc
     -> RDoc  -- No unions in here!.
best w0 r = get w0
  where
    get _ Empty            = Empty
    get _ NoDoc            = NoDoc
    get w (NilAbove p)     = nilAbove_ (get w p)
    get w (TextBeside s p) = textBeside_ s (get1 w (length s) p)
    get w (Nest k p)       = nest_ k (get (w - k) p)
    get w (p `Union` q)    = nicest w r (get w p) (get w q)
    get _ _                = error "best get"

    get1 _ _  Empty               = Empty
    get1 _ _  NoDoc               = NoDoc
    get1 w sl (NilAbove p)        = nilAbove_ (get (w - sl) p)
    get1 w sl (TextBeside s p)    = textBeside_ s (get1 w (sl + length s) p)
    get1 w sl (Nest _ p)          = get1 w sl p
    get1 w sl (p `Union` q)       = nicest1 w r sl (get1 w sl p)
                                                   (get1 w sl q)
    get1 _ _  _                   = error "best get1"

nicest :: Int -> Int -> Doc -> Doc -> Doc
nicest w r = nicest1 w r 0

nicest1 :: Int -> Int -> Int -> Doc -> Doc -> Doc
nicest1 w r sl p q | fits (minWR - sl) p = p
                   | otherwise           = q
  where minWR = min w r

fits :: Int  -- Space available
     -> Doc
     -> Bool -- True if *first line* of Doc fits in space available
fits n _ | n < 0           = False
fits _ NoDoc               = False
fits _ Empty               = True
fits _ (NilAbove _)        = True
fits n (TextBeside s p)    = fits (n - length s) p
fits _ _                   = error "fits"

---------

fcat :: [Doc] -> Doc
fcat = fill False

fsep :: [Doc] -> Doc
fsep = fill True

-- Specification:
--
-- fill g docs = fillIndent 0 docs
--
-- fillIndent k [] = []
-- fillIndent k [p] = p
-- fillIndent k (p1:p2:ps) =
--    oneLiner p1 <g> fillIndent (k + length p1 + g ? 1 : 0)
--                               (remove_nests (oneLiner p2) : ps)
--     `Union`
--    (p1 $*$ nest (-k) (fillIndent 0 ps))
--
-- $*$ is defined for layouts (not Docs) as
-- layout1 $*$ layout2 | hasMoreThanOneLine layout1 = layout1 $$ layout2
--                     | otherwise                  = layout1 $+$ layout2

fill :: Bool -> [Doc] -> RDoc
fill _ []     = empty
fill g (p:ps) = fill1 g (reduceDoc p) 0 ps

fill1 :: Bool -> RDoc -> Int -> [Doc] -> Doc
fill1 _ _                   k _  | k `seq` False = undefined
fill1 _ NoDoc               _ _  = NoDoc
fill1 g (p `Union` q)       k ys = fill1 g p k ys `union_`
                                   aboveNest q False k (fill g ys)
fill1 g Empty               k ys = mkNest k (fill g ys)
fill1 g (Nest n p)          k ys = nest_ n (fill1 g p (k - n) ys)
fill1 g (NilAbove p)        k ys = nilAbove_ (aboveNest p False k (fill g ys))
fill1 g (TextBeside s p)    k ys = textBeside_ s (fillNB g p k ys)
fill1 _ Above{}             _ _  = error "fill1 Above"
fill1 _ Beside{}            _ _  = error "fill1 Beside"

fillNB :: Bool -> Doc -> Int -> [Doc] -> Doc
fillNB _ _           k _  | k `seq` False = undefined
fillNB g (Nest _ p)  k ys   = fillNB g p k ys
                              -- Never triggered, because of invariant (2)
fillNB _ Empty _ []         = Empty
fillNB g Empty k (Empty:ys) = fillNB g Empty k ys
fillNB g Empty k (y:ys)     = fillNBE g k y ys
fillNB g p k ys             = fill1 g p k ys


fillNBE :: Bool -> Int -> Doc -> [Doc] -> Doc
fillNBE g k y ys
  = nilBeside g (fill1 g ((elideNest . oneLiner . reduceDoc) y) k' ys)
    -- XXX: TODO: PRETTY: Used to use True here (but GHC used False...)
    `mkUnion` nilAboveNest False k (fill g (y:ys))
  where k' = if g then k - 1 else k

elideNest :: Doc -> Doc
elideNest (Nest _ d) = d
elideNest d          = d
