module Text.Fixity.Internal
    ( Associativity (..)
    , FixityOver (..)
    , Direction (..)
    , RenderContextOver (..)
    , encloseIn
    ) where

{- Note [Approaches to precedence-aware pretty-printing]
It's not trivial to find papers on precedence-aware pretty-printing.

1. The only paper that I was able to find targetting specifically that topic is

    "Unparsing Expressions with Prefix and Postfix Operators", Norman Ramsey --
    https://www.cs.tufts.edu/~nr/pubs/unparse-abstract.html

("unparsing" = "pretty-printing")

Here's the gist:

> The unparsing method uses information about precedence, associativity, and "fixity" of operators
> to transform an internal form into a concrete syntax. The method works from the bottom up and from
> the inside out. In each expression, it finds the operator, and it considers the subexpressions and
> their positions, left or right, relative to the operator. It decides whether to parenthesize
> subexpressions by comparing precedence and associativity of the current operator with the
> precedences and associativities of the most loosely binding operators in the subexpressions.
> Operators that are "covered" by parenthesises do not participate in the comparison.

So the algorithm is non-local, i.e. it's not possible to determine if parenthesises are needed only
by looking at an outer operator and an inner one, you have to analyze the entire syntax tree from
the bottom up.

In the paper's system unary operators don't have associativity:

> no matter what the precedences of `++` and `*`, `++*p` and `*++p` are both correct and unambiguous,
> equivalent to `++(*p)` and `*(++p)`, respectively

Other relevant papers I've found are about parsing rather than pretty-printing, but they describe
approaches to mixfix/distfix syntax and so are useful for us.

2. This one contains plenty of interesting info:

    "Parsing Mixfix Operators", Nils Anders Danielsson and Ulf Norell --
    http://www.cse.chalmers.se/~nad/publications/danielsson-norell-mixfix.pdf

Their precedence relation is quite general as it only needs to be a DAG:

> Instead we just require that the precedence relation forms a directed acyclic
> graph (DAG), where an edge from one node to another means that the operators
> in the second node bind tighter than those in the first one, and operators in
> the same node have equal precedence. This makes it possible to define a small
> domain-specific library (language) with a couple of operators and a natural,
> possibly domain-specific precedence relation, without relating these operators to
> those from other libraries. However, we note that partial and total orders are
> DAGs, so the results below apply also to those cases.

And it could be even weirder:

> Missura also argues that precedence relations should not have to be total
> orders, and Heinlein (2004) argues that precedence relations should be partial
> orders. The language Fortress uses a non-transitive precedence relation, hard-
> coded in the language’s grammar (Allen et al. 2008).

They don't allow unary operators to have associativity (as in the Ramsey's system):

> Fixities are combined with associativities, but only for infix operators;
> prefix, postfix and closed operators are viewed as being right, left and
> non-associative, respectively

Their rendering algorithm is local due to the system being restrictive (this is an important quote):

> In our system the string `0 + $ 0` is syntactically
> incorrect since $ binds weaker than `+`, whereas Aasa’s system accepts arbi-
> trary prefix operators immediately to the right of an infix operator, so in her
> system the string can be unambiguously parsed as `0 + ($ 0)`. It does not stop
> there, though. The string `# $ 0 + 0`, which is also syntactically incorrect in our
> system, is parsed as `# ($ (0 + 0))` in Aasa’s. It is accepted because, even though
> `#` binds tighter than `+`, the occurrence of `+` is covered by `$`. Our system
> has the advantage that one can tell whether a syntax tree is precedence correct
> by inspecting every node in isolation and considering the relation between the
> node’s operator and the operators of the child nodes. In Aasa’s system this is
> not enough: even though the syntax tree `# ($ 0)` (where the parentheses indi-
> cate the structure of the syntax tree) is precedence correct and `#` binds strictly
> tighter than `+` the syntax tree `(# ($ 0)) + 0` is not precedence correct.

The work that they reference is

3. A paper and an entire PhD thesis (containing the paper), respectively:

    "Precedences in specifications and implementations of programming languages", Annika Aasa --
    https://core.ac.uk/download/pdf/82260562.pdf

    "User Defined Syntax", Annika Aasa --
    http://citeseerx.ist.psu.edu/viewdoc/summary?doi=10.1.1.47.3542

The paper goes into much detail on how to parse what (lots of examples), what problems arise if
the same name can be used for, say, both a prefix and an infix operator or if an operator name
is a substring of another operator name.

Unary operators don't have associativity.

The system is expressive, hence a rendering algorithm for it has to be non-local (unlike in the
Parsing Mixfix Operators paper)

4. Our system

We allow unary operators to have associativity. It makes sense to render @-(-x)@ as @--x@ and it
makes sense to render @~(~x)@ as @~~x@ (where @~@is boolean NOT). It really should be configurable
and associativity is one way to configure how unary operators get pretty-printed. See docs of
'FixityOver' for details.

Apart from that and the fact that we're generic over the choice of precedence (see the docs of
'FixityOver') our current system is pretty much the one of the Parsing Mixfix Operators paper.

I.e. in our system an expression like

    x + (if b then y else z)

is rendered as

    x + (if b then y else z)

because @if_then_else_@ is a prefix operator that binds weaker than @+@. But in Haskell

    x + if b then y else z

is a perfectly correct input and it does make sense to accept such an input and pretty-print it the
same way. Ramsey's system allows that as well as the Aasa's one. So our system is overly restrictive
(and easy to implement, because the rendering algorithm is local).

However I don't think that the way to relax the restriction is by employing the strategy of either
of the other systems. Consider this Haskell expression:

    f x {y = z}

It parses as

    f (x {y = z})

so clearly there are unary operators out there that bind even tighter than juxtaposition.

Moreover, the same operator can bind tighter or weaked than juxtaposition depending on flags enabled,
for example

    f \ x -> x

is accepted by GHC with `-XBlockArguments` enabled and is not accepted otherwise (while in Agda such
an expression is accepted by default).

This suggests a peculiar idea: unary operators have two precedences, the left one and the right one.
So @if_then_else_@ binds tigthly to the left and it binds weakly to the right, making it possible
to render

    x + (if b then y else z)

as

    x + if b then y else z

and to render

    (if b then x else y) + z

as

    (if b then x else y) + z

(because @if b then x else y + z@ would be a completely different expression).

The same way a lambda binds tightly to the left, so that

    a >>= (\x -> f x)

is rendered as

    a >>= \x -> f x

and weakly to the right, so that

    (\x -> f x) =<< a

is rendered as

    (\x -> f x) =<< a

And the exact left precedence of a lambda depends on whether `-XBlockArguments` is enabled or not:
it can be higher than the one of juxtaposition or it can be smaller.

What is particularly fortunate is that Aasa's system already works like that:

> we introduce two different kinds of precedence weights of a syntax tree, the left weight, Lw,
> and the right weight, Rw. Prefix operators have precedence only to the right, postfix operators
> only to the left and infix operators in both directions.

It seems the only thing needed to get full generality is to allow unary operators to have two
precedences.

Implementing all of that is left as future work.
-}

-- It's not necessary to deal with associativity, see: https://stackoverflow.com/a/43639618
-- But I find it easier and nicer than changing precedence on the fly.
-- | Associativity of an operator.
data Associativity
    = LeftAssociative
    | RightAssociative
    | NonAssociative
    deriving (Show, Eq)

-- See Note [Approaches to precedence-aware pretty-printing].
-- | Fixity of an operator.
--
-- We allow unary operators to have associativity, because it's useful to distinguish
-- between an expression like @-(-x)@ (unary minus, left-associative) and @~~b@
-- (boolean NOT, right-associative).
--
-- Associativity of unary operators also matters when pretty-printing expressions like @(-x) + y@,
-- which is pretty-printed as @-x + y@, assuming unary minus has the same fixity as @+@ (and both
-- the operators are left-associative). I.e. unary minus is handled just like the binary one:
-- @(0 - x) + y@ is pretty-printed as @0 - x + y@.
--
-- Postfix operators are handled similarly. E.g. if @!@ is left-associative, then @(x!)!@ is
-- pretty-printed as @x!!@ and if it's right-associative -- @(x!)!@.
--
-- The data type is parameterized, so that the user can choose precedence to be integer\/fractional,
-- bounded\/unbounded, etc (we could also allows operators to be partially or totally ordered, but
-- at the moment @prec@ is required to implement 'Ord', i.e. it has to be totally ordered).
-- By default we go with bounded fractional precedence, see the main "Text.Fixity" module.
data FixityOver prec = Fixity
    { _fixityAssociativity :: !Associativity
    , _fixityPrecedence    :: !prec
    } deriving (Show, Eq)

-- | Direction in which pretty-printing goes. For example in @x + y@ @x@ is pretty-printed to the
-- left of @+@ and @y@ is pretty-printed to the right of @+@.
data Direction
    = ToTheLeft
    | ToTheRight
    deriving (Show, Eq)

-- | A context that an expression is being rendered in.
data RenderContextOver prec = RenderContext
    { _renderContextDirection :: !Direction
    , _renderContextFixity    :: !(FixityOver prec)
    } deriving (Show, Eq)

-- Instead of receiving a @a -> a@ this function could simply return a 'Bool'.
-- | Enclose an @a@ (using the provided function) if required or leave it as is.
-- The need for enclosing is determined from an outer 'RenderContext' and the inner fixity.
encloseIn
    :: Ord prec
    => (a -> a)                -- ^ Enclose a value of type @a@ in parens.
    -> RenderContextOver prec  -- ^ An outer context.
    -> FixityOver prec         -- ^ An inner fixity.
    -> a
    -> a
encloseIn parens (RenderContext dir (Fixity assocOut precOut)) (Fixity assocInn precInn) =
    case precOut `compare` precInn of
        LT -> id                       -- If the outer precedence is lower than the inner, then
                                       -- do not add parens. E.g. in @Add x (Mul y z)@ the precedence
                                       -- of @Add@ is lower than the one of @Mul@, hence there is
                                       -- no need for parens in @x + y * z@.
        GT -> parens                   -- If the outer precedence is greater than the inner, then
                                       -- do add parens. E.g. in @Mul x (Add y z)@ the precedence
                                       -- of @Mul@ is greater than the one of @Add@, hence
                                       -- parens are needed in @x * (y + z)@.
        EQ -> case (assocOut, dir) of  -- If precedences are equal, then judge from associativity.
            _ | assocOut /= assocInn       -> parens  -- Associativities differ => parens are needed.
            (LeftAssociative, ToTheLeft)   -> id      -- No need for parens in @Add (Add x y) z@
                                                      -- which is rendered as @x + y + z@.
            (RightAssociative, ToTheRight) -> id      -- No need for parens in @Concat xs (Concat ys zs)@
                                                      -- which is rendered as @xs ++ ys ++ zs@.
            _                              -> parens  -- Every other case requires parens.
