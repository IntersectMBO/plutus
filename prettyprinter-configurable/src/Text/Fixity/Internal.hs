module Text.Fixity.Internal
    ( Associativity (..)
    , FixityOver (..)
    , Direction (..)
    , RenderContextOver (..)
    , encloseIn
    ) where

-- It's not necessary to deal with associativity, see: https://stackoverflow.com/a/43639618
-- But I find it easier and nicer than changing precedence on the fly.
-- | Associativity of an expression.
data Associativity
    = LeftAssociative
    | RightAssociative
    | NonAssociative
    deriving (Show, Eq)

-- | Fixity of an operator.
data FixityOver prec = Fixity
    { _fixityAssociativity :: !Associativity
    , _fixityPrecedence    :: !prec
    } deriving (Show, Eq)

data Direction
    = ToTheLeft
    | ToTheRight
    deriving (Show, Eq)

-- | A context that an expression is being rendered in.
data RenderContextOver prec = RenderContext
    { _renderContextDirection :: !Direction
    , _renderContextFixity    :: !(FixityOver prec)
    } deriving (Show, Eq)

-- two precedencies
-- (a + if b then c else d) * e
-- (a * if b then c else d) * e
-- (a # (b ? @ % c)) $ d

-- | Enclose an @a@ (using the provided function) if required or leave it as is.
-- The need for enclosing is determined from an outer 'RenderContext' and the inner fixity.
encloseIn
    :: Ord prec
    => (a -> a)
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
