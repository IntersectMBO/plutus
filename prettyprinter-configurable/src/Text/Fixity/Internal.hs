module Text.Fixity.Internal
    ( Associativity (..)
    , Arity (..)
    , Fixity (..)
    , Direction (..)
    , RenderContext (..)
    , nullary
    , unary
    , prefix
    , postfix
    , binary
    , flipDirection
    , toOuterPrec
    , toInnerPrec
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

data Arity prec
    = Nullary !prec
    | Unary !prec !prec
    | Binary !prec
    deriving (Show, Eq)

-- | Fixity of an operator.
data Fixity prec = Fixity
    { _fixityAssociativity :: !Associativity
    , _fixityArity         :: !(Arity prec)
    } deriving (Show, Eq)

data Direction
    = ToTheLeft
    | ToTheRight
    deriving (Show, Eq)

-- | A context that an expression is being rendered in.
data RenderContext prec = RenderContext
    { _renderContextDirection :: !Direction
    , _renderContextFixity    :: !(Fixity prec)
    } deriving (Show, Eq)

nullary :: Associativity -> prec -> Fixity prec
nullary assoc = Fixity assoc . Nullary

unary :: Associativity -> prec -> Fixity prec
unary assoc prec = Fixity assoc $ Unary prec prec

prefix :: Associativity -> prec -> prec -> Fixity prec
prefix assoc precL precR = Fixity assoc $ Unary precL precR

postfix :: Associativity -> prec -> prec -> Fixity prec
postfix assoc precL precR = Fixity assoc $ Unary precR precL

binary :: Associativity -> prec -> Fixity prec
binary assoc = Fixity assoc . Binary

flipDirection :: Direction -> Direction
flipDirection ToTheLeft  = ToTheRight
flipDirection ToTheRight = ToTheLeft

toOuterPrec :: Direction -> Arity prec -> prec
toOuterPrec _          (Nullary prec)    = prec
toOuterPrec ToTheLeft  (Unary _ precInn) = precInn
toOuterPrec ToTheRight (Unary precOut _) = precOut
toOuterPrec _          (Binary prec)     = prec

toInnerPrec :: Direction -> Arity prec -> prec
toInnerPrec = toOuterPrec . flipDirection

-- | Enclose an @a@ in parens if required or leave it as is.
-- The need for enclosing is determined from an outer 'RenderContext' and the inner fixity.
encloseIn
    :: Ord prec
    => (a -> a)
    -> RenderContext prec  -- ^ An outer context.
    -> Fixity prec         -- ^ An inner fixity.
    -> a
    -> a
encloseIn parens (RenderContext dir (Fixity assocOut fixityPrecOut)) (Fixity assocInn fixityPrecInn) =
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
  where
    precOut = toOuterPrec dir fixityPrecOut
    precInn = toInnerPrec dir fixityPrecInn



-- - (- 3)
-- ~~b

-- 5 * (- 3) ~> 5 * (- 3)
-- (- 3) * 5 ~> (- 3) * 5
-- - (3 * 5) ~> - 3 * 5

-- 5 + (- 3) ~> 5 + (- 3)
-- (- 3) + 5 ~> - 3 + 5    -- Only for the left-associative @+@?
-- - (3 + 5) ~> - (3 + 5)

-- if_then_else_ -- right associative


-- - (- x)
-- x + (-y)

-- ~~x
-- x && ~y

-- newtype Precedence = Precedence
--     { unPrecedence :: Double
--     } deriving newtype (Show, Eq, Ord, Num)
