{-# LANGUAGE TypeApplications #-}

{-| Common UPLC term-construction helpers shared across the
@Transform.*.Spec@ test modules.

Variables are referred to by name: @var "x"@ is an occurrence, @lam "x"
body@ a binder, and @name "x"@ the bare 'Name'. See Note [Names from strings]. -}
module Transform.Lib
  ( T
  , var
  , lam
  , app
  , force
  , delay
  , case_
  , builtin
  , constr
  , sopTrue
  , sopFalse
  , builtinTrue
  , builtinFalse
  , ite
  , con
  , text
  , err
  , name
  ) where

import Data.Text (Text)
import Data.Text qualified as Text
import Data.Word (Word64)
import GHC.Exts (fromList)
import PlutusCore.Default (DefaultBuiltinPattern, DefaultFun (IfThenElse), DefaultUni)
import PlutusCore.MkPlc (mkConstant)
import PlutusCore.Name.Unique (Name (..), Unique (..))
import UntypedPlutusCore.Core.Type (Term (..))

{- Note [Names from strings]
These test modules build UPLC terms purely, without using the 'Quote' monad to
allocate fresh uniques. A variable is identified entirely by its name: 'name'
maps a 'String' to a 'Name' whose 'Unique' is derived injectively from it via
'uniqueFromText', and 'var' / 'lam' wrap 'name' for occurrences and binders.

This lets a binder and its occurrences be written independently
(@lam "a" (var "a")@) yet still refer to the same variable, and lets an assertion
mention a free variable by name (@isStrictIn (name "a") term@) with no plumbing.

The trade-off against 'QuoteT' is that freshness is no longer correct by
construction: reusing one name for two variables meant to differ silently aliases
them, since 'Name' equality compares only the 'Unique'. For these small,
hand-written test terms that is an acceptable price for dropping the monadic
plumbing; where capture is a genuine concern, 'QuoteT' remains available.

Alternatives considered: an 'IsString' or 'IsLabel' instance for 'Name'
(@"a" :: Name@ / @#a@), which would be an orphan on a core type; and
'OverloadedRecordDot' handles (@var.x@), which need that uncommon extension and
read as if @x@ were a bound Haskell variable. The plain @String -> Name@ used
here is the simplest: no orphan instance and no language extension at all.

'uniqueFromText' is injective only on short ASCII names, so it fails fast on
non-ASCII characters or on names long enough to overflow the 'Int' rather than
aliasing silently.
-}

-- | Convenient alias used throughout the test modules.
type T = Term Name DefaultUni DefaultFun DefaultBuiltinPattern ()

{-| A 'Var' occurrence of the variable with the given name.
See Note [Names from strings] -}
var :: String -> T
var = Var () . name

{-| A lambda binding the variable with the given name.
See Note [Names from strings] -}
lam :: String -> T -> T
lam = LamAbs () . name

app :: T -> T -> T
app = Apply ()

force :: T -> T
force = Force ()

delay :: T -> T
delay = Delay ()

case_ :: T -> [T] -> T
case_ scrut branches = Case () scrut (fromList branches)

builtin :: DefaultFun -> T
builtin = Builtin ()

-- | A 'Constr' term tagged with the given index.
constr :: Word64 -> [T] -> T
constr = Constr ()

-- | @True@ as a sum-of-products value, @Constr 0 []@ (the datatype encoding of @Bool@).
sopTrue :: T
sopTrue = constr 0 []

-- | @False@ as a sum-of-products value, @Constr 1 []@.
sopFalse :: T
sopFalse = constr 1 []

-- | @True@ as the builtin @bool@ constant.
builtinTrue :: T
builtinTrue = mkConstant @Bool () True

-- | @False@ as the builtin @bool@ constant.
builtinFalse :: T
builtinFalse = mkConstant @Bool () False

-- | @ifThenElse@ forced and applied to a condition and the two branches.
ite :: T -> T -> T -> T
ite cond t f = force (builtin IfThenElse) `app` cond `app` t `app` f

-- | An 'Integer' constant.
con :: Integer -> T
con = mkConstant @Integer ()

-- | A 'Text' constant from a literal.
text :: String -> T
text = mkConstant @Text () . Text.pack

err :: T
err = Error ()

-- | Build a 'Name' from a 'String'. See Note [Names from strings]
name :: String -> Name
name s = Name t (Unique (uniqueFromText t))
  where
    t = Text.pack s

{-| Pack the string's bytes big-endian into an 'Int' (> 7 bytes overflow).
See Note [Names from strings] for the injectivity and fail-fast contract. -}
uniqueFromText :: Text -> Int
uniqueFromText t
  | Text.any ((> 127) . fromEnum) t =
      error ("Transform.Lib: non-ASCII name: " <> show t)
  | Text.length t > 7 =
      error ("Transform.Lib: name too long (would overflow Unique): " <> show t)
  | otherwise = Text.foldl' (\acc c -> acc * 256 + fromEnum c) 0 t
