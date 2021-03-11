This document contains the types used to represent Plutus Core abstract syntax trees for the benefit of readers not familiar with the codebase.  All of these are parametrised over a type `ann` of annotations, which is currently always `()`.  Every AST node contains an annotation.  Many of the types below are also parametric over types `Name` and `TyName`, names of types and variables respectively;  both of these are usually instantiated to the `Name` type:

The type used to represent ASTs are as follows:

```haskell
-- From PlutusCore.Name

data Name ann = Name
    { nameAttribute :: ann
    , nameString    :: Data.Text.Text
    , nameUnique    :: Unique
    }
```
Here `nameString` is a textual name, obtained from program source for example.  This is only included for readability in error messages and textual representations of ASTs .  Names are disambiguated early in the compilation process, each being given a unique `Unique` identifier, essentially an `Integer`. The rest of the information in a name can be discarded without any semantic loss. We could also use de Bruijn indices here.

The main AST types are given below.  These are taken from `PlutusCore.Core.Type` and are slightly simplified (derived instances are omitted for example). The definitions should be fairly self-explanatory.

```haskell
data Kind ann = Type ann | KindArrow ann (Kind ann) (Kind ann)

data TypeBuiltin = TyByteString | TyInteger | TyString

data Type tyname ann
    = TyVar      ann (tyname ann)
    | TyFun      ann (Type tyname ann) (Type tyname ann)
    | TyIFix     ann (Type tyname ann) (Type tyname ann)
    | TyForall   ann (tyname ann) (Kind ann) (Type tyname ann)
    | TyBuiltin  ann TypeBuiltin
    | TyLam      ann (tyname ann) (Kind ann) (Type tyname ann)
    | TyApp      ann (Type tyname ann) (Type tyname ann)

data BuiltinName = AddInteger | SubtractInteger | ...

data Builtin ann
    = BuiltinName ann BuiltinName  -- true built-in names.
    | DynBuiltinName ann DynamicBuiltinName  -- names of extensible built-ins, definition omitted.

data Constant ann
    = BuiltinInt ann Integer
    | BuiltinBS  ann BSL.ByteString
    | BuiltinStr ann String

data Term tyname name ann
    = Var      ann (name ann)
    | TyAbs    ann (tyname ann) (Kind ann) (Term tyname name ann)
    | LamAbs   ann (name ann) (Type tyname ann) (Term tyname name ann)
    | Apply    ann (Term tyname name ann) (Term tyname name ann)
    | Constant ann (Constant ann)
    | Builtin  ann (Builtin ann)
    | TyInst   ann (Term tyname name ann) (Type tyname ann)
    | Unwrap   ann (Term tyname name ann)
    | IWrap    ann (Type tyname ann) (Type tyname ann) (Term tyname name ann)
    | Error    ann (Type tyname ann)

data Version ann = Version ann Natural Natural Natural

data Program tyname name ann = Program ann (Version ann) (Term tyname name ann)
```
