# Pretty printing

This document talks about problems and possible solutions to the hard problem of configurable pretty-printing.

## Cases

"Configurable" means that you can switch the way pretty-printing works by tweaking various flags. There are several situations here:

1. a pure function throws an exception which uses some pretty-printing inside. Since exceptions should be thrown only in the case of an internal error, the most sensible thing here seems to be just not to make pretty-printing configurable. Choose the way that dumps as much available information as possible in the most readable way.
2. a pure function uses pretty-printing to convert some expression into `Text` and return it as a part of the result or process somehow. Just don't do that.
3. an endpoint that does pretty-printing. In that case passing a pretty-printing config explicitly is fine as well as wrapping the resulting type into `ReaderT RenderConfig` or similar.
4. an effecful function that does pretty-printing and can be used as a building block. Wrap in `ReaderT RenderConfig` or similar.

## Rules

- Postpone pretty-printing as much as possible.
- If we're doing configurable pretty-printing, then let's do it for real. At the moment this document was written no `RenderConfig` were passed around -- only hardcoded stuff like `debugText` and `prettyText` was used.
- Separate `Pretty` instances from data types, because 1) they pollute code and 2) different pretty-printing strategies must not be interleaved. (I would be happy if we apply the same policy to pattern functors of our data types and their `recursion-schemes` instances as they are nothing but noise)

## Approaches

But how to configure pretty-printing of exact data types? There are several ways:

### 1. The `PrettyCfg` class which we use currently:

```haskell
class PrettyCfg a where
    prettyCfg :: RenderConfig -> a -> Doc ann
    default prettyCfg :: Pretty a => RenderConfig -> a -> Doc ann
    prettyCfg _ = pretty
```

Pros:

- Simple and usable.

Cons:

- If used naively, completely distinct ways to do pretty-printing become interleaved in code which looks ugly and unreadable.
- Ideally we'd like to make the approach extensible, i.e. parameterize over `cfg` rather than hardcode it to `RenderConfig`. But then the `PrettyCfg` instance for `NormalizedType` becomes:

```haskell
instance PrettyCfg cfg (Type tyname a) => PrettyCfg cfg (NormalizedType tyname a) where
    prettyCfg cfg (NormalizedType ty) = prettyCfg cfg ty
```

You may think "yes, what's bad about that?". The bad thing is that if a data type mentions not just `Type`, but also `Kind`, `NormalizedType` and `Term` (`TypeError` mentions all these), then you have to explicitly constrain each of these data types by `PrettyCfg cfg` which is ugly boilerplate.

- A quote from a discussion:

> Also we now have both `Pretty` and `PrettyCfg` used, so the `PrettyCfg` instances of polymorphic types cause minor problems sometimes. Consider

> `instance PrettyCfg a => PrettyCfg (TermOf a)`

> Now if I have `TermOf Bool` I get an error about `Bool` not having a `PrettyCfg` instance.

### 2. Have a single `Pretty` class, but wrap data types which support configurable pretty-printing like that:

```haskell
data RenderConfigured a = RenderConfigured
    { _renderConfig          :: RenderConfig
    , _renderConfiguredValue :: a
    }

type PrettyCfg a = Pretty (Configured a)

prettyCfg :: PrettyCfg a => RenderConfig -> a -> Doc b
prettyCfg = pretty .* RenderConfigured
```

It's the same thing as (1), but less convenient, so not really an option.

### 3. Lift `RenderConfig` to the type level like

```haskell
f :: Term ('RenderConfig 'Debug 'Formatted 'Annotated) -> ...
```

Pros:

- A single `Pretty` class unless you need to return something from `pretty :: a -> Doc ann` via `ann` which we do ned, see below.
- Easy to write multiple `Pretty` instances for the same data type and they're nice.

Cons:

- You can not use the same trick to return annotations from `pretty`, because it's universally quantified over `ann`. And we need them to emulate precedence for example, i.e. like with the `Show` class, but at the type level. This means that we still need a separate class like `PrettyCfg` which defeats the whole purpose of lifting configuration to the type level.
- The boilerplate-y constraints issue described above applies here as well.
- You have to either add a type variable for each data type to store `RenderConfig` or use existing annotations which do not always propagate recursively. They propagate recursively in, for example,

```haskell
-- | A 'Type' assigned to expressions.
data Type tyname a = TyVar a (tyname a)
                   | TyFun a (Type tyname a) (Type tyname a)
                   | TyFix a (tyname a) (Type tyname a) -- ^ Fix-point type, for constructing self-recursive types
                   | TyForall a (tyname a) (Kind a) (Type tyname a)
                   | TyBuiltin a TypeBuiltin -- ^ Builtin type
                   | TyInt a Natural -- ^ Type-level size
                   | TyLam a (tyname a) (Kind a) (Type tyname a)
                   | TyApp a (Type tyname a) (Type tyname a)
                   deriving (Functor, Show, Generic, NFData, Lift)
```

(`a` goes to `Kind` and to `tyname`) and in most other data types, but not in

```haskell
data TypeError a = InternalError -- ^ This is thrown if builtin lookup fails
                 | KindMismatch a (Type TyNameWithKind ()) (Kind ()) (Kind ())
                 | TypeMismatch a (Term TyNameWithKind NameWithType ()) (Type TyNameWithKind ()) (NormalizedType TyNameWithKind ())
                 | OutOfGas
                 deriving (Show, Eq, Generic, NFData)
```

This can be solved by requiring the rightmost type variable to always propagate recursively and if you need something that does not propagate, just add another type variable. But this is an additional overhead again.

### 4. Native `prettyprinter` annotations

Instead of annotating data types, we can annotate resulting `Doc`s.

Pros:

- Instances can be defined nicely like with (3).
- Built-in support.

Cons:

- Built-in support is bad. You need to roll out your own class, because `pretty` from `Pretty` returns `Doc ann` for any universally quantified `ann`.
- `Doc` is an intermediate representation between a data type and `Text`/`String` which means that you still need to pass in an additional argument to communicate how exactly you want to pretty-print data. E.g. a function that pretty-prints a data type somewhere inside has to receive a `Proxy ann`.
- Boilerplate-y constraints as usual.
- Examples render `Doc`s [manually](http://hackage.haskell.org/package/prettyprinter-1.2.1/docs/src/Data.Text.Prettyprint.Doc.Render.Tutorials.TreeRenderingTutorial.html#render) which requires knowledge on the internals of the library. I think this is irrelevant for us, though.

## Current plan.

Use 1 and separate various `Pretty` instances across files without defining actual instances, i.e. define functions like `prettyKind :: Kind a -> Doc ann`, `prettyType :: Type tyname name a -> Doc ann` in each separate file. Then turn those functions into instances in a single file that defines `RenderConfig`. This is dumb, but we need something working.
