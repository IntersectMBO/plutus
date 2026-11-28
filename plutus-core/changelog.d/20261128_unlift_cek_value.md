### Changed

The CEK evaluator and its environment now use the unlifted type `CekValueU`.
Builtin interfaces still take the lifted type `CekValue`. Code that constructs or matches
values directly should import `CekValueU (..)` and wrap the constructor in `CekValue`,
for example `CekValue (VCon c)`. The `RandomAccessList` and `IsList` interfaces to
`CekValEnv` continue to use lifted values.

The main evaluator's `Cek.Internal.Context` also has kind `UnliftedType`, so its
`Show` instance is no longer available. The steppable evaluator uses its own lifted context.
