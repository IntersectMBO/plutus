# Serialisation using the flat format.

We will serialise the program `(program 11.22.33 (con integer 11))` compiled to untyped plutus core, using DeBruijn indices.

First, lets convert the program to the desired representation.

> stack exec plc -- convert --untyped --if plc --of flat -o program.flat <<EOF
> (program 11.22.33 (con integer 11))
> EOF

Now, let's take a look at the output.

> xxd -b program.flat
> 00000000: 00001011 00010110 00100001 01001000 00000101 10000001  ..!H..

## The program preamble.

We define `Program` in the `Language.PlutusCore.Core.Type` haskell module like this:

> -- | A 'Program' is simply a 'Term' coupled with a 'Version' of the core language.
> data Program tyname name uni fun ann = Program ann (Version ann) (Term tyname name uni fun ann)
>    deriving (Show, Functor, Generic, NFData, Hashable)

Because the `Program` data type has only one constructor we know that flat will not waste any space serialising it. `ann` will always be (for serialised ASTs) `()`, which similarly to the `Program` data type has only one constructor and flat will not serialise it.

Next, the `Version` is a tuple of 3 `Natural` numbers, which are encoded as variable length unsigned integers. Because all the version numbers can fit in a 7 bit word, we only need one byte to store each of them. Also, the first bit, which represents the list constructor will always be `0` (standing for `Last`), resulting in:

> 0 (*Last*) 000 (*Unused*) 1011   (*11 in binary*)
> 0 (*Last*) 00  (*Unused*) 10110  (*22 in binary*)
> 0 (*Last*) 0   (*Unused*) 100001 (*33 in binary*)

## The integer constant `1`.

Let's take a quick look at how we defined untyped plutus terms, in the `Language.UntypedPlutusCore.Core.Type` to see what we need to serialise.

> data Term name uni fun ann
>     = Constant ann (Some (ValueOf uni))
>     | Builtin ann fun
>     | Var ann name
>     | LamAbs ann name (Term name uni fun ann)
>     | Apply ann (Term name uni fun ann) (Term name uni fun ann)
>     | Delay ann (Term name uni fun ann)
>     | Force ann (Term name uni fun ann)
>     | Error ann
>     deriving stock (Show, Functor, Generic)
>     deriving anyclass (NFData)

We need to encode the `Constant`, signed integer value `11`. Terms are encoded using 4 bits, and the `Constant` term has tag 4 (as defined in the specification, and the `Language.UntypedPlutusCore.Core.Instance.Flat` module). This results in:

> 0 (*Unused*) 100 (*4 in binary*)

We find the definition of serialisation for constant kinds in the `Language.PlutusCore.Flat` haskell module:

> -- See Note [The G, the Tag and the Auto].
> instance (Closed uni, uni `Everywhere` Flat) => Flat (Some (ValueOf uni)) where
>     encode (Some (ValueOf uni x)) =
>       encode (Some $ TypeIn uni) <> bring (Proxy @Flat) uni (encode x)

The first part is an encoding of the type of constant, and the second part is the constant itself.

For the `Default` universe we have the following definitions for constant types:

> -- See Note [Stable encoding of tags].
> encodeUni DefaultUniInteger    = [0]
> encodeUni DefaultUniByteString = [1]
> encodeUni DefaultUniString     = [2]
> encodeUni DefaultUniChar       = [3]
> encodeUni DefaultUniUnit       = [4]
> encodeUni DefaultUniBool       = [5]


So we see how, for the integer type we care about the type is encoded as a list containing the id `0`. We know that we are using 3 bits to store the type of constant, so the encoding will be:

> 1 (*Cons*) 0000 (The `0` tag using 4 bits for storage) 0 (*Nil*)

The annotation will not be serialised, and we are left with the constant itself. Because it is an variable length signed integer, we first need to find out its value after conversion to the `ZigZag` format.

> stack repl plutus-core:exe:plc
> ghci> import Data.ZigZag
> ghci> zigZag (11 :: Integer)
> 22

Next, we need to encode the variable length unsigned integer `22`. We only need one byte (as it fits in the available 7 bits), so we end up with the following:

> 0 (*Last*) 00 (*Unused*) 10110 (*22 in binary*) 000001 (*Padding to byte size*)

## Note

You may notice how in the rest of the codebase we use the `CBOR` format to serialise
everything.

So why did we choose to switch to `Flat` for on-chain serialisation?

`CBOR` pays a price for being a self-describing format. The size of the serialised
terms is consistently larger than a format that is not self-describing. Running the
`flat` benchmarks will show flat consistently out-performing `CBOR` by about 35%
without using compression.

> stack bench plutus-benchmark:flat
> cat plutus-benchmark/flat-sizes.md

> ** Contract: crowdfunding-indices **
> Codec            Size    Of minimum   Of maximum
> flat             8148    2.240308     0.62652826
> cbor             13005   3.5757492    1.0
> 
> ** Contract: escrow-indices **
> Codec            Size    Of minimum   Of maximum
> flat             8529    2.2004645    0.6302838 
> cbor             13532   3.491228     1.0
> 
> ** Contract: future-indices **
> Codec            Size    Of minimum   Of maximum
> flat             17654   2.19141      0.6628619 
> cbor             26633   3.305983     1.0
> 
> ** Contract: game-indices **
> Codec            Size   Of minimum   Of maximum
> flat             5158   2.2290406    0.6254395 
> cbor             8247   3.5639584    1.0
> 
> ** Contract: vesting-indices **
> Codec            Size    Of minimum   Of maximum
> flat             8367    2.2288227    0.6273525 
> cbor             13337   3.5527437    1.0
