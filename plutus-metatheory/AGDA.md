# Installing and Using Libraries in Agda

## Using `$AGDA_DIR` 

This guide explains how to install and use libraries in Agda. We use the `standard-library` as an example since it is treated like any other library—there is nothing special about it. The same steps apply to any other library you wish to use.

Suppose you have a `Trivial.agda` file in your current directory with the following content:

```agda
module Trivial where
import Data.Nat
```

When running `agda Trivial.agda`, Agda considers the following files to locate libraries:

- `$AGDA_DIR/libraries`
- `$AGDA_DIR/defaults`
- `*.agda-lib` (in the same directory as `Trivial.agda` or one level up, e.g. `trivial-project.agda-lib`)

Note that `$AGDA_DIR` may vary on your system. You can determine its actual path using: `agda --print-agda-app-dir`. On unix, it's `~/.agda`.


The `$AGDA_DIR/libraries` file lists the `.agda-lib` files of your installed libraries. Example:
```
/nix/store/j56804kxj67326j0llc3isrr8njxqlw3-standard-library-2.1.1/standard-library.agda-lib
/Users/me/plutus-metatheory.agda-lib
/some/other.agda-lib
```
Importantly, you can override it with a custom library file using: `agda --library-file=/path/to/my/libraries`

The `*.agda-lib` file, in the same directory as `Trivial.agda`, turns your current directory into an `agda` project and helps agda resolve dependencies. Example `trivial-project.agda-lib`:

```
name: trivial-project
depend: standard-library
include: .
```

The `$AGDA_DIR/defaults` file *is used when no `*.agda-lib` file is present*, and lists the libraries that are imported by default. Example:

```
standard-library
plutus-metatheory
other-lib
```

Obviously each of these must have a match in `$AGDA_DIR/libraries`.

In conclusion, when running `agda Trivial.agda`: Agda first looks for an `.agda-lib` file alongside `Trivial.agda` or one-level up. If found, it uses it to resolve library dependencies by looking in `$AGDA_DIR/libraries` (or using `--library-file`). If no `.agda-lib` file is found, it uses `$AGDA_DIR/defaults` to load default libraries. If no `$AGDA_DIR/defaults` file is found, it will probably fail.

## Using the `-i` option

Alternatively, you can use the `-i` flag to bypass all the above. Example:

```
agda Trivial.agda -i/path/to/standard-library/src -i/path/to/another/library/src
```

The above will resolve all dependencies by looking at source files directly, and only fall back to `$AGDA_DIR` if necessary.