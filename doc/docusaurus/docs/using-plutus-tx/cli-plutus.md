---
sidebar_position: 40
---

# CLI tool for Plutus

You can locally (without starting a Cardano Node) [run](#running) or [debug](#debugging) compiled code
by using the `plutus` CLI tool. This tool allows you also to [optimise](#converting) compiled code, [convert](#converting) between code formats,
and [check](#checking) code for common issues. A pre-built version of the `plutus` CLI executable
can be found on the [Latest release](https://github.com/IntersectMBO/plutus/releases/latest) page in the repository. Alternatively, you can build the tool
using Nix, specifically for your platform:

``` shell
$ nix build .#cabalProject.$(nix eval nixpkgs#stdenv.buildPlatform.system).hsPkgs.plutus-core.components.exes.plutus
```

To consult the tool's usage you can invoke `plutus --help` in a command line:

``` shell
$ plutus --help
USAGE: plutus [FILES...] [--stdin] [-o FILE | --stdout] [--run|--bench|--debug]...
  -h             --help               Show usage
  -V             --version            Show version
  -q             --quiet              Don't print text (error) output; rely only on exit codes
  -v             --verbose            Print more than than the default
                 --print-builtins     Print the Default universe & builtins
                 --print-cost-model   Print the cost model of latest Plutus Version as JSON
                 --stdin              Use stdin
  -e[NAME]       --example[=NAME]     Use example NAME as input. Leave out NAME to see the list of examples' names
  -p STYLE       --pretty=STYLE       Make program's textual-output&error output pretty. Ignored for non-textual output (flat/cbor). Values: `classic`, `readable, `classic-simple`, `readable-simple`
  -o FILE                             Write compiled program to file
                 --stdout             Write compiled program to stdout
  -O[INT]                             Set optimisation level; default: 0 , safe optimisations: 1, >=2: unsafe optimisations
                 --whole-opt          Run an extra optimisation pass after all inputs are applied together. Ignored if only 1 input given.
  -x SUFFIX                           Causes all files following this option on the command line to be processed as if they had the suffix SUFFIX
  -n NAMING      --nam=NAMING         Change naming to `name` (default), `debruijn` or `named-debruijn`
  -a ANNOTATION  --ann=ANNOTATION     Change annotation to `unit` (default) or `srcspan`
                 --run                Compile and run
                 --bench[=SECS]       Compile then run repeatedly up to these number of seconds (default:10) and print statistics
                 --debug[=INTERFACE]  Compile then Debug program after compilation. Uses a `tui` (default) or a `cli` interface.
                 --debug-dir[=DIR]    When `--debug`, try to search for PlutusTx source files in given DIR (default: .)
                 --budget=INT,INT     Set CPU,MEM budget limit. The default is no limit. Only if --run, --bench, or --debug is given
```

Two interesting sub-commands which can aid during Plutus-based script development (e.g. Aiken, Plutarch, Plutus Tx) are `--print-builtins` and `--print-cost-model` which as their name suggest print detailed lists of currently recognized builtin functions and cost model parameters, respectively.

## Converting Code with the CLI {#converting}

Before you can even run or debug your code, you first need to compile and extract the plutus code from the high-level source code.
The steps for extracting plutus code vary depending on the source language you are using (Plutus Tx, Aiken, ...);
if your are using Plutus Tx as source, you can follow the instructions on [how to inspect compiled code](./inspecting.md#inspecting-the-compiled-code).

Although the CLI tool cannot help with compiling high-level code (e.g. Plutus Tx), it can aid with compiling and converting
between formats and intermediate representations of lower-level plutus code (PIR, TPLC, UPLC).

In the following example we check a program written in the PIR (Plutus Intermediate Representation) language:

``` shell
$ echo '(program 1.1.0 (lam x (con integer) (lam y (con integer) x)))' > const.pir
$ plutus const.pir
Program passed all static checks. If you want the output result, use -o FILE or --stdout.
```

Or as a single command:

``` shell
$ echo '(program 1.1.0 (lam x (con integer) (lam y (con integer) x)))' | plutus -x pir --stdin
Program passed all static checks. If you want the output result, use -o FILE or --stdout.
```

In the command above, the `-x pir` option is necessary for letting the CLI tool know
the format/language of the supplied input. If the `-x` option is not passed, the CLI tool will try to guess the input's format/language
by looking at its filename extension `.SUFFIX` &mdash; will default to `uplc` for `--stdin` or missing/other suffix.
What the `-x SUFFIX` option does is instructing the CLI tool to treat subsequent filenames
as if they had a `.SUFFIX` file extension.
The following table lists some recognized suffixes and corresponding `-x` values:

|Filename Suffix|-x Option|Format Type|Description|
|---|---|---|---|
|.uplc|-x uplc|Textual|Untyped Plutus Core with Names|
|.tplc|-x tplc|Textual|Typed Plutus Core with Names|
|.pir|-x pir|Textual|PIR with Names|
|.data|-x data|Binary|Values of `Data` serialised in CBOR|
|.data-txt|-x data-txt|Textual|Values of `Data` in Haskell's `Show` format|
|.uplc-flat|-x uplc-flat|Binary|Untyped PlutusCore with NamedDeBruijn serialised in Flat|
|.uplc-cbor|-x uplc-cbor|Binary|Untyped PlutusCore with DeBruijn serialised in CBOR|

In case the input format is more complex (contains a non-default variable-naming scheme or annotations),
the `-n NAMING` and `-a ANNOTATION` options can be used respectively to override the defaults.

|-n Short Option|-n Long Option|Description|
|---|---|---|
|-n n|-n name|Use descriptive textual names for variables|
|-n d|-n debruijn|Use debruijn indices for variables|
|-n nd|-n named-debruijn|Use name with debruijn index for variables: "name-index"|

|-a Option|Description|
|---|---|
|-a unit|Code does not contain any annotations (default)|
|-a srcspan|Code is annotated with source spans|

Note that the `-x`,`-n`,`-a` options are *positional*: if
there are multiple input filenames, multiple calls to these options can be used
to override previous occurrences so that you can combine code of different formats. For example:

``` shell
# plutus -x pir FILE_PIR FILE_ALSO_PIR -x tplc FILE_NOW_TPLC -a srcspan FILE_TPLC_BUT_WITH_ANNOTATIONS
```

Positioning the input files one after the other (juxtaposing) as such, acts
like Haskell's function application:
it compiles individually each plutus snippet to a common *output target* and combines left-to-right
their compilation result with plutus' function application. Both inputs and final compiled output are (type-)checked.

``` shell
# plutus FUNC_FILE ARG1 ARG2 ...
$ echo '(program 1.1.0 (lam x (lam y [(builtin appendString) x y])))' > append.uplc
$ echo '(program 1.1.0 (con string "Hello, "))' > hello.uplc

# "Hello, world"
$ echo '(program 1.1.0 (con string "world"))' | plutus append.uplc hello.uplc --stdin --stdout
(program
  1.1.0
  [
    [
      (lam x-0 (lam y-1 [ [ (builtin appendString) x-0 ] y-1 ]))
      (con string "Hello, ")
    ]
    (con string "world")
  ]
)
# "worldHello, " Note the flip of stdin and hello arguments
$ echo '(program 1.1.0 (con string "world"))' | plutus append.uplc --stdin hello.uplc --stdout
(program
  1.1.0
  [
    [
      (lam x-0 (lam y-1 [ [ (builtin appendString) x-0 ] y-1 ]))
      (con string "world")
    ]
    (con string "Hello, ")
  ]
)
```

To override the output's target format the `-x`,`-n`,`-a` options are again used;
note that the *last occurrence* of `-x`,`-n`,`-a` will be the one that dictates the output format.

``` shell
# Checks and compiles PIR to UPLC (the default)
$ plutus const.pir --stdout
(program 1.1.0 (lam x-256 (lam y-257 x-256)))
# Overrides to pir for both input&output. Can be used for pretty-printing or self-optimising (--whole-opt).
$ plutus -x pir const.pir --stdout
(program 1.1.0 (lam x-0 (con integer) (lam y-1 (con integer) x-0)))
# Overrides input to be tplc instead of guessed pir (example still works because pir is superset of tplc)
# Overrides output to uplc with debruijn naming
$ plutus -x tplc const.pir -x uplc -n debruijn --stdout
(program 1.1.0 (lam !0 (lam !0 !2)))
```

If the output's format type is *textual* (see table above) the compiled code
will be printed to the designated output (file or stdout) in a "pretty" format.
You can change how this output looks by specifying a different `-p STYLE` style (defaults to `classic`).
Note that *textual output* with pretty style other than the default may not be recognized
back again as *textual input* to the CLI.

``` shell
$ plutus sub.pir -x pir --stdout
(program
  1.1.0
  (lam
    x-0
    (con integer)
    (lam y-1 (con integer) [ [ (builtin subtractInteger) x-0 ] y-1 ])
  )
)
$ plutus sub.pir -x pir --stdout --pretty=readable-simple
program 1.1.0 (\(x : integer) (y : integer) -> subtractInteger x y)
```

|-p Option|Description|
|---|---|
|-p classic|Lisp-like syntax with unique variable names  (default)|
|-p classic-simple|Lisp-like syntax with ambiguous (no unique) variable names|
|-p readable|Succinct syntax with unique variable names|
|-p readable-simple|Succinct syntax with ambiguous (no unique) variable names|

## Checking Code with the CLI {#checking}

Depending on the input and output formats, certain checks will be run by the tool (syntax check, type checking).
Any errors during these checks will be reported to `stderr`:

``` shell
$ echo "(program 1.1.0 (lam x (con integer) [(builtin addIntege) x (con integer 1)]))" | plutus -x tplc --stdin
<stdin>:1:56:
  |
1 | (program 1.1.0 (lam x (con integer) [(builtin addIntege) x (con integer 1)]))
  |                                                        ^
Unknown built-in function 'addIntege' at <stdin>:1:56.
Parsable functions are  [ addInteger, ...]
```

The tool can be made more `--verbose` about the checking/compilation process, or
more `--quiet` if you prefer to rely solely on the tool's exit status.

Fixing the typo in the example above, then applying it to an argument using the CLI's juxtaposition:

``` shell
$ echo "(program 1.1.0 (lam x (con integer) [(builtin addInteger) x (con integer 1)]))" | plutus -x tplc --stdin -x uplc -o inc.uplc
$ echo "(program 1.1.0 (con bool True))" | plutus inc.uplc --stdin --stdout
(program
  1.1.0
  [
    (lam x-21 [ [ (builtin addInteger) x-21 ] (con integer 1) ]) (con bool True)
  ]
)
```

There is a type error above (expected type: integer, actual type: bool),
however all static checks pass and the compiled code is successfully returned. This is
because our compilation target (output format) is `uplc`, a.k.a. untyped plutus core.
Although the 2 input snippets are written in `tplc` (a.k.a. typed plutus core) and thus type-checked by the tool,
they are only typechecked *separately*; their combined, compiled output is in `uplc`, a.k.a untyped plutus core,
which means no type-checking will be done statically. We could however change the output format to be tplc, which would
raise the type error:

``` shell
$ echo "(program 1.1.0 (lam x (con integer) [(builtin addInteger) x (con integer 1)]))" | plutus -x tplc --stdin -o inc.tplc
$ echo "(program 1.1.0 (con bool True))" | plutus -x tplc inc.tplc --stdin --stdout
Failed to typecheck fully-applied program. The error was:
Error from the PLC compiler:
Type mismatch at ()
Expected a term of type
  '(con integer)'
But found one of type
  '(con bool)'
Namely,
  '(con bool True)'
```

## Running Code with the CLI {#running}

We saw earlier that certain type errors cannot be caught statically for `uplc`
since the language is untyped. We do have the option, however, to run
the compiled code using the interpreter and look for runtime type errors.
Running the program locally using the CLI tool is simply an extra step which is executed
after [checking](#checking) and [compilation](#converting) have been completed, simply by adding the `--run` option:

``` shell
$ echo "(program 1.1.0 (con bool True))" | plutus inc.uplc --stdin --run
Program passed all static checks. If you want the output result, use -o FILE or --stdout.
Running the program: An error has occurred:
Could not unlift a value:
Type mismatch: expected: integer; actual: bool
Caused by: addInteger True 1
```

Other times catching such "type errors" at runtime is not even possible; consider for example:

``` shell
# if True then "" else 5
$ echo '(program 1.1.0 [(force (builtin ifThenElse)) (con bool True) (con string "") (con integer 5)])' | plutus --stdin --run
Program passed all static checks. If you want the output result, use -o FILE or --stdout.
Running the program: Execution succeeded. Final Term:
(con string "")
Used budget: ExBudget {exBudgetCPU = ExCPU 204149, exBudgetMemory = ExMemory 901}
```

> :pushpin: **NOTE**
> The above example shows that `uplc` -- the language which actually *runs on the chain* --
> is lower-level and more akin to assembly. Users that are concerned about the safety of their smart contracts
> are advised instead to develop in a higher-level typed language (e.g. Plutus Tx) which compiles down to `uplc`.

After plutus program's execution is completed (succeeded or failed), the final used budget will be printed to `stderr`.
Because the CLI tool employs the same `uplc` interpreter as the one that the Cardano node runs, we can be sure
that the program's execution result&budget match *precisely* &mdash; assuming same program
and cost model &mdash; the result&budget computed by the chain.

You can pass a maximum CPU and/or Memory budget that is allowed to be spent with the `--budget=CPU` or `-budget=,MEM` or `--budget=CPU,MEM` options; if given budget runs out, the execution will fail and stop earlier.
If there is no CPU and/or MEM limit given, the budget is practically unlimited.

``` shell
$ echo "(program 1.1.0 (con integer 1))" | $plutus inc.uplc --stdin --run --budget=229307,903
Program passed all checks. No output file was written, use -o or --stdout.
An error has occurred:
The machine terminated part way through evaluation due to overspending the budget.
The budget when the machine terminated was:
({cpu: -1
| mem: 1})
Negative numbers indicate the overspent budget; note that this only indicates the budget that was needed for the next step, not to run the program to completion.

$ echo "(program 1.1.0 (con integer 1))" | $plutus inc.uplc --stdin --run --budget=,903
Program passed all checks. No output file was written, use -o or --stdout.
Execution succeeded. Final Term:
(con integer 2)
Remaining budget: ExBudget {exBudgetCPU = ExCPU 9223372036854546499, exBudgetMemory = ExMemory 1}
Used budget: ExBudget {exBudgetCPU = ExCPU 229308, exBudgetMemory = ExMemory 902}
```

As shown in [compilation](#converting) section, you are free to mix and match
different input languages (pir/tplc/uplc); as long as the output target at the CLI
is set to `uplc`, their compiled output will be `--run` through the
the local `uplc` interpreter (same interpreter as that on chain).

> :pushpin: **NOTE**
> Attempting to run a `tplc` target will use a `tplc` interpreter. Although
> the `tplc` interpreter behaves the same as the default `uplc` interpreter (for *type correct* programs),
> it comes with caveats: cannot execute `uplc` code,
> cannot have budget accounting and budget limits, runs way slower and your program must be fully type correct.
> The last point is not necessarily a caveat, but it diverges from the on-chain behavior:
> the `tplc` interpreter accepts less programs than the chain (and the default `uplc` interpreter) would accept.

## Debugging Code with the CLI *(Experimental)*

The `plutus` tool's built-in debugger provides a different way to
to execute compiled plutus code (only if you are targeting untyped plutus core, a.k.a `uplc`).
The `--debug` option starts a TUI (Terminal User Interface) in your console:

``` shell
$ plutus inc.uplc --debug
```

The debugger will load the program, display its text code on a window,
and wait for a user command to start executing it using the `uplc` interpreter.
The commands available to the user are:

|Keyboard Shortcut|Command|
|-----|-----|
|?|Show help dialog|
|Esc|Quit help dialog or debugger|
|Ctrl+up/down/left/right|Resize window|
|Tab|Switch focus to other window|
|s|Step once the interpreter|

Unlike the `--run` option, the `step` command does not execute the program
to completion. Instead, the `uplc` interpreter is moved one "budgeting" step forward &mdash;
the smallest step possible that gets accounted for and subtracted from the current budget &mdash;
and the screen will be updated to show the remaining budget.
You can still combine `--debug` with the `--budget=CPU,MEM` option to limit the initial total budget given.

Every time an interactive step is taken, the debugger
highlights the code region (sub-term) that the `uplc` interpreter
is about to "step into" (execute) next, in the program's text window. A separate
"Logs" window is kept up-to-date with any printed plutus' `trace`s and debugger's messages.

FIXME: add screenshot
