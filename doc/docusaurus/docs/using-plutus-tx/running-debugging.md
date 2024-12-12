---
sidebar_position: X
---

# Running and Debugging Compiled Code

You can run compiled code locally (without the need of a Cardano Node)
using the `plutus` CLI tool. Besides running the code to completion, you can step through the
execution interactively much like a debugger, again using the same tool.

A pre-built version of the `plutus` CLI executable
is hosted on the [Releases] page. Alternatively, you can build the tool specifically
for your platform using Nix:

``` shell
$ nix build .#cabalProject.x86_64-linux.hsPkgs.plutus-core.components.exes.plutus
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
Two interesting sub-commands which can aid during Plutus-based script development (e.g. Aiken, Plutus Tx, Plutarch) are `--print-builtins` and `--print-cost-model` which as their name suggest print detailed lists of currently recognized builtin functions and cost model parameters, respectively.

## Compiling with the `plutus` CLI

Before you can even run or debug your code, you first need to compile and extract the plutus code from the high-level source code.
The steps for extracting plutus code vary depending on the source language you are using (Plutus Tx, Aiken, ...);
if your are using Plutus Tx as source, you can follow the instructions on [how to extract compiled code].

Although the CLI tool cannot help with compiling high-level code (e.g. Plutus Tx), it can aid with compiling and converting
between different formats and intermediate representations of plutus code.

In the following example we check a program written in the PIR (Plutus Intermediate Representation) language:

``` shell
$ echo "(program 1.1.0 (lam x (con integer) (lam y (con integer) x)))" > const.pir
$ plutus const.pir
Program passed all static checks. If you want the output result, use -o FILE or --stdout.
```

Or as a single step:

``` shell
$ echo "(program 1.1.0 (lam x (con integer) (lam y (con integer) x)))" | plutus -x pir --stdin
Program passed all static checks. If you want the output result, use -o FILE or --stdout.
```

In the command above, the `-x pir` option is necessary for letting the CLI tool know
the format/language of the supplied input. If the `-x` option is not passed, the CLI tool will try to guess the input's format/language
by looking at its filename extension `.SUFFIX` --- and will default to `plc` for `--stdin` or no suffix.
What the `-x SUFFIX` option does is instructing the CLI tool to treat subsequent filenames
as if they had a `.SUFFIX` file extension.
The following table lists the recognized suffixes and corresponding `-x` values:

|Filename Suffix|-x Value|Format Type|Description|
|---|---|---|---|


FIXME table

In case the input format is more complex (contains a non-default variable-naming scheme or annotations),
the `-n NAMING` and `-a ANNOTATION` options can be used respectively to override the defaults.

FIXME naming and annotation table

Note that the `-x`,`-n`,`-a` options are *positional*: if
there are multiple input filenames, multiple calls to these options can be used
to override previous occurrences so that you can combine code of different formats. For example:

``` shell
$ plutus -x pir FILE_PIR FILE_ALSO_PIR -x tplc FILE_NOW_TPLC -a SrcSpans FILE_TPLC_BUT_WITH_ANNOTATIONS
```

Positionining the input files one after the other (juxtaposing) as such, acts
like Haskell's function application:
it compiles individually each plutus snippet to a common *output target* and combines left-to-right
their compilation result with plutus' function application. Both inputs and final compiled output are (type)checked.

``` shell
# plutus FUNC_FILE ARG1_FILE ARG2_FILE ...
$ echo "(program 1.1.0 (lam x (lam y [(builtin subtractInteger) x y])))" > func.uplc
$ echo "(program 1.1.0 (con integer 2))" > arg2.uplc
$ echo "(program 1.1.0 (con integer 1))" | plutus func.uplc --stdin arg2.uplc
```

To override the output's target format the `-x`,`-n`,`-a` options are again used;
note that the *last occurrence* of `-x`,`-n`,`-a` will be the one that dictates the output format.

``` shell
# Checks and compiles PIR to PLC (the default)
$ plutus const.pir --stdout
(program 1.1.0 (lam x-256 (lam y-257 x-256)))
# Overrides to pir for both input&output. Can be used for prettyprinting or self-optimising (--whole-opt).
$ plutus -x pir const.pir --stdout
(program 1.1.0 (lam x-0 (con integer) (lam y-1 (con integer) x-0)))
# Overrides input to be tplc instead of guessed pir (example still works because pir is superset of plc)
# Overrides output to plc with debruijn naming
$ plutus -x tplc const.pir -x plc -n debruijn --stdout
(program 1.1.0 (lam !0 (lam !0 !2)))
```

If the output's format type is *textual* (see table above) the compiled code
will be printed to the designated output (file or stdout) in a "pretty" format.
You can change how this output looks by specifying a different `--pretty=STYLE` style (defaults to `classic`).
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


## Checking with `plutus` CLI

Depending on the input and output formats, certain checks will be run by the tool (syntax check, typechecking).
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
$ echo "(program 1.1.0 (lam x (con integer) [(builtin addInteger) x (con integer 1)]))" | plutus -x tplc --stdin -x plc -o inc.plc
$ echo "(program 1.1.0 (con bool True))" | plutus inc.plc --stdin --stdout
(program
  1.1.0
  [
    (lam x-21 [ [ (builtin addInteger) x-21 ] (con integer 1) ]) (con bool True)
  ]
)
```

There is a type error above (expected type: integer, actual type: bool),
however all static checks pass and the compiled code is successfully returned. This is
because our compilation target (output format) is `plc`, a.k.a. untyped plutus core.
Although the 2 input snippets are written in `tplc` (a.k.a. typed plutus core) and thus type-checked by the tool,
they are only typechecked *separately*; their combined, compiled output is in `plc`, a.k.a untyped plutus core,
which means no type-checking will be done statically. We could however change the output format to be plc, which would
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

## Running Compiled Code with the `plutus` CLI

We saw earlier that certain type errors cannot be caught statically for `plc`
since the language is untyped. We do have the option, however, to run
the compiled code using the interpreter and look for runtime type errors.
Running the program locally using the CLI tool is simply an extra step which is executed
after [checking]() and [compilation]() have been completed, simply by adding the `--run` option:

``` shell
$ echo "(program 1.1.0 (con bool True))" | plutus inc.plc --stdin --run
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

note :pin: FIXME
The above example shows that `plc` -- the language which actually *runs on the chain* --
is lower-level and more akin to assembly. Users that are concerned about the safety of their smart contracts
are advised instead to use a higher-level typed language (e.g. Plutus Tx) which compiles down to `plc`.

After plutus program's execution is completed (succeeded or failed), the final used budget will be printed to 'stderr'.
Because the CLI tool employs the same `plc` interpreter as the one that the Cardano node runs, we can be sure
that the program's execution result & budget match precisely those computed on the chain (assuming same program
and same cost model).

You can pass a maximum CPU and/or MEMory budget that is allowed to be spent with the `--budget=CPU` or `-budget=,MEM` or `--budget=CPU,MEM` options; if given budget runs outs, the execution will fail and stop earlier.
If there is no CPU and/or MEM limit given, the budget is practically unlimited.

``` shell
$ echo "(program 1.1.0 (con integer 1))" | $plutus inc.plc --stdin --run --budget=229307,903
Program passed all checks. No output file was written, use -o or --stdout.
An error has occurred:
The machine terminated part way through evaluation due to overspending the budget.
The budget when the machine terminated was:
({cpu: -1
| mem: 1})
Negative numbers indicate the overspent budget; note that this only indicates the budget that was needed for the next step, not to run the program to completion.
$ echo "(program 1.1.0 (con integer 1))" | $plutus inc.plc --stdin --run --budget=,903
Program passed all checks. No output file was written, use -o or --stdout.
Execution succeeded. Final Term:
(con integer 2)
Remaining budget: ExBudget {exBudgetCPU = ExCPU 9223372036854546499, exBudgetMemory = ExMemory 1}
Used budget: ExBudget {exBudgetCPU = ExCPU 229308, exBudgetMemory = ExMemory 902}
```

The executable takes as input-arguments the paths containing the plutus code to run. For example, consider the plutus code
that expects two integers and adds them together:

``` shell
$ echo "(program 1.1.0 (lam x (lam y [(builtin subtractInteger) x y])))" > add.uplc
$ plutus add.uplc
Program passed all static checks. No output file was written, use -o or --stdout.
```

Same as above but using instead the `--stdin` option:

``` shell
$ echo "(program 1.1.0 (lam x (lam y [(builtin subtractInteger) x y])))" | plutus --stdin
Program passed all static checks. No output file was written, use -o or --stdout.
```

Fixing the syntax error above makes the evaluator succeed, returning the final value
as the result of the evaluation (a function in our example):

``` shell
$ echo "(program 1.1.0 (lam x (lam y [(builtin subtractInteger) x y])))" | plutus --stdin --stdout
(program 1.1.0 (lam x-0 (lam y-1 [ [ (builtin subtractInteger) x-0 ] y-1 ])))
```

note :: pin FIXME

As shown in [compilation](FIXME) section, you are free to mix and match
different input languages (pir/tplc/plc); as long as the output target at the CLI
is set to `plc`, their compiled output will be `--run` through the
the local `plc` interpreter (same interpreter as on-chain). Alternatively, you can
target `tplc` which changes to a different, `tplc` interpreter. Although
the `tplc` interpreter behaves the same as the default `plc` interpreter for *type correct* programs,
it is not advised to use it because it comes with caveats: cannot execute `plc` code,
cannot have budget accounting and budget limits, runs way slower and your program must be fully type correct.
The last point is not necessarily a caveat, but it diverges from the on-chain behaviour:
the `tplc` interpreter accepts less programs than the default `plc` interpreter.

## Debugging Compiled Code

The `plutus` tool's built-in debugger provides another way to
to execute compiled plutus code. The `--debug` option
starts a TUI (Terminal User Interface) in your console:

``` shell
$ plutus inc.plc --debug
```

The debugger will load the program, display its text code on a window,
and wait for a user command to start executing it using the `plc` interpreter.
The commands available to the user are:

|Keyboard Shortcut|Command|
|-----|-----|
|?|Show help dialog|
|Esc|Quit help dialog or debugger|
|Ctrl+up/down/left/right|Resize window|
|Tab|Switch focus to other window|
|s|Step once the interpreter|

Unlike the `--run` option, the `step` command does not execute the program
to completion. Instead, the interpreter is moved one "budgeting" step forward ---
the smallest step possible that is accounted for and subtracted from the current budget ---
and the lower window will be updated to show the remaining budget.
You can still combine `--debug` with the `--budget=CPU,MEM` option to limit the initial total budget given.

Every time an interactive step is taken, the debugger
highlights the code region (subterm) that the `plc` interpreter
is about to "step into" (execute) next, in the program's text window. A separate
"Logs" window is kept up-to-date with any printed plutus' `trace`s and debugger's messages.

FIXME: add screenshot
