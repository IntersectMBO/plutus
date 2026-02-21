"use strict";
(self["webpackChunkdocusaurus"] = self["webpackChunkdocusaurus"] || []).push([[1483],{

/***/ 4757:
/***/ ((__unused_webpack_module, __webpack_exports__, __webpack_require__) => {

// ESM COMPAT FLAG
__webpack_require__.r(__webpack_exports__);

// EXPORTS
__webpack_require__.d(__webpack_exports__, {
  assets: () => (/* binding */ assets),
  contentTitle: () => (/* binding */ contentTitle),
  "default": () => (/* binding */ MDXContent),
  frontMatter: () => (/* binding */ frontMatter),
  metadata: () => (/* reexport */ site_docs_using_plinth_cli_plutus_md_d65_namespaceObject),
  toc: () => (/* binding */ toc)
});

;// ./.docusaurus/docusaurus-plugin-content-docs/default/site-docs-using-plinth-cli-plutus-md-d65.json
const site_docs_using_plinth_cli_plutus_md_d65_namespaceObject = /*#__PURE__*/JSON.parse('{"id":"using-plinth/cli-plutus","title":"CLI tool for Plutus","description":"The plutus CLI tool allows you to:","source":"@site/docs/using-plinth/cli-plutus.md","sourceDirName":"using-plinth","slug":"/using-plinth/cli-plutus","permalink":"/pr-preview/docs/pr-7403/using-plinth/cli-plutus","draft":false,"unlisted":false,"editUrl":"https://github.com/IntersectMBO/plutus/edit/master/doc/docusaurus/docs/using-plinth/cli-plutus.md","tags":[],"version":"current","sidebarPosition":40,"frontMatter":{"sidebar_position":40},"sidebar":"tutorialSidebar","previous":{"title":"Inspecting Compilation and Compiled Code","permalink":"/pr-preview/docs/pr-7403/using-plinth/inspecting"},"next":{"title":"Working with scripts","permalink":"/pr-preview/docs/pr-7403/category/working-with-scripts"}}');
// EXTERNAL MODULE: ./node_modules/react/jsx-runtime.js
var jsx_runtime = __webpack_require__(4848);
// EXTERNAL MODULE: ./node_modules/@mdx-js/react/lib/index.js
var lib = __webpack_require__(8453);
;// ./docs/using-plinth/cli-plutus.md


const frontMatter = {
	sidebar_position: 40
};
const contentTitle = 'CLI tool for Plutus';

const assets = {

};



const toc = [{
  "value": "Optimising UPLC with the CLI",
  "id": "optimising-uplc-with-the-cli",
  "level": 2
}, {
  "value": "Running UPLC with the CLI",
  "id": "running",
  "level": 2
}, {
  "value": "Debugging UPLC with the CLI <em>(Experimental)</em>",
  "id": "debugging",
  "level": 2
}, {
  "value": "Advanced: Converting between languages &amp; formats",
  "id": "converting",
  "level": 2
}, {
  "value": "Filename Extensions",
  "id": "extensions",
  "level": 3
}, {
  "value": "Manually set language&amp;format",
  "id": "override",
  "level": 3
}, {
  "value": "Pretty-printing output",
  "id": "pretty-printing-output",
  "level": 3
}];
function _createMdxContent(props) {
  const _components = {
    a: "a",
    blockquote: "blockquote",
    code: "code",
    em: "em",
    h1: "h1",
    h2: "h2",
    h3: "h3",
    header: "header",
    img: "img",
    li: "li",
    ol: "ol",
    p: "p",
    pre: "pre",
    strong: "strong",
    table: "table",
    tbody: "tbody",
    td: "td",
    th: "th",
    thead: "thead",
    tr: "tr",
    ul: "ul",
    ...(0,lib/* useMDXComponents */.R)(),
    ...props.components
  };
  return (0,jsx_runtime.jsxs)(jsx_runtime.Fragment, {
    children: [(0,jsx_runtime.jsx)(_components.header, {
      children: (0,jsx_runtime.jsx)(_components.h1, {
        id: "cli-tool-for-plutus",
        children: "CLI tool for Plutus"
      })
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["The ", (0,jsx_runtime.jsx)(_components.code, {
        children: "plutus"
      }), " CLI tool allows you to:"]
    }), "\n", (0,jsx_runtime.jsxs)(_components.ul, {
      children: ["\n", (0,jsx_runtime.jsxs)(_components.li, {
        children: [(0,jsx_runtime.jsx)(_components.strong, {
          children: "check"
        }), " statically your plutus-related (PIR/TPLC/UPLC) program for common errors."]
      }), "\n", (0,jsx_runtime.jsxs)(_components.li, {
        children: [(0,jsx_runtime.jsx)(_components.strong, {
          children: "compile"
        }), " (convert) between plutus-derived languages and code formats."]
      }), "\n", (0,jsx_runtime.jsxs)(_components.li, {
        children: [(0,jsx_runtime.jsx)(_components.strong, {
          children: "optimise"
        }), " the code."]
      }), "\n", (0,jsx_runtime.jsxs)(_components.li, {
        children: [(0,jsx_runtime.jsx)(_components.strong, {
          children: "run"
        }), " or interactively ", (0,jsx_runtime.jsx)(_components.strong, {
          children: "debug"
        }), " your program ", (0,jsx_runtime.jsx)(_components.em, {
          children: "locally"
        }), " (without starting a Cardano Node)."]
      }), "\n"]
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["A pre-built executable of the ", (0,jsx_runtime.jsx)(_components.code, {
        children: "plutus"
      }), " CLI\ncan be found on the ", (0,jsx_runtime.jsx)(_components.a, {
        href: "https://github.com/IntersectMBO/plutus/releases/latest",
        children: "Latest Release"
      }), " page in the repository. Alternatively, you can build the tool\nusing Nix, specifically for your platform:"]
    }), "\n", (0,jsx_runtime.jsx)(_components.pre, {
      children: (0,jsx_runtime.jsx)(_components.code, {
        className: "language-shell",
        children: "$ nix build \".#cabalProject.$(nix eval nixpkgs#stdenv.buildPlatform.system).hsPkgs.plutus-core.components.exes.plutus\"\n"
      })
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["To consult the tool's usage you can invoke ", (0,jsx_runtime.jsx)(_components.code, {
        children: "plutus --help"
      }), " in your command line:"]
    }), "\n", (0,jsx_runtime.jsx)(_components.pre, {
      children: (0,jsx_runtime.jsx)(_components.code, {
        className: "language-shell",
        children: "$ plutus --help\nUSAGE: plutus [--run|--debug] [-OLEVEL] FILES... [-o FILE]\n"
      })
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["In general, a ", (0,jsx_runtime.jsx)(_components.em, {
        children: "compiler tool"
      }), " operates in a certain pattern:"]
    }), "\n", (0,jsx_runtime.jsxs)(_components.blockquote, {
      children: ["\n", (0,jsx_runtime.jsxs)(_components.ol, {
        children: ["\n", (0,jsx_runtime.jsxs)(_components.li, {
          children: ["Read (Parse or Deserialise) input program(s) of a ", (0,jsx_runtime.jsx)(_components.em, {
            children: "source"
          }), " language\n", (0,jsx_runtime.jsx)("br", {}), "↓", (0,jsx_runtime.jsx)("br", {})]
        }), "\n", (0,jsx_runtime.jsxs)(_components.li, {
          children: ["Check program(s) for certain errors\n", (0,jsx_runtime.jsx)("br", {}), "↓", (0,jsx_runtime.jsx)("br", {})]
        }), "\n", (0,jsx_runtime.jsxs)(_components.li, {
          children: ["Compile to a lower-level ", (0,jsx_runtime.jsx)(_components.em, {
            children: "target"
          }), " language\n", (0,jsx_runtime.jsx)("br", {}), "↓", (0,jsx_runtime.jsx)("br", {})]
        }), "\n", (0,jsx_runtime.jsxs)(_components.li, {
          children: ["Optimise the compiled code (", (0,jsx_runtime.jsx)(_components.em, {
            children: "optional"
          }), ")\n", (0,jsx_runtime.jsx)("br", {}), "↓", (0,jsx_runtime.jsx)("br", {})]
        }), "\n", (0,jsx_runtime.jsxs)(_components.li, {
          children: ["Write code to output (", (0,jsx_runtime.jsx)(_components.em, {
            children: "optional"
          }), ")"]
        }), "\n"]
      }), "\n"]
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["In case of ", (0,jsx_runtime.jsx)(_components.code, {
        children: "plutus"
      }), " tool, ", (0,jsx_runtime.jsx)(_components.em, {
        children: "Step 1"
      }), " is more or less straightforward:\nthe input programs are read from the specified ", (0,jsx_runtime.jsx)(_components.code, {
        children: "FILES..."
      }), " in the CLI and/or from Standard Input (", (0,jsx_runtime.jsx)(_components.code, {
        children: "--stdin"
      }), " option)."]
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["After reading the input program(s), the tool continues\nto run certain static ", (0,jsx_runtime.jsx)(_components.strong, {
        children: "checks"
      }), " on those programs (", (0,jsx_runtime.jsx)(_components.em, {
        children: "Step 2"
      }), "); currently there is no way to turn these static checks off."]
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["In ", (0,jsx_runtime.jsx)(_components.em, {
        children: "Step 3"
      }), " the tool will try to ", (0,jsx_runtime.jsx)(_components.strong, {
        children: "compile"
      }), " (convert) the higher-level source language (PIR, TPLC) of the input program to the lower-level target language (TPLC, UPLC).\nIn case the source and target languages are the same, this step is a \"no-op\" (has to be for UPLC, since it is the lowest-level Plutus language after all)."]
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: [(0,jsx_runtime.jsx)(_components.em, {
        children: "Step 4"
      }), " (", (0,jsx_runtime.jsx)(_components.strong, {
        children: "Optimising"
      }), " code) is optional and has to be manually turned on by using the option ", (0,jsx_runtime.jsx)(_components.code, {
        children: "-OLEVEL"
      }), " where ", (0,jsx_runtime.jsx)(_components.em, {
        children: "LEVEL"
      }), " is a number between zero and two.\n", (0,jsx_runtime.jsx)(_components.code, {
        children: "-O0"
      }), " specifies that no optimisations should be run (basically same as omitting the ", (0,jsx_runtime.jsx)(_components.code, {
        children: "-OLEVEL"
      }), " option). ", (0,jsx_runtime.jsx)(_components.code, {
        children: "-O1"
      }), " applies safe optimisations (guarantees no change to the program's semantics),\nwhereas ", (0,jsx_runtime.jsx)(_components.code, {
        children: "-O2"
      }), " applies aggressive / unsafe optimisations (may alter program's semantics)."]
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: [(0,jsx_runtime.jsx)(_components.em, {
        children: "Step 5"
      }), " writes the resulting (compiled and/or optimised) code to given output specified with ", (0,jsx_runtime.jsx)(_components.code, {
        children: "-o FILE"
      }), " or ", (0,jsx_runtime.jsx)(_components.code, {
        children: "--stdout"
      }), ".\nThis step is optional: there is no program output when both options above are omitted. This is so that users can use the ", (0,jsx_runtime.jsx)(_components.code, {
        children: "plutus"
      }), " tool as a background checker when developing a Plutus program\nor if they want to continue with an extra ", (0,jsx_runtime.jsx)(_components.em, {
        children: "Step 6"
      }), ":"]
    }), "\n", (0,jsx_runtime.jsxs)(_components.blockquote, {
      children: ["\n", (0,jsx_runtime.jsxs)(_components.p, {
        children: ["...\n", (0,jsx_runtime.jsx)("br", {}), "↓", (0,jsx_runtime.jsx)("br", {}), "\n5. Write code to output (", (0,jsx_runtime.jsx)(_components.em, {
          children: "optional"
        }), ")\n", (0,jsx_runtime.jsx)("br", {}), "↓", (0,jsx_runtime.jsx)("br", {}), "\n6. Run ", (0,jsx_runtime.jsx)(_components.em, {
          children: "OR"
        }), " Debug code (", (0,jsx_runtime.jsx)(_components.em, {
          children: "optional"
        }), ")"]
      }), "\n"]
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["Users can pass a ", (0,jsx_runtime.jsx)(_components.code, {
        children: "--run"
      }), " ", (0,jsx_runtime.jsx)(_components.em, {
        children: "or"
      }), " ", (0,jsx_runtime.jsx)(_components.code, {
        children: "--debug"
      }), " as an extra option to ", (0,jsx_runtime.jsx)(_components.strong, {
        children: "run"
      }), " or ", (0,jsx_runtime.jsx)(_components.strong, {
        children: "debug"
      }), " the resulting program of the compilation,\nusing the tool's built-in interpreter and debugger, respectively."]
    }), "\n", (0,jsx_runtime.jsx)(_components.h2, {
      id: "optimising-uplc-with-the-cli",
      children: "Optimising UPLC with the CLI"
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["In this section we only focus on UPLC; a prerequisite is that you have already acquired (extracted) the UPLC code corresponding to your high-level source program.\nThe process to ", (0,jsx_runtime.jsx)(_components.em, {
        children: "extract"
      }), " plutus code varies depending on the source language you are using (Plinth, Aiken, ...);\nif Plinth is the source language, you can follow the instructions on ", (0,jsx_runtime.jsx)(_components.a, {
        href: "/pr-preview/docs/pr-7403/using-plinth/inspecting#inspecting-the-compiled-code",
        children: "how to inspect compiled code"
      }), "."]
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["Since UPLC is the lowest-level language, compiling (", (0,jsx_runtime.jsx)(_components.em, {
        children: "Step 3"
      }), ") is not applicable for UPLC input programs and thus omitted\n— for actual compiling (converting) between different intermediate languages (PIR, TPLC) or serialisation formats (e.g. Flat, CBOR)\nsee the ", (0,jsx_runtime.jsx)(_components.a, {
        href: "#converting",
        children: "Advanced section"
      }), " on converting between Plutus languages & formats.\nInstead, we can use the ", (0,jsx_runtime.jsx)(_components.code, {
        children: "plutus"
      }), " tool to check for certain static errors in our UPLC, as in the example:"]
    }), "\n", (0,jsx_runtime.jsx)(_components.pre, {
      children: (0,jsx_runtime.jsx)(_components.code, {
        className: "language-shell",
        children: "$ echo '(program 1.1.0 (lam x (lam y z)))' > const_err.uplc\n$ plutus const_err.uplc\nError from the PLC compiler:\nVariable 2 is free at ()\n"
      })
    }), "\n", (0,jsx_runtime.jsx)(_components.p, {
      children: "After fixing the error:"
    }), "\n", (0,jsx_runtime.jsx)(_components.pre, {
      children: (0,jsx_runtime.jsx)(_components.code, {
        children: "$ echo '(program 1.1.0 (lam x (lam y x)))' | plutus --stdin\nCompilation succeeded, but no output file was written; use -o or --stdout.\n"
      })
    }), "\n", (0,jsx_runtime.jsx)(_components.p, {
      children: "We can try to turn on some optimisations and write the resulting optimised code to standard output:"
    }), "\n", (0,jsx_runtime.jsx)(_components.pre, {
      children: (0,jsx_runtime.jsx)(_components.code, {
        className: "language-shell",
        children: "# no optimisations by default\n$ echo '(program 1.1.0 (force (delay (con unit ()))))' | plutus --stdin --stdout\n(program 1.1.0 (force (delay (con unit ()))))\n\n$ echo '(program 1.1.0 (force (delay (con unit ()))))' | plutus --stdin --stdout -O1\n(program 1.1.0 (con unit ()))\n"
      })
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["When multiple input programs (files) are passed to the CLI, the ", (0,jsx_runtime.jsx)(_components.code, {
        children: "plutus"
      }), " tool\nwill ", (0,jsx_runtime.jsx)(_components.strong, {
        children: "check"
      }), ", ", (0,jsx_runtime.jsx)(_components.strong, {
        children: "compile"
      }), " (not applicable for UPLC), and (optionally) ", (0,jsx_runtime.jsx)(_components.strong, {
        children: "optimise"
      }), " each program separately.\nAfter this is done for ", (0,jsx_runtime.jsx)(_components.em, {
        children: "all"
      }), " programs, the tool gathers the result of each compilation/optimisation and combines them into a single output program.\nThis is done by placing (interposing) an ", (0,jsx_runtime.jsx)(_components.code, {
        children: "Apply"
      }), " term between the code of each compiled/optimised program, similar\nto Haskell's juxtaposition of a function and its series of applied arguments."]
    }), "\n", (0,jsx_runtime.jsx)(_components.pre, {
      children: (0,jsx_runtime.jsx)(_components.code, {
        className: "language-shell",
        children: "$ echo '(program 1.1.0 (lam x (lam y x)))' > func.uplc\n$ echo '(program 1.1.0 (con string \"OK\"))' > arg1.uplc\n$ echo '(program 1.1.0 (con bool True))' > arg2.uplc\n$ plutus func.uplc arg1.uplc arg2.uplc --stdout -O2\n(program 1.1.0 [ [ (lam x (lam y x)) (con string \"OK\") ] (con bool True) ])\n"
      })
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["In the example above, even with all optimisations turned on (", (0,jsx_runtime.jsx)(_components.code, {
        children: "-O2"
      }), "), the ", (0,jsx_runtime.jsx)(_components.code, {
        children: "plutus"
      }), " tool will not reduce\nthe obviously reducible function applications in the output program; this is because the input programs are optimised only ", (0,jsx_runtime.jsx)(_components.em, {
        children: "individually"
      }), " (separately). You can\ninstruct the tool to perform an ", (0,jsx_runtime.jsx)(_components.strong, {
        children: "extra"
      }), " optimisation pass of the whole (combined) program\nby passing ", (0,jsx_runtime.jsx)(_components.code, {
        children: "--whole-opt"
      }), " to the CLI — the given ", (0,jsx_runtime.jsx)(_components.code, {
        children: "-OLEVEL"
      }), " will be taken into account also for this final extra pass (", (0,jsx_runtime.jsx)(_components.code, {
        children: "-O2"
      }), " in this case)."]
    }), "\n", (0,jsx_runtime.jsx)(_components.pre, {
      children: (0,jsx_runtime.jsx)(_components.code, {
        className: "language-shell",
        children: "$ plutus func.uplc arg1.uplc arg2.uplc --stdout -O2 --whole-opt\n(program 1.1.0 (con string \"OK\"))\n"
      })
    }), "\n", (0,jsx_runtime.jsx)(_components.h2, {
      id: "running",
      children: "Running UPLC with the CLI"
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["Certain errors in ", (0,jsx_runtime.jsx)(_components.code, {
        children: "uplc"
      }), " code cannot be caught by the static checks (", (0,jsx_runtime.jsx)(_components.em, {
        children: "Step 2"
      }), ")\nbecause the UPLC language is untyped:"]
    }), "\n", (0,jsx_runtime.jsx)(_components.pre, {
      children: (0,jsx_runtime.jsx)(_components.code, {
        className: "language-shell",
        children: "# Pseudocode: 1 + True\n$ echo \"(program 1.1.0 [(builtin addInteger) (con integer 1) (con bool True)])\" > typ_err.uplc\n$ plutus typ_err.uplc\nCompilation succeeded, but no output file was written; use -o or --stdout.\n"
      })
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["Alternatively we can try to run the program using the tool's built-in ", (0,jsx_runtime.jsx)(_components.em, {
        children: "interpreter"
      }), " and look for any runtime (type) errors.\nThe ", (0,jsx_runtime.jsx)(_components.code, {
        children: "--run"
      }), " option will invoke the interpreter passing to it the final output program.\nAn execution that raised an error will show information about the error and in which term\nthe error happened:"]
    }), "\n", (0,jsx_runtime.jsx)(_components.pre, {
      children: (0,jsx_runtime.jsx)(_components.code, {
        className: "language-shell",
        children: "$ plutus typ_err.uplc --run\nRunning the program: An error has occurred:\nCould not unlift a value:\nType mismatch: expected: integer; actual: bool\nCaused by: addInteger 1 True\n"
      })
    }), "\n", (0,jsx_runtime.jsx)(_components.p, {
      children: "Other times catching such (type) errors at runtime is not even possible. Consider the following\nexample program which contains a type error but the execution nevertheless succeeds with the final\nevaluated result (term):"
    }), "\n", (0,jsx_runtime.jsx)(_components.pre, {
      children: (0,jsx_runtime.jsx)(_components.code, {
        className: "language-shell",
        children: "# Pseudocode: if True then \"\" else unit\n$ echo '(program 1.1.0 [(force (builtin ifThenElse)) (con bool True) (con string \"\") (con unit ())])' > if.uplc\n$ plutus if.uplc --run\nRunning the program: Execution succeeded, final term:\n(con string \"\")\nUsed budget: ExBudget {exBudgetCPU = ExCPU 204149, exBudgetMemory = ExMemory 901}\n"
      })
    }), "\n", (0,jsx_runtime.jsxs)(_components.blockquote, {
      children: ["\n", (0,jsx_runtime.jsxs)(_components.p, {
        children: ["📌", " ", (0,jsx_runtime.jsx)(_components.strong, {
          children: "NOTE"
        }), "\nThe above example demonstrates that ", (0,jsx_runtime.jsx)(_components.code, {
          children: "uplc"
        }), " — the language which actually ", (0,jsx_runtime.jsx)(_components.em, {
          children: "runs on the chain"
        }), " —\nis low-level and more akin to assembly. Users that are concerned about the safety of their smart contracts\nare advised instead to develop in a higher-level (typed) language (e.g. Plinth) which compiles down to ", (0,jsx_runtime.jsx)(_components.code, {
          children: "uplc"
        }), "."]
      }), "\n"]
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["After plutus program's execution is completed (either succeeded or failed), the final used budget will be printed as well.\nBecause the CLI tool employs the same ", (0,jsx_runtime.jsx)(_components.code, {
        children: "uplc"
      }), " interpreter as the one that the Cardano node runs, you can be sure\nthat the program's execution result&budget match ", (0,jsx_runtime.jsx)(_components.em, {
        children: "precisely"
      }), " — assuming same program\nand cost model — the result&budget computed by the chain."]
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["You can pass a maximum ", (0,jsx_runtime.jsx)(_components.em, {
        children: "CPU"
      }), " and/or ", (0,jsx_runtime.jsx)(_components.em, {
        children: "Memory"
      }), " budget that is allowed to be spent with the ", (0,jsx_runtime.jsx)(_components.code, {
        children: "--budget=CPU"
      }), " or ", (0,jsx_runtime.jsx)(_components.code, {
        children: "-budget=,MEM"
      }), " or ", (0,jsx_runtime.jsx)(_components.code, {
        children: "--budget=CPU,MEM"
      }), " options; if given budget runs out, the execution will fail and stop earlier.\nIf there is no CPU and/or MEM limit given, the budget is practically unlimited."]
    }), "\n", (0,jsx_runtime.jsx)(_components.pre, {
      children: (0,jsx_runtime.jsx)(_components.code, {
        className: "language-shell",
        children: "$ plutus if.uplc --run --budget=204148,903\nRunning the program: An error has occurred:\nThe machine terminated part way through evaluation due to overspending the budget.\nThe budget when the machine terminated was:\n({cpu: -1\n| mem: 2})\nNegative numbers indicate the overspent budget; note that this only indicates the budget that was needed for the next step, not to run the program to completion.\n\n$ plutus if.uplc --run --budget=,903\nRunning the program: Execution succeeded, final term:\n(con string \"\")\nRemaining budget: ExBudget {exBudgetCPU = ExCPU 9223372036854571658, exBudgetMemory = ExMemory 2}\nUsed budget: ExBudget {exBudgetCPU = ExCPU 204149, exBudgetMemory = ExMemory 901}\n"
      })
    }), "\n", (0,jsx_runtime.jsxs)(_components.blockquote, {
      children: ["\n", (0,jsx_runtime.jsxs)(_components.p, {
        children: ["📌", " ", (0,jsx_runtime.jsx)(_components.strong, {
          children: "NOTE"
        }), "\nAttempting to run a ", (0,jsx_runtime.jsx)(_components.code, {
          children: "tplc"
        }), " target will use the ", (0,jsx_runtime.jsx)(_components.code, {
          children: "tplc"
        }), " interpreter. Although\nthe ", (0,jsx_runtime.jsx)(_components.code, {
          children: "tplc"
        }), " interpreter behaves the same as the default ", (0,jsx_runtime.jsx)(_components.code, {
          children: "uplc"
        }), " interpreter (for ", (0,jsx_runtime.jsx)(_components.em, {
          children: "type correct"
        }), " programs),\nit comes with caveats: cannot execute ", (0,jsx_runtime.jsx)(_components.code, {
          children: "uplc"
        }), " code,\ncannot have budget accounting and budget limits, runs way slower and your program must be fully type correct.\nThe last point is not necessarily a caveat, but it diverges from the on-chain behavior:\nthe ", (0,jsx_runtime.jsx)(_components.code, {
          children: "tplc"
        }), " interpreter accepts less programs than the chain (and the default ", (0,jsx_runtime.jsx)(_components.code, {
          children: "uplc"
        }), " interpreter) would accept.\nPIR target programs cannot be directly executed."]
      }), "\n"]
    }), "\n", (0,jsx_runtime.jsxs)(_components.h2, {
      id: "debugging",
      children: ["Debugging UPLC with the CLI ", (0,jsx_runtime.jsx)(_components.em, {
        children: "(Experimental)"
      })]
    }), "\n", (0,jsx_runtime.jsxs)(_components.blockquote, {
      children: ["\n", (0,jsx_runtime.jsxs)(_components.p, {
        children: ["📌", " ", (0,jsx_runtime.jsx)(_components.strong, {
          children: "NOTE"
        }), "\nThe debugger is in a ", (0,jsx_runtime.jsx)(_components.em, {
          children: "preliminary"
        }), " , ", (0,jsx_runtime.jsx)(_components.em, {
          children: "experimental"
        }), " state. What is described below is\nsubject to change when new features are added to the debugger."]
      }), "\n"]
    }), "\n", (0,jsx_runtime.jsx)(_components.p, {
      children: "Another way to check for runtime errors or the execution budget\nis by firing up the tool's built-in debugger. Again, the debugger utilises underneath the same UPLC interpreter\nas the one the Cardano node runs, so you can be sure about its execution results and budget costs.\nThe difference compared to \"running the code\" is that with the debugger you can step by step progress over the execution\nover your UPLC program's sub-terms, or interactively decide to pause the execution on specific UPLC sub-term(s) of interest."
    }), "\n", (0,jsx_runtime.jsxs)(_components.blockquote, {
      children: ["\n", (0,jsx_runtime.jsxs)(_components.p, {
        children: ["📌", " ", (0,jsx_runtime.jsx)(_components.strong, {
          children: "NOTE"
        }), "\nUnlike the ", (0,jsx_runtime.jsx)(_components.code, {
          children: "--run"
        }), " option that can execute both UPLC ", (0,jsx_runtime.jsx)(_components.em, {
          children: "and"
        }), " TPLC target programs, the ", (0,jsx_runtime.jsx)(_components.code, {
          children: "--debug"
        }), " option works ", (0,jsx_runtime.jsx)(_components.em, {
          children: "exclusively"
        }), " for UPLC targets."]
      }), "\n"]
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["The ", (0,jsx_runtime.jsx)(_components.code, {
        children: "--debug"
      }), " option will launch the debugger after\nthe prior checking/compilation/optimisation steps of your input program(s) have been completed, for example:"]
    }), "\n", (0,jsx_runtime.jsx)(_components.pre, {
      children: (0,jsx_runtime.jsx)(_components.code, {
        className: "language-shell",
        children: "$ plutus if.uplc -O1 --debug\n"
      })
    }), "\n", (0,jsx_runtime.jsx)(_components.p, {
      children: "The debugger has a Terminal User Interface (TUI) with three windows that are kept automatically updated: (1)\nthe compiled/optimised target UPLC program, (2) the log/trace messages, and (3) the (current) return value."
    }), "\n", (0,jsx_runtime.jsx)(_components.p, {
      children: (0,jsx_runtime.jsx)(_components.img, {
        alt: "TUI Debugger Screenshot",
        src: (__webpack_require__(7789)/* ["default"] */ .A) + "",
        width: "1906",
        height: "1014"
      })
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["You can interact (issue ", (0,jsx_runtime.jsx)(_components.strong, {
        children: "Commands"
      }), ") to the debugger by pressing keyboard shortcuts:"]
    }), "\n", (0,jsx_runtime.jsxs)(_components.table, {
      children: [(0,jsx_runtime.jsx)(_components.thead, {
        children: (0,jsx_runtime.jsxs)(_components.tr, {
          children: [(0,jsx_runtime.jsx)(_components.th, {
            children: "Keyboard Shortcut"
          }), (0,jsx_runtime.jsx)(_components.th, {
            children: "Command"
          })]
        })
      }), (0,jsx_runtime.jsxs)(_components.tbody, {
        children: [(0,jsx_runtime.jsxs)(_components.tr, {
          children: [(0,jsx_runtime.jsx)(_components.td, {
            children: "?"
          }), (0,jsx_runtime.jsx)(_components.td, {
            children: "Show help dialog"
          })]
        }), (0,jsx_runtime.jsxs)(_components.tr, {
          children: [(0,jsx_runtime.jsx)(_components.td, {
            children: "Esc"
          }), (0,jsx_runtime.jsx)(_components.td, {
            children: "Quit help dialog or debugger"
          })]
        }), (0,jsx_runtime.jsxs)(_components.tr, {
          children: [(0,jsx_runtime.jsx)(_components.td, {
            children: "Ctrl+up/down/left/right"
          }), (0,jsx_runtime.jsx)(_components.td, {
            children: "Resize window"
          })]
        }), (0,jsx_runtime.jsxs)(_components.tr, {
          children: [(0,jsx_runtime.jsx)(_components.td, {
            children: "Tab"
          }), (0,jsx_runtime.jsx)(_components.td, {
            children: "Switch focus to other window"
          })]
        }), (0,jsx_runtime.jsxs)(_components.tr, {
          children: [(0,jsx_runtime.jsx)(_components.td, {
            children: "s"
          }), (0,jsx_runtime.jsx)(_components.td, {
            children: "Step once the interpreter"
          })]
        })]
      })]
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["Unlike the ", (0,jsx_runtime.jsx)(_components.code, {
        children: "--run"
      }), " option, the ", (0,jsx_runtime.jsx)(_components.code, {
        children: "step"
      }), " command does not execute the program\nto completion. Instead, the underlying ", (0,jsx_runtime.jsx)(_components.code, {
        children: "uplc"
      }), " interpreter is moved one \"budgeting\" step forward —\nthe smallest step possible that gets accounted for and subtracted from the current budget."]
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["After every such ", (0,jsx_runtime.jsx)(_components.code, {
        children: "step"
      }), ", the debugger\nhighlights in window (1) the code region (sub-term) which will be executed in the future (next ", (0,jsx_runtime.jsx)(_components.code, {
        children: "step"
      }), ");\nA footer in the TUI screen will update to show the remaining budget.\nYou can combine ", (0,jsx_runtime.jsx)(_components.code, {
        children: "--debug"
      }), " with the ", (0,jsx_runtime.jsx)(_components.code, {
        children: "--budget=CPU,MEM"
      }), " option to limit the starting total budget:\nthe debugger fails the execution the moment the budget runs out, similar as to what happens with ", (0,jsx_runtime.jsx)(_components.code, {
        children: "--run"
      }), "."]
    }), "\n", (0,jsx_runtime.jsx)(_components.h2, {
      id: "converting",
      children: "Advanced: Converting between languages & formats"
    }), "\n", (0,jsx_runtime.jsx)(_components.pre, {
      children: (0,jsx_runtime.jsx)(_components.code, {
        className: "language-shell",
        children: "$ plutus IN_FILES... -o OUT_FILE\n"
      })
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["The filename extensions of the input files and output file\ndetermine the language and format of the ", (0,jsx_runtime.jsx)(_components.em, {
        children: "sources"
      }), " and ", (0,jsx_runtime.jsx)(_components.em, {
        children: "target"
      }), ", respectively.\nYou can take a look at the ", (0,jsx_runtime.jsx)(_components.a, {
        href: "#extensions",
        children: "Table of Filename Extensions"
      }), " recognised by the ", (0,jsx_runtime.jsx)(_components.code, {
        children: "plutus"
      }), " tool.\nAlternatively, you can ", (0,jsx_runtime.jsx)(_components.a, {
        href: "#override",
        children: "manually set"
      }), " (or override) the language&format."]
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["You are allowed to mix and match different input ", (0,jsx_runtime.jsx)(_components.em, {
        children: "sources"
      }), " as long\nas that make sense: the ", (0,jsx_runtime.jsx)(_components.em, {
        children: "target"
      }), " must be a lower- or equal-level language to the sources.\nAll sources will be then compiled and combined to the given target, for example:"]
    }), "\n", (0,jsx_runtime.jsx)(_components.pre, {
      children: (0,jsx_runtime.jsx)(_components.code, {
        className: "language-shell",
        children: "$ plutus func.pir arg1.tplc arg2.uplc -o fully_applied.uplc\n\n$ plutus func.pir arg1.tplc -o partially_applied.tplc\n$ plutus partially_applied.tplc arg2.uplc -o also_fully_applied.uplc\n\n$ plutus arg2.uplc -o arg2.tplc # does not make sense, cannot lift to a higher level language\n$ plutus -O2 func.pir -o func_optimised.pir # makes sense for check / optimise\n"
      })
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["It is worth to re-iterate that the input files are checked/compiled/optimised ", (0,jsx_runtime.jsx)(_components.strong, {
        children: "separately"
      }), ";\nthis means that although the input programs are ", (0,jsx_runtime.jsx)(_components.em, {
        children: "individually"
      }), " type correct, when ", (0,jsx_runtime.jsx)(_components.em, {
        children: "combined"
      }), " to a specific target\nthey may become type incorrect:"]
    }), "\n", (0,jsx_runtime.jsx)(_components.pre, {
      children: (0,jsx_runtime.jsx)(_components.code, {
        className: "language-shell",
        children: "$ echo \"(program 1.1.0 (lam x (con integer) [(builtin addInteger) x (con integer 1)]))\" > inc.pir\n$ echo \"(program 1.1.0 (con bool True))\" > true.pir\n\n$ plutus inc.pir true.pir -o applied.uplc # NO TYPE ERROR because target is untyped (UPLC)\n$ echo applied.uplc\n(program\n  1.1.0\n  [ (lam i [ [ (builtin addInteger) (con integer 1) ] i ]) (con bool True) ]\n)\n\n$ plutus inc.pir true.pir -o applied.pir # TYPE ERROR because PIR target\n$ plutus inc.pir true.pir -o applied.tplc # TYPE ERROR because TPLC target\n"
      })
    }), "\n", (0,jsx_runtime.jsx)(_components.h3, {
      id: "extensions",
      children: "Filename Extensions"
    }), "\n", (0,jsx_runtime.jsx)(_components.p, {
      children: "The following table lists the recognized extensions."
    }), "\n", (0,jsx_runtime.jsxs)(_components.table, {
      children: [(0,jsx_runtime.jsx)(_components.thead, {
        children: (0,jsx_runtime.jsxs)(_components.tr, {
          children: [(0,jsx_runtime.jsx)(_components.th, {
            children: "Filename Extension"
          }), (0,jsx_runtime.jsx)(_components.th, {
            children: "Format Type"
          }), (0,jsx_runtime.jsx)(_components.th, {
            children: "Description"
          })]
        })
      }), (0,jsx_runtime.jsxs)(_components.tbody, {
        children: [(0,jsx_runtime.jsxs)(_components.tr, {
          children: [(0,jsx_runtime.jsxs)(_components.td, {
            children: ["*", (0,jsx_runtime.jsx)(_components.em, {
              children: "NO-EXTENSION*"
            })]
          }), (0,jsx_runtime.jsx)(_components.td, {
            children: "Textual"
          }), (0,jsx_runtime.jsx)(_components.td, {
            children: "Untyped Plutus Core with Names"
          })]
        }), (0,jsx_runtime.jsxs)(_components.tr, {
          children: [(0,jsx_runtime.jsx)(_components.td, {
            children: ".uplc"
          }), (0,jsx_runtime.jsx)(_components.td, {
            children: "Textual"
          }), (0,jsx_runtime.jsx)(_components.td, {
            children: "Untyped Plutus Core with Names"
          })]
        }), (0,jsx_runtime.jsxs)(_components.tr, {
          children: [(0,jsx_runtime.jsx)(_components.td, {
            children: ".tplc"
          }), (0,jsx_runtime.jsx)(_components.td, {
            children: "Textual"
          }), (0,jsx_runtime.jsx)(_components.td, {
            children: "Typed Plutus Core with Names"
          })]
        }), (0,jsx_runtime.jsxs)(_components.tr, {
          children: [(0,jsx_runtime.jsx)(_components.td, {
            children: ".pir"
          }), (0,jsx_runtime.jsx)(_components.td, {
            children: "Textual"
          }), (0,jsx_runtime.jsx)(_components.td, {
            children: "PIR with Names"
          })]
        }), (0,jsx_runtime.jsxs)(_components.tr, {
          children: [(0,jsx_runtime.jsx)(_components.td, {
            children: ".data"
          }), (0,jsx_runtime.jsx)(_components.td, {
            children: "Binary"
          }), (0,jsx_runtime.jsxs)(_components.td, {
            children: ["Values of ", (0,jsx_runtime.jsx)(_components.code, {
              children: "Data"
            }), " serialised in CBOR"]
          })]
        }), (0,jsx_runtime.jsxs)(_components.tr, {
          children: [(0,jsx_runtime.jsx)(_components.td, {
            children: ".data-txt"
          }), (0,jsx_runtime.jsx)(_components.td, {
            children: "Textual"
          }), (0,jsx_runtime.jsxs)(_components.td, {
            children: ["Values of ", (0,jsx_runtime.jsx)(_components.code, {
              children: "Data"
            }), " in Haskell's ", (0,jsx_runtime.jsx)(_components.code, {
              children: "Show"
            }), " format"]
          })]
        }), (0,jsx_runtime.jsxs)(_components.tr, {
          children: [(0,jsx_runtime.jsx)(_components.td, {
            children: ".uplc-flat"
          }), (0,jsx_runtime.jsx)(_components.td, {
            children: "Binary"
          }), (0,jsx_runtime.jsx)(_components.td, {
            children: "Untyped PlutusCore with NamedDeBruijn serialised in Flat"
          })]
        }), (0,jsx_runtime.jsxs)(_components.tr, {
          children: [(0,jsx_runtime.jsx)(_components.td, {
            children: ".uplc-cbor"
          }), (0,jsx_runtime.jsx)(_components.td, {
            children: "Binary"
          }), (0,jsx_runtime.jsxs)(_components.td, {
            children: ["Untyped PlutusCore with DeBruijn serialised in CBOR ", (0,jsx_runtime.jsx)("br", {}), " (the on-chain format)"]
          })]
        })]
      })]
    }), "\n", (0,jsx_runtime.jsxs)(_components.blockquote, {
      children: ["\n", (0,jsx_runtime.jsxs)(_components.p, {
        children: ["📌", " ", (0,jsx_runtime.jsx)(_components.strong, {
          children: "NOTE"
        }), " If file has no extension or in case of ", (0,jsx_runtime.jsx)(_components.code, {
          children: "--stdin"
        }), " / ", (0,jsx_runtime.jsx)(_components.code, {
          children: "--stdout"
        }), ", the extension is assumed to be ", (0,jsx_runtime.jsx)(_components.code, {
          children: ".uplc"
        })]
      }), "\n"]
    }), "\n", (0,jsx_runtime.jsx)(_components.h3, {
      id: "override",
      children: "Manually set language&format"
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["If the extension cannot be determined (missing / ", (0,jsx_runtime.jsx)(_components.code, {
        children: "--stdin"
      }), " / ", (0,jsx_runtime.jsx)(_components.code, {
        children: "--stdout"
      }), ")\nor you would like to override the recognised extension,\nyou may use the ", (0,jsx_runtime.jsx)(_components.code, {
        children: "-x .EXTENSION"
      }), " option (with or without the leading dot ", (0,jsx_runtime.jsx)(_components.code, {
        children: "."
      }), " taken from ", (0,jsx_runtime.jsx)(_components.a, {
        href: "#extensions",
        children: "Table"
      }), " above) to manually set the\nextension for the given file(s):"]
    }), "\n", (0,jsx_runtime.jsx)(_components.pre, {
      children: (0,jsx_runtime.jsx)(_components.code, {
        className: "language-shell",
        children: "$ plutus file1 -x pir file2 file3\n"
      })
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["Note ", (0,jsx_runtime.jsx)(_components.code, {
        children: "-x"
      }), " is positional: it applies its effect to all files after the option till the end or another ", (0,jsx_runtime.jsx)(_components.code, {
        children: "-x"
      }), " is reached.\nIn the example above the effect (set to ", (0,jsx_runtime.jsx)(_components.code, {
        children: "pir"
      }), ")  will not apply to ", (0,jsx_runtime.jsx)(_components.code, {
        children: "file1"
      }), ", but will apply to ", (0,jsx_runtime.jsx)(_components.code, {
        children: "file2"
      }), ", ", (0,jsx_runtime.jsx)(_components.code, {
        children: "file3"
      }), " ", (0,jsx_runtime.jsx)(_components.strong, {
        children: "and"
      }), " target.\nPossible filename extensions on ", (0,jsx_runtime.jsx)(_components.code, {
        children: "file2"
      }), " and ", (0,jsx_runtime.jsx)(_components.code, {
        children: "file3"
      }), " will be ignored. Using multiple invocations of ", (0,jsx_runtime.jsx)(_components.code, {
        children: "-x"
      }), " may come handy\nfor mixing different sources or setting the output target. The next example sets the first two files\nto be ", (0,jsx_runtime.jsx)(_components.code, {
        children: "pir"
      }), ", the following two to ", (0,jsx_runtime.jsx)(_components.code, {
        children: "tplc"
      }), ", and the target (the last invocation of ", (0,jsx_runtime.jsx)(_components.code, {
        children: "-x"
      }), ") to ", (0,jsx_runtime.jsx)(_components.code, {
        children: "uplc"
      }), "."]
    }), "\n", (0,jsx_runtime.jsx)(_components.pre, {
      children: (0,jsx_runtime.jsx)(_components.code, {
        className: "language-shell",
        children: "$ plutus -x pir Pir_File Also_Pir -x tplc Now_Tplc Also_Tplc -x uplc\n"
      })
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["In case ", (0,jsx_runtime.jsx)(_components.code, {
        children: "-x"
      }), " is not enough and the ", (0,jsx_runtime.jsx)(_components.em, {
        children: "format"
      }), " is more complex because it contains a non-default variable-naming scheme or annotations,\nyou may extra specify the ", (0,jsx_runtime.jsx)(_components.code, {
        children: "-n NAMING"
      }), " and ", (0,jsx_runtime.jsx)(_components.code, {
        children: "-a ANNOTATION"
      }), " options to override the defaults."]
    }), "\n", (0,jsx_runtime.jsxs)(_components.table, {
      children: [(0,jsx_runtime.jsx)(_components.thead, {
        children: (0,jsx_runtime.jsxs)(_components.tr, {
          children: [(0,jsx_runtime.jsx)(_components.th, {
            children: "-n Short Option"
          }), (0,jsx_runtime.jsx)(_components.th, {
            children: "-n Long Option"
          }), (0,jsx_runtime.jsx)(_components.th, {
            children: "Description"
          })]
        })
      }), (0,jsx_runtime.jsxs)(_components.tbody, {
        children: [(0,jsx_runtime.jsxs)(_components.tr, {
          children: [(0,jsx_runtime.jsx)(_components.td, {
            children: "-n n"
          }), (0,jsx_runtime.jsx)(_components.td, {
            children: "-n name"
          }), (0,jsx_runtime.jsx)(_components.td, {
            children: "Use descriptive textual names for variables"
          })]
        }), (0,jsx_runtime.jsxs)(_components.tr, {
          children: [(0,jsx_runtime.jsx)(_components.td, {
            children: "-n d"
          }), (0,jsx_runtime.jsx)(_components.td, {
            children: "-n debruijn"
          }), (0,jsx_runtime.jsx)(_components.td, {
            children: "Use debruijn indices for variables"
          })]
        }), (0,jsx_runtime.jsxs)(_components.tr, {
          children: [(0,jsx_runtime.jsx)(_components.td, {
            children: "-n nd"
          }), (0,jsx_runtime.jsx)(_components.td, {
            children: "-n named-debruijn"
          }), (0,jsx_runtime.jsx)(_components.td, {
            children: "Use name with debruijn index for variables: \"name-index\""
          })]
        })]
      })]
    }), "\n", (0,jsx_runtime.jsxs)(_components.table, {
      children: [(0,jsx_runtime.jsx)(_components.thead, {
        children: (0,jsx_runtime.jsxs)(_components.tr, {
          children: [(0,jsx_runtime.jsx)(_components.th, {
            children: "-a Option"
          }), (0,jsx_runtime.jsx)(_components.th, {
            children: "Description"
          })]
        })
      }), (0,jsx_runtime.jsxs)(_components.tbody, {
        children: [(0,jsx_runtime.jsxs)(_components.tr, {
          children: [(0,jsx_runtime.jsx)(_components.td, {
            children: "-a unit"
          }), (0,jsx_runtime.jsx)(_components.td, {
            children: "Code does not contain any annotations (default)"
          })]
        }), (0,jsx_runtime.jsxs)(_components.tr, {
          children: [(0,jsx_runtime.jsx)(_components.td, {
            children: "-a srcspan"
          }), (0,jsx_runtime.jsx)(_components.td, {
            children: "Code is annotated with source spans"
          })]
        })]
      })]
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["The ", (0,jsx_runtime.jsx)(_components.code, {
        children: "-n"
      }), " and ", (0,jsx_runtime.jsx)(_components.code, {
        children: "-a"
      }), " options are also positional."]
    }), "\n", (0,jsx_runtime.jsx)(_components.h3, {
      id: "pretty-printing-output",
      children: "Pretty-printing output"
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["If the output's format type is ", (0,jsx_runtime.jsx)(_components.em, {
        children: "textual"
      }), " (see the ", (0,jsx_runtime.jsx)(_components.a, {
        href: "#extensions",
        children: "Filename Extensions Table"
      }), ") the compiled code\nwill be printed to the designated output (file or stdout) in a \"pretty\" format.\nYou can change how the output's looks by specifying a different ", (0,jsx_runtime.jsx)(_components.code, {
        children: "-p STYLE"
      }), " style (defaults to ", (0,jsx_runtime.jsx)(_components.code, {
        children: "classic"
      }), ")."]
    }), "\n", (0,jsx_runtime.jsxs)(_components.table, {
      children: [(0,jsx_runtime.jsx)(_components.thead, {
        children: (0,jsx_runtime.jsxs)(_components.tr, {
          children: [(0,jsx_runtime.jsx)(_components.th, {
            children: "-p Option"
          }), (0,jsx_runtime.jsx)(_components.th, {
            children: "Description"
          })]
        })
      }), (0,jsx_runtime.jsxs)(_components.tbody, {
        children: [(0,jsx_runtime.jsxs)(_components.tr, {
          children: [(0,jsx_runtime.jsx)(_components.td, {
            children: "-p classic"
          }), (0,jsx_runtime.jsx)(_components.td, {
            children: "Lisp-like syntax with unique variable names  (default)"
          })]
        }), (0,jsx_runtime.jsxs)(_components.tr, {
          children: [(0,jsx_runtime.jsx)(_components.td, {
            children: "-p classic-simple"
          }), (0,jsx_runtime.jsx)(_components.td, {
            children: "Lisp-like syntax with ambiguous (no unique) variable names"
          })]
        }), (0,jsx_runtime.jsxs)(_components.tr, {
          children: [(0,jsx_runtime.jsx)(_components.td, {
            children: "-p readable"
          }), (0,jsx_runtime.jsx)(_components.td, {
            children: "Succinct syntax with unique variable names"
          })]
        }), (0,jsx_runtime.jsxs)(_components.tr, {
          children: [(0,jsx_runtime.jsx)(_components.td, {
            children: "-p readable-simple"
          }), (0,jsx_runtime.jsx)(_components.td, {
            children: "Succinct syntax with ambiguous (no unique) variable names"
          })]
        })]
      })]
    }), "\n", (0,jsx_runtime.jsx)(_components.pre, {
      children: (0,jsx_runtime.jsx)(_components.code, {
        className: "language-shell",
        children: "$ plutus inc.pir -x pir --stdout\n(program\n  1.1.0 (lam x-0 (con integer) [ [ (builtin addInteger) x-0 ] (con integer 1) ])\n)\n\n$ plutus inc.pir -x pir --stdout --pretty=readable-simple\nprogram 1.1.0 (\\(x : integer) -> addInteger x 1)\n"
      })
    }), "\n", (0,jsx_runtime.jsxs)(_components.blockquote, {
      children: ["\n", (0,jsx_runtime.jsxs)(_components.p, {
        children: ["📌", " ", (0,jsx_runtime.jsx)(_components.strong, {
          children: "NOTE"
        }), " Specifying a textual ", (0,jsx_runtime.jsx)(_components.em, {
          children: "output"
        }), " with pretty style other than the default (classic) may not be possible to be read\nback again (as textual ", (0,jsx_runtime.jsx)(_components.em, {
          children: "input"
        }), " this time) in the CLI."]
      }), "\n"]
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["Using the standard output to capture the (pretty-printed) output program is safe,\nbecause the tool's logs and error messages are sent by default to ", (0,jsx_runtime.jsx)(_components.code, {
        children: "stderr"
      }), ".\nYou can of course silence those messages using ", (0,jsx_runtime.jsx)(_components.code, {
        children: "--quiet"
      }), " option, or instead\nincrease their rate using ", (0,jsx_runtime.jsx)(_components.code, {
        children: "--verbose"
      }), " (for tracing through the compilation process)."]
    })]
  });
}
function MDXContent(props = {}) {
  const {wrapper: MDXLayout} = {
    ...(0,lib/* useMDXComponents */.R)(),
    ...props.components
  };
  return MDXLayout ? (0,jsx_runtime.jsx)(MDXLayout, {
    ...props,
    children: (0,jsx_runtime.jsx)(_createMdxContent, {
      ...props
    })
  }) : _createMdxContent(props);
}



/***/ }),

/***/ 7789:
/***/ ((__unused_webpack_module, __webpack_exports__, __webpack_require__) => {

/* harmony export */ __webpack_require__.d(__webpack_exports__, {
/* harmony export */   A: () => (__WEBPACK_DEFAULT_EXPORT__)
/* harmony export */ });
/* harmony default export */ const __WEBPACK_DEFAULT_EXPORT__ = (__webpack_require__.p + "assets/images/tui_debugger_screenshot-71770559a1078f4b08eb5935dcb5c2f6.png");

/***/ }),

/***/ 8453:
/***/ ((__unused_webpack___webpack_module__, __webpack_exports__, __webpack_require__) => {

/* harmony export */ __webpack_require__.d(__webpack_exports__, {
/* harmony export */   R: () => (/* binding */ useMDXComponents),
/* harmony export */   x: () => (/* binding */ MDXProvider)
/* harmony export */ });
/* harmony import */ var react__WEBPACK_IMPORTED_MODULE_0__ = __webpack_require__(6540);
/**
 * @import {MDXComponents} from 'mdx/types.js'
 * @import {Component, ReactElement, ReactNode} from 'react'
 */

/**
 * @callback MergeComponents
 *   Custom merge function.
 * @param {Readonly<MDXComponents>} currentComponents
 *   Current components from the context.
 * @returns {MDXComponents}
 *   Additional components.
 *
 * @typedef Props
 *   Configuration for `MDXProvider`.
 * @property {ReactNode | null | undefined} [children]
 *   Children (optional).
 * @property {Readonly<MDXComponents> | MergeComponents | null | undefined} [components]
 *   Additional components to use or a function that creates them (optional).
 * @property {boolean | null | undefined} [disableParentContext=false]
 *   Turn off outer component context (default: `false`).
 */



/** @type {Readonly<MDXComponents>} */
const emptyComponents = {}

const MDXContext = react__WEBPACK_IMPORTED_MODULE_0__.createContext(emptyComponents)

/**
 * Get current components from the MDX Context.
 *
 * @param {Readonly<MDXComponents> | MergeComponents | null | undefined} [components]
 *   Additional components to use or a function that creates them (optional).
 * @returns {MDXComponents}
 *   Current components.
 */
function useMDXComponents(components) {
  const contextComponents = react__WEBPACK_IMPORTED_MODULE_0__.useContext(MDXContext)

  // Memoize to avoid unnecessary top-level context changes
  return react__WEBPACK_IMPORTED_MODULE_0__.useMemo(
    function () {
      // Custom merge via a function prop
      if (typeof components === 'function') {
        return components(contextComponents)
      }

      return {...contextComponents, ...components}
    },
    [contextComponents, components]
  )
}

/**
 * Provider for MDX context.
 *
 * @param {Readonly<Props>} properties
 *   Properties.
 * @returns {ReactElement}
 *   Element.
 * @satisfies {Component}
 */
function MDXProvider(properties) {
  /** @type {Readonly<MDXComponents>} */
  let allComponents

  if (properties.disableParentContext) {
    allComponents =
      typeof properties.components === 'function'
        ? properties.components(emptyComponents)
        : properties.components || emptyComponents
  } else {
    allComponents = useMDXComponents(properties.components)
  }

  return react__WEBPACK_IMPORTED_MODULE_0__.createElement(
    MDXContext.Provider,
    {value: allComponents},
    properties.children
  )
}


/***/ })

}]);