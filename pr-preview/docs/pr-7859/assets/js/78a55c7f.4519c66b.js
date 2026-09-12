"use strict";
(globalThis["webpackChunkdocusaurus"] = globalThis["webpackChunkdocusaurus"] || []).push([[7171],{

/***/ 2379
(__unused_webpack_module, __webpack_exports__, __webpack_require__) {

// ESM COMPAT FLAG
__webpack_require__.r(__webpack_exports__);

// EXPORTS
__webpack_require__.d(__webpack_exports__, {
  assets: () => (/* binding */ assets),
  contentTitle: () => (/* binding */ contentTitle),
  "default": () => (/* binding */ MDXContent),
  frontMatter: () => (/* binding */ frontMatter),
  metadata: () => (/* reexport */ site_docs_uplc_cli_tool_md_78a_namespaceObject),
  toc: () => (/* binding */ toc)
});

;// ./.docusaurus/docusaurus-plugin-content-docs/default/site-docs-uplc-cli-tool-md-78a.json
const site_docs_uplc_cli_tool_md_78a_namespaceObject = /*#__PURE__*/JSON.parse('{"id":"uplc-cli-tool","title":"UPLC CLI Tool","description":"uplc is a command-line tool for working with Untyped Plutus Core (UPLC).","source":"@site/docs/uplc-cli-tool.md","sourceDirName":".","slug":"/uplc-cli-tool","permalink":"/pr-preview/docs/pr-7859/uplc-cli-tool","draft":false,"unlisted":false,"editUrl":"https://github.com/IntersectMBO/plutus/edit/master/doc/docusaurus/docs/uplc-cli-tool.md","tags":[],"version":"current","sidebarPosition":28,"frontMatter":{"sidebar_position":28},"sidebar":"tutorialSidebar","previous":{"title":"Glossary","permalink":"/pr-preview/docs/pr-7859/glossary"},"next":{"title":"Haddock Documentation","permalink":"/pr-preview/docs/pr-7859/haddock-documentation"}}');
// EXTERNAL MODULE: ./node_modules/react/jsx-runtime.js
var jsx_runtime = __webpack_require__(4848);
// EXTERNAL MODULE: ./node_modules/@mdx-js/react/lib/index.js
var lib = __webpack_require__(8453);
;// ./docs/uplc-cli-tool.md


const frontMatter = {
	sidebar_position: 28
};
const contentTitle = 'UPLC CLI Tool';

const assets = {

};



const toc = [{
  "value": "Subcommands at a glance",
  "id": "subcommands-at-a-glance",
  "level": 2
}, {
  "value": "Shell completion",
  "id": "shell-completion",
  "level": 2
}, {
  "value": "Evaluating scripts",
  "id": "evaluating-scripts",
  "level": 2
}, {
  "value": "Applying arguments to a script",
  "id": "applying-arguments-to-a-script",
  "level": 2
}, {
  "value": "Script optimization",
  "id": "script-optimization",
  "level": 2
}, {
  "value": "The optimization report",
  "id": "the-optimization-report",
  "level": 3
}, {
  "value": "Input and output formats",
  "id": "input-and-output-formats",
  "level": 3
}, {
  "value": "Configuring the optimization pipeline",
  "id": "configuring-the-optimization-pipeline",
  "level": 3
}, {
  "value": "Certifying optimizations",
  "id": "certifying-optimizations",
  "level": 3
}, {
  "value": "Evaluating before and after each optimization",
  "id": "evaluating-before-and-after-each-optimization",
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
    li: "li",
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
        id: "uplc-cli-tool",
        children: "UPLC CLI Tool"
      })
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: [(0,jsx_runtime.jsx)(_components.code, {
        children: "uplc"
      }), " is a command-line tool for working with Untyped Plutus Core (UPLC).\nIt ships with every ", (0,jsx_runtime.jsx)(_components.a, {
        href: "https://github.com/IntersectMBO/plutus/releases",
        children: "Plutus release"
      }), " and is useful for developers who build, test, or ship Plutus scripts."]
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["You can also build ", (0,jsx_runtime.jsx)(_components.code, {
        children: "uplc"
      }), " from source by cloning the Plutus repository, running ", (0,jsx_runtime.jsx)(_components.code, {
        children: "nix develop"
      }), ", and then running ", (0,jsx_runtime.jsx)(_components.code, {
        children: "cabal build uplc"
      }), "."]
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: [(0,jsx_runtime.jsx)(_components.code, {
        children: "uplc"
      }), " supports a variety of subcommands.\nRun ", (0,jsx_runtime.jsx)(_components.code, {
        children: "uplc --help"
      }), " to see the available subcommands, and ", (0,jsx_runtime.jsx)(_components.code, {
        children: "uplc <subcommand> --help"
      }), " to see the options of a particular subcommand.\nBoth ", (0,jsx_runtime.jsx)(_components.code, {
        children: "uplc --help"
      }), " and the ", (0,jsx_runtime.jsx)(_components.code, {
        children: "--help"
      }), " of the most commonly used subcommands end with a short, worked ", (0,jsx_runtime.jsx)(_components.strong, {
        children: "Examples"
      }), " section, so the fastest way to remember how a command is invoked is usually to ask it."]
    }), "\n", (0,jsx_runtime.jsx)(_components.h2, {
      id: "subcommands-at-a-glance",
      children: "Subcommands at a glance"
    }), "\n", (0,jsx_runtime.jsxs)(_components.table, {
      children: [(0,jsx_runtime.jsx)(_components.thead, {
        children: (0,jsx_runtime.jsxs)(_components.tr, {
          children: [(0,jsx_runtime.jsx)(_components.th, {
            children: "Subcommand"
          }), (0,jsx_runtime.jsx)(_components.th, {
            children: "What it does"
          })]
        })
      }), (0,jsx_runtime.jsxs)(_components.tbody, {
        children: [(0,jsx_runtime.jsxs)(_components.tr, {
          children: [(0,jsx_runtime.jsx)(_components.td, {
            children: (0,jsx_runtime.jsx)(_components.code, {
              children: "evaluate"
            })
          }), (0,jsx_runtime.jsx)(_components.td, {
            children: "Run a UPLC program on the CEK machine and print the result."
          })]
        }), (0,jsx_runtime.jsxs)(_components.tr, {
          children: [(0,jsx_runtime.jsx)(_components.td, {
            children: (0,jsx_runtime.jsx)(_components.code, {
              children: "time"
            })
          }), (0,jsx_runtime.jsx)(_components.td, {
            children: "Time the evaluation of a UPLC program on the CEK machine."
          })]
        }), (0,jsx_runtime.jsxs)(_components.tr, {
          children: [(0,jsx_runtime.jsx)(_components.td, {
            children: (0,jsx_runtime.jsx)(_components.code, {
              children: "debug"
            })
          }), (0,jsx_runtime.jsx)(_components.td, {
            children: "Step through a UPLC program interactively on the CEK machine."
          })]
        }), (0,jsx_runtime.jsxs)(_components.tr, {
          children: [(0,jsx_runtime.jsx)(_components.td, {
            children: (0,jsx_runtime.jsx)(_components.code, {
              children: "apply"
            })
          }), (0,jsx_runtime.jsxs)(_components.td, {
            children: ["Apply one script to others, producing ", (0,jsx_runtime.jsx)(_components.code, {
              children: "(... ((f g1) g2) ... gn)"
            }), "."]
          })]
        }), (0,jsx_runtime.jsxs)(_components.tr, {
          children: [(0,jsx_runtime.jsxs)(_components.td, {
            children: [(0,jsx_runtime.jsx)(_components.code, {
              children: "apply-to-flat-data"
            }), " / ", (0,jsx_runtime.jsx)(_components.code, {
              children: "apply-to-cbor-data"
            })]
          }), (0,jsx_runtime.jsxs)(_components.td, {
            children: ["Apply a script to flat- or CBOR-encoded ", (0,jsx_runtime.jsx)(_components.code, {
              children: "Data"
            }), " arguments."]
          })]
        }), (0,jsx_runtime.jsxs)(_components.tr, {
          children: [(0,jsx_runtime.jsx)(_components.td, {
            children: (0,jsx_runtime.jsx)(_components.code, {
              children: "convert"
            })
          }), (0,jsx_runtime.jsx)(_components.td, {
            children: "Convert a program between formats (textual, flat, hex, blueprint, …)."
          })]
        }), (0,jsx_runtime.jsxs)(_components.tr, {
          children: [(0,jsx_runtime.jsx)(_components.td, {
            children: (0,jsx_runtime.jsx)(_components.code, {
              children: "print"
            })
          }), (0,jsx_runtime.jsx)(_components.td, {
            children: "Parse a program and pretty-print it."
          })]
        }), (0,jsx_runtime.jsxs)(_components.tr, {
          children: [(0,jsx_runtime.jsxs)(_components.td, {
            children: [(0,jsx_runtime.jsx)(_components.code, {
              children: "optimise"
            }), " / ", (0,jsx_runtime.jsx)(_components.code, {
              children: "optimize"
            })]
          }), (0,jsx_runtime.jsx)(_components.td, {
            children: "Run the UPLC optimisation pipeline."
          })]
        }), (0,jsx_runtime.jsxs)(_components.tr, {
          children: [(0,jsx_runtime.jsx)(_components.td, {
            children: (0,jsx_runtime.jsx)(_components.code, {
              children: "benchmark"
            })
          }), (0,jsx_runtime.jsxs)(_components.td, {
            children: ["Benchmark evaluation with ", (0,jsx_runtime.jsx)(_components.a, {
              href: "https://hackage.haskell.org/package/criterion",
              children: "Criterion"
            }), "."]
          })]
        }), (0,jsx_runtime.jsxs)(_components.tr, {
          children: [(0,jsx_runtime.jsx)(_components.td, {
            children: (0,jsx_runtime.jsx)(_components.code, {
              children: "example"
            })
          }), (0,jsx_runtime.jsxs)(_components.td, {
            children: ["Show built-in example programs (", (0,jsx_runtime.jsx)(_components.code, {
              children: "uplc example -a"
            }), " lists them)."]
          })]
        }), (0,jsx_runtime.jsxs)(_components.tr, {
          children: [(0,jsx_runtime.jsx)(_components.td, {
            children: (0,jsx_runtime.jsx)(_components.code, {
              children: "dump-cost-model"
            })
          }), (0,jsx_runtime.jsx)(_components.td, {
            children: "Dump the cost model parameters."
          })]
        }), (0,jsx_runtime.jsxs)(_components.tr, {
          children: [(0,jsx_runtime.jsx)(_components.td, {
            children: (0,jsx_runtime.jsx)(_components.code, {
              children: "print-builtin-signatures"
            })
          }), (0,jsx_runtime.jsx)(_components.td, {
            children: "Print the signatures of the built-in functions."
          })]
        })]
      })]
    }), "\n", (0,jsx_runtime.jsx)(_components.h2, {
      id: "shell-completion",
      children: "Shell completion"
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: [(0,jsx_runtime.jsx)(_components.code, {
        children: "uplc"
      }), " can generate a completion script for ", (0,jsx_runtime.jsx)(_components.code, {
        children: "bash"
      }), ", ", (0,jsx_runtime.jsx)(_components.code, {
        children: "zsh"
      }), ", or ", (0,jsx_runtime.jsx)(_components.code, {
        children: "fish"
      }), ".\nCompletion covers subcommand names, option flags, file paths (for ", (0,jsx_runtime.jsx)(_components.code, {
        children: "-i"
      }), ", ", (0,jsx_runtime.jsx)(_components.code, {
        children: "-o"
      }), ", ", (0,jsx_runtime.jsx)(_components.code, {
        children: "--eval-apply"
      }), ", …), and the allowed values of enumerated options such as ", (0,jsx_runtime.jsx)(_components.code, {
        children: "--if"
      }), "/", (0,jsx_runtime.jsx)(_components.code, {
        children: "--of"
      }), ", ", (0,jsx_runtime.jsx)(_components.code, {
        children: "--print-mode"
      }), ", ", (0,jsx_runtime.jsx)(_components.code, {
        children: "--trace-mode"
      }), ", and ", (0,jsx_runtime.jsx)(_components.code, {
        children: "-S"
      }), "/", (0,jsx_runtime.jsx)(_components.code, {
        children: "--builtin-semantics-variant"
      }), "."]
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["To enable completion in the ", (0,jsx_runtime.jsx)(_components.strong, {
        children: "current"
      }), " shell:"]
    }), "\n", (0,jsx_runtime.jsx)(_components.pre, {
      children: (0,jsx_runtime.jsx)(_components.code, {
        className: "language-bash",
        children: "# bash\nsource <(uplc --bash-completion-script \"$(command -v uplc)\")\n"
      })
    }), "\n", (0,jsx_runtime.jsx)(_components.pre, {
      children: (0,jsx_runtime.jsx)(_components.code, {
        className: "language-bash",
        children: "# zsh — the generated script is a completion function body, so it cannot be\n# sourced directly; install it as `_uplc` on your $fpath instead:\nmkdir -p ~/.zsh/completions\nuplc --zsh-completion-script \"$(command -v uplc)\" > ~/.zsh/completions/_uplc\nfpath+=(~/.zsh/completions)\nautoload -U compinit && compinit\n"
      })
    }), "\n", (0,jsx_runtime.jsx)(_components.pre, {
      children: (0,jsx_runtime.jsx)(_components.code, {
        className: "language-bash",
        children: "# fish\nuplc --fish-completion-script (command -v uplc) | source\n"
      })
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["To install completion ", (0,jsx_runtime.jsx)(_components.strong, {
        children: "permanently"
      }), ", write the generated script to the location your shell loads completions from, for example:"]
    }), "\n", (0,jsx_runtime.jsx)(_components.pre, {
      children: (0,jsx_runtime.jsx)(_components.code, {
        className: "language-bash",
        children: "# bash (system-wide; use a user directory if you prefer)\nuplc --bash-completion-script \"$(command -v uplc)\" | sudo tee /etc/bash_completion.d/uplc > /dev/null\n\n# zsh (a directory on your $fpath; add the fpath+= and compinit lines above to your .zshrc)\nuplc --zsh-completion-script \"$(command -v uplc)\" > ~/.zsh/completions/_uplc\n\n# fish\nuplc --fish-completion-script (command -v uplc) > ~/.config/fish/completions/uplc.fish\n"
      })
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["The same flags work for the ", (0,jsx_runtime.jsx)(_components.code, {
        children: "plc"
      }), " and ", (0,jsx_runtime.jsx)(_components.code, {
        children: "pir"
      }), " tools; just substitute the program name."]
    }), "\n", (0,jsx_runtime.jsx)(_components.h2, {
      id: "evaluating-scripts",
      children: "Evaluating scripts"
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: [(0,jsx_runtime.jsx)(_components.code, {
        children: "uplc evaluate"
      }), " runs a UPLC program on the CEK machine.\nAs with every subcommand, if ", (0,jsx_runtime.jsx)(_components.code, {
        children: "-i"
      }), " is omitted the program is read from stdin, which makes it easy to use in a pipeline:"]
    }), "\n", (0,jsx_runtime.jsx)(_components.pre, {
      children: (0,jsx_runtime.jsx)(_components.code, {
        className: "language-bash",
        children: "uplc evaluate -i program.uplc\necho '(program 1.1.0 (con integer 42))' | uplc evaluate\n"
      })
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["Scripts as they appear on-chain (in blueprints, wallets, or block explorers) are usually hex-encoded, so pass ", (0,jsx_runtime.jsx)(_components.code, {
        children: "--if hex"
      }), ":"]
    }), "\n", (0,jsx_runtime.jsx)(_components.pre, {
      children: (0,jsx_runtime.jsx)(_components.code, {
        className: "language-bash",
        children: "uplc evaluate --if hex -i script.hex\n"
      })
    }), "\n", (0,jsx_runtime.jsx)(_components.p, {
      children: "By default evaluation is silent about resource usage. To see how much CPU and memory a program consumes, pick a budget mode:"
    }), "\n", (0,jsx_runtime.jsxs)(_components.ul, {
      children: ["\n", (0,jsx_runtime.jsxs)(_components.li, {
        children: [(0,jsx_runtime.jsx)(_components.code, {
          children: "--counting"
        }), " (", (0,jsx_runtime.jsx)(_components.code, {
          children: "-c"
        }), ") — run to completion and report the total budget spent."]
      }), "\n", (0,jsx_runtime.jsxs)(_components.li, {
        children: [(0,jsx_runtime.jsx)(_components.code, {
          children: "--tallying"
        }), " (", (0,jsx_runtime.jsx)(_components.code, {
          children: "-t"
        }), ") — like ", (0,jsx_runtime.jsx)(_components.code, {
          children: "--counting"
        }), ", but also break the cost down per builtin and per AST-node type."]
      }), "\n", (0,jsx_runtime.jsxs)(_components.li, {
        children: [(0,jsx_runtime.jsx)(_components.code, {
          children: "--restricting ExCPU:ExMemory"
        }), " (", (0,jsx_runtime.jsx)(_components.code, {
          children: "-R"
        }), ") — run within the given budget and fail if it is exceeded, e.g. ", (0,jsx_runtime.jsx)(_components.code, {
          children: "--restricting 1000000:5000"
        }), "."]
      }), "\n", (0,jsx_runtime.jsxs)(_components.li, {
        children: [(0,jsx_runtime.jsx)(_components.code, {
          children: "--restricting-enormous"
        }), " (", (0,jsx_runtime.jsx)(_components.code, {
          children: "-r"
        }), ") — run within a very large (effectively unlimited) budget and print the budget ", (0,jsx_runtime.jsx)(_components.strong, {
          children: "remaining"
        }), " afterwards. Evaluation already uses this enormous budget by default; ", (0,jsx_runtime.jsx)(_components.code, {
          children: "-r"
        }), " only adds the report. To see what a run ", (0,jsx_runtime.jsx)(_components.em, {
          children: "consumed"
        }), ", use ", (0,jsx_runtime.jsx)(_components.code, {
          children: "--counting"
        }), " or ", (0,jsx_runtime.jsx)(_components.code, {
          children: "--tallying"
        }), "."]
      }), "\n"]
    }), "\n", (0,jsx_runtime.jsx)(_components.pre, {
      children: (0,jsx_runtime.jsx)(_components.code, {
        className: "language-bash",
        children: "uplc evaluate -i program.uplc --tallying\n"
      })
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["To capture ", (0,jsx_runtime.jsx)(_components.code, {
        children: "trace"
      }), " output emitted by the program, use ", (0,jsx_runtime.jsx)(_components.code, {
        children: "--trace-mode"
      }), ", e.g. ", (0,jsx_runtime.jsx)(_components.code, {
        children: "--trace-mode Logs"
      }), "."]
    }), "\n", (0,jsx_runtime.jsx)(_components.h2, {
      id: "applying-arguments-to-a-script",
      children: "Applying arguments to a script"
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["A validator becomes a runnable program only once its arguments (datum, redeemer, script context, …) have been applied.\n", (0,jsx_runtime.jsx)(_components.code, {
        children: "uplc apply"
      }), " builds that application for you.\nUse ", (0,jsx_runtime.jsx)(_components.code, {
        children: "apply"
      }), " when the arguments are themselves UPLC scripts, and ", (0,jsx_runtime.jsx)(_components.code, {
        children: "apply-to-flat-data"
      }), " / ", (0,jsx_runtime.jsx)(_components.code, {
        children: "apply-to-cbor-data"
      }), " when they are encoded ", (0,jsx_runtime.jsx)(_components.code, {
        children: "Data"
      }), " values (the common case for on-chain arguments):"]
    }), "\n", (0,jsx_runtime.jsx)(_components.pre, {
      children: (0,jsx_runtime.jsx)(_components.code, {
        className: "language-bash",
        children: "# arguments are UPLC scripts\nuplc apply --if flat Validator.flat Datum.flat Redeemer.flat Context.flat --of flat -o Script.flat\n\n# arguments are CBOR-encoded Data\nuplc apply-to-cbor-data --if flat Validator.flat Datum.cbor Redeemer.cbor Context.cbor --of flat -o Script.flat\n"
      })
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["You can then evaluate the fully-applied script with ", (0,jsx_runtime.jsx)(_components.code, {
        children: "uplc evaluate"
      }), "."]
    }), "\n", (0,jsx_runtime.jsx)(_components.h2, {
      id: "script-optimization",
      children: "Script optimization"
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["For most users, the most immediately useful subcommand is ", (0,jsx_runtime.jsx)(_components.code, {
        children: "optimize"
      }), " (or ", (0,jsx_runtime.jsx)(_components.code, {
        children: "optimise"
      }), "), which optimizes UPLC programs.\nIt runs the same UPLC optimization pipeline that the Plinth compiler uses internally: case-of-known-constructor, inlining, common subexpression elimination (CSE), and more."]
    }), "\n", (0,jsx_runtime.jsx)(_components.p, {
      children: "Basic usage:"
    }), "\n", (0,jsx_runtime.jsx)(_components.pre, {
      children: (0,jsx_runtime.jsx)(_components.code, {
        children: "uplc optimize -i MyValidator.uplc -o MyValidator-opt.uplc\n"
      })
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["By default, both input and output files use the textual format.\nIf ", (0,jsx_runtime.jsx)(_components.code, {
        children: "-i"
      }), " or ", (0,jsx_runtime.jsx)(_components.code, {
        children: "-o"
      }), " is omitted, ", (0,jsx_runtime.jsx)(_components.code, {
        children: "uplc"
      }), " reads from stdin and writes to stdout, so it fits naturally into shell pipelines."]
    }), "\n", (0,jsx_runtime.jsx)(_components.h3, {
      id: "the-optimization-report",
      children: "The optimization report"
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["Running ", (0,jsx_runtime.jsx)(_components.code, {
        children: "uplc optimize"
      }), " prints an ", (0,jsx_runtime.jsx)(_components.em, {
        children: "optimization report"
      }), " to stderr.\nThe report lists each pass that ran, in order, and shows the AST size before and after every pass, along with the size delta.\nWhen evaluation is enabled (see below), each row additionally shows the CPU and memory cost at that stage and the deltas against the previous stage.\nWhen ", (0,jsx_runtime.jsx)(_components.code, {
        children: "--certify --certifier-report"
      }), " is used, the same per-pass numbers are also included in the certifier report file."]
    }), "\n", (0,jsx_runtime.jsx)(_components.h3, {
      id: "input-and-output-formats",
      children: "Input and output formats"
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: [(0,jsx_runtime.jsx)(_components.code, {
        children: "uplc"
      }), " has always supported textual and flat-encoded scripts, but two recent additions make it much easier to plug into existing toolchains:"]
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: [(0,jsx_runtime.jsx)(_components.strong, {
        children: "Hex-encoded scripts"
      }), ".\nThis is the format most off-chain tools, wallets, and block explorers use.\nTo use hex input or output, specify the formats with ", (0,jsx_runtime.jsx)(_components.code, {
        children: "--if"
      }), " and ", (0,jsx_runtime.jsx)(_components.code, {
        children: "--of"
      }), ":"]
    }), "\n", (0,jsx_runtime.jsx)(_components.pre, {
      children: (0,jsx_runtime.jsx)(_components.code, {
        children: "uplc optimize --if hex --of hex -i MyValidator.uplc -o MyValidator-opt.uplc\n"
      })
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: [(0,jsx_runtime.jsx)(_components.strong, {
        children: "Blueprint JSON"
      }), ".\nA ", (0,jsx_runtime.jsx)(_components.a, {
        href: "https://cips.cardano.org/cips/cip57/",
        children: "CIP-57"
      }), " blueprint is the standard packaging format for Plutus contracts and may contain multiple validators.\nYou can feed a blueprint straight into ", (0,jsx_runtime.jsx)(_components.code, {
        children: "uplc"
      }), " and get an optimized blueprint back, with every validator optimized and the corresponding hash field recomputed:"]
    }), "\n", (0,jsx_runtime.jsx)(_components.pre, {
      children: (0,jsx_runtime.jsx)(_components.code, {
        children: "uplc optimize --if blueprint --of blueprint -i MyBlueprint.json -o MyBlueprint.opt.json\n"
      })
    }), "\n", (0,jsx_runtime.jsx)(_components.p, {
      children: "The full list of supported formats is:"
    }), "\n", (0,jsx_runtime.jsxs)(_components.ul, {
      children: ["\n", (0,jsx_runtime.jsxs)(_components.li, {
        children: [(0,jsx_runtime.jsx)(_components.code, {
          children: "textual"
        }), " — human-readable UPLC syntax"]
      }), "\n", (0,jsx_runtime.jsxs)(_components.li, {
        children: [(0,jsx_runtime.jsx)(_components.code, {
          children: "flat"
        }), " / ", (0,jsx_runtime.jsx)(_components.code, {
          children: "flat-deBruijn"
        }), " — flat-encoded with de Bruijn indices"]
      }), "\n", (0,jsx_runtime.jsxs)(_components.li, {
        children: [(0,jsx_runtime.jsx)(_components.code, {
          children: "flat-named"
        }), " — flat-encoded with textual names"]
      }), "\n", (0,jsx_runtime.jsxs)(_components.li, {
        children: [(0,jsx_runtime.jsx)(_components.code, {
          children: "flat-namedDeBruijn"
        }), " — flat-encoded with named de Bruijn indices"]
      }), "\n", (0,jsx_runtime.jsxs)(_components.li, {
        children: [(0,jsx_runtime.jsx)(_components.code, {
          children: "serialised"
        }), " — CBOR-wrapped flat with de Bruijn indices"]
      }), "\n", (0,jsx_runtime.jsxs)(_components.li, {
        children: [(0,jsx_runtime.jsx)(_components.code, {
          children: "hex"
        }), " — ", (0,jsx_runtime.jsx)(_components.code, {
          children: "serialised"
        }), " plus hex encoding (what blueprints and most tools use)"]
      }), "\n", (0,jsx_runtime.jsxs)(_components.li, {
        children: [(0,jsx_runtime.jsx)(_components.code, {
          children: "blueprint"
        }), " — blueprint JSON"]
      }), "\n"]
    }), "\n", (0,jsx_runtime.jsx)(_components.h3, {
      id: "configuring-the-optimization-pipeline",
      children: "Configuring the optimization pipeline"
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["The ", (0,jsx_runtime.jsx)(_components.code, {
        children: "opt-*"
      }), " flags let you configure the optimization pipeline.\nRun ", (0,jsx_runtime.jsx)(_components.code, {
        children: "uplc optimize --help"
      }), " to see the full list."]
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["The flags most worth experimenting with when you're optimizing primarily for either execution cost or script size are the inliner-aggressiveness flags — ", (0,jsx_runtime.jsx)(_components.code, {
        children: "--opt-inline-unconditional-growth"
      }), " and ", (0,jsx_runtime.jsx)(_components.code, {
        children: "--opt-inline-callsite-growth"
      }), " — plus ", (0,jsx_runtime.jsx)(_components.code, {
        children: "--opt-no-inline-constants"
      }), " and ", (0,jsx_runtime.jsx)(_components.code, {
        children: "--opt-cse-which-subterms"
      }), ".\nThey give you direct control over the cost-vs-size tradeoff."]
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["The two ", (0,jsx_runtime.jsx)(_components.code, {
        children: "--opt-inline-...-growth"
      }), " flags govern how much AST growth the inliner accepts.\nHigher values mean more aggressive inlining, and more inlining usually reduces cost, but sometimes increases size.\n", (0,jsx_runtime.jsx)(_components.code, {
        children: "--opt-no-inline-constants"
      }), " controls the inlining of constants specifically: inlining constants is good for cost, but if a large constant occurs at many callsites, inlining it copies the constant each time and inflates size.\n", (0,jsx_runtime.jsx)(_components.code, {
        children: "--opt-cse-which-subterms"
      }), " controls how aggressive common subexpression elimination is: ", (0,jsx_runtime.jsx)(_components.code, {
        children: "all"
      }), " is more aggressive than the default ", (0,jsx_runtime.jsx)(_components.code, {
        children: "exclude-work-free"
      }), ".\nAggressive CSE typically reduces size (more duplicates get factored out) but can raise cost (each factored subterm adds a small evaluation overhead)."]
    }), "\n", (0,jsx_runtime.jsx)(_components.h3, {
      id: "certifying-optimizations",
      children: "Certifying optimizations"
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: [(0,jsx_runtime.jsx)(_components.code, {
        children: "uplc"
      }), " includes certifiers for optimization passes.\nEach pass is formalized in Agda as a translation relation between pre- and post-terms together with a procedure that decides whether the relation holds."]
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["Each certifier takes the pre- and post-terms of a single pass and either accepts the transformation as valid or rejects it.\nThe ", (0,jsx_runtime.jsx)(_components.code, {
        children: "--certify"
      }), " flag runs the certifier, and can produce an Agda artifact that can be checked independently by Agda."]
    }), "\n", (0,jsx_runtime.jsxs)(_components.blockquote, {
      children: ["\n", (0,jsx_runtime.jsxs)(_components.p, {
        children: ["📌", " ", (0,jsx_runtime.jsx)(_components.strong, {
          children: "NOTE"
        })]
      }), "\n", (0,jsx_runtime.jsx)(_components.p, {
        children: "Certification is currently experimental."
      }), "\n"]
    }), "\n", (0,jsx_runtime.jsx)(_components.p, {
      children: "Basic usage:"
    }), "\n", (0,jsx_runtime.jsx)(_components.pre, {
      children: (0,jsx_runtime.jsx)(_components.code, {
        children: "uplc optimize -i MyValidator.uplc -o MyValidator-opt.uplc --certify MyProof\n"
      })
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["This produces an Agda project (the default output mode) that encodes a correctness proof of the transformation, named after the ", (0,jsx_runtime.jsx)(_components.code, {
        children: "MyProof"
      }), " argument.\nYou can then run the Agda type checker on the generated project to verify the certificate."]
    }), "\n", (0,jsx_runtime.jsx)(_components.p, {
      children: "The certifier has three output modes:"
    }), "\n", (0,jsx_runtime.jsxs)(_components.ul, {
      children: ["\n", (0,jsx_runtime.jsxs)(_components.li, {
        children: [(0,jsx_runtime.jsx)(_components.code, {
          children: "--certifier-project"
        }), " — emit a full Agda project that can be type-checked with Agda.\nThis is the default."]
      }), "\n", (0,jsx_runtime.jsxs)(_components.li, {
        children: [(0,jsx_runtime.jsx)(_components.code, {
          children: "--certifier-report REPORT_FILE"
        }), " — emit a human-readable report to the given file.\nThe report summarizes the optimization passes that ran, and includes the AST size at each stage.\nIt can also include the execution cost at each stage when evaluation is enabled (explained below)."]
      }), "\n", (0,jsx_runtime.jsxs)(_components.li, {
        children: [(0,jsx_runtime.jsx)(_components.code, {
          children: "--certifier-basic"
        }), " — emit minimal output."]
      }), "\n"]
    }), "\n", (0,jsx_runtime.jsx)(_components.p, {
      children: "For blueprints, the certifier runs once per validator.\nReport filenames and project directories have the validator's title appended automatically."
    }), "\n", (0,jsx_runtime.jsx)(_components.h3, {
      id: "evaluating-before-and-after-each-optimization",
      children: "Evaluating before and after each optimization"
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["The ", (0,jsx_runtime.jsx)(_components.code, {
        children: "--eval*"
      }), " flags supply arguments to the script and run it on the CEK machine at every stage of the optimization pipeline, recording the execution cost at each step.\nThe CPU and memory cost at every stage are then shown alongside AST sizes in the optimization report.\nWhen ", (0,jsx_runtime.jsx)(_components.code, {
        children: "--certify --certifier-report"
      }), " is used, the same per-pass costs are also included in the certifier report file."]
    }), "\n", (0,jsx_runtime.jsx)(_components.p, {
      children: "For a single script:"
    }), "\n", (0,jsx_runtime.jsx)(_components.pre, {
      children: (0,jsx_runtime.jsx)(_components.code, {
        children: "uplc optimize -i MyValidator.uplc -o MyValidator-opt.uplc \\\n  --certify MyProof --certifier-report MyValidator.report \\\n  --eval-apply datum.hex \\\n  --eval-apply redeemer.hex \\\n  --eval-apply context.hex\n"
      })
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["By default ", (0,jsx_runtime.jsx)(_components.code, {
        children: "--eval-apply"
      }), " arguments are interpreted as hex-encoded ", (0,jsx_runtime.jsx)(_components.code, {
        children: "Data"
      }), ".\nIf you want to supply a UPLC program instead, use ", (0,jsx_runtime.jsx)(_components.code, {
        children: "--eval-arg-kind prog"
      }), ".\nTo evaluate a script without supplying any arguments, use ", (0,jsx_runtime.jsx)(_components.code, {
        children: "--eval"
      }), "."]
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["For blueprints, since a blueprint may contain multiple validators, use ", (0,jsx_runtime.jsx)(_components.code, {
        children: "--eval-args-dir DIR"
      }), " to point at a directory with the following layout:"]
    }), "\n", (0,jsx_runtime.jsx)(_components.pre, {
      children: (0,jsx_runtime.jsx)(_components.code, {
        children: "args/\n├── MyMintingPolicy/\n│   ├── 0        # first argument to MyMintingPolicy\n│   └── 1        # second argument\n└── MySpendingValidator/\n    ├── 0\n    ├── 1\n    └── 2\n"
      })
    }), "\n", (0,jsx_runtime.jsx)(_components.p, {
      children: "Then run:"
    }), "\n", (0,jsx_runtime.jsx)(_components.pre, {
      children: (0,jsx_runtime.jsx)(_components.code, {
        children: "uplc optimize --if blueprint --of blueprint -i MyBlueprint.json -o MyBlueprint-opt.json \\\n  --certify MyProof --certifier-report MyProof.report \\\n  --eval-args-dir args\n"
      })
    }), "\n", (0,jsx_runtime.jsx)(_components.p, {
      children: "Each validator is evaluated with the arguments under the corresponding subdirectory.\nThe result is an optimized blueprint, and a per-validator report showing how the execution budget changed at each optimization step."
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



/***/ },

/***/ 8453
(__unused_webpack___webpack_module__, __webpack_exports__, __webpack_require__) {

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


/***/ }

}]);