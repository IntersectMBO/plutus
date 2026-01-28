"use strict";
(self["webpackChunkdocusaurus"] = self["webpackChunkdocusaurus"] || []).push([[7804],{

/***/ 4393:
/***/ ((__unused_webpack_module, __webpack_exports__, __webpack_require__) => {

// ESM COMPAT FLAG
__webpack_require__.r(__webpack_exports__);

// EXPORTS
__webpack_require__.d(__webpack_exports__, {
  assets: () => (/* binding */ assets),
  contentTitle: () => (/* binding */ contentTitle),
  "default": () => (/* binding */ MDXContent),
  frontMatter: () => (/* binding */ frontMatter),
  metadata: () => (/* reexport */ site_docs_delve_deeper_plinth_compiler_options_md_a79_namespaceObject),
  toc: () => (/* binding */ toc)
});

;// ./.docusaurus/docusaurus-plugin-content-docs/default/site-docs-delve-deeper-plinth-compiler-options-md-a79.json
const site_docs_delve_deeper_plinth_compiler_options_md_a79_namespaceObject = /*#__PURE__*/JSON.parse('{"id":"delve-deeper/plinth-compiler-options","title":"Plinth Compiler Options","description":"These options can be passed to the compiler via the OPTIONS_GHC pragma, for instance","source":"@site/docs/delve-deeper/plinth-compiler-options.md","sourceDirName":"delve-deeper","slug":"/delve-deeper/plinth-compiler-options","permalink":"/pr-preview/docs/pr-7511/delve-deeper/plinth-compiler-options","draft":false,"unlisted":false,"editUrl":"https://github.com/IntersectMBO/plutus/edit/master/doc/docusaurus/docs/delve-deeper/plinth-compiler-options.md","tags":[],"version":"current","sidebarPosition":5,"frontMatter":{"sidebar_position":5},"sidebar":"tutorialSidebar","previous":{"title":"Overview of Languages Compiling to UPLC","permalink":"/pr-preview/docs/pr-7511/delve-deeper/languages"},"next":{"title":"Cost Model","permalink":"/pr-preview/docs/pr-7511/delve-deeper/cost-model"}}');
// EXTERNAL MODULE: ./node_modules/react/jsx-runtime.js
var jsx_runtime = __webpack_require__(4848);
// EXTERNAL MODULE: ./node_modules/@mdx-js/react/lib/index.js
var lib = __webpack_require__(8453);
;// ./docs/delve-deeper/plinth-compiler-options.md


const frontMatter = {
	sidebar_position: 5
};
const contentTitle = 'Plinth Compiler Options';

const assets = {

};



const toc = [];
function _createMdxContent(props) {
  const _components = {
    code: "code",
    h1: "h1",
    header: "header",
    p: "p",
    pre: "pre",
    table: "table",
    tbody: "tbody",
    td: "td",
    th: "th",
    thead: "thead",
    tr: "tr",
    ...(0,lib/* useMDXComponents */.R)(),
    ...props.components
  };
  return (0,jsx_runtime.jsxs)(jsx_runtime.Fragment, {
    children: [(0,jsx_runtime.jsx)(_components.header, {
      children: (0,jsx_runtime.jsx)(_components.h1, {
        id: "plinth-compiler-options",
        children: "Plinth Compiler Options"
      })
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["These options can be passed to the compiler via the ", (0,jsx_runtime.jsx)(_components.code, {
        children: "OPTIONS_GHC"
      }), " pragma, for instance"]
    }), "\n", (0,jsx_runtime.jsx)(_components.pre, {
      children: (0,jsx_runtime.jsx)(_components.code, {
        className: "language-haskell",
        children: "{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:dump-uplc #-}\n{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:max-simplifier-iterations-uplc=3 #-}\n"
      })
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["For each boolean option, you can add a ", (0,jsx_runtime.jsx)(_components.code, {
        children: "no-"
      }), " prefix to switch it off, such as ", (0,jsx_runtime.jsx)(_components.code, {
        children: "no-typecheck"
      }), ", ", (0,jsx_runtime.jsx)(_components.code, {
        children: "no-simplifier-beta"
      }), "."]
    }), "\n", (0,jsx_runtime.jsxs)(_components.table, {
      children: [(0,jsx_runtime.jsx)(_components.thead, {
        children: (0,jsx_runtime.jsxs)(_components.tr, {
          children: [(0,jsx_runtime.jsx)(_components.th, {
            children: "Option"
          }), (0,jsx_runtime.jsx)(_components.th, {
            children: "Value Type"
          }), (0,jsx_runtime.jsx)(_components.th, {
            children: "Default"
          }), (0,jsx_runtime.jsx)(_components.th, {
            children: "Description"
          })]
        })
      }), (0,jsx_runtime.jsxs)(_components.tbody, {
        children: [(0,jsx_runtime.jsxs)(_components.tr, {
          children: [(0,jsx_runtime.jsx)(_components.td, {
            children: (0,jsx_runtime.jsx)(_components.code, {
              children: "certify"
            })
          }), (0,jsx_runtime.jsx)(_components.td, {
            children: "Maybe [Char]"
          }), (0,jsx_runtime.jsx)(_components.td, {}), (0,jsx_runtime.jsx)(_components.td, {
            children: "Produce a certificate for the compiled program, with the given name. This certificate provides evidence that the compiler optimizations have preserved the functional behavior of the original program. Currently, this is only supported for the UPLC compilation pipeline. Warning: this is an experimental feature and may not work as expected."
          })]
        }), (0,jsx_runtime.jsxs)(_components.tr, {
          children: [(0,jsx_runtime.jsx)(_components.td, {
            children: (0,jsx_runtime.jsx)(_components.code, {
              children: "conservative-optimisation"
            })
          }), (0,jsx_runtime.jsx)(_components.td, {
            children: "Bool"
          }), (0,jsx_runtime.jsx)(_components.td, {
            children: "False"
          }), (0,jsx_runtime.jsxs)(_components.td, {
            children: ["When conservative optimisation is used, only the optimisations that never make the program worse (in terms of cost or size) are employed. Implies ", (0,jsx_runtime.jsx)(_components.code, {
              children: "no-relaxed-float-in"
            }), ", ", (0,jsx_runtime.jsx)(_components.code, {
              children: "no-inline-constants"
            }), ", ", (0,jsx_runtime.jsx)(_components.code, {
              children: "no-inline-fix"
            }), ", ", (0,jsx_runtime.jsx)(_components.code, {
              children: "no-simplifier-evaluate-builtins"
            }), ", and ", (0,jsx_runtime.jsx)(_components.code, {
              children: "preserve-logging"
            }), "."]
          })]
        }), (0,jsx_runtime.jsxs)(_components.tr, {
          children: [(0,jsx_runtime.jsx)(_components.td, {
            children: (0,jsx_runtime.jsx)(_components.code, {
              children: "context-level"
            })
          }), (0,jsx_runtime.jsx)(_components.td, {
            children: "Int"
          }), (0,jsx_runtime.jsx)(_components.td, {
            children: "1"
          }), (0,jsx_runtime.jsx)(_components.td, {
            children: "Set context level for error messages."
          })]
        }), (0,jsx_runtime.jsxs)(_components.tr, {
          children: [(0,jsx_runtime.jsx)(_components.td, {
            children: (0,jsx_runtime.jsx)(_components.code, {
              children: "coverage-all"
            })
          }), (0,jsx_runtime.jsx)(_components.td, {
            children: "Bool"
          }), (0,jsx_runtime.jsx)(_components.td, {
            children: "False"
          }), (0,jsx_runtime.jsx)(_components.td, {
            children: "Add all available coverage annotations in the trace output"
          })]
        }), (0,jsx_runtime.jsxs)(_components.tr, {
          children: [(0,jsx_runtime.jsx)(_components.td, {
            children: (0,jsx_runtime.jsx)(_components.code, {
              children: "coverage-boolean"
            })
          }), (0,jsx_runtime.jsx)(_components.td, {
            children: "Bool"
          }), (0,jsx_runtime.jsx)(_components.td, {
            children: "False"
          }), (0,jsx_runtime.jsx)(_components.td, {
            children: "Add boolean coverage annotations in the trace output"
          })]
        }), (0,jsx_runtime.jsxs)(_components.tr, {
          children: [(0,jsx_runtime.jsx)(_components.td, {
            children: (0,jsx_runtime.jsx)(_components.code, {
              children: "coverage-location"
            })
          }), (0,jsx_runtime.jsx)(_components.td, {
            children: "Bool"
          }), (0,jsx_runtime.jsx)(_components.td, {
            children: "False"
          }), (0,jsx_runtime.jsx)(_components.td, {
            children: "Add location coverage annotations in the trace output"
          })]
        }), (0,jsx_runtime.jsxs)(_components.tr, {
          children: [(0,jsx_runtime.jsx)(_components.td, {
            children: (0,jsx_runtime.jsx)(_components.code, {
              children: "datatypes"
            })
          }), (0,jsx_runtime.jsx)(_components.td, {
            children: "DatatypeCompilationOpts"
          }), (0,jsx_runtime.jsx)(_components.td, {
            children: "SumsOfProducts"
          }), (0,jsx_runtime.jsx)(_components.td, {
            children: "BuiltinCasing"
          })]
        }), (0,jsx_runtime.jsxs)(_components.tr, {
          children: [(0,jsx_runtime.jsx)(_components.td, {
            children: (0,jsx_runtime.jsx)(_components.code, {
              children: "defer-errors"
            })
          }), (0,jsx_runtime.jsx)(_components.td, {
            children: "Bool"
          }), (0,jsx_runtime.jsx)(_components.td, {
            children: "False"
          }), (0,jsx_runtime.jsx)(_components.td, {
            children: "If a compilation error happens and this option is turned on, the compilation error is suppressed and the original Haskell expression is replaced with a runtime-error expression."
          })]
        }), (0,jsx_runtime.jsxs)(_components.tr, {
          children: [(0,jsx_runtime.jsx)(_components.td, {
            children: (0,jsx_runtime.jsx)(_components.code, {
              children: "dump-compilation-trace"
            })
          }), (0,jsx_runtime.jsx)(_components.td, {
            children: "Bool"
          }), (0,jsx_runtime.jsx)(_components.td, {
            children: "False"
          }), (0,jsx_runtime.jsx)(_components.td, {
            children: "Dump compilation trace for debugging"
          })]
        }), (0,jsx_runtime.jsxs)(_components.tr, {
          children: [(0,jsx_runtime.jsx)(_components.td, {
            children: (0,jsx_runtime.jsx)(_components.code, {
              children: "dump-pir"
            })
          }), (0,jsx_runtime.jsx)(_components.td, {
            children: "Bool"
          }), (0,jsx_runtime.jsx)(_components.td, {
            children: "False"
          }), (0,jsx_runtime.jsx)(_components.td, {
            children: "Dump Plutus IR"
          })]
        }), (0,jsx_runtime.jsxs)(_components.tr, {
          children: [(0,jsx_runtime.jsx)(_components.td, {
            children: (0,jsx_runtime.jsx)(_components.code, {
              children: "dump-tplc"
            })
          }), (0,jsx_runtime.jsx)(_components.td, {
            children: "Bool"
          }), (0,jsx_runtime.jsx)(_components.td, {
            children: "False"
          }), (0,jsx_runtime.jsx)(_components.td, {
            children: "Dump Typed Plutus Core"
          })]
        }), (0,jsx_runtime.jsxs)(_components.tr, {
          children: [(0,jsx_runtime.jsx)(_components.td, {
            children: (0,jsx_runtime.jsx)(_components.code, {
              children: "dump-uplc"
            })
          }), (0,jsx_runtime.jsx)(_components.td, {
            children: "Bool"
          }), (0,jsx_runtime.jsx)(_components.td, {
            children: "False"
          }), (0,jsx_runtime.jsx)(_components.td, {
            children: "Dump Untyped Plutus Core"
          })]
        }), (0,jsx_runtime.jsxs)(_components.tr, {
          children: [(0,jsx_runtime.jsx)(_components.td, {
            children: (0,jsx_runtime.jsx)(_components.code, {
              children: "inline-callsite-growth"
            })
          }), (0,jsx_runtime.jsx)(_components.td, {
            children: "Int"
          }), (0,jsx_runtime.jsx)(_components.td, {
            children: "5"
          }), (0,jsx_runtime.jsxs)(_components.td, {
            children: ["Sets the inlining threshold for callsites. 0 disables inlining a binding at a callsite if it increases the AST size; ", (0,jsx_runtime.jsx)(_components.code, {
              children: "n"
            }), " allows inlining if the AST size grows by no more than ", (0,jsx_runtime.jsx)(_components.code, {
              children: "n"
            }), ". Keep in mind that doing so does not mean the final program will be bigger, since inlining can often unlock further optimizations."]
          })]
        }), (0,jsx_runtime.jsxs)(_components.tr, {
          children: [(0,jsx_runtime.jsx)(_components.td, {
            children: (0,jsx_runtime.jsx)(_components.code, {
              children: "inline-constants"
            })
          }), (0,jsx_runtime.jsx)(_components.td, {
            children: "Bool"
          }), (0,jsx_runtime.jsx)(_components.td, {
            children: "True"
          }), (0,jsx_runtime.jsxs)(_components.td, {
            children: ["Always inline constants. Inlining constants always reduces script costs slightly, but may increase script sizes if a large constant is used more than once. Implied by ", (0,jsx_runtime.jsx)(_components.code, {
              children: "no-conservative-optimisation"
            }), "."]
          })]
        }), (0,jsx_runtime.jsxs)(_components.tr, {
          children: [(0,jsx_runtime.jsx)(_components.td, {
            children: (0,jsx_runtime.jsx)(_components.code, {
              children: "inline-fix"
            })
          }), (0,jsx_runtime.jsx)(_components.td, {
            children: "Bool"
          }), (0,jsx_runtime.jsx)(_components.td, {
            children: "True"
          }), (0,jsx_runtime.jsx)(_components.td, {
            children: "Always inline fixed point combinators. This is generally preferable as it often enables further optimization, though it may increase script size."
          })]
        }), (0,jsx_runtime.jsxs)(_components.tr, {
          children: [(0,jsx_runtime.jsx)(_components.td, {
            children: (0,jsx_runtime.jsx)(_components.code, {
              children: "max-cse-iterations"
            })
          }), (0,jsx_runtime.jsx)(_components.td, {
            children: "Int"
          }), (0,jsx_runtime.jsx)(_components.td, {
            children: "4"
          }), (0,jsx_runtime.jsx)(_components.td, {
            children: "Set the max iterations for CSE"
          })]
        }), (0,jsx_runtime.jsxs)(_components.tr, {
          children: [(0,jsx_runtime.jsx)(_components.td, {
            children: (0,jsx_runtime.jsx)(_components.code, {
              children: "cse-which-subterms"
            })
          }), (0,jsx_runtime.jsx)(_components.td, {
            children: "CseWhichSubterms"
          }), (0,jsx_runtime.jsx)(_components.td, {
            children: "ExcludeWorkFree"
          }), (0,jsx_runtime.jsxs)(_components.td, {
            children: ["Which subterms should CSE consider? Either ", (0,jsx_runtime.jsx)(_components.code, {
              children: "AllSubterms"
            }), " or ", (0,jsx_runtime.jsx)(_components.code, {
              children: "ExcludeWorkFree"
            })]
          })]
        }), (0,jsx_runtime.jsxs)(_components.tr, {
          children: [(0,jsx_runtime.jsx)(_components.td, {
            children: (0,jsx_runtime.jsx)(_components.code, {
              children: "max-simplifier-iterations-pir"
            })
          }), (0,jsx_runtime.jsx)(_components.td, {
            children: "Int"
          }), (0,jsx_runtime.jsx)(_components.td, {
            children: "12"
          }), (0,jsx_runtime.jsx)(_components.td, {
            children: "Set the max iterations for the PIR simplifier"
          })]
        }), (0,jsx_runtime.jsxs)(_components.tr, {
          children: [(0,jsx_runtime.jsx)(_components.td, {
            children: (0,jsx_runtime.jsx)(_components.code, {
              children: "max-simplifier-iterations-uplc"
            })
          }), (0,jsx_runtime.jsx)(_components.td, {
            children: "Int"
          }), (0,jsx_runtime.jsx)(_components.td, {
            children: "12"
          }), (0,jsx_runtime.jsx)(_components.td, {
            children: "Set the max iterations for the UPLC simplifier"
          })]
        }), (0,jsx_runtime.jsxs)(_components.tr, {
          children: [(0,jsx_runtime.jsx)(_components.td, {
            children: (0,jsx_runtime.jsx)(_components.code, {
              children: "optimize"
            })
          }), (0,jsx_runtime.jsx)(_components.td, {
            children: "Bool"
          }), (0,jsx_runtime.jsx)(_components.td, {
            children: "True"
          }), (0,jsx_runtime.jsx)(_components.td, {
            children: "Run optimization passes such as simplification and floating let-bindings."
          })]
        }), (0,jsx_runtime.jsxs)(_components.tr, {
          children: [(0,jsx_runtime.jsx)(_components.td, {
            children: (0,jsx_runtime.jsx)(_components.code, {
              children: "pedantic"
            })
          }), (0,jsx_runtime.jsx)(_components.td, {
            children: "Bool"
          }), (0,jsx_runtime.jsx)(_components.td, {
            children: "False"
          }), (0,jsx_runtime.jsx)(_components.td, {
            children: "Run type checker after each compilation pass"
          })]
        }), (0,jsx_runtime.jsxs)(_components.tr, {
          children: [(0,jsx_runtime.jsx)(_components.td, {
            children: (0,jsx_runtime.jsx)(_components.code, {
              children: "preserve-logging"
            })
          }), (0,jsx_runtime.jsx)(_components.td, {
            children: "Bool"
          }), (0,jsx_runtime.jsx)(_components.td, {
            children: "True"
          }), (0,jsx_runtime.jsxs)(_components.td, {
            children: ["Turn off optimisations that may alter (i.e., add, remove or change the order of) trace messages. Implied by ", (0,jsx_runtime.jsx)(_components.code, {
              children: "conservative-optimisation"
            }), "."]
          })]
        }), (0,jsx_runtime.jsxs)(_components.tr, {
          children: [(0,jsx_runtime.jsx)(_components.td, {
            children: (0,jsx_runtime.jsx)(_components.code, {
              children: "profile-all"
            })
          }), (0,jsx_runtime.jsx)(_components.td, {
            children: "ProfileOpts"
          }), (0,jsx_runtime.jsx)(_components.td, {
            children: "None"
          }), (0,jsx_runtime.jsx)(_components.td, {
            children: "Set profiling options to All, which adds tracing when entering and exiting a term."
          })]
        }), (0,jsx_runtime.jsxs)(_components.tr, {
          children: [(0,jsx_runtime.jsx)(_components.td, {
            children: (0,jsx_runtime.jsx)(_components.code, {
              children: "relaxed-float-in"
            })
          }), (0,jsx_runtime.jsx)(_components.td, {
            children: "Bool"
          }), (0,jsx_runtime.jsx)(_components.td, {
            children: "True"
          }), (0,jsx_runtime.jsxs)(_components.td, {
            children: ["Use a more aggressive float-in pass, which often leads to reduced costs but may occasionally lead to slightly increased costs. Implied by ", (0,jsx_runtime.jsx)(_components.code, {
              children: "no-conservative-optimisation"
            }), "."]
          })]
        }), (0,jsx_runtime.jsxs)(_components.tr, {
          children: [(0,jsx_runtime.jsx)(_components.td, {
            children: (0,jsx_runtime.jsx)(_components.code, {
              children: "remove-trace"
            })
          }), (0,jsx_runtime.jsx)(_components.td, {
            children: "Bool"
          }), (0,jsx_runtime.jsx)(_components.td, {
            children: "False"
          }), (0,jsx_runtime.jsxs)(_components.td, {
            children: ["Eliminate calls to ", (0,jsx_runtime.jsx)(_components.code, {
              children: "trace"
            }), " from Plutus Core"]
          })]
        }), (0,jsx_runtime.jsxs)(_components.tr, {
          children: [(0,jsx_runtime.jsx)(_components.td, {
            children: (0,jsx_runtime.jsx)(_components.code, {
              children: "simplifier-beta"
            })
          }), (0,jsx_runtime.jsx)(_components.td, {
            children: "Bool"
          }), (0,jsx_runtime.jsx)(_components.td, {
            children: "True"
          }), (0,jsx_runtime.jsx)(_components.td, {
            children: "Run a simplification pass that performs beta transformations"
          })]
        }), (0,jsx_runtime.jsxs)(_components.tr, {
          children: [(0,jsx_runtime.jsx)(_components.td, {
            children: (0,jsx_runtime.jsx)(_components.code, {
              children: "simplifier-evaluate-builtins"
            })
          }), (0,jsx_runtime.jsx)(_components.td, {
            children: "Bool"
          }), (0,jsx_runtime.jsx)(_components.td, {
            children: "True"
          }), (0,jsx_runtime.jsxs)(_components.td, {
            children: ["Run a simplification pass that evaluates fully saturated builtin applications. Implied by ", (0,jsx_runtime.jsx)(_components.code, {
              children: "no-conservative-optimisation"
            }), "."]
          })]
        }), (0,jsx_runtime.jsxs)(_components.tr, {
          children: [(0,jsx_runtime.jsx)(_components.td, {
            children: (0,jsx_runtime.jsx)(_components.code, {
              children: "simplifier-inline"
            })
          }), (0,jsx_runtime.jsx)(_components.td, {
            children: "Bool"
          }), (0,jsx_runtime.jsx)(_components.td, {
            children: "True"
          }), (0,jsx_runtime.jsx)(_components.td, {
            children: "Run a simplification pass that performs inlining"
          })]
        }), (0,jsx_runtime.jsxs)(_components.tr, {
          children: [(0,jsx_runtime.jsx)(_components.td, {
            children: (0,jsx_runtime.jsx)(_components.code, {
              children: "simplifier-remove-dead-bindings"
            })
          }), (0,jsx_runtime.jsx)(_components.td, {
            children: "Bool"
          }), (0,jsx_runtime.jsx)(_components.td, {
            children: "True"
          }), (0,jsx_runtime.jsx)(_components.td, {
            children: "Run a simplification pass that removes dead bindings"
          })]
        }), (0,jsx_runtime.jsxs)(_components.tr, {
          children: [(0,jsx_runtime.jsx)(_components.td, {
            children: (0,jsx_runtime.jsx)(_components.code, {
              children: "simplifier-unwrap-cancel"
            })
          }), (0,jsx_runtime.jsx)(_components.td, {
            children: "Bool"
          }), (0,jsx_runtime.jsx)(_components.td, {
            children: "True"
          }), (0,jsx_runtime.jsx)(_components.td, {
            children: "Run a simplification pass that cancels unwrap/wrap pairs"
          })]
        }), (0,jsx_runtime.jsxs)(_components.tr, {
          children: [(0,jsx_runtime.jsx)(_components.td, {
            children: (0,jsx_runtime.jsx)(_components.code, {
              children: "strictify-bindings"
            })
          }), (0,jsx_runtime.jsx)(_components.td, {
            children: "Bool"
          }), (0,jsx_runtime.jsx)(_components.td, {
            children: "True"
          }), (0,jsx_runtime.jsx)(_components.td, {
            children: "Run a simplification pass that makes bindings stricter"
          })]
        }), (0,jsx_runtime.jsxs)(_components.tr, {
          children: [(0,jsx_runtime.jsx)(_components.td, {
            children: (0,jsx_runtime.jsx)(_components.code, {
              children: "target-version"
            })
          }), (0,jsx_runtime.jsx)(_components.td, {
            children: "Version"
          }), (0,jsx_runtime.jsx)(_components.td, {
            children: "1.1.0"
          }), (0,jsx_runtime.jsx)(_components.td, {
            children: "The target Plutus Core language version"
          })]
        }), (0,jsx_runtime.jsxs)(_components.tr, {
          children: [(0,jsx_runtime.jsx)(_components.td, {
            children: (0,jsx_runtime.jsx)(_components.code, {
              children: "typecheck"
            })
          }), (0,jsx_runtime.jsx)(_components.td, {
            children: "Bool"
          }), (0,jsx_runtime.jsx)(_components.td, {
            children: "True"
          }), (0,jsx_runtime.jsx)(_components.td, {
            children: "Perform type checking during compilation."
          })]
        }), (0,jsx_runtime.jsxs)(_components.tr, {
          children: [(0,jsx_runtime.jsx)(_components.td, {
            children: (0,jsx_runtime.jsx)(_components.code, {
              children: "verbosity"
            })
          }), (0,jsx_runtime.jsx)(_components.td, {
            children: "Verbosity"
          }), (0,jsx_runtime.jsx)(_components.td, {
            children: "Quiet"
          }), (0,jsx_runtime.jsx)(_components.td, {
            children: "Set logging verbosity level (0=Quiet, 1=Verbose, 2=Debug)"
          })]
        })]
      })]
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