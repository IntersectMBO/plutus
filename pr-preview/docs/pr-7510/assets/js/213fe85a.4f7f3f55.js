"use strict";
(self["webpackChunkdocusaurus"] = self["webpackChunkdocusaurus"] || []).push([[9130],{

/***/ 156:
/***/ ((__unused_webpack_module, __webpack_exports__, __webpack_require__) => {

// ESM COMPAT FLAG
__webpack_require__.r(__webpack_exports__);

// EXPORTS
__webpack_require__.d(__webpack_exports__, {
  assets: () => (/* binding */ assets),
  contentTitle: () => (/* binding */ contentTitle),
  "default": () => (/* binding */ MDXContent),
  frontMatter: () => (/* binding */ frontMatter),
  metadata: () => (/* reexport */ site_docs_using_plinth_evaluating_plinth_md_213_namespaceObject),
  toc: () => (/* binding */ toc)
});

;// ./.docusaurus/docusaurus-plugin-content-docs/default/site-docs-using-plinth-evaluating-plinth-md-213.json
const site_docs_using_plinth_evaluating_plinth_md_213_namespaceObject = /*#__PURE__*/JSON.parse('{"id":"using-plinth/evaluating-plinth","title":"Evaluating CompiledCode","description":"CompiledCode is intended to be evaluated by Cardano nodes during transaction validation. For this purpose, it is serialized and included in a transaction.","source":"@site/docs/using-plinth/evaluating-plinth.md","sourceDirName":"using-plinth","slug":"/using-plinth/evaluating-plinth","permalink":"/pr-preview/docs/pr-7510/using-plinth/evaluating-plinth","draft":false,"unlisted":false,"editUrl":"https://github.com/IntersectMBO/plutus/edit/master/doc/docusaurus/docs/using-plinth/evaluating-plinth.md","tags":[],"version":"current","sidebarPosition":12,"frontMatter":{"sidebar_position":12},"sidebar":"tutorialSidebar","previous":{"title":"Lifting Values into CompiledCode","permalink":"/pr-preview/docs/pr-7510/using-plinth/lifting"},"next":{"title":"Differences From Haskell","permalink":"/pr-preview/docs/pr-7510/using-plinth/differences-from-haskell"}}');
// EXTERNAL MODULE: ./node_modules/react/jsx-runtime.js
var jsx_runtime = __webpack_require__(4848);
// EXTERNAL MODULE: ./node_modules/@mdx-js/react/lib/index.js
var lib = __webpack_require__(8453);
;// ./docs/using-plinth/evaluating-plinth.md


const frontMatter = {
	sidebar_position: 12
};
const contentTitle = 'Evaluating CompiledCode';

const assets = {

};



const toc = [];
function _createMdxContent(props) {
  const _components = {
    a: "a",
    admonition: "admonition",
    code: "code",
    h1: "h1",
    header: "header",
    li: "li",
    ol: "ol",
    p: "p",
    pre: "pre",
    ...(0,lib/* useMDXComponents */.R)(),
    ...props.components
  }, {Details, LiteralInclude} = _components;
  if (!Details) _missingMdxReference("Details", true);
  if (!LiteralInclude) _missingMdxReference("LiteralInclude", true);
  return (0,jsx_runtime.jsxs)(jsx_runtime.Fragment, {
    children: [(0,jsx_runtime.jsx)(_components.header, {
      children: (0,jsx_runtime.jsx)(_components.h1, {
        id: "evaluating-compiledcode",
        children: "Evaluating CompiledCode"
      })
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: [(0,jsx_runtime.jsx)(_components.code, {
        children: "CompiledCode"
      }), " is intended to be evaluated by Cardano nodes during transaction validation. For this purpose, it is serialized and included in a transaction."]
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["However, it is also possible to evaluate ", (0,jsx_runtime.jsx)(_components.code, {
        children: "CompiledCode"
      }), " without running a node. The Plutus evaluator, called the CEK Machine, can be used independently of the Cardano node for testing and troubleshooting. By evaluating Plinth programs locally, developers can not only obtain the immediate result of the code but also access the traces emitted during evaluation and the consumed execution budget."]
    }), "\n", (0,jsx_runtime.jsx)(_components.admonition, {
      title: "Version Information",
      type: "info",
      children: (0,jsx_runtime.jsx)(_components.p, {
        children: "This functionality was released in version 1.47."
      })
    }), "\n", (0,jsx_runtime.jsx)(_components.p, {
      children: "Let's consider the following example Plinth program:"
    }), "\n", (0,jsx_runtime.jsx)(LiteralInclude, {
      file: "Example/Evaluation/Main.hs",
      language: "haskell",
      title: "Example Plinth code",
      start: "-- BEGIN Plinth",
      end: "-- END Plinth"
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["This code defines a function that expects an ", (0,jsx_runtime.jsx)(_components.code, {
        children: "Integer"
      }), " argument and returns an ", (0,jsx_runtime.jsx)(_components.code, {
        children: "Integer"
      }), " value."]
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["To compile it, use the ", (0,jsx_runtime.jsx)(_components.code, {
        children: "compile"
      }), " function as described earlier in the ", (0,jsx_runtime.jsx)(_components.a, {
        href: "/pr-preview/docs/pr-7510/using-plinth/compiling-plinth",
        children: "Compiling Plinth code"
      }), " section:"]
    }), "\n", (0,jsx_runtime.jsx)(LiteralInclude, {
      file: "Example/Evaluation/Main.hs",
      language: "haskell",
      title: "Plinth code compiled",
      start: "-- BEGIN CompiledCode",
      end: "-- END CompiledCode"
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["To evaluate ", (0,jsx_runtime.jsx)(_components.code, {
        children: "compiledCode"
      }), ", add the following dependencies to your cabal file:"]
    }), "\n", (0,jsx_runtime.jsx)(_components.pre, {
      children: (0,jsx_runtime.jsx)(_components.code, {
        className: "language-cabal",
        children: "build-depends: \n  plutus-tx, \n  plutus-tx:plutus-tx-testlib, \n  plutus-ledger-api \n"
      })
    }), "\n", (0,jsx_runtime.jsx)(_components.p, {
      children: "This allows you to import the necessary functionality:"
    }), "\n", (0,jsx_runtime.jsx)(LiteralInclude, {
      file: "Example/Evaluation/Main.hs",
      language: "haskell",
      title: "Required imports",
      start: "-- BEGIN Imports",
      end: "-- END Imports"
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["You can evaluate this compiled code without applying it to any arguments. The evaluation will succeed, returning a value of type ", (0,jsx_runtime.jsx)(_components.code, {
        children: "Integer -> Integer"
      }), ":"]
    }), "\n", (0,jsx_runtime.jsx)(_components.pre, {
      children: (0,jsx_runtime.jsx)(_components.code, {
        className: "language-haskell",
        children: "result :: EvalResult\nresult = evaluateCompiledCode compiledCode\n"
      })
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["The ", (0,jsx_runtime.jsx)(_components.code, {
        children: "EvalResult"
      }), " type is declared as follows:"]
    }), "\n", (0,jsx_runtime.jsx)(_components.pre, {
      children: (0,jsx_runtime.jsx)(_components.code, {
        className: "language-haskell",
        children: "data EvalResult = EvalResult\n  { evalResult\n      :: Either\n           (CekEvaluationException NamedDeBruijn DefaultUni DefaultFun)\n           (NTerm DefaultUni DefaultFun ())\n  , evalResultBudget :: ExBudget\n  , evalResultTraces :: [Text]\n  }\n  deriving stock (Show)\n"
      })
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["The ", (0,jsx_runtime.jsx)(_components.code, {
        children: "evalResult"
      }), " field contains the result of the evaluation, which can be either a successful result or an error."]
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["The ", (0,jsx_runtime.jsx)(_components.code, {
        children: "evalResultBudget"
      }), " field contains the execution budget used during evaluation, including CPU and memory usage."]
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["The ", (0,jsx_runtime.jsx)(_components.code, {
        children: "evalResultTraces"
      }), " field contains any traces emitted during evaluation."]
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["The ", (0,jsx_runtime.jsx)(_components.code, {
        children: "evaluateCompiledCode"
      }), " function is the main workhorse of the evaluation process. Under the hood, it uses the Plutus Core evaluator (CEK machine) configured with the latest cost model stored statically in the Plutus repository."]
    }), "\n", (0,jsx_runtime.jsx)(_components.admonition, {
      title: "Caveat",
      type: "caution",
      children: (0,jsx_runtime.jsxs)(_components.p, {
        children: ["The execution budget reported by ", (0,jsx_runtime.jsx)(_components.code, {
          children: "evaluateCompiledCode"
        }), " is not guaranteed to exactly match the execution budget spent by Cardano mainnet nodes. This discrepancy arises because the cost model used by ", (0,jsx_runtime.jsx)(_components.code, {
          children: "evaluateCompiledCode"
        }), " may differ from the cost model active on the Cardano chain at a specific moment. The definitive values for on-chain cost calculations are protocol parameters, which are part of the chain's state. In practice, these parameters are typically derived from the cost model stored in the Plutus repository at some earlier point, though this is not guaranteed. During on-chain evaluation, the ledger provides a cost model to the Plutus Core evaluator."]
      })
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["The companion function ", (0,jsx_runtime.jsx)(_components.code, {
        children: "evaluateCompiledCode'"
      }), " is a more general version of ", (0,jsx_runtime.jsx)(_components.code, {
        children: "evaluateCompiledCode"
      }), ", allowing you to specify the cost model via the ", (0,jsx_runtime.jsx)(_components.code, {
        children: "MachineParameters"
      }), " type. This function is useful for testing, but in most cases, you can use ", (0,jsx_runtime.jsx)(_components.code, {
        children: "evaluateCompiledCode"
      }), " without worrying about these details."]
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["To use it, supply a ", (0,jsx_runtime.jsx)(_components.code, {
        children: "MachineParameters"
      }), " value like this:"]
    }), "\n", (0,jsx_runtime.jsx)(LiteralInclude, {
      file: "Example/Evaluation/Main.hs",
      language: "haskell",
      title: "Evaluating with custom MachineParameters",
      start: "-- BEGIN MachineParameters",
      end: "-- END MachineParameters"
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["You can use the ", (0,jsx_runtime.jsx)(_components.code, {
        children: "Show"
      }), " instance of ", (0,jsx_runtime.jsx)(_components.code, {
        children: "EvalResult"
      }), " to print the result of the evaluation:"]
    }), "\n", (0,jsx_runtime.jsxs)(Details, {
      children: [(0,jsx_runtime.jsxs)("summary", {
        children: ["Show raw ", (0,jsx_runtime.jsx)("code", {
          children: "EvalResult"
        }), " output"]
      }), (0,jsx_runtime.jsx)(_components.pre, {
        children: (0,jsx_runtime.jsx)(_components.code, {
          className: "language-haskell",
          children: "EvalResult\n  { evalResult =\n      Right\n        ( LamAbs\n            ()\n            (NamedDeBruijn{ndbnString = \"x\", ndbnIndex = 0})\n            ( Apply\n                ()\n                ( Apply\n                    ()\n                    (Builtin () AddInteger)\n                    ( Apply\n                        ()\n                        ( Apply\n                            ()\n                            ( Force\n                                ()\n                                (Builtin () Trace)\n                            )\n                            ( Constant\n                                ()\n                                (Some (ValueOf DefaultUniString \"Evaluating x\"))\n                            )\n                        )\n                        (Var () (NamedDeBruijn{ndbnString = \"x\", ndbnIndex = 1}))\n                    )\n                )\n                ( Apply\n                    ()\n                    ( Apply\n                        ()\n                        (Force () (Builtin () Trace))\n                        (Constant () (Some (ValueOf DefaultUniString \"Evaluating constant\")))\n                    )\n                    (Constant () (Some (ValueOf DefaultUniInteger 2)))\n                )\n            )\n        )\n  , evalResultBudget =\n      ExBudget\n        { exBudgetCPU = ExCPU 16100\n        , exBudgetMemory = ExMemory 200\n        }\n  , evalResultTraces = []\n  }\n"
        })
      })]
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["However, there is a dedicated function, ", (0,jsx_runtime.jsx)(_components.code, {
        children: "displayEvalResult"
      }), ", that prints the result in a more concise and human-readable format:"]
    }), "\n", (0,jsx_runtime.jsx)(_components.pre, {
      children: (0,jsx_runtime.jsx)(_components.code, {
        children: "Evaluation was SUCCESSFUL, result is:\n  \\x ->\n    addInteger\n      (force trace \"Evaluating x\" x)\n      (force trace \"Evaluating constant\" 2)\n\nExecution budget spent:\n  CPU 16,100\n  MEM 200\n\nNo traces were emitted\n"
      })
    }), "\n", (0,jsx_runtime.jsx)(_components.p, {
      children: "This output shows that the evaluation was successful, and the resulting UPLC value is an (unapplied) lambda abstraction."
    }), "\n", (0,jsx_runtime.jsx)(_components.p, {
      children: "To apply the compiled lambda abstraction to an argument, you need a compiled argument. There are several ways to obtain it from a Haskell value known at compile time:"
    }), "\n", (0,jsx_runtime.jsxs)(_components.ol, {
      children: ["\n", (0,jsx_runtime.jsxs)(_components.li, {
        children: ["\n", (0,jsx_runtime.jsxs)(_components.p, {
          children: ["\"Lift\" it into ", (0,jsx_runtime.jsx)(_components.code, {
            children: "CompiledCode"
          }), ". See the ", (0,jsx_runtime.jsx)(_components.a, {
            href: "/pr-preview/docs/pr-7510/using-plinth/lifting",
            children: "Lifting Values into CompiledCode"
          }), " section for more details."]
        }), "\n", (0,jsx_runtime.jsx)(LiteralInclude, {
          file: "Example/Evaluation/Main.hs",
          language: "haskell",
          title: "Lift a constant value into CompiledCode",
          start: "-- BEGIN LiftedArgument",
          end: "-- END LiftedArgument"
        }), "\n"]
      }), "\n", (0,jsx_runtime.jsxs)(_components.li, {
        children: ["\n", (0,jsx_runtime.jsxs)(_components.p, {
          children: ["Use ", (0,jsx_runtime.jsx)(_components.code, {
            children: "$(compile [|| ... ||])"
          }), " in the same way as when compiling the function itself."]
        }), "\n", (0,jsx_runtime.jsx)(LiteralInclude, {
          file: "Example/Evaluation/Main.hs",
          language: "haskell",
          title: "Compile a constant value into CompiledCode",
          start: "-- BEGIN CompiledArgument",
          end: "-- END CompiledArgument"
        }), "\n"]
      }), "\n"]
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["Once you have an argument of type ", (0,jsx_runtime.jsx)(_components.code, {
        children: "CompiledCode a"
      }), ", you can apply it to the compiled function using either the ", (0,jsx_runtime.jsx)(_components.a, {
        href: "https://plutus.cardano.intersectmbo.org/haddock/latest/plutus-tx/PlutusTx-Code.html#v:applyCode",
        children: (0,jsx_runtime.jsx)(_components.code, {
          children: "applyCode"
        })
      }), " function"]
    }), "\n", (0,jsx_runtime.jsx)(LiteralInclude, {
      file: "Example/Evaluation/Main.hs",
      language: "haskell",
      title: "Applying compiled function to an argument (type-safe way)",
      start: "-- BEGIN SafeApplicationResult",
      end: "-- END SafeApplicationResult"
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["or the ", (0,jsx_runtime.jsx)(_components.a, {
        href: "https://plutus.cardano.intersectmbo.org/haddock/latest/plutus-tx/PlutusTx-Code.html#v:unsafeApplyCode",
        children: (0,jsx_runtime.jsx)(_components.code, {
          children: "unsafeApplyCode"
        })
      }), " function."]
    }), "\n", (0,jsx_runtime.jsx)(LiteralInclude, {
      file: "Example/Evaluation/Main.hs",
      language: "haskell",
      title: "Applying compiled function to an argument (unsafe way)",
      start: "-- BEGIN UnsafeApplicationResult",
      end: "-- END UnsafeApplicationResult"
    }), "\n", (0,jsx_runtime.jsx)(_components.p, {
      children: "Let's print the result of the evaluation:"
    }), "\n", (0,jsx_runtime.jsx)(LiteralInclude, {
      file: "Example/Evaluation/Main.hs",
      language: "haskell",
      title: "Pretty-printng the result",
      start: "-- BEGIN PrintResult",
      end: "-- END PrintResult"
    }), "\n", (0,jsx_runtime.jsx)(_components.pre, {
      children: (0,jsx_runtime.jsx)(_components.code, {
        children: "Simulating latest Plutus Ledger Language and\nthe latest Protocol Version evaluation:\n--------------------------------------------\nEvaluation was SUCCESSFUL, result is:\n  4\n\nExecution budget spent:\n  CPU 508,304\n  MEM 1,966\n"
      })
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["Nice! Now we can see that calculating ", (0,jsx_runtime.jsx)(_components.code, {
        children: "2 + 2 = 4"
      }), " using the CEK Machine (UPLC interpreter) requires 508,304 CPU and 1,966 MEM units."]
    }), "\n", (0,jsx_runtime.jsx)(_components.p, {
      children: "For completeness, here is an example of a failed evaluation:"
    }), "\n", (0,jsx_runtime.jsx)(_components.pre, {
      children: (0,jsx_runtime.jsx)(_components.code, {
        children: "Evaluation FAILED:\n  An error has occurred:\n  The machine terminated because of an error,  \n  either from a built-in function or from an explicit use of 'error'.\n\nExecution budget spent:\n  CPU 220,304\n  MEM 166\n\nEvaluation traces:\n  1. Evaluating x\n  2. Evaluating constant\n"
      })
    }), "\n", (0,jsx_runtime.jsx)(_components.p, {
      children: "Both example outputs include execution traces emitted during evaluation. These can be helpful when debugging your Plinth code."
    }), "\n", (0,jsx_runtime.jsx)(_components.p, {
      children: "Caveat: traces add to the script size, so make sure to remove them when you are done debugging."
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["You can find the complete example code in ", (0,jsx_runtime.jsx)(_components.a, {
        target: "_blank",
        "data-noBrokenLinkCheck": true,
        href: (__webpack_require__(4602)/* ["default"] */ .A) + "",
        children: (0,jsx_runtime.jsx)(_components.code, {
          children: "Example/Evaluation/Main.hs"
        })
      }), " in the Plutus repository."]
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
function _missingMdxReference(id, component) {
  throw new Error("Expected " + (component ? "component" : "object") + " `" + id + "` to be defined: you likely forgot to import, pass, or provide it.");
}



/***/ }),

/***/ 4602:
/***/ ((__unused_webpack_module, __webpack_exports__, __webpack_require__) => {

/* harmony export */ __webpack_require__.d(__webpack_exports__, {
/* harmony export */   A: () => (__WEBPACK_DEFAULT_EXPORT__)
/* harmony export */ });
/* harmony default export */ const __WEBPACK_DEFAULT_EXPORT__ = (__webpack_require__.p + "assets/files/Main-ee5a1d56b41be0f39d9842a827e7f5ed.hs");

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