"use strict";
(self["webpackChunkdocusaurus"] = self["webpackChunkdocusaurus"] || []).push([[6286],{

/***/ 7346:
/***/ ((__unused_webpack_module, __webpack_exports__, __webpack_require__) => {

// ESM COMPAT FLAG
__webpack_require__.r(__webpack_exports__);

// EXPORTS
__webpack_require__.d(__webpack_exports__, {
  assets: () => (/* binding */ assets),
  contentTitle: () => (/* binding */ contentTitle),
  "default": () => (/* binding */ MDXContent),
  frontMatter: () => (/* binding */ frontMatter),
  metadata: () => (/* reexport */ site_docs_working_with_scripts_other_optimization_techniques_md_c33_namespaceObject),
  toc: () => (/* binding */ toc)
});

;// ./.docusaurus/docusaurus-plugin-content-docs/default/site-docs-working-with-scripts-other-optimization-techniques-md-c33.json
const site_docs_working_with_scripts_other_optimization_techniques_md_c33_namespaceObject = /*#__PURE__*/JSON.parse('{"id":"working-with-scripts/other-optimization-techniques","title":"Other Optimization Techniques","description":"Identifying problem areas","source":"@site/docs/working-with-scripts/other-optimization-techniques.md","sourceDirName":"working-with-scripts","slug":"/working-with-scripts/other-optimization-techniques","permalink":"/pr-preview/docs/pr-7544/working-with-scripts/other-optimization-techniques","draft":false,"unlisted":false,"editUrl":"https://github.com/IntersectMBO/plutus/edit/master/doc/docusaurus/docs/working-with-scripts/other-optimization-techniques.md","tags":[],"version":"current","sidebarPosition":25,"frontMatter":{"sidebar_position":25},"sidebar":"tutorialSidebar","previous":{"title":"Compile Time Evaluation","permalink":"/pr-preview/docs/pr-7544/working-with-scripts/compile-time-evaluation"},"next":{"title":"Profiling Script Budget Usage","permalink":"/pr-preview/docs/pr-7544/working-with-scripts/profiling-budget-usage"}}');
// EXTERNAL MODULE: ./node_modules/react/jsx-runtime.js
var jsx_runtime = __webpack_require__(4848);
// EXTERNAL MODULE: ./node_modules/@mdx-js/react/lib/index.js
var lib = __webpack_require__(8453);
;// ./docs/working-with-scripts/other-optimization-techniques.md


const frontMatter = {
	sidebar_position: 25
};
const contentTitle = 'Other Optimization Techniques';

const assets = {

};



const toc = [{
  "value": "Identifying problem areas",
  "id": "identifying-problem-areas",
  "level": 2
}, {
  "value": "Using a Recent Version of the Plinth Compiler",
  "id": "using-a-recent-version-of-the-plinth-compiler",
  "level": 2
}, {
  "value": "Try <code>conservative-optimisation</code> or Flags Implied by It",
  "id": "try-conservative-optimisation-or-flags-implied-by-it",
  "level": 2
}, {
  "value": "Using the <code>Strict</code> Extension",
  "id": "using-the-strict-extension",
  "level": 2
}, {
  "value": "Avoiding the <code>INLINE</code> Pragma",
  "id": "avoiding-the-inline-pragma",
  "level": 2
}, {
  "value": "Be Mindful of Strict Applications",
  "id": "be-mindful-of-strict-applications",
  "level": 2
}, {
  "value": "Avoiding Intermediate Results",
  "id": "avoiding-intermediate-results",
  "level": 2
}, {
  "value": "Specializing higher-order functions",
  "id": "specializing-higher-order-functions",
  "level": 2
}, {
  "value": "Removing Traces",
  "id": "removing-traces",
  "level": 2
}, {
  "value": "Using <code>BuiltinArray</code> for index-based lookups",
  "id": "using-builtinarray-for-index-based-lookups",
  "level": 2
}, {
  "value": "Using <code>error</code> for faster failure",
  "id": "using-error-for-faster-failure",
  "level": 2
}];
function _createMdxContent(props) {
  const _components = {
    a: "a",
    code: "code",
    em: "em",
    h1: "h1",
    h2: "h2",
    header: "header",
    p: "p",
    pre: "pre",
    ...(0,lib/* useMDXComponents */.R)(),
    ...props.components
  };
  return (0,jsx_runtime.jsxs)(jsx_runtime.Fragment, {
    children: [(0,jsx_runtime.jsx)(_components.header, {
      children: (0,jsx_runtime.jsx)(_components.h1, {
        id: "other-optimization-techniques",
        children: "Other Optimization Techniques"
      })
    }), "\n", (0,jsx_runtime.jsx)(_components.h2, {
      id: "identifying-problem-areas",
      children: "Identifying problem areas"
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["Profiling your script is a good way  to identify which parts of the script are responsible for significant resource consumption.\nFor more details, see ", (0,jsx_runtime.jsx)(_components.a, {
        href: "/pr-preview/docs/pr-7544/working-with-scripts/profiling-budget-usage",
        children: "Profiling the Budget Usage of Plutus Scripts"
      }), "."]
    }), "\n", (0,jsx_runtime.jsx)(_components.h2, {
      id: "using-a-recent-version-of-the-plinth-compiler",
      children: "Using a Recent Version of the Plinth Compiler"
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["The Plinth compiler is available through the ", (0,jsx_runtime.jsx)(_components.code, {
        children: "plutus-tx-plugin"
      }), " package.\nThe Plutus team continuously improves compiler optimization, so using the latest or a recent version of ", (0,jsx_runtime.jsx)(_components.code, {
        children: "plutus-tx-plugin"
      }), " will likely result in more compact and efficient scripts."]
    }), "\n", (0,jsx_runtime.jsxs)(_components.h2, {
      id: "try-conservative-optimisation-or-flags-implied-by-it",
      children: ["Try ", (0,jsx_runtime.jsx)(_components.code, {
        children: "conservative-optimisation"
      }), " or Flags Implied by It"]
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["Certain optimizations, such as inlining constants, can occasionally have negative effects, making scripts larger or more expensive.\nIt is worth disabling them to see how it affects your script.\nYou can do this using the ", (0,jsx_runtime.jsx)(_components.code, {
        children: "conservative-optimisation"
      }), " plugin flag, which implies several other flags like ", (0,jsx_runtime.jsx)(_components.code, {
        children: "no-inline-constants"
      }), ".\nAlternatively, try turning on the flags implied by ", (0,jsx_runtime.jsx)(_components.code, {
        children: "conservative-optimisation"
      }), " individually.\nSee ", (0,jsx_runtime.jsx)(_components.a, {
        href: "/pr-preview/docs/pr-7544/delve-deeper/plinth-compiler-options",
        children: "Plinth Compiler Options"
      }), "."]
    }), "\n", (0,jsx_runtime.jsxs)(_components.h2, {
      id: "using-the-strict-extension",
      children: ["Using the ", (0,jsx_runtime.jsx)(_components.code, {
        children: "Strict"
      }), " Extension"]
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["The ", (0,jsx_runtime.jsx)(_components.code, {
        children: "Strict"
      }), " extension, which makes all bindings in a module strict, generally improves performance.\nSee ", (0,jsx_runtime.jsx)(_components.a, {
        href: "/pr-preview/docs/pr-7544/using-plinth/extensions-flags-pragmas",
        children: "GHC Extensions, Flags and Pragmas"
      }), " for an explanation.\nHowever, care should be taken to avoid triggering unnecessary evaluations.\nFor example, in"]
    }), "\n", (0,jsx_runtime.jsx)(_components.pre, {
      children: (0,jsx_runtime.jsx)(_components.code, {
        className: "language-haskell",
        children: "let a = <expr1>\n    b = <expr2>\n in a && b\n"
      })
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: [(0,jsx_runtime.jsx)(_components.code, {
        children: "b"
      }), " will always be evaluated, even when ", (0,jsx_runtime.jsx)(_components.code, {
        children: "a"
      }), " evaluates to ", (0,jsx_runtime.jsx)(_components.code, {
        children: "False"
      }), ".\nTo avoid this, you can write either ", (0,jsx_runtime.jsx)(_components.code, {
        children: "~b = <expr2>"
      }), ", or ", (0,jsx_runtime.jsx)(_components.code, {
        children: "a && <expr2>"
      }), " (recall that ", (0,jsx_runtime.jsx)(_components.code, {
        children: "&&"
      }), " and ", (0,jsx_runtime.jsx)(_components.code, {
        children: "||"
      }), " are ", (0,jsx_runtime.jsx)(_components.a, {
        href: "/pr-preview/docs/pr-7544/using-plinth/special-functions-and-types",
        children: "special"
      }), " in Plinth in that their second arguments are non-strict, unlike ordinary Plinth functions).\nHowever, keep in mind that with ", (0,jsx_runtime.jsx)(_components.code, {
        children: "~b = <expr2>"
      }), ", ", (0,jsx_runtime.jsx)(_components.code, {
        children: "<expr2>"
      }), " will be evaluated each time ", (0,jsx_runtime.jsx)(_components.code, {
        children: "b"
      }), " is referenced, since Plinth does not employ lazy evaluation, i.e., there is no memoization."]
    }), "\n", (0,jsx_runtime.jsxs)(_components.h2, {
      id: "avoiding-the-inline-pragma",
      children: ["Avoiding the ", (0,jsx_runtime.jsx)(_components.code, {
        children: "INLINE"
      }), " Pragma"]
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["The ", (0,jsx_runtime.jsx)(_components.code, {
        children: "INLINE"
      }), " pragma strongly encourages GHC to inline a function, even if it has a large body and is used multiple times.\nThis can lead to significant increase in the size of the resulting UPLC program, which is problematic since size is a much scarcer resource for Plutus scripts than for regular Haskell programs."]
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["Instead, use the ", (0,jsx_runtime.jsx)(_components.code, {
        children: "INLINEABLE"
      }), " pragma.\nThis would leave most inlining decisions to the PIR and UPLC inliners, which are tailored for Plutus scripts and make more informed inlining decisions."]
    }), "\n", (0,jsx_runtime.jsx)(_components.h2, {
      id: "be-mindful-of-strict-applications",
      children: "Be Mindful of Strict Applications"
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["In Plinth, as with all strict languages, function applications are strict (call by value), with the exception of a few special functions like ", (0,jsx_runtime.jsx)(_components.code, {
        children: "&&"
      }), " and ", (0,jsx_runtime.jsx)(_components.code, {
        children: "||"
      }), ", which are treated specially by the compiler."]
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["If you define your own version of ", (0,jsx_runtime.jsx)(_components.code, {
        children: "&&"
      }), ":"]
    }), "\n", (0,jsx_runtime.jsx)(_components.pre, {
      children: (0,jsx_runtime.jsx)(_components.code, {
        className: "language-haskell",
        children: "myAnd :: Bool -> Bool -> Bool\nmyAnd = (&&)\n"
      })
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["then it won't have the same behavior as ", (0,jsx_runtime.jsx)(_components.code, {
        children: "&&"
      }), ", as it will always evaluate both arguments, even if the first argument evaluates to ", (0,jsx_runtime.jsx)(_components.code, {
        children: "False"
      }), "."]
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["It is particularly important to recognize that builtin functions like ", (0,jsx_runtime.jsx)(_components.code, {
        children: "chooseList"
      }), " and ", (0,jsx_runtime.jsx)(_components.code, {
        children: "chooseData"
      }), " are ", (0,jsx_runtime.jsx)(_components.em, {
        children: "not"
      }), " special, i.e., they are also strict in all arguments.\nThus the following example, which directly invokes the ", (0,jsx_runtime.jsx)(_components.code, {
        children: "chooseList"
      }), " builtin, can be inefficient:"]
    }), "\n", (0,jsx_runtime.jsx)(_components.pre, {
      children: (0,jsx_runtime.jsx)(_components.code, {
        className: "language-haskell",
        children: "res = PlutusTx.Builtins.Internal.chooseList xs nilCase consCase\n"
      })
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["It may even be semantically incorrect, if ", (0,jsx_runtime.jsx)(_components.code, {
        children: "nilCase = traceError \"empty list\""
      }), ", since it would always evaluate to an error."]
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["Instead, use the wrapper provided by ", (0,jsx_runtime.jsx)(_components.code, {
        children: "PlutusTx.Builtins"
      }), ", which suspends the evaluation of ", (0,jsx_runtime.jsx)(_components.code, {
        children: "nilCase"
      }), " with a lambda:"]
    }), "\n", (0,jsx_runtime.jsx)(_components.pre, {
      children: (0,jsx_runtime.jsx)(_components.code, {
        className: "language-haskell",
        children: "res = PlutusTx.Builtins.matchList (\\_ -> nilCase) consCase\n"
      })
    }), "\n", (0,jsx_runtime.jsx)(_components.h2, {
      id: "avoiding-intermediate-results",
      children: "Avoiding Intermediate Results"
    }), "\n", (0,jsx_runtime.jsx)(_components.p, {
      children: "In a strict language, when composing several operations on a structure, the intermediate results are often fully materialized.\nAs examples, consider"
    }), "\n", (0,jsx_runtime.jsx)(_components.pre, {
      children: (0,jsx_runtime.jsx)(_components.code, {
        className: "language-haskell",
        children: "res1 = find (== 5) (xs ++ ys)\n"
      })
    }), "\n", (0,jsx_runtime.jsx)(_components.p, {
      children: "and"
    }), "\n", (0,jsx_runtime.jsx)(_components.pre, {
      children: (0,jsx_runtime.jsx)(_components.code, {
        className: "language-haskell",
        children: "res2 = sum (Map.elems m)\n"
      })
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["These are perfectly efficient in Haskell, but since function applications are strict in Plinth, the results of ", (0,jsx_runtime.jsx)(_components.code, {
        children: "xs ++ ys"
      }), " and ", (0,jsx_runtime.jsx)(_components.code, {
        children: "Map.elems m"
      }), " will be fully materialized before invoking ", (0,jsx_runtime.jsx)(_components.code, {
        children: "find"
      }), " and ", (0,jsx_runtime.jsx)(_components.code, {
        children: "sum"
      }), ", respectively.\nYou might consider rewriting these expressions to be less succinct but more efficient."]
    }), "\n", (0,jsx_runtime.jsx)(_components.h2, {
      id: "specializing-higher-order-functions",
      children: "Specializing higher-order functions"
    }), "\n", (0,jsx_runtime.jsx)(_components.p, {
      children: "The use of higher-order functions is a common technique to facilitate code reuse.\nHigher-order functions are widely used in the Plutus libraries but can be less efficient than specialized versions."
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["For instance, the Plutus function ", (0,jsx_runtime.jsx)(_components.code, {
        children: "findOwnInput"
      }), " makes use of the higher-order function ", (0,jsx_runtime.jsx)(_components.code, {
        children: "find"
      }), " to search for the current script input."]
    }), "\n", (0,jsx_runtime.jsx)(_components.pre, {
      children: (0,jsx_runtime.jsx)(_components.code, {
        className: "language-haskell",
        children: "findOwnInput :: ScriptContext -> Maybe TxInInfo\nfindOwnInput ScriptContext{scriptContextTxInfo=TxInfo{txInfoInputs},\n             scriptContextPurpose=Spending txOutRef} =\n    find (\\TxInInfo{txInInfoOutRef} -> txInInfoOutRef == txOutRef) txInfoInputs\nfindOwnInput _ = Nothing\n"
      })
    }), "\n", (0,jsx_runtime.jsx)(_components.p, {
      children: "This can be rewritten with a recursive function specialized to the specific check in question."
    }), "\n", (0,jsx_runtime.jsx)(_components.pre, {
      children: (0,jsx_runtime.jsx)(_components.code, {
        className: "language-haskell",
        children: "findOwnInput :: ScriptContext -> Maybe TxInInfo\nfindOwnInput ScriptContext{scriptContextTxInfo=TxInfo{txInfoInputs},\n             scriptContextPurpose=Spending txOutRef} = go txInfoInputs\n    where\n        go [] = Nothing\n        go (i@TxInInfo{txInInfoOutRef} : rest) = if txInInfoOutRef == txOutRef\n                                                 then Just i\n                                                 else go rest\nfindOwnInput _ = Nothing\n"
      })
    }), "\n", (0,jsx_runtime.jsx)(_components.h2, {
      id: "removing-traces",
      children: "Removing Traces"
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["Traces can be expensive especially in terms of script sizes.\nIt is advisable to use traces during development, but to remove them when deploying your scripts on mainnet.\nTraces can be removed via the ", (0,jsx_runtime.jsx)(_components.code, {
        children: "remove-trace"
      }), " plugin flag."]
    }), "\n", (0,jsx_runtime.jsxs)(_components.h2, {
      id: "using-builtinarray-for-index-based-lookups",
      children: ["Using ", (0,jsx_runtime.jsx)(_components.code, {
        children: "BuiltinArray"
      }), " for index-based lookups"]
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["For optimizing multiple index-based lookups, see the upcoming ", (0,jsx_runtime.jsx)(_components.a, {
        href: "/pr-preview/docs/pr-7544/upcoming-features/builtin-arrays",
        children: "Builtin Arrays"
      }), " feature."]
    }), "\n", (0,jsx_runtime.jsxs)(_components.h2, {
      id: "using-error-for-faster-failure",
      children: ["Using ", (0,jsx_runtime.jsx)(_components.code, {
        children: "error"
      }), " for faster failure"]
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["Plutus scripts have access to one impure effect, ", (0,jsx_runtime.jsx)(_components.code, {
        children: "error"
      }), ", which immediately terminates the script evaluation and will fail validation.\nThis failure is very fast, but it is also unrecoverable, so only use it in cases where you want to fail the entire validation if there is a failure."]
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["The Plutus libraries have some functions that fail with ", (0,jsx_runtime.jsx)(_components.code, {
        children: "error"
      }), ".\nUsually these are given an ", (0,jsx_runtime.jsx)(_components.code, {
        children: "unsafe"
      }), " prefix to their name.\nFor example, ", (0,jsx_runtime.jsx)(_components.code, {
        children: "PlutusTx.IsData.Class.FromData"
      }), " parses a value of type ", (0,jsx_runtime.jsx)(_components.code, {
        children: "Data"
      }), ", returning the result in a ", (0,jsx_runtime.jsx)(_components.code, {
        children: "Maybe"
      }), " value to indicate whether it succeeded or failed; whereas ", (0,jsx_runtime.jsx)(_components.code, {
        children: "PlutusTx.IsData.Class.UnsafeFromData"
      }), " does the same but fails with ", (0,jsx_runtime.jsx)(_components.code, {
        children: "error"
      }), "."]
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