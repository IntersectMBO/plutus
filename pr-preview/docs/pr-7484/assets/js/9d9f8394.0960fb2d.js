"use strict";
(self["webpackChunkdocusaurus"] = self["webpackChunkdocusaurus"] || []).push([[9013],{

/***/ 2245:
/***/ ((__unused_webpack_module, __webpack_exports__, __webpack_require__) => {

// ESM COMPAT FLAG
__webpack_require__.r(__webpack_exports__);

// EXPORTS
__webpack_require__.d(__webpack_exports__, {
  assets: () => (/* binding */ assets),
  contentTitle: () => (/* binding */ contentTitle),
  "default": () => (/* binding */ MDXContent),
  frontMatter: () => (/* binding */ frontMatter),
  metadata: () => (/* reexport */ site_docs_troubleshooting_md_9d9_namespaceObject),
  toc: () => (/* binding */ toc)
});

;// ./.docusaurus/docusaurus-plugin-content-docs/default/site-docs-troubleshooting-md-9d9.json
const site_docs_troubleshooting_md_9d9_namespaceObject = /*#__PURE__*/JSON.parse('{"id":"troubleshooting","title":"Troubleshooting","description":"Compilation Errors","source":"@site/docs/troubleshooting.md","sourceDirName":".","slug":"/troubleshooting","permalink":"/pr-preview/docs/pr-7484/troubleshooting","draft":false,"unlisted":false,"editUrl":"https://github.com/IntersectMBO/plutus/edit/master/doc/docusaurus/docs/troubleshooting.md","tags":[],"version":"current","sidebarPosition":80,"frontMatter":{"sidebar_position":80},"sidebar":"tutorialSidebar","previous":{"title":"Builtin Arrays","permalink":"/pr-preview/docs/pr-7484/upcoming-features/builtin-arrays"}}');
// EXTERNAL MODULE: ./node_modules/react/jsx-runtime.js
var jsx_runtime = __webpack_require__(4848);
// EXTERNAL MODULE: ./node_modules/@mdx-js/react/lib/index.js
var lib = __webpack_require__(8453);
;// ./docs/troubleshooting.md


const frontMatter = {
	sidebar_position: 80
};
const contentTitle = 'Troubleshooting';

const assets = {

};



const toc = [{
  "value": "Compilation Errors",
  "id": "compilation-errors",
  "level": 2
}, {
  "value": "&quot;No unfolding&quot;",
  "id": "no-unfolding",
  "level": 3
}, {
  "value": "&quot;Unsupported feature: Cannot case on a value on type: {type}&quot;",
  "id": "unsupported-feature-cannot-case-on-a-value-on-type-type",
  "level": 3
}, {
  "value": "&quot;Unsupported feature: Cannot construct a value of type&quot;",
  "id": "unsupported-feature-cannot-construct-a-value-of-type",
  "level": 3
}, {
  "value": "Runtime Issues",
  "id": "runtime-issues",
  "level": 2
}, {
  "value": "Missing Trace Messages",
  "id": "missing-trace-messages",
  "level": 3
}, {
  "value": "Unexpected Evaluation Failure",
  "id": "unexpected-evaluation-failure",
  "level": 3
}, {
  "value": "Haddock",
  "id": "haddock",
  "level": 2
}, {
  "value": "Error codes",
  "id": "error-codes",
  "level": 2
}];
function _createMdxContent(props) {
  const _components = {
    a: "a",
    code: "code",
    h1: "h1",
    h2: "h2",
    h3: "h3",
    header: "header",
    li: "li",
    ol: "ol",
    p: "p",
    pre: "pre",
    ul: "ul",
    ...(0,lib/* useMDXComponents */.R)(),
    ...props.components
  };
  return (0,jsx_runtime.jsxs)(jsx_runtime.Fragment, {
    children: [(0,jsx_runtime.jsx)(_components.header, {
      children: (0,jsx_runtime.jsx)(_components.h1, {
        id: "troubleshooting",
        children: "Troubleshooting"
      })
    }), "\n", (0,jsx_runtime.jsx)(_components.h2, {
      id: "compilation-errors",
      children: "Compilation Errors"
    }), "\n", (0,jsx_runtime.jsx)(_components.h3, {
      id: "no-unfolding",
      children: "\"No unfolding\""
    }), "\n", (0,jsx_runtime.jsx)(_components.p, {
      children: "This means the plugin cannot access to the definition of a Haskell identifier, which it needs to be able to compile that identifier to Plutus Core."
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["If the identifier in question is defined in the source code, try adding the ", (0,jsx_runtime.jsx)(_components.code, {
        children: "INLINEABLE"
      }), " pragma to it (not the ", (0,jsx_runtime.jsx)(_components.code, {
        children: "INLINE"
      }), " pragma, which should generally be avoided).\nIf it already has the ", (0,jsx_runtime.jsx)(_components.code, {
        children: "INLINEABLE"
      }), " pragma, try adding the GHC flags\n", (0,jsx_runtime.jsx)(_components.code, {
        children: "-fno-ignore-interface-pragmas"
      }), " and ", (0,jsx_runtime.jsx)(_components.code, {
        children: "-fno-omit-interface-pragmas"
      }), "."]
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["If this doesn't resolve the issue, or if the identifier in question isn't directly defined in the code but is produced by GHC optimizations,\nensure that you apply all GHC flags listed in ", (0,jsx_runtime.jsx)(_components.a, {
        href: "/pr-preview/docs/pr-7484/using-plinth/extensions-flags-pragmas",
        children: "GHC Extensions, Flags and Pragmas"
      }), ".\nThese flags disable GHC optimizations that can interfere with the plugin, and ensure that unfoldings are neither omitted nor ignored."]
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["If the identifier with missing unfolding is from ", (0,jsx_runtime.jsx)(_components.code, {
        children: "base"
      }), " or invoked by a function from ", (0,jsx_runtime.jsx)(_components.code, {
        children: "base"
      }), ", you should use instead the corresponding function from the ", (0,jsx_runtime.jsx)(_components.code, {
        children: "plutus-tx"
      }), " package.\nNote that the plugin lacks support for certain functions and methods from ", (0,jsx_runtime.jsx)(_components.code, {
        children: "base"
      }), "."]
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["This error can also occur if the definition of an identifier isn't available at compile time, as is the case with function parameters - e.g., ", (0,jsx_runtime.jsx)(_components.code, {
        children: "f x = $$(compile [|| x + 1 ||])"
      }), ".\nHere ", (0,jsx_runtime.jsx)(_components.code, {
        children: "x"
      }), " is a parameter and thus has no unfolding at compile time.\nTo make this work, you should lift ", (0,jsx_runtime.jsx)(_components.code, {
        children: "x + 1"
      }), " into ", (0,jsx_runtime.jsx)(_components.code, {
        children: "CompiledCode"
      }), ", instead of compiling it.\nSee ", (0,jsx_runtime.jsx)(_components.a, {
        href: "/pr-preview/docs/pr-7484/using-plinth/lifting",
        children: "Lifting Values into CompiledCode"
      }), " for more details."]
    }), "\n", (0,jsx_runtime.jsx)(_components.p, {
      children: "Alternatively, this error may happen when using GHCi, which is not fully supported by the plugin.\nNot only does GHCi often hide unfoldings from the plugin, but it may also introduce debugging information like breakpoints in GHC Core, causing the plugin to fail."
    }), "\n", (0,jsx_runtime.jsx)(_components.h3, {
      id: "unsupported-feature-cannot-case-on-a-value-on-type-type",
      children: "\"Unsupported feature: Cannot case on a value on type: {type}\""
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["If ", (0,jsx_runtime.jsx)(_components.code, {
        children: "{type}"
      }), " is a builtin type like ", (0,jsx_runtime.jsx)(_components.code, {
        children: "BuiltinInteger"
      }), ": to convert a builtin type to the corresponding Haskell type (such as ", (0,jsx_runtime.jsx)(_components.code, {
        children: "BuiltinInteger"
      }), " to ", (0,jsx_runtime.jsx)(_components.code, {
        children: "Integer"
      }), " or ", (0,jsx_runtime.jsx)(_components.code, {
        children: "BuiltinList"
      }), " to a Haskell list) in Plinth, you should use ", (0,jsx_runtime.jsx)(_components.code, {
        children: "fromOpaque"
      }), ".\nPattern matching on the builtin type or using ", (0,jsx_runtime.jsx)(_components.code, {
        children: "fromBuiltin"
      }), " is not permitted, and will lead to the above error."]
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["If ", (0,jsx_runtime.jsx)(_components.code, {
        children: "{type}"
      }), " is a GHC type like ", (0,jsx_runtime.jsx)(_components.code, {
        children: "GHC.Num.Integer.Integer"
      }), ": you may be using operations from ", (0,jsx_runtime.jsx)(_components.code, {
        children: "base"
      }), " (such as ", (0,jsx_runtime.jsx)(_components.code, {
        children: "GHC.Classes.=="
      }), ") on that type, or using a literal of that type in a pattern.\nAn example of the latter:"]
    }), "\n", (0,jsx_runtime.jsx)(_components.pre, {
      children: (0,jsx_runtime.jsx)(_components.code, {
        className: "language-haskell",
        children: "case (x :: Maybe Integer) of Just 42 -> ...\n"
      })
    }), "\n", (0,jsx_runtime.jsx)(_components.p, {
      children: "This is not supported, and you should instead write"
    }), "\n", (0,jsx_runtime.jsx)(_components.pre, {
      children: (0,jsx_runtime.jsx)(_components.code, {
        className: "language-haskell",
        children: "case (x :: Maybe Integer) of Just y | y PlutusTx.== 42 -> ...\n"
      })
    }), "\n", (0,jsx_runtime.jsx)(_components.h3, {
      id: "unsupported-feature-cannot-construct-a-value-of-type",
      children: "\"Unsupported feature: Cannot construct a value of type\""
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["Conversely, to convert a Haskell type to the corresponding builtin type in Plinth, you should use ", (0,jsx_runtime.jsx)(_components.code, {
        children: "toOpaque"
      }), ", rather than directly using the data constructor or ", (0,jsx_runtime.jsx)(_components.code, {
        children: "toBuiltin"
      }), "."]
    }), "\n", (0,jsx_runtime.jsx)(_components.h2, {
      id: "runtime-issues",
      children: "Runtime Issues"
    }), "\n", (0,jsx_runtime.jsx)(_components.h3, {
      id: "missing-trace-messages",
      children: "Missing Trace Messages"
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["If your expected trace messages are missing, check the following ", (0,jsx_runtime.jsx)(_components.a, {
        href: "/pr-preview/docs/pr-7484/delve-deeper/plinth-compiler-options",
        children: "plugin flags"
      }), ":"]
    }), "\n", (0,jsx_runtime.jsxs)(_components.ul, {
      children: ["\n", (0,jsx_runtime.jsxs)(_components.li, {
        children: ["If the ", (0,jsx_runtime.jsx)(_components.code, {
          children: "remove-trace"
        }), " flag (default off) is on, all trace messages will be removed."]
      }), "\n", (0,jsx_runtime.jsxs)(_components.li, {
        children: ["If the ", (0,jsx_runtime.jsx)(_components.code, {
          children: "preserve-logging"
        }), " flag (default off) is off, the compiler may remove some trace messages during optimization."]
      }), "\n"]
    }), "\n", (0,jsx_runtime.jsx)(_components.h3, {
      id: "unexpected-evaluation-failure",
      children: "Unexpected Evaluation Failure"
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["It is usually ", (0,jsx_runtime.jsx)(_components.a, {
        href: "/pr-preview/docs/pr-7484/using-plinth/extensions-flags-pragmas",
        children: "advisable"
      }), " to use the ", (0,jsx_runtime.jsx)(_components.code, {
        children: "Strict"
      }), " extension when writing Plinth, which improves performance.\nHowever, be cautious, as this can result in unexpected evaluation failures.\nConsider the following script:"]
    }), "\n", (0,jsx_runtime.jsx)(_components.pre, {
      children: (0,jsx_runtime.jsx)(_components.code, {
        className: "language-haskell",
        children: "{-# LANGUAGE Strict #-}\n\ndata MyRedeemer = A | B\n\nmyScript :: MyRedeemer -> ScriptContext -> Bool\nmyScript redeemer ctx = case redeemer of\n  A -> condition1\n  B -> condition2\n  where\n    condition1, condition2 :: Bool\n    condition1 = ...\n    condition2 = if ... then True else traceError \"condition 2 not met\"\n"
      })
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["The ", (0,jsx_runtime.jsx)(_components.code, {
        children: "Strict"
      }), " extension makes all bindings strict, which means even if ", (0,jsx_runtime.jsx)(_components.code, {
        children: "redeemer"
      }), " matches ", (0,jsx_runtime.jsx)(_components.code, {
        children: "A"
      }), ", ", (0,jsx_runtime.jsx)(_components.code, {
        children: "condition2"
      }), " will still be evaluated.\nThis can be inefficient at best and, at worst, cause unexpected failures if ", (0,jsx_runtime.jsx)(_components.code, {
        children: "condition2"
      }), " is not met when the redeemer matches ", (0,jsx_runtime.jsx)(_components.code, {
        children: "A"
      }), "."]
    }), "\n", (0,jsx_runtime.jsx)(_components.p, {
      children: "There are multiple ways to fix this:"
    }), "\n", (0,jsx_runtime.jsxs)(_components.ol, {
      children: ["\n", (0,jsx_runtime.jsxs)(_components.li, {
        children: ["You can make ", (0,jsx_runtime.jsx)(_components.code, {
          children: "condition1"
        }), " and ", (0,jsx_runtime.jsx)(_components.code, {
          children: "condition2"
        }), " non-strict by adding tildes:"]
      }), "\n"]
    }), "\n", (0,jsx_runtime.jsx)(_components.pre, {
      children: (0,jsx_runtime.jsx)(_components.code, {
        className: "language-haskell",
        children: "~condition1 = ...\n~condition2 = ...\n"
      })
    }), "\n", (0,jsx_runtime.jsxs)(_components.ol, {
      start: "2",
      children: ["\n", (0,jsx_runtime.jsxs)(_components.li, {
        children: ["Alternatively, you can define ", (0,jsx_runtime.jsx)(_components.code, {
          children: "condition1"
        }), " and ", (0,jsx_runtime.jsx)(_components.code, {
          children: "condition2"
        }), " within the ", (0,jsx_runtime.jsx)(_components.code, {
          children: "case"
        }), " branches:"]
      }), "\n"]
    }), "\n", (0,jsx_runtime.jsx)(_components.pre, {
      children: (0,jsx_runtime.jsx)(_components.code, {
        className: "language-haskell",
        children: "case redeemer of\n  A -> let condition1 = ... in condition1\n  B -> let condition2 = ... in condition2\n"
      })
    }), "\n", (0,jsx_runtime.jsxs)(_components.ol, {
      start: "3",
      children: ["\n", (0,jsx_runtime.jsxs)(_components.li, {
        children: ["Another option is to turn ", (0,jsx_runtime.jsx)(_components.code, {
          children: "condition1"
        }), " and ", (0,jsx_runtime.jsx)(_components.code, {
          children: "condition2"
        }), " into functions that take some arguments and return a ", (0,jsx_runtime.jsx)(_components.code, {
          children: "Bool"
        }), ", as functions are not evaluated until all their arguments are provided."]
      }), "\n"]
    }), "\n", (0,jsx_runtime.jsx)(_components.h2, {
      id: "haddock",
      children: "Haddock"
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["The plugin will typically fail when producing Haddock documentation.\nHowever, in this instance, you can simply tell it to defer any errors to runtime, using the ", (0,jsx_runtime.jsx)(_components.code, {
        children: "defer-errors"
      }), " plugin flag. Since you are only building documentation, runtime errors won't occur."]
    }), "\n", (0,jsx_runtime.jsx)(_components.h2, {
      id: "error-codes",
      children: "Error codes"
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["Some Plinth library functions produce error messages when failing.\nTo reduce code size, error codes are used instead of full error messages.\nThe mapping from error codes to error messages can be found in ", (0,jsx_runtime.jsx)(_components.a, {
        href: "https://plutus.cardano.intersectmbo.org/haddock/latest/plutus-tx/src/PlutusTx.ErrorCodes.html#plutusPreludeErrorCodes",
        children: (0,jsx_runtime.jsx)(_components.code, {
          children: "PlutusTx.ErrorCodes"
        })
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