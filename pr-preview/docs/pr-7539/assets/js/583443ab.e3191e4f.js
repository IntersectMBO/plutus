"use strict";
(self["webpackChunkdocusaurus"] = self["webpackChunkdocusaurus"] || []).push([[2351],{

/***/ 9994:
/***/ ((__unused_webpack_module, __webpack_exports__, __webpack_require__) => {

// ESM COMPAT FLAG
__webpack_require__.r(__webpack_exports__);

// EXPORTS
__webpack_require__.d(__webpack_exports__, {
  assets: () => (/* binding */ assets),
  contentTitle: () => (/* binding */ contentTitle),
  "default": () => (/* binding */ MDXContent),
  frontMatter: () => (/* binding */ frontMatter),
  metadata: () => (/* reexport */ site_docs_working_with_scripts_compile_time_evaluation_md_583_namespaceObject),
  toc: () => (/* binding */ toc)
});

;// ./.docusaurus/docusaurus-plugin-content-docs/default/site-docs-working-with-scripts-compile-time-evaluation-md-583.json
const site_docs_working_with_scripts_compile_time_evaluation_md_583_namespaceObject = /*#__PURE__*/JSON.parse('{"id":"working-with-scripts/compile-time-evaluation","title":"Compile Time Evaluation","description":"Compile-time evaluation of expressions is usually preferable as it can reduce script size and execution cost.","source":"@site/docs/working-with-scripts/compile-time-evaluation.md","sourceDirName":"working-with-scripts","slug":"/working-with-scripts/compile-time-evaluation","permalink":"/pr-preview/docs/pr-7539/working-with-scripts/compile-time-evaluation","draft":false,"unlisted":false,"editUrl":"https://github.com/IntersectMBO/plutus/edit/master/doc/docusaurus/docs/working-with-scripts/compile-time-evaluation.md","tags":[],"version":"current","sidebarPosition":23,"frontMatter":{"sidebar_position":23},"sidebar":"tutorialSidebar","previous":{"title":"Simplifying Code Before Compilation","permalink":"/pr-preview/docs/pr-7539/working-with-scripts/simplifying-before-compilation"},"next":{"title":"Other Optimization Techniques","permalink":"/pr-preview/docs/pr-7539/working-with-scripts/other-optimization-techniques"}}');
// EXTERNAL MODULE: ./node_modules/react/jsx-runtime.js
var jsx_runtime = __webpack_require__(4848);
// EXTERNAL MODULE: ./node_modules/@mdx-js/react/lib/index.js
var lib = __webpack_require__(8453);
;// ./docs/working-with-scripts/compile-time-evaluation.md


const frontMatter = {
	sidebar_position: 23
};
const contentTitle = 'Compile Time Evaluation';

const assets = {

};



const toc = [{
  "value": "Relying on Compiler Optimizations",
  "id": "relying-on-compiler-optimizations",
  "level": 2
}, {
  "value": "Using Template Haskell",
  "id": "using-template-haskell",
  "level": 2
}, {
  "value": "Using Lifting",
  "id": "using-lifting",
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
    li: "li",
    p: "p",
    strong: "strong",
    ul: "ul",
    ...(0,lib/* useMDXComponents */.R)(),
    ...props.components
  };
  return (0,jsx_runtime.jsxs)(jsx_runtime.Fragment, {
    children: [(0,jsx_runtime.jsx)(_components.header, {
      children: (0,jsx_runtime.jsx)(_components.h1, {
        id: "compile-time-evaluation",
        children: "Compile Time Evaluation"
      })
    }), "\n", (0,jsx_runtime.jsx)(_components.p, {
      children: "Compile-time evaluation of expressions is usually preferable as it can reduce script size and execution cost.\nThere are several ways to achieve this."
    }), "\n", (0,jsx_runtime.jsx)(_components.h2, {
      id: "relying-on-compiler-optimizations",
      children: "Relying on Compiler Optimizations"
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["Some compiler optimizations - like constant folding and inlining - enable compile-time evaluation.\nConstant folding reduces expressions such as ", (0,jsx_runtime.jsx)(_components.code, {
        children: "3 + 4"
      }), " to ", (0,jsx_runtime.jsx)(_components.code, {
        children: "7"
      }), ".\nInlining can result in beta-reduction - for example, ", (0,jsx_runtime.jsx)(_components.code, {
        children: "(\\x -> x + y) 3"
      }), " becomes ", (0,jsx_runtime.jsx)(_components.code, {
        children: "3 + y"
      }), "."]
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["Inlining can also unlock further optimizations; for instance, inlining ", (0,jsx_runtime.jsx)(_components.code, {
        children: "x"
      }), " in ", (0,jsx_runtime.jsx)(_components.code, {
        children: "let x = 3 in x + 4"
      }), " enables constant folding, eventually simplifying the expression to 7.\nThis requires ", (0,jsx_runtime.jsx)(_components.code, {
        children: "inline-constants"
      }), " to be enabled (it is enabled by default).\nKeep in mind that this may increase program size if a large constant appears multiple times."]
    }), "\n", (0,jsx_runtime.jsx)(_components.p, {
      children: "This method is straightforward - you don't need to do anything manually; the compiler handles it for you.\nThe catch is that you’re limited to what the compiler is able (and willing) to optimize."
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["Specifically, at present constant folding is limited to builtin functions applied to constant arguments.\nIt won't, for example, reduce ", (0,jsx_runtime.jsx)(_components.code, {
        children: "x * 0"
      }), " to ", (0,jsx_runtime.jsx)(_components.code, {
        children: "0"
      }), ", or ", (0,jsx_runtime.jsx)(_components.code, {
        children: "3 + (4 + x)"
      }), " to ", (0,jsx_runtime.jsx)(_components.code, {
        children: "7 + x"
      }), ".\nInlining happens only when the compiler knows it is safe (i.e., won’t alter the program semantics) and beneficial (i.e., won’t substantially increase program size or cost).\nThe compiler is conservative in both respects, though the inliner can be made more aggressive using the ", (0,jsx_runtime.jsx)(_components.code, {
        children: "inline-callsite-growth"
      }), " flag."]
    }), "\n", (0,jsx_runtime.jsx)(_components.h2, {
      id: "using-template-haskell",
      children: "Using Template Haskell"
    }), "\n", (0,jsx_runtime.jsx)(_components.p, {
      children: "This is a standard Haskell metaprogramming technique for evaluating and generating code at compile time.\nSince Plinth is a subset of Haskell, it applies equally to Plinth."
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["Template Haskell offers a lot of power, but it also introduces a fair bit of complexity, syntactic overhead and cognitive burden.\nIt lets you generate arbitrary Haskell code at compile time, so you can do everything from basic constant folding to far more advanced transformations - see ", (0,jsx_runtime.jsx)(_components.a, {
        href: "/pr-preview/docs/pr-7539/working-with-scripts/simplifying-before-compilation",
        children: "Simplifying Code Before Compilation"
      }), " for more examples.\nA general principle is to reserve this for cases where the complexity of the problem really calls for it."]
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["Even putting the complexity aside, this method may still be unsuitable depending on what transformation you want to apply.\nFor example, to implement a general constant folding optimizer for ", (0,jsx_runtime.jsx)(_components.code, {
        children: "addInteger"
      }), ", you may need to handle all possible syntaxes for adding two integers: ", (0,jsx_runtime.jsx)(_components.code, {
        children: "addInteger 3 4"
      }), ", ", (0,jsx_runtime.jsx)(_components.code, {
        children: "3 + 4"
      }), ", and even ", (0,jsx_runtime.jsx)(_components.code, {
        children: "3 `addInteger` 4"
      }), ".\nThis is why optimizations like constant folding are better done in a smaller intermediate language, rather than in the surface language.\nAnd if you also want to perform inlining - such as rewriting ", (0,jsx_runtime.jsx)(_components.code, {
        children: "let x = 3 in addInteger x 4"
      }), " to ", (0,jsx_runtime.jsx)(_components.code, {
        children: "7"
      }), ", then it's even more difficult."]
    }), "\n", (0,jsx_runtime.jsx)(_components.p, {
      children: "For simple compile-time evaluation like constant folding, it is better  to let the compiler handle it.\nUse Template Haskell for complex transformations, or transformations that the Plinth compiler can't yet do."
    }), "\n", (0,jsx_runtime.jsx)(_components.h2, {
      id: "using-lifting",
      children: "Using Lifting"
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["You can find a detailed explanation of lifting in ", (0,jsx_runtime.jsx)(_components.a, {
        href: "/pr-preview/docs/pr-7539/using-plinth/lifting",
        children: "Lifting Values into CompiledCode"
      }), ".\nLifting is a regular Haskell function application that happens at runtime, and it always operates on values that have been fully evaluated.\nFor instance, when you call ", (0,jsx_runtime.jsx)(_components.code, {
        children: "liftCodeDef (...)"
      }), " where the argument - ", (0,jsx_runtime.jsx)(_components.code, {
        children: "(...)"
      }), " - is some complex Haskell computation of type ", (0,jsx_runtime.jsx)(_components.code, {
        children: "Integer"
      }), ", ", (0,jsx_runtime.jsx)(_components.code, {
        children: "liftCodeDef"
      }), " will evaluate the argument to an integer constant, and produce a ", (0,jsx_runtime.jsx)(_components.code, {
        children: "CompiledCode"
      }), " that contains a PIR/UPLC constant."]
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["It is important to understand that the \"runtime\" here is the ", (0,jsx_runtime.jsx)(_components.em, {
        children: "runtime of your Haskell program"
      }), ", ", (0,jsx_runtime.jsx)(_components.strong, {
        children: "not"
      }), " the runtime (on-chain execution) of your script.\nSo from the script's perspective, this is still compile-time evaluation, as it is still part of the process of creating the script to be executed on-chain."]
    }), "\n", (0,jsx_runtime.jsx)(_components.p, {
      children: "The fact that lifting happens at runtime, rather than compile time, of your Haskell program, gives it some unique advantages:"
    }), "\n", (0,jsx_runtime.jsxs)(_components.ul, {
      children: ["\n", (0,jsx_runtime.jsxs)(_components.li, {
        children: ["This is the only way to turn values that are only known at runtime into ", (0,jsx_runtime.jsx)(_components.code, {
          children: "CompiledCode"
        }), "."]
      }), "\n", (0,jsx_runtime.jsxs)(_components.li, {
        children: ["The value being lifted can come from any arbitrary Haskell computation.\nYou can, for example, write arbitrary Haskell code that produces an ", (0,jsx_runtime.jsx)(_components.code, {
          children: "Integer"
        }), ", and lift it into ", (0,jsx_runtime.jsx)(_components.code, {
          children: "CompiledCode"
        }), ".\nThis code can read from a file, or do anything else possible in Haskell."]
      }), "\n"]
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["The main limitation is that, in general, functions, or any data type containing functions, cannot be lifted.\nIndeed, given a Haskell function at runtime, you can only call it with some arguments - you cannot inspect it or reify it into a ", (0,jsx_runtime.jsx)(_components.code, {
        children: "CompiledCode"
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