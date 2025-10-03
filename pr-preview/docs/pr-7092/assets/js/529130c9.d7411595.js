"use strict";
(self["webpackChunkdocusaurus"] = self["webpackChunkdocusaurus"] || []).push([[1541],{

/***/ 3484:
/***/ ((__unused_webpack_module, __webpack_exports__, __webpack_require__) => {

// ESM COMPAT FLAG
__webpack_require__.r(__webpack_exports__);

// EXPORTS
__webpack_require__.d(__webpack_exports__, {
  assets: () => (/* binding */ assets),
  contentTitle: () => (/* binding */ contentTitle),
  "default": () => (/* binding */ MDXContent),
  frontMatter: () => (/* binding */ frontMatter),
  metadata: () => (/* reexport */ site_docs_using_plinth_differences_from_haskell_md_529_namespaceObject),
  toc: () => (/* binding */ toc)
});

;// ./.docusaurus/docusaurus-plugin-content-docs/default/site-docs-using-plinth-differences-from-haskell-md-529.json
const site_docs_using_plinth_differences_from_haskell_md_529_namespaceObject = /*#__PURE__*/JSON.parse('{"id":"using-plinth/differences-from-haskell","title":"Differences From Haskell","description":"Strictness","source":"@site/docs/using-plinth/differences-from-haskell.md","sourceDirName":"using-plinth","slug":"/using-plinth/differences-from-haskell","permalink":"/pr-preview/docs/pr-7092/using-plinth/differences-from-haskell","draft":false,"unlisted":false,"editUrl":"https://github.com/IntersectMBO/plutus/edit/master/doc/docusaurus/docs/using-plinth/differences-from-haskell.md","tags":[],"version":"current","sidebarPosition":15,"frontMatter":{"sidebar_position":15},"sidebar":"tutorialSidebar","previous":{"title":"Evaluating CompiledCode","permalink":"/pr-preview/docs/pr-7092/using-plinth/evaluating-plinth"},"next":{"title":"GHC Extensions, Flags and Pragmas","permalink":"/pr-preview/docs/pr-7092/using-plinth/extensions-flags-pragmas"}}');
// EXTERNAL MODULE: ./node_modules/react/jsx-runtime.js
var jsx_runtime = __webpack_require__(4848);
// EXTERNAL MODULE: ./node_modules/@mdx-js/react/lib/index.js
var lib = __webpack_require__(8453);
;// ./docs/using-plinth/differences-from-haskell.md


const frontMatter = {
	sidebar_position: 15
};
const contentTitle = 'Differences From Haskell';

const assets = {

};



const toc = [{
  "value": "Strictness",
  "id": "strictness",
  "level": 2
}, {
  "value": "Function Applications",
  "id": "function-applications",
  "level": 3
}, {
  "value": "Bindings",
  "id": "bindings",
  "level": 3
}, {
  "value": "Supported Haskell Features",
  "id": "supported-haskell-features",
  "level": 2
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
    strong: "strong",
    ul: "ul",
    ...(0,lib/* useMDXComponents */.R)(),
    ...props.components
  };
  return (0,jsx_runtime.jsxs)(jsx_runtime.Fragment, {
    children: [(0,jsx_runtime.jsx)(_components.header, {
      children: (0,jsx_runtime.jsx)(_components.h1, {
        id: "differences-from-haskell",
        children: "Differences From Haskell"
      })
    }), "\n", (0,jsx_runtime.jsx)(_components.h2, {
      id: "strictness",
      children: "Strictness"
    }), "\n", (0,jsx_runtime.jsx)(_components.h3, {
      id: "function-applications",
      children: "Function Applications"
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["Unlike in Haskell, function applications in Plinth are strict.\nIn other words, when evaluating ", (0,jsx_runtime.jsx)(_components.code, {
        children: "(\\x -> 42) (3 + 4)"
      }), " the expression ", (0,jsx_runtime.jsx)(_components.code, {
        children: "3 + 4"
      }), " is evaluated first, before evaluating the function body (", (0,jsx_runtime.jsx)(_components.code, {
        children: "42"
      }), "), even though ", (0,jsx_runtime.jsx)(_components.code, {
        children: "x"
      }), " is not used in the function body."]
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["Using lazy patterns on function parameters does not change this behavior: : ", (0,jsx_runtime.jsx)(_components.code, {
        children: "(\\(~x) -> 42) (3 + 4)"
      }), " still evaluates ", (0,jsx_runtime.jsx)(_components.code, {
        children: "3 + 4"
      }), " strictly.\nAt this time, it is not possible to make function applications non-strict in Plinth."]
    }), "\n", (0,jsx_runtime.jsx)(_components.h3, {
      id: "bindings",
      children: "Bindings"
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["Bindings in Plinth are by default non-strict, but they can be made strict via the bang pattern (", (0,jsx_runtime.jsx)(_components.code, {
        children: "!"
      }), "), as in ", (0,jsx_runtime.jsx)(_components.code, {
        children: "let !x = 3 + 4 in 42"
      }), ".\nConversely, in modules with the ", (0,jsx_runtime.jsx)(_components.code, {
        children: "Strict"
      }), " language extension on, bindings are by default strict, but they can be made non-strict via the lazy pattern (", (0,jsx_runtime.jsx)(_components.code, {
        children: "~"
      }), "), as in ", (0,jsx_runtime.jsx)(_components.code, {
        children: "let ~x = 3 + 4 in 42"
      }), "."]
    }), "\n", (0,jsx_runtime.jsxs)(_components.blockquote, {
      children: ["\n", (0,jsx_runtime.jsxs)(_components.p, {
        children: ["📌", " ", (0,jsx_runtime.jsx)(_components.strong, {
          children: "NOTE"
        })]
      }), "\n", (0,jsx_runtime.jsx)(_components.p, {
        children: "It is important to note that the UPLC evaluator does not perform lazy evaluation, which means a non-strict binding will be evaluated each time it is used, rather than at most once."
      }), "\n"]
    }), "\n", (0,jsx_runtime.jsx)(_components.h2, {
      id: "supported-haskell-features",
      children: "Supported Haskell Features"
    }), "\n", (0,jsx_runtime.jsx)(_components.p, {
      children: "The Plinth compiler provides good support for basic Haskell features, including regular algebraic data types, type classes, higher order functions, parametric polymorphism, etc.\nHowever, it doesn’t support many of Haskell’s more advanced features.\nA good rule of thumb for writing Plinth is to stick with simple Haskell (which is also typically good advice for Haskell development in general)."
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["Some notable Haskell features ", (0,jsx_runtime.jsx)(_components.em, {
        children: "not"
      }), " supported by Plinth include:"]
    }), "\n", (0,jsx_runtime.jsxs)(_components.ul, {
      children: ["\n", (0,jsx_runtime.jsxs)(_components.li, {
        children: ["Many functions and methods in ", (0,jsx_runtime.jsx)(_components.a, {
          href: "https://hackage.haskell.org/package/base",
          children: (0,jsx_runtime.jsx)(_components.code, {
            children: "base"
          })
        }), ".\nUse the counterparts in the ", (0,jsx_runtime.jsx)(_components.a, {
          href: "https://plutus.cardano.intersectmbo.org/haddock/latest/plutus-tx/",
          children: (0,jsx_runtime.jsx)(_components.code, {
            children: "plutus-tx"
          })
        }), " library instead.\nThis also means most Haskell third-party libraries are not supported, unless the library is developed specifically for Plinth."]
      }), "\n", (0,jsx_runtime.jsx)(_components.li, {
        children: "Mutually recursive data types."
      }), "\n", (0,jsx_runtime.jsx)(_components.li, {
        children: "Type families"
      }), "\n", (0,jsx_runtime.jsx)(_components.li, {
        children: "Existential types"
      }), "\n", (0,jsx_runtime.jsx)(_components.li, {
        children: "GADTs"
      }), "\n", (0,jsx_runtime.jsx)(_components.li, {
        children: "IO and FFI"
      }), "\n"]
    }), "\n", (0,jsx_runtime.jsx)(_components.p, {
      children: "Use of these features often leads the Plinth compiler to report an \"Unsupported feature\" error, though you may sometimes get a different error."
    }), "\n", (0,jsx_runtime.jsx)(_components.p, {
      children: "Since the Plinth compiler is a GHC plugin that runs after GHC's type checking, unsupported Haskell features cannot be detected at type checking time.\nAs a result, it's unlikely that an IDE will be able to report these errors.\nYou will need to compile the Haskell module to determine if everything is compiled successfully."
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