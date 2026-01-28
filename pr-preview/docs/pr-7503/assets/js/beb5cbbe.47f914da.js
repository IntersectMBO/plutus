"use strict";
(self["webpackChunkdocusaurus"] = self["webpackChunkdocusaurus"] || []).push([[9679],{

/***/ 6662:
/***/ ((__unused_webpack_module, __webpack_exports__, __webpack_require__) => {

// ESM COMPAT FLAG
__webpack_require__.r(__webpack_exports__);

// EXPORTS
__webpack_require__.d(__webpack_exports__, {
  assets: () => (/* binding */ assets),
  contentTitle: () => (/* binding */ contentTitle),
  "default": () => (/* binding */ MDXContent),
  frontMatter: () => (/* binding */ frontMatter),
  metadata: () => (/* reexport */ site_docs_using_plinth_extensions_flags_pragmas_md_beb_namespaceObject),
  toc: () => (/* binding */ toc)
});

;// ./.docusaurus/docusaurus-plugin-content-docs/default/site-docs-using-plinth-extensions-flags-pragmas-md-beb.json
const site_docs_using_plinth_extensions_flags_pragmas_md_beb_namespaceObject = /*#__PURE__*/JSON.parse('{"id":"using-plinth/extensions-flags-pragmas","title":"GHC Extensions, Flags and Pragmas","description":"Plinth is a subset of Haskell and is compiled to Untyped Plutus Core by the Plinth compiler, a GHC (Glasgow Haskell Compiler) plugin.","source":"@site/docs/using-plinth/extensions-flags-pragmas.md","sourceDirName":"using-plinth","slug":"/using-plinth/extensions-flags-pragmas","permalink":"/pr-preview/docs/pr-7503/using-plinth/extensions-flags-pragmas","draft":false,"unlisted":false,"editUrl":"https://github.com/IntersectMBO/plutus/edit/master/doc/docusaurus/docs/using-plinth/extensions-flags-pragmas.md","tags":[],"version":"current","sidebarPosition":20,"frontMatter":{"sidebar_position":20},"sidebar":"tutorialSidebar","previous":{"title":"Differences From Haskell","permalink":"/pr-preview/docs/pr-7503/using-plinth/differences-from-haskell"},"next":{"title":"Special Functions and Types","permalink":"/pr-preview/docs/pr-7503/using-plinth/special-functions-and-types"}}');
// EXTERNAL MODULE: ./node_modules/react/jsx-runtime.js
var jsx_runtime = __webpack_require__(4848);
// EXTERNAL MODULE: ./node_modules/@mdx-js/react/lib/index.js
var lib = __webpack_require__(8453);
;// ./docs/using-plinth/extensions-flags-pragmas.md


const frontMatter = {
	sidebar_position: 20
};
const contentTitle = 'GHC Extensions, Flags and Pragmas';

const assets = {

};



const toc = [{
  "value": "Extensions",
  "id": "extensions",
  "level": 3
}, {
  "value": "Flags",
  "id": "flags",
  "level": 3
}, {
  "value": "Pragmas",
  "id": "pragmas",
  "level": 3
}];
function _createMdxContent(props) {
  const _components = {
    a: "a",
    blockquote: "blockquote",
    code: "code",
    h1: "h1",
    h3: "h3",
    header: "header",
    li: "li",
    p: "p",
    pre: "pre",
    strong: "strong",
    ul: "ul",
    ...(0,lib/* useMDXComponents */.R)(),
    ...props.components
  };
  return (0,jsx_runtime.jsxs)(jsx_runtime.Fragment, {
    children: [(0,jsx_runtime.jsx)(_components.header, {
      children: (0,jsx_runtime.jsx)(_components.h1, {
        id: "ghc-extensions-flags-and-pragmas",
        children: "GHC Extensions, Flags and Pragmas"
      })
    }), "\n", (0,jsx_runtime.jsx)(_components.p, {
      children: "Plinth is a subset of Haskell and is compiled to Untyped Plutus Core by the Plinth compiler, a GHC (Glasgow Haskell Compiler) plugin."
    }), "\n", (0,jsx_runtime.jsx)(_components.p, {
      children: "In order to ensure the success and correct compilation of Plinth programs, all Plinth modules (that is, Haskell modules that contain code to be compiled by the Plinth compiler) should use the following GHC extensions, flags and pragmas."
    }), "\n", (0,jsx_runtime.jsx)(_components.h3, {
      id: "extensions",
      children: "Extensions"
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["Plinth modules should use the ", (0,jsx_runtime.jsx)(_components.code, {
        children: "Strict"
      }), " extension: :"]
    }), "\n", (0,jsx_runtime.jsx)(_components.pre, {
      children: (0,jsx_runtime.jsx)(_components.code, {
        children: "    {-# LANGUAGE Strict #-}\n"
      })
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["As mentioned in ", (0,jsx_runtime.jsx)(_components.a, {
        href: "/pr-preview/docs/pr-7503/using-plinth/differences-from-haskell",
        children: "Differences from Haskell"
      }), ", function applications in Plinth are always strict, while bindings can be strict or non-strict.\nIn addition, the UPLC evaluator does not perform lazy evaluation, meaning a non-strict binding is evaluated as many times as it is used.\nGiven these facts, making let bindings strict by default has the following advantages:"]
    }), "\n", (0,jsx_runtime.jsxs)(_components.ul, {
      children: ["\n", (0,jsx_runtime.jsxs)(_components.li, {
        children: ["It makes let bindings and function applications semantically equivalent. For example, ", (0,jsx_runtime.jsx)(_components.code, {
          children: "let x = 3 + 4 in 42"
        }), " has the same semantics as ", (0,jsx_runtime.jsx)(_components.code, {
          children: "(\\x -> 42) (3 + 4)"
        }), ".\nThis is what one would come to expect, as it is the case in most other programming languages, regardless of whether the language is strict or non-strict."]
      }), "\n", (0,jsx_runtime.jsxs)(_components.li, {
        children: ["Using non-strict bindings can cause an expression to be inadvertently evaluated for an unbounded number of times.\nConsider ", (0,jsx_runtime.jsx)(_components.code, {
          children: "let x = <expensive> in \\y -> x + y"
        }), ".\nIf ", (0,jsx_runtime.jsx)(_components.code, {
          children: "x"
        }), " is non-strict, ", (0,jsx_runtime.jsx)(_components.code, {
          children: "<expensive>"
        }), " will be evaluated every time ", (0,jsx_runtime.jsx)(_components.code, {
          children: "\\y -> x + y"
        }), " is applied to an argument, which means it can be evaluated 0 times, 1 time, 2 times, or any number of times (this is not the case if lazy evaluation was employed).\nOn the other hand, if ", (0,jsx_runtime.jsx)(_components.code, {
          children: "x"
        }), " is strict, it is always evaluated once, which is at most one more time than what is necessary."]
      }), "\n"]
    }), "\n", (0,jsx_runtime.jsx)(_components.h3, {
      id: "flags",
      children: "Flags"
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["GHC has a variety of optimization flags, many of which are on by default.\nAlthough Plinth is, syntactically, a subset of Haskell, it has different semantics and a different evaluation strategy (Haskell: non-strict semantics, call by need; Plinth: strict semantics, call by value). As a result, some GHC optimizations are not helpful for Plinth programs, and can even be harmful, in the sense that it can make Plinth programs less efficient, or fail to be compiled.\nAn example is the full laziness optimization, controlled by GHC flag ", (0,jsx_runtime.jsx)(_components.code, {
        children: "-ffull-laziness"
      }), ", which floats let bindings out of lambdas whenever possible.\nSince Untyped Plutus Core does not employ lazy evaluation, the full laziness optimization is usually not beneficial, and can sometimes make a Plinth program more expensive.\nConversely, some GHC features must be turned on in order to ensure Plinth programs are compiled successfully."]
    }), "\n", (0,jsx_runtime.jsx)(_components.p, {
      children: "All Plinth modules should use the following GHC flags:"
    }), "\n", (0,jsx_runtime.jsx)(_components.pre, {
      children: (0,jsx_runtime.jsx)(_components.code, {
        children: "    -fno-ignore-interface-pragmas\n    -fno-omit-interface-pragmas\n    -fno-full-laziness\n    -fno-spec-constr\n    -fno-specialise\n    -fno-strictness\n    -fno-unbox-strict-fields\n    -fno-unbox-small-strict-fields\n"
      })
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: [(0,jsx_runtime.jsx)(_components.code, {
        children: "-fno-ignore-interface-pragmas"
      }), " and ", (0,jsx_runtime.jsx)(_components.code, {
        children: "-fno-omit-interface-pragmas"
      }), " ensure unfoldings of Plinth functions are available.\nThe rest are GHC optimizations that are generally bad for Plinth, and should thus be turned off."]
    }), "\n", (0,jsx_runtime.jsx)(_components.p, {
      children: "These flags can be specified either in a Haskell module, for example:"
    }), "\n", (0,jsx_runtime.jsx)(_components.pre, {
      children: (0,jsx_runtime.jsx)(_components.code, {
        children: "    {-# OPTIONS_GHC -fno-ignore-interface-pragmas #-}\n"
      })
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["or in a build file.\nFor example, if your project is built using Cabal, you can add the flags to the ", (0,jsx_runtime.jsx)(_components.code, {
        children: ".cabal"
      }), " files, like so:"]
    }), "\n", (0,jsx_runtime.jsx)(_components.pre, {
      children: (0,jsx_runtime.jsx)(_components.code, {
        children: "ghc-options:\n  -fno-ignore-interface-pragmas\n"
      })
    }), "\n", (0,jsx_runtime.jsxs)(_components.blockquote, {
      children: ["\n", (0,jsx_runtime.jsxs)(_components.p, {
        children: ["📌", " ", (0,jsx_runtime.jsx)(_components.strong, {
          children: "NOTE"
        })]
      }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
        children: ["This section only covers GHC flags, not Plinth compiler flags.\nA number of options can be passed to the Plinth compiler.\nSee ", (0,jsx_runtime.jsx)(_components.a, {
          href: "/pr-preview/docs/pr-7503/delve-deeper/plinth-compiler-options",
          children: "Plinth Compiler Options"
        }), " for details."]
      }), "\n"]
    }), "\n", (0,jsx_runtime.jsx)(_components.h3, {
      id: "pragmas",
      children: "Pragmas"
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["All functions and methods should have the ", (0,jsx_runtime.jsx)(_components.code, {
        children: "INLINEABLE"
      }), " pragma (not the ", (0,jsx_runtime.jsx)(_components.code, {
        children: "INLINE"
      }), " pragma, which should generally be avoided), so that their unfoldings are made available to the Plinth compiler."]
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["The ", (0,jsx_runtime.jsx)(_components.code, {
        children: "-fexpose-all-unfoldings"
      }), " flag also makes GHC expose all unfoldings, but unfoldings exposed this way can be more optimized than unfoldings exposed via ", (0,jsx_runtime.jsx)(_components.code, {
        children: "INLINEABLE"
      }), ".\nIn general, we do not want GHC to perform optimizations, since GHC optimizes a program based on the assumption that it has non-strict semantics and is evaluated lazily (call by need), which is not true for Plinth programs.\nTherefore, ", (0,jsx_runtime.jsx)(_components.code, {
        children: "INLINEABLE"
      }), " is preferred over ", (0,jsx_runtime.jsx)(_components.code, {
        children: "-fexpose-all-unfoldings"
      }), ", even though the latter is simpler."]
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: [(0,jsx_runtime.jsx)(_components.code, {
        children: "-fexpose-all-unfoldings"
      }), " can be useful for functions that are generated by GHC and do not have the ", (0,jsx_runtime.jsx)(_components.code, {
        children: "INLINEABLE"
      }), " pragma.\n", (0,jsx_runtime.jsx)(_components.code, {
        children: "-fspecialise"
      }), " and ", (0,jsx_runtime.jsx)(_components.code, {
        children: "-fspec-constr"
      }), " are two examples of optimizations that can generate such functions.\nThe most reliable solution, however, is to simply turn these optimizations off.\nAnother option is to bump ", (0,jsx_runtime.jsx)(_components.code, {
        children: "-funfolding-creation-threshold"
      }), " to make it more likely for GHC to retain unfoldings for functions without the ", (0,jsx_runtime.jsx)(_components.code, {
        children: "INLINEABLE"
      }), " pragma.\n", (0,jsx_runtime.jsx)(_components.code, {
        children: "-fexpose-all-unfoldings"
      }), " should be used as a last resort."]
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