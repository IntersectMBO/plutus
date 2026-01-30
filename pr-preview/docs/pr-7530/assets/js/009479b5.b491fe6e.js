"use strict";
(self["webpackChunkdocusaurus"] = self["webpackChunkdocusaurus"] || []).push([[295],{

/***/ 4884:
/***/ ((__unused_webpack_module, __webpack_exports__, __webpack_require__) => {

// ESM COMPAT FLAG
__webpack_require__.r(__webpack_exports__);

// EXPORTS
__webpack_require__.d(__webpack_exports__, {
  assets: () => (/* binding */ assets),
  contentTitle: () => (/* binding */ contentTitle),
  "default": () => (/* binding */ MDXContent),
  frontMatter: () => (/* binding */ frontMatter),
  metadata: () => (/* reexport */ site_docs_upcoming_features_builtin_arrays_md_009_namespaceObject),
  toc: () => (/* binding */ toc)
});

;// ./.docusaurus/docusaurus-plugin-content-docs/default/site-docs-upcoming-features-builtin-arrays-md-009.json
const site_docs_upcoming_features_builtin_arrays_md_009_namespaceObject = /*#__PURE__*/JSON.parse('{"id":"upcoming-features/builtin-arrays","title":"Builtin Arrays","description":"This is an upcoming feature that is not yet available for use. The BuiltinArray type and related functions are currently under development and will be included in a future version of Plutus. This documentation is provided for preview purposes only.","source":"@site/docs/upcoming-features/builtin-arrays.md","sourceDirName":"upcoming-features","slug":"/upcoming-features/builtin-arrays","permalink":"/pr-preview/docs/pr-7530/upcoming-features/builtin-arrays","draft":false,"unlisted":false,"editUrl":"https://github.com/IntersectMBO/plutus/edit/master/doc/docusaurus/docs/upcoming-features/builtin-arrays.md","tags":[],"version":"current","sidebarPosition":1,"frontMatter":{"sidebar_position":1},"sidebar":"tutorialSidebar","previous":{"title":"Upcoming Features","permalink":"/pr-preview/docs/pr-7530/category/upcoming-features"},"next":{"title":"Troubleshooting","permalink":"/pr-preview/docs/pr-7530/troubleshooting"}}');
// EXTERNAL MODULE: ./node_modules/react/jsx-runtime.js
var jsx_runtime = __webpack_require__(4848);
// EXTERNAL MODULE: ./node_modules/@mdx-js/react/lib/index.js
var lib = __webpack_require__(8453);
;// ./docs/upcoming-features/builtin-arrays.md


const frontMatter = {
	sidebar_position: 1
};
const contentTitle = 'Builtin Arrays';

const assets = {

};



const toc = [{
  "value": "Choosing Arrays vs Lists",
  "id": "choosing-arrays-vs-lists",
  "level": 2
}];
function _createMdxContent(props) {
  const _components = {
    admonition: "admonition",
    code: "code",
    h1: "h1",
    h2: "h2",
    header: "header",
    img: "img",
    li: "li",
    p: "p",
    pre: "pre",
    strong: "strong",
    ul: "ul",
    ...(0,lib/* useMDXComponents */.R)(),
    ...props.components
  }, {Details, LiteralInclude} = _components;
  if (!Details) _missingMdxReference("Details", true);
  if (!LiteralInclude) _missingMdxReference("LiteralInclude", true);
  return (0,jsx_runtime.jsxs)(jsx_runtime.Fragment, {
    children: [(0,jsx_runtime.jsx)(_components.header, {
      children: (0,jsx_runtime.jsx)(_components.h1, {
        id: "builtin-arrays",
        children: "Builtin Arrays"
      })
    }), "\n", (0,jsx_runtime.jsx)(_components.admonition, {
      title: "Upcoming Feature",
      type: "danger",
      children: (0,jsx_runtime.jsxs)(_components.p, {
        children: [(0,jsx_runtime.jsx)(_components.strong, {
          children: "This is an upcoming feature that is not yet available for use."
        }), " The ", (0,jsx_runtime.jsx)(_components.code, {
          children: "BuiltinArray"
        }), " type and related functions are currently under development and will be included in a future version of Plutus. This documentation is provided for preview purposes only."]
      })
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["For multiple lookups by index, ", (0,jsx_runtime.jsx)(_components.code, {
        children: "BuiltinArray"
      }), " provides significantly better performance than lists. The key advantage is in the lookup operations themselves."]
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: [(0,jsx_runtime.jsx)(_components.strong, {
        children: "Lookup Performance Comparison:"
      }), "\nA single lookup at index 99 of a 100-element data structure shows that the CPU cost for lookup on a standard Plinth list (", (0,jsx_runtime.jsx)(_components.code, {
        children: "[Integer]"
      }), ", a sum-of-products type) is ", (0,jsx_runtime.jsx)(_components.strong, {
        children: "206 times higher"
      }), " than on a ", (0,jsx_runtime.jsx)(_components.code, {
        children: "BuiltinArray"
      }), "."]
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: [(0,jsx_runtime.jsx)(_components.strong, {
        children: "Important Considerations:"
      }), "\nCurrently, ", (0,jsx_runtime.jsx)(_components.code, {
        children: "BuiltinArray"
      }), " creation is implemented as conversion from lists, which involves traversing the entire list. This conversion cost should be factored into your performance calculations - the dramatic lookup performance improvement needs to be amortized over multiple lookups to justify the conversion overhead."]
    }), "\n", (0,jsx_runtime.jsx)(_components.p, {
      children: "As a rule of thumb, if you only need to perform a single lookup, the conversion cost may not be worthwhile. The benefits become apparent when performing several lookups on the same data structure."
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: [(0,jsx_runtime.jsx)(_components.strong, {
        children: "Future Development:"
      }), "\nIn future language versions, arrays are planned to be added to the ", (0,jsx_runtime.jsx)(_components.code, {
        children: "Data"
      }), "-encoded ", (0,jsx_runtime.jsx)(_components.code, {
        children: "ScriptContext"
      }), " precisely to avoid these high conversion costs, allowing arrays to be provided directly without requiring conversion from lists."]
    }), "\n", (0,jsx_runtime.jsx)(_components.h2, {
      id: "choosing-arrays-vs-lists",
      children: "Choosing Arrays vs Lists"
    }), "\n", (0,jsx_runtime.jsx)(_components.p, {
      children: "When designing your data structures, consider your access patterns:"
    }), "\n", (0,jsx_runtime.jsx)(_components.p, {
      children: (0,jsx_runtime.jsx)(_components.strong, {
        children: "Choose arrays when:"
      })
    }), "\n", (0,jsx_runtime.jsxs)(_components.ul, {
      children: ["\n", (0,jsx_runtime.jsxs)(_components.li, {
        children: ["You need multiple index-based lookups (e.g., ", (0,jsx_runtime.jsx)(_components.code, {
          children: "arr[42]"
        }), ", ", (0,jsx_runtime.jsx)(_components.code, {
          children: "arr[17]"
        }), ")"]
      }), "\n", (0,jsx_runtime.jsx)(_components.li, {
        children: "Your access pattern is primarily random access rather than sequential"
      }), "\n", (0,jsx_runtime.jsx)(_components.li, {
        children: "The data structure size is relatively stable after creation"
      }), "\n", (0,jsx_runtime.jsx)(_components.li, {
        children: "You're building lookup tables or similar structures"
      }), "\n"]
    }), "\n", (0,jsx_runtime.jsx)(_components.p, {
      children: (0,jsx_runtime.jsx)(_components.strong, {
        children: "Choose lists when:"
      })
    }), "\n", (0,jsx_runtime.jsxs)(_components.ul, {
      children: ["\n", (0,jsx_runtime.jsx)(_components.li, {
        children: "You primarily need sequential access (head/tail operations, pattern matching)"
      }), "\n", (0,jsx_runtime.jsxs)(_components.li, {
        children: ["You frequently prepend elements (", (0,jsx_runtime.jsx)(_components.code, {
          children: ":"
        }), " operator)"]
      }), "\n", (0,jsx_runtime.jsx)(_components.li, {
        children: "Your access pattern is mostly single-pass iteration"
      }), "\n", (0,jsx_runtime.jsx)(_components.li, {
        children: "You're following functional programming patterns that work naturally with lists"
      }), "\n"]
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: [(0,jsx_runtime.jsx)(_components.strong, {
        children: "Current limitations:"
      }), "\nNote that you can't always choose arrays \"from the start\" because data often comes from external sources as lists (like elements in ", (0,jsx_runtime.jsx)(_components.code, {
        children: "ScriptContext"
      }), "). This is why the conversion scenario is currently common, and why future versions plan to provide arrays directly in these contexts."]
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["Functions for working with ", (0,jsx_runtime.jsx)(_components.code, {
        children: "BuiltinArray"
      }), " are available in the ", (0,jsx_runtime.jsx)(_components.code, {
        children: "PlutusTx.Builtins"
      }), " module:"]
    }), "\n", (0,jsx_runtime.jsx)(_components.pre, {
      children: (0,jsx_runtime.jsx)(_components.code, {
        className: "language-haskell",
        children: "import PlutusTx.Builtins \n  ( BuiltinArray\n  , indexArray\n  , listToArray\n  , lengthOfArray\n  )\n"
      })
    }), "\n", (0,jsx_runtime.jsxs)(Details, {
      children: [(0,jsx_runtime.jsx)("summary", {
        children: "Lookup comparison: SOP List vs. BuiltinList vs. BuiltinArray"
      }), (0,jsx_runtime.jsx)(LiteralInclude, {
        file: "Example/Builtin/Array/Main.hs",
        language: "haskell"
      }), (0,jsx_runtime.jsxs)(_components.p, {
        children: ["Result of the evaluation:\n", (0,jsx_runtime.jsx)(_components.img, {
          alt: "BuiltinArray Performance Comparison",
          src: (__webpack_require__(6179)/* ["default"] */ .A) + "",
          width: "1128",
          height: "814"
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
function _missingMdxReference(id, component) {
  throw new Error("Expected " + (component ? "component" : "object") + " `" + id + "` to be defined: you likely forgot to import, pass, or provide it.");
}



/***/ }),

/***/ 6179:
/***/ ((__unused_webpack_module, __webpack_exports__, __webpack_require__) => {

/* harmony export */ __webpack_require__.d(__webpack_exports__, {
/* harmony export */   A: () => (__WEBPACK_DEFAULT_EXPORT__)
/* harmony export */ });
/* harmony default export */ const __WEBPACK_DEFAULT_EXPORT__ = (__webpack_require__.p + "assets/images/Screenshot-22294853a6885c600fa937d4159ce2c2.png");

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