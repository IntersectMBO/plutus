"use strict";
(globalThis["webpackChunkdocusaurus"] = globalThis["webpackChunkdocusaurus"] || []).push([[7944],{

/***/ 3856
(__unused_webpack_module, __webpack_exports__, __webpack_require__) {

// ESM COMPAT FLAG
__webpack_require__.r(__webpack_exports__);

// EXPORTS
__webpack_require__.d(__webpack_exports__, {
  assets: () => (/* binding */ assets),
  contentTitle: () => (/* binding */ contentTitle),
  "default": () => (/* binding */ MDXContent),
  frontMatter: () => (/* binding */ frontMatter),
  metadata: () => (/* reexport */ site_docs_upcoming_features_builtin_values_md_36d_namespaceObject),
  toc: () => (/* binding */ toc)
});

;// ./.docusaurus/docusaurus-plugin-content-docs/default/site-docs-upcoming-features-builtin-values-md-36d.json
const site_docs_upcoming_features_builtin_values_md_36d_namespaceObject = /*#__PURE__*/JSON.parse('{"id":"upcoming-features/builtin-values","title":"Builtin Values","description":"These functions become available at a protocol version. The functions from CIP-0153 are available to Plutus V1, V2 and V3 scripts from protocol version 11. The functions from CIP-0168 (policies, assetCount, keepPolicies and dropPolicies) are available to all Plutus versions from protocol version 12, which also introduces Plutus V4 with all of them. The ledger rejects a script that uses a function before its protocol version.","source":"@site/docs/upcoming-features/builtin-values.md","sourceDirName":"upcoming-features","slug":"/upcoming-features/builtin-values","permalink":"/pr-preview/docs/pr-8041/upcoming-features/builtin-values","draft":false,"unlisted":false,"editUrl":"https://github.com/IntersectMBO/plutus/edit/master/doc/docusaurus/docs/upcoming-features/builtin-values.md","tags":[],"version":"current","sidebarPosition":2,"frontMatter":{"sidebar_position":2},"sidebar":"tutorialSidebar","previous":{"title":"Builtin Arrays","permalink":"/pr-preview/docs/pr-8041/upcoming-features/builtin-arrays"},"next":{"title":"Troubleshooting","permalink":"/pr-preview/docs/pr-8041/troubleshooting"}}');
// EXTERNAL MODULE: ./node_modules/react/jsx-runtime.js
var jsx_runtime = __webpack_require__(4848);
// EXTERNAL MODULE: ./node_modules/@mdx-js/react/lib/index.js
var lib = __webpack_require__(8453);
;// ./docs/upcoming-features/builtin-values.md


const frontMatter = {
	sidebar_position: 2
};
const contentTitle = 'Builtin Values';

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
    p: "p",
    pre: "pre",
    strong: "strong",
    ...(0,lib/* useMDXComponents */.R)(),
    ...props.components
  }, {Details, LiteralInclude} = _components;
  if (!Details) _missingMdxReference("Details", true);
  if (!LiteralInclude) _missingMdxReference("LiteralInclude", true);
  return (0,jsx_runtime.jsxs)(jsx_runtime.Fragment, {
    children: [(0,jsx_runtime.jsx)(_components.header, {
      children: (0,jsx_runtime.jsx)(_components.h1, {
        id: "builtin-values",
        children: "Builtin Values"
      })
    }), "\n", (0,jsx_runtime.jsx)(_components.admonition, {
      title: "Upcoming Feature",
      type: "danger",
      children: (0,jsx_runtime.jsxs)(_components.p, {
        children: [(0,jsx_runtime.jsx)(_components.strong, {
          children: "These functions become available at a protocol version."
        }), " The functions from ", (0,jsx_runtime.jsx)(_components.a, {
          href: "https://cips.cardano.org/cip/CIP-0153",
          children: "CIP-0153"
        }), " are available to Plutus V1, V2 and V3 scripts from protocol version 11. The functions from ", (0,jsx_runtime.jsx)(_components.a, {
          href: "https://cips.cardano.org/cip/CIP-0168",
          children: "CIP-0168"
        }), " (", (0,jsx_runtime.jsx)(_components.code, {
          children: "policies"
        }), ", ", (0,jsx_runtime.jsx)(_components.code, {
          children: "assetCount"
        }), ", ", (0,jsx_runtime.jsx)(_components.code, {
          children: "keepPolicies"
        }), " and ", (0,jsx_runtime.jsx)(_components.code, {
          children: "dropPolicies"
        }), ") are available to all Plutus versions from protocol version 12, which also introduces Plutus V4 with all of them. The ledger rejects a script that uses a function before its protocol version."]
      })
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: [(0,jsx_runtime.jsx)(_components.code, {
        children: "BuiltinValue"
      }), " is a Plutus Core type for multi-asset values: a map from currency symbol to a map from token name to quantity. The script context carries values as ", (0,jsx_runtime.jsx)(_components.code, {
        children: "Data"
      }), ", and checking a token in that encoding means walking it. Builtin operations on a ", (0,jsx_runtime.jsx)(_components.code, {
        children: "BuiltinValue"
      }), " look up or insert a token in logarithmic time, and keep, drop or count the policies and assets of a value in a single call."]
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: [(0,jsx_runtime.jsx)(_components.strong, {
        children: "Conversion cost:"
      }), " a ", (0,jsx_runtime.jsx)(_components.code, {
        children: "BuiltinValue"
      }), " is decoded from ", (0,jsx_runtime.jsx)(_components.code, {
        children: "Data"
      }), " with ", (0,jsx_runtime.jsx)(_components.code, {
        children: "unsafeDataAsValue"
      }), ", which validates the whole encoding, so its cost grows with the size of the value. Decode a value once and reuse the result."]
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["Functions for working with ", (0,jsx_runtime.jsx)(_components.code, {
        children: "BuiltinValue"
      }), " are available in the ", (0,jsx_runtime.jsx)(_components.code, {
        children: "PlutusTx.Builtins"
      }), " module:"]
    }), "\n", (0,jsx_runtime.jsx)(_components.pre, {
      children: (0,jsx_runtime.jsx)(_components.code, {
        className: "language-haskell",
        children: "import PlutusTx.Builtins\n  ( BuiltinValue\n  , unsafeDataAsValue\n  , mkValue\n  , lookupCoin\n  , insertCoin\n  , unionValue\n  , scaleValue\n  , valueContains\n  , policies\n  , assetCount\n  , keepPolicies\n  , dropPolicies\n  )\n"
      })
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["The ", (0,jsx_runtime.jsx)(_components.a, {
        href: "https://plutus.cardano.intersectmbo.org/haddock/latest/plutus-tx/PlutusTx-Builtins.html#g:14",
        children: "Haddock documentation"
      }), " of these functions states what each returns and when it fails, and the ", (0,jsx_runtime.jsx)(_components.a, {
        href: "https://plutus.cardano.intersectmbo.org/resources/plutus-core-spec.pdf",
        children: "Plutus Core specification"
      }), " defines them precisely."]
    }), "\n", (0,jsx_runtime.jsxs)(Details, {
      children: [(0,jsx_runtime.jsx)("summary", {
        children: "Example: an output that keeps a protocol's tokens"
      }), (0,jsx_runtime.jsx)(LiteralInclude, {
        file: "Example/Builtin/Value/Main.hs",
        language: "haskell"
      }), (0,jsx_runtime.jsxs)(_components.p, {
        children: ["Running it evaluates the check twice: the output that keeps the protocol's ", (0,jsx_runtime.jsx)(_components.code, {
          children: "state"
        }), " token passes, and the output that loses it fails."]
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