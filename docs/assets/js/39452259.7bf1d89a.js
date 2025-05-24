"use strict";
(self["webpackChunkdocusaurus"] = self["webpackChunkdocusaurus"] || []).push([[1836],{

/***/ 7325:
/***/ ((__unused_webpack_module, __webpack_exports__, __webpack_require__) => {

// ESM COMPAT FLAG
__webpack_require__.r(__webpack_exports__);

// EXPORTS
__webpack_require__.d(__webpack_exports__, {
  assets: () => (/* binding */ assets),
  contentTitle: () => (/* binding */ contentTitle),
  "default": () => (/* binding */ MDXContent),
  frontMatter: () => (/* binding */ frontMatter),
  metadata: () => (/* reexport */ site_docs_using_plinth_special_functions_and_types_md_394_namespaceObject),
  toc: () => (/* binding */ toc)
});

;// ./.docusaurus/docusaurus-plugin-content-docs/default/site-docs-using-plinth-special-functions-and-types-md-394.json
const site_docs_using_plinth_special_functions_and_types_md_394_namespaceObject = /*#__PURE__*/JSON.parse('{"id":"using-plinth/special-functions-and-types","title":"Special Functions and Types","description":"Normally, the Plinth compiler compiles a Haskell identifier by obtaining and compiling its definition (also known as unfolding), and creating a term binding in PIR, an intermediate representation used by the Plinth compiler.","source":"@site/docs/using-plinth/special-functions-and-types.md","sourceDirName":"using-plinth","slug":"/using-plinth/special-functions-and-types","permalink":"/docs/using-plinth/special-functions-and-types","draft":false,"unlisted":false,"editUrl":"https://github.com/IntersectMBO/plutus/edit/master/doc/docusaurus/docs/using-plinth/special-functions-and-types.md","tags":[],"version":"current","sidebarPosition":25,"frontMatter":{"sidebar_position":25},"sidebar":"tutorialSidebar","previous":{"title":"GHC Extensions, Flags and Pragmas","permalink":"/docs/using-plinth/extensions-flags-pragmas"},"next":{"title":"Inspecting Compilation and Compiled Code","permalink":"/docs/using-plinth/inspecting"}}');
// EXTERNAL MODULE: ./node_modules/react/jsx-runtime.js
var jsx_runtime = __webpack_require__(4848);
// EXTERNAL MODULE: ./node_modules/@mdx-js/react/lib/index.js
var lib = __webpack_require__(8453);
;// ./docs/using-plinth/special-functions-and-types.md


const frontMatter = {
	sidebar_position: 25
};
const contentTitle = 'Special Functions and Types';

const assets = {

};



const toc = [{
  "value": "Builtin Functions and Types",
  "id": "builtin-functions-and-types",
  "level": 2
}, {
  "value": "<code>PlutusTx.Bool.&amp;&amp;</code> and <code>PlutusTx.Bool.||</code>",
  "id": "plutustxbool-and-plutustxbool",
  "level": 2
}, {
  "value": "<code>IsString</code> Instances",
  "id": "isstring-instances",
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
    ...(0,lib/* useMDXComponents */.R)(),
    ...props.components
  };
  return (0,jsx_runtime.jsxs)(jsx_runtime.Fragment, {
    children: [(0,jsx_runtime.jsx)(_components.header, {
      children: (0,jsx_runtime.jsx)(_components.h1, {
        id: "special-functions-and-types",
        children: "Special Functions and Types"
      })
    }), "\n", (0,jsx_runtime.jsx)(_components.p, {
      children: "Normally, the Plinth compiler compiles a Haskell identifier by obtaining and compiling its definition (also known as unfolding), and creating a term binding in PIR, an intermediate representation used by the Plinth compiler.\nTypes are compiled in a similar manner, by compiling the type's definition and generating a type or datatype binding in PIR."
    }), "\n", (0,jsx_runtime.jsx)(_components.p, {
      children: "However, there are certain special functions and types that aren't compiled this way.\nRather, they are handled specially and directly converted to terms or types in PIR.\nIt is useful to be aware of these, as these functions and types work differently than regular user-defined functions and types, and cannot be defined in user space."
    }), "\n", (0,jsx_runtime.jsx)(_components.h2, {
      id: "builtin-functions-and-types",
      children: "Builtin Functions and Types"
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["There are a number of builtin functions and builtin types in UPLC.\nThe list of builtin functions and types can be found in the ", (0,jsx_runtime.jsx)(_components.a, {
        href: "https://plutus.cardano.intersectmbo.org/resources/plutus-core-spec.pdf",
        children: "Plutus Core Specification"
      }), "."]
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["In ", (0,jsx_runtime.jsx)(_components.a, {
        href: "https://plutus.cardano.intersectmbo.org/haddock/latest/plutus-tx/PlutusTx-Builtins-Internal.html",
        children: (0,jsx_runtime.jsx)(_components.code, {
          children: "PlutusTx.Builtins.Internal"
        })
      }), ", functions marked ", (0,jsx_runtime.jsx)(_components.code, {
        children: "OPAQUE"
      }), " are directly converted to the corresponding builtin function.\nFor instance, ", (0,jsx_runtime.jsx)(_components.code, {
        children: "PlutusTx.Builtins.Internal.addInteger"
      }), " is converted to UPLC term ", (0,jsx_runtime.jsx)(_components.code, {
        children: "(builtin addInteger)"
      }), ".\nUsing the ", (0,jsx_runtime.jsx)(_components.code, {
        children: "OPAQUE"
      }), " pragma prevents GHC from inlining these functions, allowing the Plinth compiler to determine where exactly they are invoked, and compile them appropriately."]
    }), "\n", (0,jsx_runtime.jsx)(_components.p, {
      children: "Builtin types are handled similarly: rather than compiling their definition, they are directly converted to builtin types in PIR.\nIn UPLC, most types are erased, but constants remain tagged with the corresponding builtin types."
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["Since functions in ", (0,jsx_runtime.jsx)(_components.code, {
        children: "PlutusTx.Builtins.Internal"
      }), " correspond to builtin functions that operate on builtin types, it's usually preferable to use functions in ", (0,jsx_runtime.jsx)(_components.a, {
        href: "https://plutus.cardano.intersectmbo.org/haddock/latest/plutus-tx/PlutusTx-Builtins.html",
        children: (0,jsx_runtime.jsx)(_components.code, {
          children: "PlutusTx.Builtins"
        })
      }), ".\nThese functions wrap their counterparts in the ", (0,jsx_runtime.jsx)(_components.code, {
        children: "Internal"
      }), " module, and operate on standard Haskell types whenever possible, which are often more convenient."]
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["Aside from ", (0,jsx_runtime.jsx)(_components.code, {
        children: "BuiltinInteger"
      }), ", which is an alias for ", (0,jsx_runtime.jsx)(_components.code, {
        children: "Integer"
      }), ", other builtin types are distinct from their corresponding Haskell types.\nNot all of these Haskell types can be used in Plinth.\nFor instance, ", (0,jsx_runtime.jsx)(_components.code, {
        children: "String"
      }), " and ", (0,jsx_runtime.jsx)(_components.code, {
        children: "ByteString"
      }), " are not supported, whereas regular algebraic data types like ", (0,jsx_runtime.jsx)(_components.code, {
        children: "Bool"
      }), ", lists and pairs are supported."]
    }), "\n", (0,jsx_runtime.jsxs)(_components.h2, {
      id: "plutustxbool-and-plutustxbool",
      children: [(0,jsx_runtime.jsx)(_components.code, {
        children: "PlutusTx.Bool.&&"
      }), " and ", (0,jsx_runtime.jsx)(_components.code, {
        children: "PlutusTx.Bool.||"
      })]
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["In ", (0,jsx_runtime.jsx)(_components.a, {
        href: "https://plutus.cardano.intersectmbo.org/haddock/latest/plutus-tx/PlutusTx-Bool.html",
        children: (0,jsx_runtime.jsx)(_components.code, {
          children: "PlutusTx.Bool"
        })
      }), ", the ", (0,jsx_runtime.jsx)(_components.code, {
        children: "&&"
      }), " and ", (0,jsx_runtime.jsx)(_components.code, {
        children: "||"
      }), " operators are handled specially in the plugin to ensure they can short-circuit.\nIn most strict languages, these operators are special and cannot be defined by users, which is also the case for Plinth."]
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["Note that in regular Haskell, ", (0,jsx_runtime.jsx)(_components.code, {
        children: "&&"
      }), " and ", (0,jsx_runtime.jsx)(_components.code, {
        children: "||"
      }), " are ", (0,jsx_runtime.jsx)(_components.em, {
        children: "not"
      }), " special, as Haskell supports non-strict function applications (and it is the default behavior)."]
    }), "\n", (0,jsx_runtime.jsxs)(_components.h2, {
      id: "isstring-instances",
      children: [(0,jsx_runtime.jsx)(_components.code, {
        children: "IsString"
      }), " Instances"]
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: [(0,jsx_runtime.jsx)(_components.a, {
        href: "https://hackage.haskell.org/package/base/docs/Data-String.html#t:IsString",
        children: (0,jsx_runtime.jsx)(_components.code, {
          children: "IsString"
        })
      }), " is a type class from ", (0,jsx_runtime.jsx)(_components.code, {
        children: "base"
      }), ", and can be used along with the ", (0,jsx_runtime.jsx)(_components.code, {
        children: "OverloadedStrings"
      }), " language extension to convert string literals to types other than ", (0,jsx_runtime.jsx)(_components.code, {
        children: "String"
      }), "."]
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["Most ", (0,jsx_runtime.jsx)(_components.code, {
        children: "IsString"
      }), " instances are unsupported by the Plinth compiler, other than a few special cases.\nAt present, it provides support for ", (0,jsx_runtime.jsx)(_components.code, {
        children: "BuiltinString"
      }), " and ", (0,jsx_runtime.jsx)(_components.code, {
        children: "BuiltinByteString"
      }), ", with the caveat that the ", (0,jsx_runtime.jsx)(_components.code, {
        children: "fromString"
      }), " method must be applied to a string literal."]
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["As previously noted, ", (0,jsx_runtime.jsx)(_components.code, {
        children: "String"
      }), " and ", (0,jsx_runtime.jsx)(_components.code, {
        children: "ByteString"
      }), " are not available in Plinth, so you'll need to use ", (0,jsx_runtime.jsx)(_components.code, {
        children: "BuiltinString"
      }), " or ", (0,jsx_runtime.jsx)(_components.code, {
        children: "BulitinByteString"
      }), ".\nThis lets you write ", (0,jsx_runtime.jsx)(_components.code, {
        children: "\"hello\" :: BuiltinString"
      }), " and ", (0,jsx_runtime.jsx)(_components.code, {
        children: "\"world\" :: BuiltinByteString"
      }), " in Plinth, which is quite convenient."]
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