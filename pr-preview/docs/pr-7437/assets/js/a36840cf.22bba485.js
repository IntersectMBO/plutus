"use strict";
(self["webpackChunkdocusaurus"] = self["webpackChunkdocusaurus"] || []).push([[42],{

/***/ 7806:
/***/ ((__unused_webpack_module, __webpack_exports__, __webpack_require__) => {

// ESM COMPAT FLAG
__webpack_require__.r(__webpack_exports__);

// EXPORTS
__webpack_require__.d(__webpack_exports__, {
  assets: () => (/* binding */ assets),
  contentTitle: () => (/* binding */ contentTitle),
  "default": () => (/* binding */ MDXContent),
  frontMatter: () => (/* binding */ frontMatter),
  metadata: () => (/* reexport */ site_docs_delve_deeper_encoding_md_a36_namespaceObject),
  toc: () => (/* binding */ toc)
});

;// ./.docusaurus/docusaurus-plugin-content-docs/default/site-docs-delve-deeper-encoding-md-a36.json
const site_docs_delve_deeper_encoding_md_a36_namespaceObject = /*#__PURE__*/JSON.parse('{"id":"delve-deeper/encoding","title":"Encoding Data Types in UPLC","description":"Untyped Plutus Core (UPLC) is a language based on untyped lambda calculus.","source":"@site/docs/delve-deeper/encoding.md","sourceDirName":"delve-deeper","slug":"/delve-deeper/encoding","permalink":"/pr-preview/docs/pr-7437/delve-deeper/encoding","draft":false,"unlisted":false,"editUrl":"https://github.com/IntersectMBO/plutus/edit/master/doc/docusaurus/docs/delve-deeper/encoding.md","tags":[],"version":"current","sidebarPosition":25,"frontMatter":{"sidebar_position":25},"sidebar":"tutorialSidebar","previous":{"title":"Understanding Script Hashes","permalink":"/pr-preview/docs/pr-7437/delve-deeper/understanding-script-hashes"},"next":{"title":"Further Resources","permalink":"/pr-preview/docs/pr-7437/category/further-resources"}}');
// EXTERNAL MODULE: ./node_modules/react/jsx-runtime.js
var jsx_runtime = __webpack_require__(4848);
// EXTERNAL MODULE: ./node_modules/@mdx-js/react/lib/index.js
var lib = __webpack_require__(8453);
;// ./docs/delve-deeper/encoding.md


const frontMatter = {
	sidebar_position: 25
};
const contentTitle = 'Encoding Data Types in UPLC';

const assets = {

};



const toc = [{
  "value": "Scott Encoding",
  "id": "scott-encoding",
  "level": 2
}, {
  "value": "Sums of Products",
  "id": "sums-of-products",
  "level": 2
}, {
  "value": "Data Objects",
  "id": "data-objects",
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
        id: "encoding-data-types-in-uplc",
        children: "Encoding Data Types in UPLC"
      })
    }), "\n", (0,jsx_runtime.jsx)(_components.p, {
      children: "Untyped Plutus Core (UPLC) is a language based on untyped lambda calculus.\nThe AST does not offer explicit support for encoding data types, but there are several alternative methods that can be used.\nDifferent surface languages and compilers may adopt different encoding methods."
    }), "\n", (0,jsx_runtime.jsx)(_components.h2, {
      id: "scott-encoding",
      children: "Scott Encoding"
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["Scott encoding (", (0,jsx_runtime.jsx)(_components.a, {
        href: "https://en.wikipedia.org/wiki/Mogensen%E2%80%93Scott_encoding",
        children: "Wikipedia"
      }), ") is the original method we adopted for the Plinth compiler, when targeting Plutus Core 1.0.0.\nIt can be done in untyped lambda calculus, and any language that extends untyped lambda calculus, including UPLC."]
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["As an example, consider the ", (0,jsx_runtime.jsx)(_components.code, {
        children: "These"
      }), " type, a value of ", (0,jsx_runtime.jsx)(_components.code, {
        children: "These"
      }), ", and a function that inspects a ", (0,jsx_runtime.jsx)(_components.code, {
        children: "These"
      }), ":"]
    }), "\n", (0,jsx_runtime.jsx)(_components.pre, {
      children: (0,jsx_runtime.jsx)(_components.code, {
        className: "language-haskell",
        children: "data These a b\n  = This a\n  | That b\n  | These a b\n\nx :: These Integer BuiltinString\nx = These 1 \"hello\"\n\nf :: These Integer BuiltinString -> Integer\nf = \\case\n  This a -> a\n  That b -> 42\n  These a b -> a\n"
      })
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["In Scott encoding, ", (0,jsx_runtime.jsx)(_components.code, {
        children: "x"
      }), " and ", (0,jsx_runtime.jsx)(_components.code, {
        children: "f"
      }), " are encoded as"]
    }), "\n", (0,jsx_runtime.jsx)(_components.pre, {
      children: (0,jsx_runtime.jsx)(_components.code, {
        children: "x = \\this that these -> these 1 \"hello\"\n\nf = \\x -> x (\\a -> a) (\\b -> 42) (\\a b -> a)\n"
      })
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["To illustrate a recursive data type, consider a value of ", (0,jsx_runtime.jsx)(_components.code, {
        children: "[Integer]"
      }), " and the ", (0,jsx_runtime.jsx)(_components.code, {
        children: "head"
      }), " and ", (0,jsx_runtime.jsx)(_components.code, {
        children: "tail"
      }), " functions:"]
    }), "\n", (0,jsx_runtime.jsx)(_components.pre, {
      children: (0,jsx_runtime.jsx)(_components.code, {
        className: "language-haskell",
        children: "xs :: [Integer]\nxs = [1, 2, 3]\n\nhead :: [Integer] -> Integer\nhead xs = case xs of\n  y : ys -> y\n  [] -> 42\n\ntail :: [Integer] -> [Integer]\ntail xs = case xs of\n  y : ys -> ys\n  [] -> []\n"
      })
    }), "\n", (0,jsx_runtime.jsx)(_components.p, {
      children: "These are encoded in Scott encoding as"
    }), "\n", (0,jsx_runtime.jsx)(_components.pre, {
      children: (0,jsx_runtime.jsx)(_components.code, {
        children: "xs = let c y ys = \\cons nil -> cons y ys\n         n = \\cons nil -> nil\n      in c 1 (c 2 (c 3 n))\n\nhead = \\xs -> xs (\\y ys -> y) 42\n\ntail = let n = \\cons nil -> nil\n        in \\xs -> xs (\\y ys -> ys) n\n"
      })
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["(There is no let-bindings in UPLC, but ", (0,jsx_runtime.jsx)(_components.code, {
        children: "let a = rhs in b"
      }), " can be read as ", (0,jsx_runtime.jsx)(_components.code, {
        children: "(\\a -> b) rhs"
      }), ".)"]
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["A related method of encoding data types is Church encoding (", (0,jsx_runtime.jsx)(_components.a, {
        href: "https://en.wikipedia.org/wiki/Church_encoding",
        children: "Wikipedia"
      }), ").\nIt is identical to Scott encoding for non-recursive data types, but differs for recursive data types.\nThe Church encoding of ", (0,jsx_runtime.jsx)(_components.code, {
        children: "xs"
      }), " and ", (0,jsx_runtime.jsx)(_components.code, {
        children: "head"
      }), " is:"]
    }), "\n", (0,jsx_runtime.jsx)(_components.pre, {
      children: (0,jsx_runtime.jsx)(_components.code, {
        children: "xs = \\c n -> c 1 (c 2 (c 3 n))\n\nhead = \\xs -> xs (\\y ys -> y) 42\n"
      })
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["However, ", (0,jsx_runtime.jsx)(_components.code, {
        children: "tail"
      }), " is much more complex and less efficient with Church encoding compared to Scott encoding.\nIntuitively, expressing ", (0,jsx_runtime.jsx)(_components.code, {
        children: "tail"
      }), " on a Church-encoded list involves taking a term where ", (0,jsx_runtime.jsx)(_components.code, {
        children: "c"
      }), " is applied a number of times, and producing a new term where ", (0,jsx_runtime.jsx)(_components.code, {
        children: "c"
      }), " is applied one less time - not a trivial task.\nThis is also the case with many other operations on Church encoded values, which is the main reason Scott encoding is chosen over Church encoding in the Plinth compiler."]
    }), "\n", (0,jsx_runtime.jsx)(_components.p, {
      children: "In Typed Plutus Core (TPLC), Scott encoding requires the ability to represent recursive types, hence the existence of isorecursive types in TPLC.\nChurch encoding, on the other hand, can be done in plain System F, a non-Turing-complete subset of TPLC."
    }), "\n", (0,jsx_runtime.jsx)(_components.h2, {
      id: "sums-of-products",
      children: "Sums of Products"
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["Sums of products (SOP) is a more direct way of encoding data types in UPLC and TPLC.\nIt requires adding two new kinds of AST nodes: ", (0,jsx_runtime.jsx)(_components.code, {
        children: "Case"
      }), " and ", (0,jsx_runtime.jsx)(_components.code, {
        children: "Constr"
      }), ".\n", (0,jsx_runtime.jsx)(_components.code, {
        children: "Constr i [arg]"
      }), " represents a value obtained by applying the ", (0,jsx_runtime.jsx)(_components.code, {
        children: "i"
      }), "th constructor of a data type to arguments ", (0,jsx_runtime.jsx)(_components.code, {
        children: "[arg]"
      }), ".\n", (0,jsx_runtime.jsx)(_components.code, {
        children: "Case scrut [handler]"
      }), " represents pattern matching on ", (0,jsx_runtime.jsx)(_components.code, {
        children: "scrut"
      }), " (which must evaluate to a ", (0,jsx_runtime.jsx)(_components.code, {
        children: "Constr"
      }), " term), invoking the appropriate handler depending on the constructor index."]
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["In the ", (0,jsx_runtime.jsx)(_components.code, {
        children: "These"
      }), " example above, ", (0,jsx_runtime.jsx)(_components.code, {
        children: "x"
      }), " and ", (0,jsx_runtime.jsx)(_components.code, {
        children: "f"
      }), " are encoded as"]
    }), "\n", (0,jsx_runtime.jsx)(_components.pre, {
      children: (0,jsx_runtime.jsx)(_components.code, {
        children: "x = constr 2 [1, \"hello\"]\n\nf = \\x -> case x [(\\a -> a), (\\b -> 42), (\\a b -> a)]\n"
      })
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["where 2 is the index of constructor ", (0,jsx_runtime.jsx)(_components.code, {
        children: "These"
      }), "."]
    }), "\n", (0,jsx_runtime.jsx)(_components.p, {
      children: "In the list example,"
    }), "\n", (0,jsx_runtime.jsx)(_components.pre, {
      children: (0,jsx_runtime.jsx)(_components.code, {
        children: "x = constr 0 [1, constr 0 [2, constr 0 [3, constr 1 []]]]\n\nhead = \\xs -> case xs [(\\y ys -> y), 42]\n\ntail = \\xs -> case xs [(\\y ys -> ys), constr 1 []]\n"
      })
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["SOP is cheaper and results in smaller scripts compared to Scott encoding, since it involves fewer lambdas and applications.\nThis is true both in terms of constant factors and asymptotically.\nFor example, pattern matching on a data type with ", (0,jsx_runtime.jsx)(_components.em, {
        children: "k"
      }), " constructors costs ", (0,jsx_runtime.jsx)(_components.em, {
        children: "O(k)"
      }), " since it involves ", (0,jsx_runtime.jsx)(_components.em, {
        children: "k"
      }), " applications, whereas it incurs constant cost with SOP."]
    }), "\n", (0,jsx_runtime.jsx)(_components.p, {
      children: "SOP is available as of Plutus Core 1.1.0, and is what the Plinth compiler uses when targeting Plutus Core 1.1.0.\nAt the moment, Plutus Core 1.1.0 is only supported in Plutus V3 and cannot be used in V1 or V2."
    }), "\n", (0,jsx_runtime.jsx)(_components.h2, {
      id: "data-objects",
      children: "Data Objects"
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: [(0,jsx_runtime.jsx)(_components.a, {
        href: "https://plutus.cardano.intersectmbo.org/haddock/latest/plutus-core/PlutusCore-Data.html#t:Data",
        children: "Data"
      }), " is a builtin type in Untyped Plutus Core.\nIt is intended primarily for data interchange, specifically for encoding datums, redeemers, and script contexts.\nData makes it simpler to create datums and redeemers using various languages and tools, or even manually, which is much easier than constructing UPLC terms."]
    }), "\n", (0,jsx_runtime.jsx)(_components.p, {
      children: "Data objects can be used to encode data types (though not as expressive as Scott encoding or SOP, since Data objects cannot contain functions).\nHowever, as with other data serialization/interchange formats (e.g., JSON or Protobuf-generated types), writing business logic directly using Data objects is inefficient and cumbersome.\nInstead, the standard practice is to validate the incoming data, turn it into proper, efficient domain types, operate on those domain types, and if necessary, convert them back to the serialization/interchange format at the end."
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["For UPLC, the proper domain type is Scott or SOP terms.\nThus a standard way of writing Plinth is to immediately validate the incoming Data objects and turning them into Scott or SOP terms via ", (0,jsx_runtime.jsx)(_components.code, {
        children: "unsafeFromBuiltinData"
      }), " (see ", (0,jsx_runtime.jsx)(_components.a, {
        href: "/pr-preview/docs/pr-7437/working-with-scripts/ledger-language-version",
        children: "Plutus Ledger Language Version"
      }), "), before working with them.\nThen, after all computation is done, convert the output datums back into Data objects if needed."]
    }), "\n", (0,jsx_runtime.jsx)(_components.p, {
      children: "However, when it comes to Plutus scripts, working directly with Data can sometimes be beneficial, especially for scripts with simpler logic.\nThis is because script size and execution units (CPU and memory) are much scarcer resources for Plutus scripts compared to regular programs.\nSince script arguments (datums, redeemers, script contexts) and output datums are encoded as Data objects, the overhead of converting the arguments and output to/from Scott/SOP terms can sometimes outweigh the benefits, especially for scripts with simple business logic.\nIn extreme scenarios where an argument isn’t even used, the validation and conversion process becomes entirely unnecessary."
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["Another benefits of Data objects is efficient equality checks.\nWhile working with Data objects is generally slower than using Scott/SOP terms, equality checks can be faster due to the ", (0,jsx_runtime.jsx)(_components.code, {
        children: "equalsData"
      }), " builtin function."]
    }), "\n", (0,jsx_runtime.jsx)(_components.p, {
      children: "The optimal encoding method may vary for different types within the same script.\nGenerally speaking, the more a data type is used, the more advantageous it is to use Scott or SOP encoding, compared to manipulating Data objects directly, as the efficiency of Scott/SOP can justify the conversion overhead between Data and Scott/SOP."
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["When writing Plinth, it is possible to have your data types encoded using Data objects, rather than Scott/SOP, by utilizing the ", (0,jsx_runtime.jsx)(_components.code, {
        children: "asData"
      }), " mechanism.\nFor more details, see ", (0,jsx_runtime.jsx)(_components.a, {
        href: "/pr-preview/docs/pr-7437/working-with-scripts/optimizing-scripts-with-asData",
        children: "Optimizing Scripts with asData"
      }), "."]
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["As for script context, we are actively working on a Data-encoded script context API, though it is still in development. In the absence of that, you can also interact with Data objects directly using builtin functions that operate on Data.\nFor example, the following function extracts the ", (0,jsx_runtime.jsx)(_components.code, {
        children: "ScriptInfo"
      }), " field from Plutus V3's ", (0,jsx_runtime.jsx)(_components.code, {
        children: "ScriptContext"
      }), ", which is its third field:"]
    }), "\n", (0,jsx_runtime.jsx)(_components.pre, {
      children: (0,jsx_runtime.jsx)(_components.code, {
        className: "language-haskell",
        children: "import PlutusTx.Builtins.Internal qualified as BI\n\ngetScriptInfo :: BuiltinData -> BuiltinData\ngetScriptInfo scriptContext =\n  let ds = BI.snd (BI.unsafeDataAsConstr scriptContext)\n   in -- extract the third element of the list\n      BI.head (BI.tail (BI.tail ds))\n"
      })
    }), "\n", (0,jsx_runtime.jsx)(_components.p, {
      children: "This is of course much less type safe compared to working with regular data types, so exercise caution."
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