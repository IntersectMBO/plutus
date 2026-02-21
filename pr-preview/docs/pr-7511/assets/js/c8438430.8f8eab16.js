"use strict";
(self["webpackChunkdocusaurus"] = self["webpackChunkdocusaurus"] || []).push([[4312],{

/***/ 6054:
/***/ ((__unused_webpack_module, __webpack_exports__, __webpack_require__) => {

// ESM COMPAT FLAG
__webpack_require__.r(__webpack_exports__);

// EXPORTS
__webpack_require__.d(__webpack_exports__, {
  assets: () => (/* binding */ assets),
  contentTitle: () => (/* binding */ contentTitle),
  "default": () => (/* binding */ MDXContent),
  frontMatter: () => (/* binding */ frontMatter),
  metadata: () => (/* reexport */ site_docs_delve_deeper_casing_constants_md_c84_namespaceObject),
  toc: () => (/* binding */ toc)
});

;// ./.docusaurus/docusaurus-plugin-content-docs/default/site-docs-delve-deeper-casing-constants-md-c84.json
const site_docs_delve_deeper_casing_constants_md_c84_namespaceObject = /*#__PURE__*/JSON.parse('{"id":"delve-deeper/casing-constants","title":"Case-splitting on constants","description":"This use of case in UPLC was introduced with protocol version 11 and requires","source":"@site/docs/delve-deeper/casing-constants.md","sourceDirName":"delve-deeper","slug":"/delve-deeper/casing-constants","permalink":"/pr-preview/docs/pr-7511/delve-deeper/casing-constants","draft":false,"unlisted":false,"editUrl":"https://github.com/IntersectMBO/plutus/edit/master/doc/docusaurus/docs/delve-deeper/casing-constants.md","tags":[],"version":"current","sidebarPosition":26,"frontMatter":{"sidebar_position":26},"sidebar":"tutorialSidebar","previous":{"title":"Encoding Data Types in UPLC","permalink":"/pr-preview/docs/pr-7511/delve-deeper/encoding"},"next":{"title":"Further Resources","permalink":"/pr-preview/docs/pr-7511/category/further-resources"}}');
// EXTERNAL MODULE: ./node_modules/react/jsx-runtime.js
var jsx_runtime = __webpack_require__(4848);
// EXTERNAL MODULE: ./node_modules/@mdx-js/react/lib/index.js
var lib = __webpack_require__(8453);
;// ./docs/delve-deeper/casing-constants.md


const frontMatter = {
	sidebar_position: 26
};
const contentTitle = 'Case-splitting on constants';

const assets = {

};



const toc = [{
  "value": "Usage from Plinth",
  "id": "usage-from-plinth",
  "level": 2
}, {
  "value": "Supported types",
  "id": "supported-types",
  "level": 2
}, {
  "value": "Bool",
  "id": "bool",
  "level": 3
}, {
  "value": "BuiltinUnit",
  "id": "builtinunit",
  "level": 3
}, {
  "value": "BuiltinPair",
  "id": "builtinpair",
  "level": 3
}, {
  "value": "Integer",
  "id": "integer",
  "level": 3
}, {
  "value": "BuiltinList",
  "id": "builtinlist",
  "level": 3
}];
function _createMdxContent(props) {
  const _components = {
    a: "a",
    admonition: "admonition",
    code: "code",
    h1: "h1",
    h2: "h2",
    h3: "h3",
    header: "header",
    li: "li",
    p: "p",
    pre: "pre",
    ul: "ul",
    ...(0,lib/* useMDXComponents */.R)(),
    ...props.components
  };
  return (0,jsx_runtime.jsxs)(jsx_runtime.Fragment, {
    children: [(0,jsx_runtime.jsx)(_components.header, {
      children: (0,jsx_runtime.jsx)(_components.h1, {
        id: "case-splitting-on-constants",
        children: "Case-splitting on constants"
      })
    }), "\n", (0,jsx_runtime.jsx)(_components.admonition, {
      type: "info",
      children: (0,jsx_runtime.jsxs)(_components.p, {
        children: ["This use of ", (0,jsx_runtime.jsx)(_components.code, {
          children: "case"
        }), " in UPLC was introduced with protocol version 11 and requires\n", (0,jsx_runtime.jsx)(_components.a, {
          href: "../essential-concepts/versions#plutus-core-version",
          children: "Plutus Core version"
        }), "\n", (0,jsx_runtime.jsx)(_components.code, {
          children: "1.1.0"
        }), "."]
      })
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["In UPLC, it is possible to branch on expressions of certain built-in types, like\n", (0,jsx_runtime.jsx)(_components.code, {
        children: "Integer"
      }), " and ", (0,jsx_runtime.jsx)(_components.code, {
        children: "Bool"
      }), " using ", (0,jsx_runtime.jsx)(_components.code, {
        children: "case"
      }), " syntax, which is also used\nfor ", (0,jsx_runtime.jsx)(_components.a, {
        href: "./encoding#sums-of-products",
        children: "sums-of-products"
      }), ". This may improve script performance\nand size, compared to older alternatives that use built-in functions."]
    }), "\n", (0,jsx_runtime.jsx)(_components.p, {
      children: "This page describes the built-in types that are supported in UPLC and how Plinth\ndevelopers can benefit from the improved performance."
    }), "\n", (0,jsx_runtime.jsx)(_components.h2, {
      id: "usage-from-plinth",
      children: "Usage from Plinth"
    }), "\n", (0,jsx_runtime.jsx)(_components.admonition, {
      type: "info",
      children: (0,jsx_runtime.jsxs)(_components.p, {
        children: ["The Plinth compiler option will change from ", (0,jsx_runtime.jsx)(_components.code, {
          children: "datatypes=BuiltinCasing"
        }), " to\n", (0,jsx_runtime.jsx)(_components.code, {
          children: "datatypes=SumsOfProducts"
        }), " in the future."]
      })
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["Plinth developers can benefit from the performance of ", (0,jsx_runtime.jsx)(_components.code, {
        children: "case"
      }), " by enabling the\ncompiler ", (0,jsx_runtime.jsx)(_components.a, {
        href: "./plinth-compiler-options",
        children: "option"
      }), " ", (0,jsx_runtime.jsx)(_components.code, {
        children: "datatypes=BuiltinCasing"
      }), ", and\nusing standard library functions such as ", (0,jsx_runtime.jsx)(_components.code, {
        children: "caseList"
      }), ", ", (0,jsx_runtime.jsx)(_components.code, {
        children: "fstPair"
      }), ".\nNote that Plinth's ", (0,jsx_runtime.jsx)(_components.code, {
        children: "case ... of ..."
      }), " syntax is not generally compiled to UPLC,\nas it can be more expressive."]
    }), "\n", (0,jsx_runtime.jsx)(_components.h2, {
      id: "supported-types",
      children: "Supported types"
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["The UPLC built-in types that ", (0,jsx_runtime.jsx)(_components.code, {
        children: "case"
      }), " can be used on are:"]
    }), "\n", (0,jsx_runtime.jsxs)(_components.ul, {
      children: ["\n", (0,jsx_runtime.jsx)(_components.li, {
        children: (0,jsx_runtime.jsx)(_components.code, {
          children: "bool"
        })
      }), "\n", (0,jsx_runtime.jsx)(_components.li, {
        children: (0,jsx_runtime.jsx)(_components.code, {
          children: "unit"
        })
      }), "\n", (0,jsx_runtime.jsx)(_components.li, {
        children: (0,jsx_runtime.jsx)(_components.code, {
          children: "integer"
        })
      }), "\n", (0,jsx_runtime.jsx)(_components.li, {
        children: (0,jsx_runtime.jsx)(_components.code, {
          children: "list"
        })
      }), "\n", (0,jsx_runtime.jsx)(_components.li, {
        children: (0,jsx_runtime.jsx)(_components.code, {
          children: "pair"
        })
      }), "\n"]
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["In the future, support for ", (0,jsx_runtime.jsx)(_components.code, {
        children: "data"
      }), " is also planned."]
    }), "\n", (0,jsx_runtime.jsx)(_components.h3, {
      id: "bool",
      children: "Bool"
    }), "\n", (0,jsx_runtime.jsx)(_components.p, {
      children: "The following Plinth code implements a basic assertion:"
    }), "\n", (0,jsx_runtime.jsx)(_components.pre, {
      children: (0,jsx_runtime.jsx)(_components.code, {
        className: "language-haskell",
        children: "assert :: Bool -> BuiltinUnit\nassert False = error ()\nassert True = unitval\n"
      })
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["With ", (0,jsx_runtime.jsx)(_components.code, {
        children: "datatypes=BuiltinCasing"
      }), ", it is compiled to the new casing on builtins:"]
    }), "\n", (0,jsx_runtime.jsx)(_components.pre, {
      children: (0,jsx_runtime.jsx)(_components.code, {
        className: "language-uplc",
        children: "\\b -> case b [error, ()]\n"
      })
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["In UPLC, booleans can be used in ", (0,jsx_runtime.jsx)(_components.code, {
        children: "case"
      }), " with either one or two branches, where\nthe first is always the ", (0,jsx_runtime.jsx)(_components.code, {
        children: "False"
      }), " branch. When only a single branch is provided,\nscript execution will fail when the boolean evaluates to True."]
    }), "\n", (0,jsx_runtime.jsxs)(_components.admonition, {
      type: "info",
      children: [(0,jsx_runtime.jsx)(_components.p, {
        children: "Compare this to the UPLC that would have been generated otherwise:"
      }), (0,jsx_runtime.jsx)(_components.pre, {
        children: (0,jsx_runtime.jsx)(_components.code, {
          className: "language-uplc",
          children: "\\b -> force (force ifThenElse b (delay ()) (delay error))\n"
        })
      }), (0,jsx_runtime.jsxs)(_components.p, {
        children: ["This uses the UPLC builtin function ", (0,jsx_runtime.jsx)(_components.code, {
          children: "ifThenElse"
        }), ", which requires delaying the branch\narguments, since application in UPLC is strict. The additional forcing and\ndelaying impacts the size and execution cost."]
      })]
    }), "\n", (0,jsx_runtime.jsx)(_components.h3, {
      id: "builtinunit",
      children: "BuiltinUnit"
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["The built-in unit type can be used in a trivial way with ", (0,jsx_runtime.jsx)(_components.code, {
        children: "case"
      }), " in UPLC, which\ntakes exactly one branch. With ", (0,jsx_runtime.jsx)(_components.code, {
        children: "datatypes=BuiltinCasing"
      }), ", Plinth will compile\n", (0,jsx_runtime.jsx)(_components.code, {
        children: "chooseUnit"
      }), " from ", (0,jsx_runtime.jsx)(_components.code, {
        children: "PlutusTx.Builtins.Internal"
      }), " into ", (0,jsx_runtime.jsx)(_components.code, {
        children: "case"
      }), ". For example:"]
    }), "\n", (0,jsx_runtime.jsx)(_components.pre, {
      children: (0,jsx_runtime.jsx)(_components.code, {
        className: "language-haskell",
        children: "forceUnit :: BuiltinUnit -> Integer\nforceUnit e = chooseUnit e 5\n"
      })
    }), "\n", (0,jsx_runtime.jsx)(_components.p, {
      children: "Which results in the following UPLC:"
    }), "\n", (0,jsx_runtime.jsx)(_components.pre, {
      children: (0,jsx_runtime.jsx)(_components.code, {
        className: "language-uplc",
        children: "\\e -> case e [5]\n"
      })
    }), "\n", (0,jsx_runtime.jsx)(_components.p, {
      children: "UPLC's case on built-in unit requires exactly one branch. If the expression\nbeing cased on evaluates to the unit value, evaluation will continue with the\nexpression in that branch."
    }), "\n", (0,jsx_runtime.jsx)(_components.h3, {
      id: "builtinpair",
      children: "BuiltinPair"
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["To destruct a built-in pair, use ", (0,jsx_runtime.jsx)(_components.code, {
        children: "casePair"
      }), " from ", (0,jsx_runtime.jsx)(_components.code, {
        children: "PlutusTx.Builtins"
      }), ". For example:"]
    }), "\n", (0,jsx_runtime.jsx)(_components.pre, {
      children: (0,jsx_runtime.jsx)(_components.code, {
        className: "language-haskell",
        children: "addPair :: BuiltinPair Integer Integer -> Integer\naddPair p = casePair p (+)\n"
      })
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["This compiles into ", (0,jsx_runtime.jsx)(_components.code, {
        children: "case"
      }), " in UPLC, which expects a single branch:"]
    }), "\n", (0,jsx_runtime.jsx)(_components.pre, {
      children: (0,jsx_runtime.jsx)(_components.code, {
        children: "\\p -> case p [(\\x y -> addInteger x y)]\n"
      })
    }), "\n", (0,jsx_runtime.jsxs)(_components.admonition, {
      type: "info",
      children: [(0,jsx_runtime.jsxs)(_components.p, {
        children: ["When compiling without ", (0,jsx_runtime.jsx)(_components.code, {
          children: "datatypes=BuiltinCasing"
        }), ", Plinth's ", (0,jsx_runtime.jsx)(_components.code, {
          children: "choosePair"
        }), " is\ncompiled into multiple built-in function calls to project out the pair's\ncomponents, impacting size and execution cost:"]
      }), (0,jsx_runtime.jsx)(_components.pre, {
        children: (0,jsx_runtime.jsx)(_components.code, {
          className: "language-uplc",
          children: "\\p -> addInteger (force (force fstPair) p) (force (force sndPair) p)\n"
        })
      })]
    }), "\n", (0,jsx_runtime.jsx)(_components.h3, {
      id: "integer",
      children: "Integer"
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["Casing on integers in UPLC can be used for non-negative integers only, and a variable\namount of branches may be given. If the expression ", (0,jsx_runtime.jsx)(_components.code, {
        children: "e"
      }), " evaluates to an integer\n", (0,jsx_runtime.jsx)(_components.code, {
        children: "i"
      }), ", the ", (0,jsx_runtime.jsx)(_components.code, {
        children: "i"
      }), "th branch will be evaluated. If there is no branch, ", (0,jsx_runtime.jsx)(_components.code, {
        children: "case"
      }), " will\nfail."]
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["In Plinth, use the ", (0,jsx_runtime.jsx)(_components.code, {
        children: "caseInteger"
      }), " function:"]
    }), "\n", (0,jsx_runtime.jsx)(_components.pre, {
      children: (0,jsx_runtime.jsx)(_components.code, {
        className: "language-haskell",
        children: "integerABC :: Integer -> BuiltinString\nintegerABC i = caseInteger i [\"a\", \"b\", \"c\"]\n"
      })
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["Applying this function to ", (0,jsx_runtime.jsx)(_components.code, {
        children: "2"
      }), " gives ", (0,jsx_runtime.jsx)(_components.code, {
        children: "\"c\""
      }), ", while ", (0,jsx_runtime.jsx)(_components.code, {
        children: "10"
      }), " or ", (0,jsx_runtime.jsx)(_components.code, {
        children: "-1"
      }), " produce an error.\nNote that the second argument must be given as a literal list, otherwise it is a\nPlinth compile error."]
    }), "\n", (0,jsx_runtime.jsx)(_components.p, {
      children: "Plinth generates the following UPLC:"
    }), "\n", (0,jsx_runtime.jsx)(_components.pre, {
      children: (0,jsx_runtime.jsx)(_components.code, {
        children: "\\i -> case i [\"a\", \"b\", \"c\"]\n"
      })
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["In general, if ", (0,jsx_runtime.jsx)(_components.code, {
        children: "i"
      }), "th branch is not given, or ", (0,jsx_runtime.jsx)(_components.code, {
        children: "i"
      }), " is a negative integer, evaluation will\nfail. Note that there is no way to provide a \"catch-all\" case for integers."]
    }), "\n", (0,jsx_runtime.jsxs)(_components.admonition, {
      type: "info",
      children: [(0,jsx_runtime.jsxs)(_components.p, {
        children: ["When not using ", (0,jsx_runtime.jsx)(_components.code, {
          children: "datatypes=BuiltinCasing"
        }), ", Plinth's ", (0,jsx_runtime.jsx)(_components.code, {
          children: "caseInteger"
        }), " is compiled\ninto a much less efficient implementation that turns the second argument in a\nlist (of which the representation depends on the chosen ", (0,jsx_runtime.jsx)(_components.code, {
          children: "datatypes="
        }), " flag), and\ndoes a recursive lookup in that list. The above Plinth code is compiled to:"]
      }), (0,jsx_runtime.jsx)(_components.pre, {
        children: (0,jsx_runtime.jsx)(_components.code, {
          className: "language-uplc",
          children: "(\\traceError ->\n       (\\go i ->\n          force\n            (force ifThenElse\n               (lessThanInteger i 0)\n               (delay (traceError \"PT6\"))\n               (delay\n                  (go\n                     i\n                     (constr 1\n                        [ \"a\"\n                        , (constr 1\n                             [\"b\", (constr 1 [\"c\", (constr 0 [])])]) ])))))\n         ((\\s -> s s)\n            (\\s ds ds ->\n               case\n                 ds\n                 [ (traceError \"PT7\")\n                 , (\\x xs ->\n                      force\n                        (force ifThenElse\n                           (equalsInteger 0 ds)\n                           (delay x)\n                           (delay\n                              ((\\x -> s s x) (subtractInteger ds 1) xs)))) ])))\n      (\\str -> (\\x -> error) (force trace str (constr 0 [])))\n"
        })
      })]
    }), "\n", (0,jsx_runtime.jsx)(_components.h3, {
      id: "builtinlist",
      children: "BuiltinList"
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["A ", (0,jsx_runtime.jsx)(_components.code, {
        children: "case"
      }), " on built-in lists may be given one or two branches (similar to\nbooleans), where the first one deals with the cons case, and the second one with\nthe empty list. If no second branch is given, execution will fail when the list\nturns out to be empty."]
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["This example implements a ", (0,jsx_runtime.jsx)(_components.code, {
        children: "head"
      }), " function for boolean lists, which fails if the list if empty."]
    }), "\n", (0,jsx_runtime.jsx)(_components.pre, {
      children: (0,jsx_runtime.jsx)(_components.code, {
        className: "language-uplc",
        children: "head :: BuiltinList Bool -> Bool\nhead xs = caseList (\\_ -> error ()) (\\x _ -> x) xs\n"
      })
    }), "\n", (0,jsx_runtime.jsxs)(_components.admonition, {
      type: "info",
      children: [(0,jsx_runtime.jsxs)(_components.p, {
        children: ["When compiling without ", (0,jsx_runtime.jsx)(_components.code, {
          children: "datatypes=BuiltinCasing"
        }), ", compilation falls back on\nusing multiple built-ins, such as ", (0,jsx_runtime.jsx)(_components.code, {
          children: "chooseList"
        }), ", ", (0,jsx_runtime.jsx)(_components.code, {
          children: "headList"
        }), " and ", (0,jsx_runtime.jsx)(_components.code, {
          children: "tailList"
        }), ".\nSimilarly to booleans, the branches are thunked, impacting script size and\nexecution cost:"]
      }), (0,jsx_runtime.jsx)(_components.pre, {
        children: (0,jsx_runtime.jsx)(_components.code, {
          className: "language-uplc",
          children: "(\\xs ->\n      force\n        (force (force chooseList)\n           xs\n           (delay (\\ds -> error))\n           (delay ((\\x xs ds -> x) (force headList xs) (force tailList xs))))\n        (constr 0 []))\n"
        })
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