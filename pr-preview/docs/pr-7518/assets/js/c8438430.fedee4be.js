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
const site_docs_delve_deeper_casing_constants_md_c84_namespaceObject = /*#__PURE__*/JSON.parse('{"id":"delve-deeper/casing-constants","title":"Case-splitting on constants","description":"This use of case in UPLC was introduced with protocol version 11 and requires","source":"@site/docs/delve-deeper/casing-constants.md","sourceDirName":"delve-deeper","slug":"/delve-deeper/casing-constants","permalink":"/pr-preview/docs/pr-7518/delve-deeper/casing-constants","draft":false,"unlisted":false,"editUrl":"https://github.com/IntersectMBO/plutus/edit/master/doc/docusaurus/docs/delve-deeper/casing-constants.md","tags":[],"version":"current","sidebarPosition":26,"frontMatter":{"sidebar_position":26},"sidebar":"tutorialSidebar","previous":{"title":"Encoding Data Types in UPLC","permalink":"/pr-preview/docs/pr-7518/delve-deeper/encoding"},"next":{"title":"Further Resources","permalink":"/pr-preview/docs/pr-7518/category/further-resources"}}');
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
  "value": "Compiling to <code>case</code> in Plinth",
  "id": "compiling-to-case-in-plinth",
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
  "value": "Unit",
  "id": "unit",
  "level": 3
}, {
  "value": "Pair",
  "id": "pair",
  "level": 3
}, {
  "value": "Integer",
  "id": "integer",
  "level": 3
}, {
  "value": "List",
  "id": "list",
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
      }), ". This can be done with ", (0,jsx_runtime.jsx)(_components.code, {
        children: "case"
      }), " syntax, which is also used\nfor ", (0,jsx_runtime.jsx)(_components.a, {
        href: "./encoding#sums-of-products",
        children: "sums-of-products"
      }), ". Using ", (0,jsx_runtime.jsx)(_components.code, {
        children: "case"
      }), " on built-in\nvalues may improve script performance and size.\nThe built-in types that ", (0,jsx_runtime.jsx)(_components.code, {
        children: "case"
      }), " currently supports are:"]
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
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["For each type, the allowed branches and their order differs. See ", (0,jsx_runtime.jsx)(_components.a, {
        href: "#supported-types",
        children: "Supported\nTypes"
      }), " for more detail."]
    }), "\n", (0,jsx_runtime.jsxs)(_components.h2, {
      id: "compiling-to-case-in-plinth",
      children: ["Compiling to ", (0,jsx_runtime.jsx)(_components.code, {
        children: "case"
      }), " in Plinth"]
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["When compiling Plinth code with the ", (0,jsx_runtime.jsx)(_components.a, {
        href: "./plinth-compiler-options",
        children: "option"
      }), "\n", (0,jsx_runtime.jsx)(_components.code, {
        children: "datatypes=BuiltinCasing"
      }), " (which in the future be achieved with\n", (0,jsx_runtime.jsx)(_components.code, {
        children: "datatypes=SumsOfProducts), many standard library functions will be compiled into this use of "
      }), "case", (0,jsx_runtime.jsx)(_components.code, {
        children: ", such as "
      }), "fstPair", (0,jsx_runtime.jsx)(_components.code, {
        children: ", "
      }), "ifThenElse", (0,jsx_runtime.jsx)(_components.code, {
        children: "and"
      }), "caseList", (0,jsx_runtime.jsx)(_components.code, {
        children: ". Note that Plinth's "
      }), "case ... of ...` syntax is not necessarily compiled to UPLC, as\nit can be more expressive."]
    }), "\n", (0,jsx_runtime.jsx)(_components.h2, {
      id: "supported-types",
      children: "Supported types"
    }), "\n", (0,jsx_runtime.jsx)(_components.h3, {
      id: "bool",
      children: "Bool"
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["Booleans can be used in ", (0,jsx_runtime.jsx)(_components.code, {
        children: "case"
      }), " with either one or two branches, where the first\nis the ", (0,jsx_runtime.jsx)(_components.code, {
        children: "False"
      }), " branch. Boolean negation can be written for example as:"]
    }), "\n", (0,jsx_runtime.jsx)(_components.pre, {
      children: (0,jsx_runtime.jsx)(_components.code, {
        className: "language-uplc",
        children: "lam b (case b (con bool True) (con bool False))\n"
      })
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["When only a single branch is provided, script execution will fail when the\nboolean evaluates to ", (0,jsx_runtime.jsx)(_components.code, {
        children: "True"
      }), "."]
    }), "\n", (0,jsx_runtime.jsx)(_components.p, {
      children: "Using a single branch is appropriate when the second branch was supposed to fail\nalready, saving script size."
    }), "\n", (0,jsx_runtime.jsx)(_components.admonition, {
      type: "info",
      children: (0,jsx_runtime.jsxs)(_components.p, {
        children: ["When compiling without ", (0,jsx_runtime.jsx)(_components.code, {
          children: "datatypes=BuiltinCasing"
        }), ", Plinth's ", (0,jsx_runtime.jsx)(_components.code, {
          children: "ifThenElse"
        }), " is\ncompiled into UPLC's ", (0,jsx_runtime.jsx)(_components.code, {
          children: "ifThenElse"
        }), " built-in function, which usually requires more\nAST nodes since each branch argument needs to be delayed (function application is\nstrict), and finally force the chosen branch. This impacts the size and\nexecution cost."]
      })
    }), "\n", (0,jsx_runtime.jsx)(_components.h3, {
      id: "unit",
      children: "Unit"
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["Needs exactly one branch. If the expression being cased on evaluates to a unit\nvalue, evaluation will continue with the expression in that branch. For example,\nthis expression evaluates to ", (0,jsx_runtime.jsx)(_components.code, {
        children: "con integer 5"
      }), "."]
    }), "\n", (0,jsx_runtime.jsx)(_components.pre, {
      children: (0,jsx_runtime.jsx)(_components.code, {
        className: "language-uplc",
        children: "case (con unit ()) (con integer 5)\n"
      })
    }), "\n", (0,jsx_runtime.jsx)(_components.h3, {
      id: "pair",
      children: "Pair"
    }), "\n", (0,jsx_runtime.jsx)(_components.p, {
      children: "A built-in pair expects a single branch: a function that takes both components\nof the pair."
    }), "\n", (0,jsx_runtime.jsx)(_components.p, {
      children: "This example sums the two integer constants in a pair."
    }), "\n", (0,jsx_runtime.jsx)(_components.pre, {
      children: (0,jsx_runtime.jsx)(_components.code, {
        className: "language-uplc",
        children: "lam x (case x (lam a (lam b [(builtin addInteger) a b])))\n"
      })
    }), "\n", (0,jsx_runtime.jsx)(_components.admonition, {
      type: "info",
      children: (0,jsx_runtime.jsxs)(_components.p, {
        children: ["When compiling without ", (0,jsx_runtime.jsx)(_components.code, {
          children: "datatypes=BuiltinCasing"
        }), ", Plinth's ", (0,jsx_runtime.jsx)(_components.code, {
          children: "choosePair"
        }), " is\ncompiled into multiple built-in function calls to project out the pair's\ncomponents, impacting size and execution cost."]
      })
    }), "\n", (0,jsx_runtime.jsx)(_components.h3, {
      id: "integer",
      children: "Integer"
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["Casing on integers can be used for non-negative integers only, and a variable\namount of branches may be given. If the expression ", (0,jsx_runtime.jsx)(_components.code, {
        children: "e"
      }), " evaluates to an integer\n", (0,jsx_runtime.jsx)(_components.code, {
        children: "i"
      }), ", the ", (0,jsx_runtime.jsx)(_components.code, {
        children: "i"
      }), "th branch will be evaluated. If there is no branch, ", (0,jsx_runtime.jsx)(_components.code, {
        children: "case"
      }), " will fail."]
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["For example, the following expression evaluates to ", (0,jsx_runtime.jsx)(_components.code, {
        children: "con string \"c\""
      })]
    }), "\n", (0,jsx_runtime.jsx)(_components.pre, {
      children: (0,jsx_runtime.jsx)(_components.code, {
        children: "case [(builtin addInteger) (con integer 1) (con integer 1)]\n  (con string \"a\")\n  (con string \"b\")\n  (con string \"c\")\n"
      })
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["If the ", (0,jsx_runtime.jsx)(_components.code, {
        children: "i"
      }), "th branch is not given, or ", (0,jsx_runtime.jsx)(_components.code, {
        children: "i"
      }), " is a negative integer, evaluation will\nfail:"]
    }), "\n", (0,jsx_runtime.jsx)(_components.pre, {
      children: (0,jsx_runtime.jsx)(_components.code, {
        children: "case [(builtin addInteger) (con integer 2) (con integer 2)]\n  (con string \"a\")\n  (con string \"b\")\n  (con string \"c\")\n"
      })
    }), "\n", (0,jsx_runtime.jsx)(_components.p, {
      children: "Results in"
    }), "\n", (0,jsx_runtime.jsx)(_components.pre, {
      children: (0,jsx_runtime.jsx)(_components.code, {
        children: "An error has occurred:\n'case' over a value of a built-in type failed with\n'case 4' is out of bounds for the given number of branches: 3\nCaused by: 4\n"
      })
    }), "\n", (0,jsx_runtime.jsx)(_components.p, {
      children: "Note that there is no way to provide a \"catch-all\" case for integers."
    }), "\n", (0,jsx_runtime.jsxs)(_components.admonition, {
      type: "info",
      children: [(0,jsx_runtime.jsxs)(_components.p, {
        children: ["In Plinth, using ", (0,jsx_runtime.jsx)(_components.code, {
          children: "caseInteger"
        }), " with ", (0,jsx_runtime.jsx)(_components.code, {
          children: "datatypes=BuiltinCasing"
        }), " will be compiled into\nthe above ", (0,jsx_runtime.jsx)(_components.code, {
          children: "case"
        }), " construct in PIR, provided the second argument is given as a\nliteral list (otherwise this is a compile error)."]
      }), (0,jsx_runtime.jsxs)(_components.p, {
        children: ["When not using ", (0,jsx_runtime.jsx)(_components.code, {
          children: "datatypes=BuiltinCasing"
        }), ", Plinth's ", (0,jsx_runtime.jsx)(_components.code, {
          children: "caseInteger"
        }), " is compiled\ninto a much less efficient implementation that turns the second argument in a\nlist (of which the representation depends on the chosen ", (0,jsx_runtime.jsx)(_components.code, {
          children: "datatypes="
        }), " flag), and\ndoes a recursive lookup in that list."]
      })]
    }), "\n", (0,jsx_runtime.jsx)(_components.h3, {
      id: "list",
      children: "List"
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["A ", (0,jsx_runtime.jsx)(_components.code, {
        children: "case"
      }), " on built-in lists may be given one or two branches (similar to\nbooleans), where the first one deals with the cons case, and the second one with\nthe empty list. If no second branch is given, execution will fail when the list\nturns out to be empty."]
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["This example implements the ", (0,jsx_runtime.jsx)(_components.code, {
        children: "head"
      }), " function, which fails if the list if empty."]
    }), "\n", (0,jsx_runtime.jsx)(_components.pre, {
      children: (0,jsx_runtime.jsx)(_components.code, {
        className: "language-uplc",
        children: "lam xs (case xs (lam y (lam ys y)))\n"
      })
    }), "\n", (0,jsx_runtime.jsx)(_components.admonition, {
      type: "info",
      children: (0,jsx_runtime.jsxs)(_components.p, {
        children: ["When compiling without ", (0,jsx_runtime.jsx)(_components.code, {
          children: "datatypes=BuiltinCasing"
        }), ", Plinth's ", (0,jsx_runtime.jsx)(_components.code, {
          children: "caseList"
        }), " is\ncompiled into a combination of built-in calls such as ", (0,jsx_runtime.jsx)(_components.code, {
          children: "chooseList"
        }), ", ", (0,jsx_runtime.jsx)(_components.code, {
          children: "headList"
        }), "\nand ", (0,jsx_runtime.jsx)(_components.code, {
          children: "tailList"
        }), ". Similarly to booleans, the branches are also thunked, impacting\nscript size and execution cost."]
      })
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