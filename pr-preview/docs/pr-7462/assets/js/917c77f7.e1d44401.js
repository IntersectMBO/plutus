"use strict";
(self["webpackChunkdocusaurus"] = self["webpackChunkdocusaurus"] || []).push([[5516],{

/***/ 8703:
/***/ ((__unused_webpack_module, __webpack_exports__, __webpack_require__) => {

// ESM COMPAT FLAG
__webpack_require__.r(__webpack_exports__);

// EXPORTS
__webpack_require__.d(__webpack_exports__, {
  assets: () => (/* binding */ assets),
  contentTitle: () => (/* binding */ contentTitle),
  "default": () => (/* binding */ MDXContent),
  frontMatter: () => (/* binding */ frontMatter),
  metadata: () => (/* reexport */ site_docs_using_plinth_lifting_md_917_namespaceObject),
  toc: () => (/* binding */ toc)
});

;// ./.docusaurus/docusaurus-plugin-content-docs/default/site-docs-using-plinth-lifting-md-917.json
const site_docs_using_plinth_lifting_md_917_namespaceObject = /*#__PURE__*/JSON.parse('{"id":"using-plinth/lifting","title":"Lifting Values into CompiledCode","description":"Stage Constraints","source":"@site/docs/using-plinth/lifting.md","sourceDirName":"using-plinth","slug":"/using-plinth/lifting","permalink":"/pr-preview/docs/pr-7462/using-plinth/lifting","draft":false,"unlisted":false,"editUrl":"https://github.com/IntersectMBO/plutus/edit/master/doc/docusaurus/docs/using-plinth/lifting.md","tags":[],"version":"current","sidebarPosition":11,"frontMatter":{"sidebar_position":11},"sidebar":"tutorialSidebar","previous":{"title":"Compiling Plinth","permalink":"/pr-preview/docs/pr-7462/using-plinth/compiling-plinth"},"next":{"title":"Evaluating CompiledCode","permalink":"/pr-preview/docs/pr-7462/using-plinth/evaluating-plinth"}}');
// EXTERNAL MODULE: ./node_modules/react/jsx-runtime.js
var jsx_runtime = __webpack_require__(4848);
// EXTERNAL MODULE: ./node_modules/@mdx-js/react/lib/index.js
var lib = __webpack_require__(8453);
;// ./docs/using-plinth/lifting.md


const frontMatter = {
	sidebar_position: 11
};
const contentTitle = 'Lifting Values into CompiledCode';

const assets = {

};



const toc = [{
  "value": "Stage Constraints",
  "id": "stage-constraints",
  "level": 2
}, {
  "value": "Lifting",
  "id": "lifting",
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
    hr: "hr",
    li: "li",
    ol: "ol",
    p: "p",
    pre: "pre",
    section: "section",
    sup: "sup",
    ul: "ul",
    ...(0,lib/* useMDXComponents */.R)(),
    ...props.components
  };
  return (0,jsx_runtime.jsxs)(jsx_runtime.Fragment, {
    children: [(0,jsx_runtime.jsx)(_components.header, {
      children: (0,jsx_runtime.jsx)(_components.h1, {
        id: "lifting-values-into-compiledcode",
        children: "Lifting Values into CompiledCode"
      })
    }), "\n", (0,jsx_runtime.jsx)(_components.h2, {
      id: "stage-constraints",
      children: "Stage Constraints"
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["The standard way of turning ", (0,jsx_runtime.jsx)(_components.code, {
        children: "a"
      }), " into ", (0,jsx_runtime.jsx)(_components.code, {
        children: "CompiledCode a"
      }), " is by compiling it (see ", (0,jsx_runtime.jsx)(_components.a, {
        href: "/pr-preview/docs/pr-7462/using-plinth/compiling-plinth",
        children: "Compiling Plinth"
      }), ").\nThis requires the definition of ", (0,jsx_runtime.jsx)(_components.code, {
        children: "a"
      }), " to be known at compile time.\nAs such, the following fails to compile:"]
    }), "\n", (0,jsx_runtime.jsx)(_components.pre, {
      children: (0,jsx_runtime.jsx)(_components.code, {
        className: "language-haskell",
        children: "f :: Integer -> CompiledCode Integer\nf x = $$(compile [|| x + 1 ||])\n"
      })
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["This is ", (0,jsx_runtime.jsx)(_components.em, {
        children: "not"
      }), " a Template Haskell stage error", (0,jsx_runtime.jsx)(_components.sup, {
        children: (0,jsx_runtime.jsx)(_components.a, {
          href: "#user-content-fn-1",
          id: "user-content-fnref-1",
          "data-footnote-ref": true,
          "aria-describedby": "footnote-label",
          children: "1"
        })
      }), ", but the Plinth compiler imposes additional stage constraints on top of Template Haskell's.\nTo see why the above doesn't work, recognize that in the ", (0,jsx_runtime.jsx)(_components.code, {
        children: "CompiledCode"
      }), " it is supposed to produce:"]
    }), "\n", (0,jsx_runtime.jsxs)(_components.ul, {
      children: ["\n", (0,jsx_runtime.jsxs)(_components.li, {
        children: [(0,jsx_runtime.jsx)(_components.code, {
          children: "x"
        }), " certainly cannot exist as a variable.\nBecause when ", (0,jsx_runtime.jsx)(_components.code, {
          children: "f"
        }), " is called, ", (0,jsx_runtime.jsx)(_components.code, {
          children: "x"
        }), " is replaced by an integer constant, which needs to go into the ", (0,jsx_runtime.jsx)(_components.code, {
          children: "CompiledCode"
        }), ".\nIn other words, when we call ", (0,jsx_runtime.jsx)(_components.code, {
          children: "f 42"
        }), ", we'd expect it to return a ", (0,jsx_runtime.jsx)(_components.code, {
          children: "CompiledCode"
        }), " corresponding to ", (0,jsx_runtime.jsx)(_components.code, {
          children: "42 + 1"
        }), "."]
      }), "\n", (0,jsx_runtime.jsxs)(_components.li, {
        children: ["But ", (0,jsx_runtime.jsx)(_components.code, {
          children: "x"
        }), " cannot exist as a constant either, because ", (0,jsx_runtime.jsx)(_components.code, {
          children: "compile [|| x + 1 ||]"
        }), " happens at compile time, and at compile time we don't yet know the value of ", (0,jsx_runtime.jsx)(_components.code, {
          children: "x"
        }), "."]
      }), "\n"]
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["If you try to do this, you'll get a \"no unfolding\" error, meaning the Plinth compiler cannot proceed because the unfolding (definition) of ", (0,jsx_runtime.jsx)(_components.code, {
        children: "x"
      }), " is not available."]
    }), "\n", (0,jsx_runtime.jsx)(_components.p, {
      children: "On the other hand, the following is perfectly fine:"
    }), "\n", (0,jsx_runtime.jsx)(_components.pre, {
      children: (0,jsx_runtime.jsx)(_components.code, {
        className: "language-haskell",
        children: "f :: CompiledCode (Integer -> Integer)\nf = $$(compile [|| \\x -> x + 1 ||])\n"
      })
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["Now we are just compiling a regular lambda, and in the resulting ", (0,jsx_runtime.jsx)(_components.code, {
        children: "CompiledCode"
      }), ", ", (0,jsx_runtime.jsx)(_components.code, {
        children: "x"
      }), " is simply a lambda-bound variable."]
    }), "\n", (0,jsx_runtime.jsx)(_components.p, {
      children: "The above can be summarized by the following rule for compiling Plinth Code:"
    }), "\n", (0,jsx_runtime.jsxs)(_components.ul, {
      children: ["\n", (0,jsx_runtime.jsxs)(_components.li, {
        children: [(0,jsx_runtime.jsxs)(_components.em, {
          children: ["Any variable inside the quotation passed to ", (0,jsx_runtime.jsx)(_components.code, {
            children: "compile"
          }), " (i.e., the ", (0,jsx_runtime.jsx)(_components.code, {
            children: "..."
          }), " in ", (0,jsx_runtime.jsx)(_components.code, {
            children: "$$(compile [|| ... ||])"
          }), ") must either be a top-level variable (which can be defined in the same module or imported from a different module), or bound inside the quotation"]
        }), "."]
      }), "\n"]
    }), "\n", (0,jsx_runtime.jsx)(_components.h2, {
      id: "lifting",
      children: "Lifting"
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["Similar to the ", (0,jsx_runtime.jsx)(_components.code, {
        children: "Language.Haskell.TH.Syntax.Lift"
      }), " class, which lifts Haskell values into Template Haskell ASTs, Plinth has a ", (0,jsx_runtime.jsx)(_components.code, {
        children: "PlutusTx.Lift.Class.Lift"
      }), " class which lifts Haskell values into ", (0,jsx_runtime.jsx)(_components.code, {
        children: "CompiledCode"
      }), ".\nBoth ", (0,jsx_runtime.jsx)(_components.code, {
        children: "Lift"
      }), " classes work in a similar way - for instance, Template Haskell's ", (0,jsx_runtime.jsx)(_components.code, {
        children: "Lift"
      }), " lifts integer 42 into a Template Haskell constant (", (0,jsx_runtime.jsx)(_components.code, {
        children: "LitE (IntegerL 42)"
      }), "), while Plinth's ", (0,jsx_runtime.jsx)(_components.code, {
        children: "Lift"
      }), " lifts it into a PIR/UPLC constant (", (0,jsx_runtime.jsx)(_components.code, {
        children: "con integer 42"
      }), ")."]
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: [(0,jsx_runtime.jsx)(_components.code, {
        children: "Lift"
      }), " instances can generally be derived for data types that don't contain functions.\nHowever, functions usually cannot be lifted.\nTo derive the Plinth ", (0,jsx_runtime.jsx)(_components.code, {
        children: "Lift"
      }), " instance for a data type, use ", (0,jsx_runtime.jsx)(_components.a, {
        href: "https://plutus.cardano.intersectmbo.org/haddock/latest/plutus-tx/PlutusTx-Lift-TH.html#v:makeLift",
        children: "makeLift"
      }), "."]
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: [(0,jsx_runtime.jsx)(_components.code, {
        children: "Lift"
      }), " makes it possible to write the above function of type ", (0,jsx_runtime.jsx)(_components.code, {
        children: "Integer -> CompiledCode Integer"
      }), ", which can be written as"]
    }), "\n", (0,jsx_runtime.jsx)(_components.pre, {
      children: (0,jsx_runtime.jsx)(_components.code, {
        className: "language-haskell",
        children: "f :: Integer -> CompiledCode Integer\nf x = liftCodeDef (x + 1)\n"
      })
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["Now there's no Template Haskell, hence no compile time work being done.\nWhen ", (0,jsx_runtime.jsx)(_components.code, {
        children: "f"
      }), " is called, ", (0,jsx_runtime.jsx)(_components.code, {
        children: "x + 1"
      }), " will be evaluated in Haskell into WHNF (i.e., an integer constant), which ", (0,jsx_runtime.jsx)(_components.code, {
        children: "liftCodeDef"
      }), " dutifully converts into a ", (0,jsx_runtime.jsx)(_components.code, {
        children: "con integer"
      }), "."]
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["When you call ", (0,jsx_runtime.jsx)(_components.code, {
        children: "f 42"
      }), ", the resulting ", (0,jsx_runtime.jsx)(_components.code, {
        children: "CompiledCode"
      }), " contains a single constant, 43.\nIf you want the ", (0,jsx_runtime.jsx)(_components.code, {
        children: "CompiledCode"
      }), " to instead contain ", (0,jsx_runtime.jsx)(_components.code, {
        children: "42 + 1"
      }), ", you can compile ", (0,jsx_runtime.jsx)(_components.code, {
        children: "(+ 1)"
      }), " separately, then apply it to the lifted ", (0,jsx_runtime.jsx)(_components.code, {
        children: "x"
      }), ":"]
    }), "\n", (0,jsx_runtime.jsx)(_components.pre, {
      children: (0,jsx_runtime.jsx)(_components.code, {
        className: "language-haskell",
        children: "f :: Integer -> CompiledCode Integer\nf x = $$(compile [|| (+ 1) ||]) `unsafeApplyCode` liftCodeDef x\n"
      })
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["There are variants of ", (0,jsx_runtime.jsx)(_components.code, {
        children: "liftCodeDef"
      }), " and ", (0,jsx_runtime.jsx)(_components.code, {
        children: "unsafeApplyCode"
      }), ".\nSee ", (0,jsx_runtime.jsx)(_components.a, {
        href: "https://plutus.cardano.intersectmbo.org/haddock/latest/plutus-tx/PlutusTx-Lift.html",
        children: "Haddock for PlutusTx.Lift"
      }), " and ", (0,jsx_runtime.jsx)(_components.a, {
        href: "https://plutus.cardano.intersectmbo.org/haddock/latest/plutus-tx/PlutusTx-Code.html",
        children: "Haddock for PlutusTx.Code"
      }), " for more details."]
    }), "\n", (0,jsx_runtime.jsx)(_components.hr, {}), "\n", "\n", (0,jsx_runtime.jsxs)(_components.section, {
      "data-footnotes": true,
      className: "footnotes",
      children: [(0,jsx_runtime.jsx)(_components.h2, {
        className: "sr-only",
        id: "footnote-label",
        children: "Footnotes"
      }), "\n", (0,jsx_runtime.jsxs)(_components.ol, {
        children: ["\n", (0,jsx_runtime.jsxs)(_components.li, {
          id: "user-content-fn-1",
          children: ["\n", (0,jsx_runtime.jsxs)(_components.p, {
            children: ["Here the usage of ", (0,jsx_runtime.jsx)(_components.code, {
              children: "x"
            }), " is surrounded by one quotation (", (0,jsx_runtime.jsx)(_components.code, {
              children: "[|| ... ||]"
            }), ") and one splice (", (0,jsx_runtime.jsx)(_components.code, {
              children: "$$(...)"
            }), "), which is legit from the Template Haskell point of view. It would be a Template Haskell stage error if ", (0,jsx_runtime.jsx)(_components.code, {
              children: "x"
            }), " was surrounded only by a splice (", (0,jsx_runtime.jsx)(_components.code, {
              children: "f x = $$(compile (x + 1))"
            }), ") or only by a quotation (", (0,jsx_runtime.jsx)(_components.code, {
              children: "f x = compile [|| x + 1 ||]"
            }), ", unless ", (0,jsx_runtime.jsx)(_components.code, {
              children: "x"
            }), "'s type has a ", (0,jsx_runtime.jsx)(_components.code, {
              children: "Language.Haskell.TH.Syntax.Lift"
            }), " instance). ", (0,jsx_runtime.jsx)(_components.a, {
              href: "#user-content-fnref-1",
              "data-footnote-backref": "",
              "aria-label": "Back to reference 1",
              className: "data-footnote-backref",
              children: "↩"
            })]
          }), "\n"]
        }), "\n"]
      }), "\n"]
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