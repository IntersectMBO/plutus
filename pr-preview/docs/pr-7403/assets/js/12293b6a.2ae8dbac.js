"use strict";
(self["webpackChunkdocusaurus"] = self["webpackChunkdocusaurus"] || []).push([[8329],{

/***/ 4910:
/***/ ((__unused_webpack_module, __webpack_exports__, __webpack_require__) => {

// ESM COMPAT FLAG
__webpack_require__.r(__webpack_exports__);

// EXPORTS
__webpack_require__.d(__webpack_exports__, {
  assets: () => (/* binding */ assets),
  contentTitle: () => (/* binding */ contentTitle),
  "default": () => (/* binding */ MDXContent),
  frontMatter: () => (/* binding */ frontMatter),
  metadata: () => (/* reexport */ site_docs_delve_deeper_languages_md_122_namespaceObject),
  toc: () => (/* binding */ toc)
});

;// ./.docusaurus/docusaurus-plugin-content-docs/default/site-docs-delve-deeper-languages-md-122.json
const site_docs_delve_deeper_languages_md_122_namespaceObject = /*#__PURE__*/JSON.parse('{"id":"delve-deeper/languages","title":"Overview of Languages Compiling to UPLC","description":"Untyped Plutus Core (UPLC) is the assembly-like language that runs in Cardano nodes for transaction validation.","source":"@site/docs/delve-deeper/languages.md","sourceDirName":"delve-deeper","slug":"/delve-deeper/languages","permalink":"/pr-preview/docs/pr-7403/delve-deeper/languages","draft":false,"unlisted":false,"editUrl":"https://github.com/IntersectMBO/plutus/edit/master/doc/docusaurus/docs/delve-deeper/languages.md","tags":[],"version":"current","sidebarPosition":1,"frontMatter":{"sidebar_position":1},"sidebar":"tutorialSidebar","previous":{"title":"Delve Deeper","permalink":"/pr-preview/docs/pr-7403/category/delve-deeper"},"next":{"title":"Plinth Compiler Options","permalink":"/pr-preview/docs/pr-7403/delve-deeper/plinth-compiler-options"}}');
// EXTERNAL MODULE: ./node_modules/react/jsx-runtime.js
var jsx_runtime = __webpack_require__(4848);
// EXTERNAL MODULE: ./node_modules/@mdx-js/react/lib/index.js
var lib = __webpack_require__(8453);
;// ./docs/delve-deeper/languages.md


const frontMatter = {
	sidebar_position: 1
};
const contentTitle = 'Overview of Languages Compiling to UPLC';

const assets = {

};



const toc = [{
  "value": "Standalone DSLs",
  "id": "standalone-dsls",
  "level": 2
}, {
  "value": "Embedded DSLs",
  "id": "embedded-dsls",
  "level": 2
}, {
  "value": "Subsets of Existing Languages",
  "id": "subsets-of-existing-languages",
  "level": 2
}, {
  "value": "List of Existing Languages",
  "id": "list-of-existing-languages",
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
    section: "section",
    sup: "sup",
    table: "table",
    tbody: "tbody",
    td: "td",
    th: "th",
    thead: "thead",
    tr: "tr",
    ul: "ul",
    ...(0,lib/* useMDXComponents */.R)(),
    ...props.components
  };
  return (0,jsx_runtime.jsxs)(jsx_runtime.Fragment, {
    children: [(0,jsx_runtime.jsx)(_components.header, {
      children: (0,jsx_runtime.jsx)(_components.h1, {
        id: "overview-of-languages-compiling-to-uplc",
        children: "Overview of Languages Compiling to UPLC"
      })
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["Untyped Plutus Core (UPLC) is the assembly-like language that runs in Cardano nodes for transaction validation.\nThe Cardano node ships with a UPLC evaluator, which is a ", (0,jsx_runtime.jsx)(_components.a, {
        href: "https://en.wikipedia.org/wiki/CEK_Machine",
        children: "CEK machine"
      }), "."]
    }), "\n", (0,jsx_runtime.jsx)(_components.p, {
      children: "UPLC is a low-level programming language, and is not intended to be written or modified by hand.\nBesides Plinth, several other high-level languages are designed to target UPLC.\nThese languages can be grouped into three categories:"
    }), "\n", (0,jsx_runtime.jsxs)(_components.ul, {
      children: ["\n", (0,jsx_runtime.jsx)(_components.li, {
        children: "Standalone DSLs, which are entirely new languages"
      }), "\n", (0,jsx_runtime.jsx)(_components.li, {
        children: "DSLs embedded in existing general-purpose programming languages"
      }), "\n", (0,jsx_runtime.jsx)(_components.li, {
        children: "Subsets of existing general-purpose programming languages"
      }), "\n"]
    }), "\n", (0,jsx_runtime.jsx)(_components.p, {
      children: "These are also the three common strategies for creating DSLs in general, not limited to blockchains or Cardano.\nEach strategy comes with its own benefits and drawbacks, which we'll discuss next."
    }), "\n", (0,jsx_runtime.jsx)(_components.h2, {
      id: "standalone-dsls",
      children: "Standalone DSLs"
    }), "\n", (0,jsx_runtime.jsx)(_components.p, {
      children: "A standalone DSL is a new language with its own syntax and semantics.\nBy crafting a new language from scratch, you avoid inheriting the limitations and complexities of existing languages, allowing you to tailor-make it to be as simple, intuitive and elegant as possible to program for the specific domain it targets."
    }), "\n", (0,jsx_runtime.jsx)(_components.p, {
      children: "On the other hand, standalone DSLs have some disadvantages.\nFirst, from the language developer’s perspective, designing and implementing them can be challenging.\nNot only must the syntax and semantics be created from scratch, but you also need to build all necessary compiler components, tooling, documentation, and a library ecosystem from the ground up."
    }), "\n", (0,jsx_runtime.jsx)(_components.p, {
      children: "This can be a formidable task, requiring substantial efforts, particularly with the addition of new language features over time.\nCreating adequate documentation, in particular, can be especially challenging for standalone DSLs, and is a challenge that is easy to overlook.\nGiven the limited amount of external learning resources, the official documentation often becomes the primary, if not sole, source of knowledge.\nAs a result, it needs to be thorough, detailed, and clearly written to provide a positive learning experience for users."
    }), "\n", (0,jsx_runtime.jsx)(_components.p, {
      children: "Second, from the user's perspective, they will need to adopt a new programming language and incorporate it into their existing tech stacks.\nThis can present a considerable challenge, as it involves a learning curve, increased cognitive load, and the necessity to introduce and manage additional tools.\nAdditional languages mean additional complexity."
    }), "\n", (0,jsx_runtime.jsx)(_components.p, {
      children: "In general, it's highly advantageous for a software development team to minimize the number of languages they use, as this not only reduces complexity but strengthens the network effect of programming languages.\nLearning a new DSL is harder than you might think - even a relatively simple one with a \"fluent syntax\", due to the scarcity of learning resources, and the potential irrelevance of previous experience.\nFurthermore, the knowledge learned may not transfer well."
    }), "\n", (0,jsx_runtime.jsx)(_components.h2, {
      id: "embedded-dsls",
      children: "Embedded DSLs"
    }), "\n", (0,jsx_runtime.jsx)(_components.p, {
      children: "An embedded DSL (commonly referred to as an eDSL) generally takes the form of a library in a host programming language.\nFunctional languages such as Haskell are particularly well-suited for hosting eDSLs, as the implementation of an eDSL largely involves functions that construct and transform abstract syntax trees (ASTs)."
    }), "\n", (0,jsx_runtime.jsx)(_components.p, {
      children: "Embedded DSLs can be much easier than standalone DSLs to develop, and to integrate into projects that already use the host language.\nEmbedded DSLs, however, come with the drawback that the complexity of constructing and manipulating ASTs are exposed to the users.\nWhen using an embedded DSL, you are essentially writing programs that create and manage ASTs, rather than straightforward code."
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["Take, for instance, a program that accepts two integers as input, and checks if the first is less than the second.\nNormally, you would write a function of type ", (0,jsx_runtime.jsx)(_components.code, {
        children: "Integer -> Integer -> Bool"
      }), ", which takes two integers and returns a boolean.\nHowever, when working with an eDSL, your program might have a type like ", (0,jsx_runtime.jsx)(_components.code, {
        children: "AST Integer -> AST Integer -> AST Bool"
      }), ", which takes two ASTs that evaluate to integers, combines them, and yields a larger AST that evaluates to a boolean.\nThe complexity increases further if the comparison is polymorphic, since it is unlikely that the usual method of writing polymorphic functions (such as Haskell's ", (0,jsx_runtime.jsx)(_components.code, {
        children: "Ord"
      }), " instance) can be reused.\nLike standalone DSLs, this also introduces additional learning curves and cognitive load, though for a different reason."]
    }), "\n", (0,jsx_runtime.jsx)(_components.p, {
      children: "Another disadvantage of eDSLs is that it is harder, compared to the other two approaches, to produce readable target code or accurate source mappings for debuggers.\nThis stems from the nature of eDSLs, which are libraries that construct and manipulate ASTs.\nSince they do not have direct access to the host language's ASTs, it can be challenging to retrieve information related to the source code, such as variable names, module names and code locations."
    }), "\n", (0,jsx_runtime.jsx)(_components.p, {
      children: "Lastly, eDSLs often cannot leverage the host language's existing library ecosystem.\nAgain, using an eDSL involves constructing and manipulating ASTs rather than writing regular programs, which means many existing libraries would be inapplicable."
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["The eDSLs described above fall under the category of \"deep embedding\".\nThere's another category of eDSLs, called \"shallow embedding\", which, unlikely deep embedding, does not construct intermediate ASTs.\nInstead, shallow embedding involves using overloaded functions.\nFor example, a DSL designed as a shallow embedding for working with databases might include operations such as ", (0,jsx_runtime.jsx)(_components.code, {
        children: "createTable"
      }), ", ", (0,jsx_runtime.jsx)(_components.code, {
        children: "getItem"
      }), ", and ", (0,jsx_runtime.jsx)(_components.code, {
        children: "putItem"
      }), ".\nThese functions are overloaded, allowing them to work with various database implementations, including mock databases for testing purposes.\nSuch overloaded functions are typically defined using typeclasses in functional languages, or interfaces/traits in object-oriented languages."]
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["While it is valid to call shallow embeddings ", (0,jsx_runtime.jsx)(_components.em, {
        children: "languages"
      }), ", it is a bit of a stretch.\nOverloaded functions are widespread in everyday programming, and are not usually regarded as languages due to the absence of ASTs.\nMoreover, shallow embedding is less fitting when the eDSL targets a lower level language like UPLC, as constructing ASTs for UPLC will still be necessary.\nAll existing eDSLs targeting UPLC are examples of deep embeddings."]
    }), "\n", (0,jsx_runtime.jsx)(_components.h2, {
      id: "subsets-of-existing-languages",
      children: "Subsets of Existing Languages"
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["Similar to eDSLs, this approach can be particularly appealing if your team or project is already using the host language.\nIt allows for even greater reuse of existing functions, types and idioms from the hosting language, compared to eDSLs.\nFor instance, a program that tests whether one integer is less than another can retain the type ", (0,jsx_runtime.jsx)(_components.code, {
        children: "forall a. Ord a => a -> a -> Bool"
      }), ", and can even reuse the ", (0,jsx_runtime.jsx)(_components.code, {
        children: "<"
      }), " operator in the hosting language's standard library", (0,jsx_runtime.jsx)(_components.sup, {
        children: (0,jsx_runtime.jsx)(_components.a, {
          href: "#user-content-fn-1",
          id: "user-content-fnref-1",
          "data-footnote-ref": true,
          "aria-describedby": "footnote-label",
          children: "1"
        })
      }), "."]
    }), "\n", (0,jsx_runtime.jsx)(_components.p, {
      children: "This is achieved by leveraging the host language's compiler frontend, which might include lexer, parser, type checker, AST and optimization passes, while developing a custom backend for the new language.\nBy reusing the host language's ASTs, programs maintain simple and regular types without the need for custom AST construction, which is often necessary in eDSLs."
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["A case in point is Plinth, which is a subset of Haskell, and its compiler is a GHC plugin.\nIt reuses GHC components like the parser and type checker, and transforms GHC Core (GHC's intermediate representation) into UPLC.\nAlternatively, meta-programming methods can be used to access and manipulate the host language's AST, such as quotes and splices", (0,jsx_runtime.jsx)(_components.sup, {
        children: (0,jsx_runtime.jsx)(_components.a, {
          href: "#user-content-fn-2",
          id: "user-content-fnref-2",
          "data-footnote-ref": true,
          "aria-describedby": "footnote-label",
          children: "2"
        })
      }), "."]
    }), "\n", (0,jsx_runtime.jsx)(_components.p, {
      children: "Nonetheless, developing a new language as a subset of an existing language presents several challenges.\nThe compiler components of the host language are most likely not tailored for the new language, and making them work for the new language can be difficult.\nFor example, optimizations that work well for the host language might not be effective or valid for the new language.\nAdditionally, the desugaring process might transform code in such a way that it no longer fits within the supported subset, causing issues with the new language’s compiler."
    }), "\n", (0,jsx_runtime.jsx)(_components.p, {
      children: "Furthermore, complications arise when the new language and the host language do not exactly agree on semantics or evaluation strategies.\nThis disparity can lead to behaviors where the same code might act differently when compiled and executed in the host language versus the new language.\nIt can also result in idioms that work well in the host language being inappropriate for the new language.\nFor example, while guarded recursion is a useful idiom in Haskell, it might not be suitable for Plinth due to Plinth's use of call-by-value evaluation."
    }), "\n", (0,jsx_runtime.jsx)(_components.p, {
      children: "Another drawback of using a subset of a language is that, determining whether a program conforms to the allowed subset typically doesn't happen at type checking time, but at target code generation time.\nThis not only delays error detection compared to eDSLs, but makes it harder to produce clear error messages, since by target code generation time, the AST may have already been transformed and optimized, obscuring its connection to the original source code."
    }), "\n", (0,jsx_runtime.jsx)(_components.h2, {
      id: "list-of-existing-languages",
      children: "List of Existing Languages"
    }), "\n", (0,jsx_runtime.jsxs)(_components.table, {
      children: [(0,jsx_runtime.jsx)(_components.thead, {
        children: (0,jsx_runtime.jsxs)(_components.tr, {
          children: [(0,jsx_runtime.jsx)(_components.th, {
            children: "Language"
          }), (0,jsx_runtime.jsx)(_components.th, {
            children: "Category"
          })]
        })
      }), (0,jsx_runtime.jsxs)(_components.tbody, {
        children: [(0,jsx_runtime.jsxs)(_components.tr, {
          children: [(0,jsx_runtime.jsx)(_components.td, {
            children: "Plinth"
          }), (0,jsx_runtime.jsx)(_components.td, {
            children: "Subset of Haskell"
          })]
        }), (0,jsx_runtime.jsxs)(_components.tr, {
          children: [(0,jsx_runtime.jsx)(_components.td, {
            children: (0,jsx_runtime.jsx)(_components.a, {
              href: "https://aiken-lang.org/",
              children: "Aiken"
            })
          }), (0,jsx_runtime.jsx)(_components.td, {
            children: "Standalone DSL"
          })]
        }), (0,jsx_runtime.jsxs)(_components.tr, {
          children: [(0,jsx_runtime.jsx)(_components.td, {
            children: (0,jsx_runtime.jsx)(_components.a, {
              href: "https://github.com/HeliosLang/compiler",
              children: "Helios"
            })
          }), (0,jsx_runtime.jsx)(_components.td, {
            children: "Standalone DSL"
          })]
        }), (0,jsx_runtime.jsxs)(_components.tr, {
          children: [(0,jsx_runtime.jsx)(_components.td, {
            children: (0,jsx_runtime.jsx)(_components.a, {
              href: "https://github.com/OpShin/opshin",
              children: "OpShin"
            })
          }), (0,jsx_runtime.jsx)(_components.td, {
            children: "Subset of Python"
          })]
        }), (0,jsx_runtime.jsxs)(_components.tr, {
          children: [(0,jsx_runtime.jsx)(_components.td, {
            children: (0,jsx_runtime.jsx)(_components.a, {
              href: "https://github.com/HarmonicLabs/plu-ts",
              children: "plu-ts"
            })
          }), (0,jsx_runtime.jsx)(_components.td, {
            children: "DSL embedded in TypeScript"
          })]
        }), (0,jsx_runtime.jsxs)(_components.tr, {
          children: [(0,jsx_runtime.jsx)(_components.td, {
            children: (0,jsx_runtime.jsx)(_components.a, {
              href: "https://github.com/Plutonomicon/plutarch-plutus",
              children: "Plutarch"
            })
          }), (0,jsx_runtime.jsx)(_components.td, {
            children: "DSL embedded in Haskell"
          })]
        }), (0,jsx_runtime.jsxs)(_components.tr, {
          children: [(0,jsx_runtime.jsx)(_components.td, {
            children: (0,jsx_runtime.jsx)(_components.a, {
              href: "https://github.com/nau/scalus",
              children: "Scalus"
            })
          }), (0,jsx_runtime.jsx)(_components.td, {
            children: "Subset of Scala"
          })]
        })]
      })]
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
            children: ["This statement is not entirely true for Plinth, a subset of Haskell.\nDue to certain GHC-specific technical limitations, it can't easily reuse many functions and operations from the ", (0,jsx_runtime.jsx)(_components.code, {
              children: "base"
            }), " library, so it ships with its own standard library instead.\nNevertheless, the ", (0,jsx_runtime.jsx)(_components.code, {
              children: "<"
            }), " operator in Plinth's standard library still has the type ", (0,jsx_runtime.jsx)(_components.code, {
              children: "Integer -> Integer -> Bool"
            }), ". ", (0,jsx_runtime.jsx)(_components.a, {
              href: "#user-content-fnref-1",
              "data-footnote-backref": "",
              "aria-label": "Back to reference 1",
              className: "data-footnote-backref",
              children: "↩"
            })]
          }), "\n"]
        }), "\n", (0,jsx_runtime.jsxs)(_components.li, {
          id: "user-content-fn-2",
          children: ["\n", (0,jsx_runtime.jsxs)(_components.p, {
            children: ["For further reading, check out ", (0,jsx_runtime.jsx)(_components.a, {
              href: "https://homepages.inf.ed.ac.uk/wadler/topics/qdsl.html",
              children: (0,jsx_runtime.jsx)(_components.em, {
                children: "Everything old is new again: Quoted Domain Specific Languages"
              })
            }), ". ", (0,jsx_runtime.jsx)(_components.a, {
              href: "#user-content-fnref-2",
              "data-footnote-backref": "",
              "aria-label": "Back to reference 2",
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