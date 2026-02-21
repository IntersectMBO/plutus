"use strict";
(self["webpackChunkdocusaurus"] = self["webpackChunkdocusaurus"] || []).push([[8233],{

/***/ 5152:
/***/ ((__unused_webpack_module, __webpack_exports__, __webpack_require__) => {

// ESM COMPAT FLAG
__webpack_require__.r(__webpack_exports__);

// EXPORTS
__webpack_require__.d(__webpack_exports__, {
  assets: () => (/* binding */ assets),
  contentTitle: () => (/* binding */ contentTitle),
  "default": () => (/* binding */ MDXContent),
  frontMatter: () => (/* binding */ frontMatter),
  metadata: () => (/* reexport */ site_docs_delve_deeper_further_resources_plutus_cips_md_3e4_namespaceObject),
  toc: () => (/* binding */ toc)
});

;// ./.docusaurus/docusaurus-plugin-content-docs/default/site-docs-delve-deeper-further-resources-plutus-cips-md-3e4.json
const site_docs_delve_deeper_further_resources_plutus_cips_md_3e4_namespaceObject = /*#__PURE__*/JSON.parse('{"id":"delve-deeper/further-resources/plutus-cips","title":"Plutus-Related CIPs","description":"This page lists all Cardano Improvement Proposals (CIPs) that are substantially related to Plutus smart contract platform, including core language features, builtin functions, and infrastructure improvements.","source":"@site/docs/delve-deeper/further-resources/plutus-cips.md","sourceDirName":"delve-deeper/further-resources","slug":"/delve-deeper/further-resources/plutus-cips","permalink":"/pr-preview/docs/pr-7437/delve-deeper/further-resources/plutus-cips","draft":false,"unlisted":false,"editUrl":"https://github.com/IntersectMBO/plutus/edit/master/doc/docusaurus/docs/delve-deeper/further-resources/plutus-cips.md","tags":[],"version":"current","sidebarPosition":20,"frontMatter":{"sidebar_position":20},"sidebar":"tutorialSidebar","previous":{"title":"Plutus Core Specification","permalink":"/pr-preview/docs/pr-7437/delve-deeper/further-resources/plutus-core-specification"},"next":{"title":"Videos","permalink":"/pr-preview/docs/pr-7437/delve-deeper/further-resources/videos"}}');
// EXTERNAL MODULE: ./node_modules/react/jsx-runtime.js
var jsx_runtime = __webpack_require__(4848);
// EXTERNAL MODULE: ./node_modules/@mdx-js/react/lib/index.js
var lib = __webpack_require__(8453);
;// ./docs/delve-deeper/further-resources/plutus-cips.md


const frontMatter = {
	sidebar_position: 20
};
const contentTitle = 'Plutus-Related CIPs';

const assets = {

};



const toc = [];
function _createMdxContent(props) {
  const _components = {
    a: "a",
    del: "del",
    h1: "h1",
    header: "header",
    p: "p",
    strong: "strong",
    table: "table",
    tbody: "tbody",
    td: "td",
    th: "th",
    thead: "thead",
    tr: "tr",
    ...(0,lib/* useMDXComponents */.R)(),
    ...props.components
  };
  return (0,jsx_runtime.jsxs)(jsx_runtime.Fragment, {
    children: [(0,jsx_runtime.jsx)(_components.header, {
      children: (0,jsx_runtime.jsx)(_components.h1, {
        id: "plutus-related-cips",
        children: "Plutus-Related CIPs"
      })
    }), "\n", (0,jsx_runtime.jsx)(_components.p, {
      children: "This page lists all Cardano Improvement Proposals (CIPs) that are substantially related to Plutus smart contract platform, including core language features, builtin functions, and infrastructure improvements."
    }), "\n", (0,jsx_runtime.jsxs)(_components.table, {
      children: [(0,jsx_runtime.jsx)(_components.thead, {
        children: (0,jsx_runtime.jsxs)(_components.tr, {
          children: [(0,jsx_runtime.jsx)(_components.th, {
            children: "CIP"
          }), (0,jsx_runtime.jsx)(_components.th, {
            children: "Description"
          }), (0,jsx_runtime.jsx)(_components.th, {
            children: "Status"
          })]
        })
      }), (0,jsx_runtime.jsxs)(_components.tbody, {
        children: [(0,jsx_runtime.jsxs)(_components.tr, {
          children: [(0,jsx_runtime.jsx)(_components.td, {
            children: (0,jsx_runtime.jsx)(_components.a, {
              href: "https://cips.cardano.org/cip/CIP-0031",
              children: "031"
            })
          }), (0,jsx_runtime.jsxs)(_components.td, {
            children: [(0,jsx_runtime.jsx)(_components.strong, {
              children: "Reference inputs"
            }), " - Allows looking at outputs without spending them, crucial for Plutus validators"]
          }), (0,jsx_runtime.jsx)(_components.td, {
            children: "Active"
          })]
        }), (0,jsx_runtime.jsxs)(_components.tr, {
          children: [(0,jsx_runtime.jsx)(_components.td, {
            children: (0,jsx_runtime.jsx)(_components.a, {
              href: "https://cips.cardano.org/cip/CIP-0032",
              children: "032"
            })
          }), (0,jsx_runtime.jsxs)(_components.td, {
            children: [(0,jsx_runtime.jsx)(_components.strong, {
              children: "Inline datums"
            }), " - Allows datums to be attached directly to outputs instead of datum hashes"]
          }), (0,jsx_runtime.jsx)(_components.td, {
            children: "Active"
          })]
        }), (0,jsx_runtime.jsxs)(_components.tr, {
          children: [(0,jsx_runtime.jsx)(_components.td, {
            children: (0,jsx_runtime.jsx)(_components.a, {
              href: "https://cips.cardano.org/cip/CIP-0033",
              children: "033"
            })
          }), (0,jsx_runtime.jsxs)(_components.td, {
            children: [(0,jsx_runtime.jsx)(_components.strong, {
              children: "Reference scripts"
            }), " - Allows scripts to be attached to outputs for reuse without including in transactions"]
          }), (0,jsx_runtime.jsx)(_components.td, {
            children: "Active"
          })]
        }), (0,jsx_runtime.jsxs)(_components.tr, {
          children: [(0,jsx_runtime.jsx)(_components.td, {
            children: (0,jsx_runtime.jsx)(_components.a, {
              href: "https://cips.cardano.org/cip/CIP-0035",
              children: "035"
            })
          }), (0,jsx_runtime.jsxs)(_components.td, {
            children: [(0,jsx_runtime.jsx)(_components.strong, {
              children: "Changes to Plutus Core"
            }), " - Defines the process for proposing changes to Plutus Core, its builtins, and ledger interface"]
          }), (0,jsx_runtime.jsx)(_components.td, {
            children: "Active"
          })]
        }), (0,jsx_runtime.jsxs)(_components.tr, {
          children: [(0,jsx_runtime.jsx)(_components.td, {
            children: (0,jsx_runtime.jsx)(_components.a, {
              href: "https://cips.cardano.org/cip/CIP-0040",
              children: "040"
            })
          }), (0,jsx_runtime.jsxs)(_components.td, {
            children: [(0,jsx_runtime.jsx)(_components.strong, {
              children: "Collateral Output"
            }), " - Addresses collateral requirements for Plutus smart contract execution"]
          }), (0,jsx_runtime.jsx)(_components.td, {
            children: "Active"
          })]
        }), (0,jsx_runtime.jsxs)(_components.tr, {
          children: [(0,jsx_runtime.jsx)(_components.td, {
            children: (0,jsx_runtime.jsx)(_components.a, {
              href: "https://cips.cardano.org/cip/CIP-0042",
              children: "042"
            })
          }), (0,jsx_runtime.jsxs)(_components.td, {
            children: [(0,jsx_runtime.jsx)(_components.strong, {
              children: "New Plutus Builtin serialiseData"
            }), " - Adds builtin for serializing BuiltinData to BuiltinByteString"]
          }), (0,jsx_runtime.jsx)(_components.td, {
            children: "Active"
          })]
        }), (0,jsx_runtime.jsxs)(_components.tr, {
          children: [(0,jsx_runtime.jsx)(_components.td, {
            children: (0,jsx_runtime.jsx)(_components.a, {
              href: "https://cips.cardano.org/cip/CIP-0049",
              children: "049"
            })
          }), (0,jsx_runtime.jsxs)(_components.td, {
            children: [(0,jsx_runtime.jsx)(_components.strong, {
              children: "ECDSA and Schnorr signatures in Plutus Core"
            }), " - Adds cryptographic signature verification builtins"]
          }), (0,jsx_runtime.jsx)(_components.td, {
            children: "Active"
          })]
        }), (0,jsx_runtime.jsxs)(_components.tr, {
          children: [(0,jsx_runtime.jsx)(_components.td, {
            children: (0,jsx_runtime.jsx)(_components.a, {
              href: "https://cips.cardano.org/cip/CIP-0057",
              children: "057"
            })
          }), (0,jsx_runtime.jsxs)(_components.td, {
            children: [(0,jsx_runtime.jsx)(_components.strong, {
              children: "Plutus Contract Blueprint"
            }), " - Machine-readable specification for documenting Plutus contracts"]
          }), (0,jsx_runtime.jsx)(_components.td, {
            children: "Active"
          })]
        }), (0,jsx_runtime.jsxs)(_components.tr, {
          children: [(0,jsx_runtime.jsx)(_components.td, {
            children: (0,jsx_runtime.jsx)(_components.a, {
              href: "https://cips.cardano.org/cip/CIP-0058",
              children: "058"
            })
          }), (0,jsx_runtime.jsx)(_components.td, {
            children: (0,jsx_runtime.jsxs)(_components.del, {
              children: [(0,jsx_runtime.jsx)(_components.strong, {
                children: "Plutus Bitwise Primitives"
              }), " - Superseded by CIP-121 and CIP-122"]
            })
          }), (0,jsx_runtime.jsx)(_components.td, {
            children: "Inactive"
          })]
        }), (0,jsx_runtime.jsxs)(_components.tr, {
          children: [(0,jsx_runtime.jsx)(_components.td, {
            children: (0,jsx_runtime.jsx)(_components.a, {
              href: "https://cips.cardano.org/cip/CIP-0068",
              children: "068"
            })
          }), (0,jsx_runtime.jsxs)(_components.td, {
            children: [(0,jsx_runtime.jsx)(_components.strong, {
              children: "Datum Metadata Standard"
            }), " - Token metadata standard using output datums, mentions \"inspectable metadata from within Plutus validators\""]
          }), (0,jsx_runtime.jsx)(_components.td, {
            children: "Proposed"
          })]
        }), (0,jsx_runtime.jsxs)(_components.tr, {
          children: [(0,jsx_runtime.jsx)(_components.td, {
            children: (0,jsx_runtime.jsx)(_components.a, {
              href: "https://cips.cardano.org/cip/CIP-0069",
              children: "069"
            })
          }), (0,jsx_runtime.jsxs)(_components.td, {
            children: [(0,jsx_runtime.jsx)(_components.strong, {
              children: "Script Signature Unification"
            }), " - Unifies script signature handling across different script types"]
          }), (0,jsx_runtime.jsx)(_components.td, {
            children: "Active"
          })]
        }), (0,jsx_runtime.jsxs)(_components.tr, {
          children: [(0,jsx_runtime.jsx)(_components.td, {
            children: (0,jsx_runtime.jsx)(_components.a, {
              href: "https://cips.cardano.org/cip/CIP-0085",
              children: "085"
            })
          }), (0,jsx_runtime.jsxs)(_components.td, {
            children: [(0,jsx_runtime.jsx)(_components.strong, {
              children: "Sums-of-products in Plutus Core"
            }), " - Adds algebraic data type support to Plutus Core"]
          }), (0,jsx_runtime.jsx)(_components.td, {
            children: "Active"
          })]
        }), (0,jsx_runtime.jsxs)(_components.tr, {
          children: [(0,jsx_runtime.jsx)(_components.td, {
            children: (0,jsx_runtime.jsx)(_components.a, {
              href: "https://cips.cardano.org/cip/CIP-0091",
              children: "091"
            })
          }), (0,jsx_runtime.jsxs)(_components.td, {
            children: [(0,jsx_runtime.jsx)(_components.strong, {
              children: "Don't force Built-In functions"
            }), " - Optimization for builtin function evaluation"]
          }), (0,jsx_runtime.jsx)(_components.td, {
            children: "Proposed"
          })]
        }), (0,jsx_runtime.jsxs)(_components.tr, {
          children: [(0,jsx_runtime.jsx)(_components.td, {
            children: (0,jsx_runtime.jsx)(_components.a, {
              href: "https://cips.cardano.org/cip/CIP-0101",
              children: "101"
            })
          }), (0,jsx_runtime.jsxs)(_components.td, {
            children: [(0,jsx_runtime.jsx)(_components.strong, {
              children: "Integration of keccak256 into Plutus"
            }), " - Adds Keccak-256 hash function builtin"]
          }), (0,jsx_runtime.jsx)(_components.td, {
            children: "Proposed"
          })]
        }), (0,jsx_runtime.jsxs)(_components.tr, {
          children: [(0,jsx_runtime.jsx)(_components.td, {
            children: (0,jsx_runtime.jsx)(_components.a, {
              href: "https://cips.cardano.org/cip/CIP-0109",
              children: "109"
            })
          }), (0,jsx_runtime.jsxs)(_components.td, {
            children: [(0,jsx_runtime.jsx)(_components.strong, {
              children: "Modular Exponentiation Built-in for Plutus Core"
            }), " - Adds modular exponentiation builtin"]
          }), (0,jsx_runtime.jsx)(_components.td, {
            children: "Proposed"
          })]
        }), (0,jsx_runtime.jsxs)(_components.tr, {
          children: [(0,jsx_runtime.jsx)(_components.td, {
            children: (0,jsx_runtime.jsx)(_components.a, {
              href: "https://cips.cardano.org/cip/CIP-0110",
              children: "110"
            })
          }), (0,jsx_runtime.jsxs)(_components.td, {
            children: [(0,jsx_runtime.jsx)(_components.strong, {
              children: "Plutus v1 Script References"
            }), " - Enables reference scripts for PlutusV1"]
          }), (0,jsx_runtime.jsx)(_components.td, {
            children: "Active"
          })]
        }), (0,jsx_runtime.jsxs)(_components.tr, {
          children: [(0,jsx_runtime.jsx)(_components.td, {
            children: (0,jsx_runtime.jsx)(_components.a, {
              href: "https://cips.cardano.org/cip/CIP-0112",
              children: "112"
            })
          }), (0,jsx_runtime.jsxs)(_components.td, {
            children: [(0,jsx_runtime.jsx)(_components.strong, {
              children: "Observe Script Type"
            }), " - Allows scripts to observe their own type during execution"]
          }), (0,jsx_runtime.jsx)(_components.td, {
            children: "Proposed"
          })]
        }), (0,jsx_runtime.jsxs)(_components.tr, {
          children: [(0,jsx_runtime.jsx)(_components.td, {
            children: (0,jsx_runtime.jsx)(_components.a, {
              href: "https://cips.cardano.org/cip/CIP-0117",
              children: "117"
            })
          }), (0,jsx_runtime.jsxs)(_components.td, {
            children: [(0,jsx_runtime.jsx)(_components.strong, {
              children: "Explicit script return values"
            }), " - Improves script return value handling"]
          }), (0,jsx_runtime.jsx)(_components.td, {
            children: "Active"
          })]
        }), (0,jsx_runtime.jsxs)(_components.tr, {
          children: [(0,jsx_runtime.jsx)(_components.td, {
            children: (0,jsx_runtime.jsx)(_components.a, {
              href: "https://cips.cardano.org/cip/CIP-0121",
              children: "121"
            })
          }), (0,jsx_runtime.jsxs)(_components.td, {
            children: [(0,jsx_runtime.jsx)(_components.strong, {
              children: "Integer-ByteString conversions"
            }), " - Adds integer to bytestring conversion builtins"]
          }), (0,jsx_runtime.jsx)(_components.td, {
            children: "Active"
          })]
        }), (0,jsx_runtime.jsxs)(_components.tr, {
          children: [(0,jsx_runtime.jsx)(_components.td, {
            children: (0,jsx_runtime.jsx)(_components.a, {
              href: "https://cips.cardano.org/cip/CIP-0122",
              children: "122"
            })
          }), (0,jsx_runtime.jsxs)(_components.td, {
            children: [(0,jsx_runtime.jsx)(_components.strong, {
              children: "Logical operations over BuiltinByteString"
            }), " - Adds bitwise logical operations"]
          }), (0,jsx_runtime.jsx)(_components.td, {
            children: "Active"
          })]
        }), (0,jsx_runtime.jsxs)(_components.tr, {
          children: [(0,jsx_runtime.jsx)(_components.td, {
            children: (0,jsx_runtime.jsx)(_components.a, {
              href: "https://cips.cardano.org/cip/CIP-0123",
              children: "123"
            })
          }), (0,jsx_runtime.jsxs)(_components.td, {
            children: [(0,jsx_runtime.jsx)(_components.strong, {
              children: "Bitwise operations over BuiltinByteString"
            }), " - Bitwise shift and rotation operations"]
          }), (0,jsx_runtime.jsx)(_components.td, {
            children: "Active"
          })]
        }), (0,jsx_runtime.jsxs)(_components.tr, {
          children: [(0,jsx_runtime.jsx)(_components.td, {
            children: (0,jsx_runtime.jsx)(_components.a, {
              href: "https://cips.cardano.org/cip/CIP-0127",
              children: "127"
            })
          }), (0,jsx_runtime.jsxs)(_components.td, {
            children: [(0,jsx_runtime.jsx)(_components.strong, {
              children: "ripemd-160 hashing in Plutus Core"
            }), " - Adds RIPEMD-160 hash function builtin"]
          }), (0,jsx_runtime.jsx)(_components.td, {
            children: "Active"
          })]
        }), (0,jsx_runtime.jsxs)(_components.tr, {
          children: [(0,jsx_runtime.jsx)(_components.td, {
            children: (0,jsx_runtime.jsx)(_components.a, {
              href: "https://cips.cardano.org/cip/CIP-0132",
              children: "132"
            })
          }), (0,jsx_runtime.jsxs)(_components.td, {
            children: [(0,jsx_runtime.jsx)(_components.strong, {
              children: "New Plutus Builtin dropList"
            }), " - Adds dropList builtin function"]
          }), (0,jsx_runtime.jsx)(_components.td, {
            children: "Proposed"
          })]
        }), (0,jsx_runtime.jsxs)(_components.tr, {
          children: [(0,jsx_runtime.jsx)(_components.td, {
            children: (0,jsx_runtime.jsx)(_components.a, {
              href: "https://cips.cardano.org/cip/CIP-0133",
              children: "133"
            })
          }), (0,jsx_runtime.jsxs)(_components.td, {
            children: [(0,jsx_runtime.jsx)(_components.strong, {
              children: "Plutus support for Multi-Scalar Multiplication over BLS12-381"
            }), " - Adds BLS12-381 multi-scalar multiplication"]
          }), (0,jsx_runtime.jsx)(_components.td, {
            children: "Proposed"
          })]
        }), (0,jsx_runtime.jsxs)(_components.tr, {
          children: [(0,jsx_runtime.jsx)(_components.td, {
            children: (0,jsx_runtime.jsx)(_components.a, {
              href: "https://cips.cardano.org/cip/CIP-0138",
              children: "138"
            })
          }), (0,jsx_runtime.jsxs)(_components.td, {
            children: [(0,jsx_runtime.jsx)(_components.strong, {
              children: "Plutus Core Builtin Type - Array"
            }), " - Adds Array as a builtin type"]
          }), (0,jsx_runtime.jsx)(_components.td, {
            children: "Proposed"
          })]
        }), (0,jsx_runtime.jsxs)(_components.tr, {
          children: [(0,jsx_runtime.jsx)(_components.td, {
            children: (0,jsx_runtime.jsx)(_components.a, {
              href: "https://cips.cardano.org/cip/CIP-0141",
              children: "141"
            })
          }), (0,jsx_runtime.jsxs)(_components.td, {
            children: [(0,jsx_runtime.jsx)(_components.strong, {
              children: "Web-Wallet Bridge - Plutus wallets"
            }), " - Wallet bridge specification specifically for Plutus-enabled wallets"]
          }), (0,jsx_runtime.jsx)(_components.td, {
            children: "Proposed"
          })]
        }), (0,jsx_runtime.jsxs)(_components.tr, {
          children: [(0,jsx_runtime.jsx)(_components.td, {
            children: (0,jsx_runtime.jsx)(_components.a, {
              href: "https://cips.cardano.org/cip/CIP-0152",
              children: "152"
            })
          }), (0,jsx_runtime.jsxs)(_components.td, {
            children: [(0,jsx_runtime.jsx)(_components.strong, {
              children: "Modules in UPLC"
            }), " - Introduces module system to Untyped Plutus Core"]
          }), (0,jsx_runtime.jsx)(_components.td, {
            children: "Proposed"
          })]
        }), (0,jsx_runtime.jsxs)(_components.tr, {
          children: [(0,jsx_runtime.jsx)(_components.td, {
            children: (0,jsx_runtime.jsx)(_components.a, {
              href: "https://cips.cardano.org/cip/CIP-0153",
              children: "153"
            })
          }), (0,jsx_runtime.jsxs)(_components.td, {
            children: [(0,jsx_runtime.jsx)(_components.strong, {
              children: "Plutus Core Builtin Type - MaryEraValue"
            }), " - Adds MaryEraValue as a builtin type"]
          }), (0,jsx_runtime.jsx)(_components.td, {
            children: "Proposed"
          })]
        }), (0,jsx_runtime.jsxs)(_components.tr, {
          children: [(0,jsx_runtime.jsx)(_components.td, {
            children: (0,jsx_runtime.jsx)(_components.a, {
              href: "https://cips.cardano.org/cip/CIP-0156",
              children: "156"
            })
          }), (0,jsx_runtime.jsxs)(_components.td, {
            children: [(0,jsx_runtime.jsx)(_components.strong, {
              children: "Plutus Core Builtin Function - multiIndexArray"
            }), " - Adds multi-dimensional array indexing builtin"]
          }), (0,jsx_runtime.jsx)(_components.td, {
            children: "Proposed"
          })]
        }), (0,jsx_runtime.jsxs)(_components.tr, {
          children: [(0,jsx_runtime.jsx)(_components.td, {
            children: (0,jsx_runtime.jsx)(_components.a, {
              href: "https://cips.cardano.org/cip/CIP-0381",
              children: "381"
            })
          }), (0,jsx_runtime.jsxs)(_components.td, {
            children: [(0,jsx_runtime.jsx)(_components.strong, {
              children: "Plutus support for Pairings over BLS12-381"
            }), " - Adds elliptic curve pairing operations for cryptography"]
          }), (0,jsx_runtime.jsx)(_components.td, {
            children: "Active"
          })]
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