"use strict";
(self["webpackChunkdocusaurus"] = self["webpackChunkdocusaurus"] || []).push([[15],{

/***/ 1402:
/***/ ((__unused_webpack_module, __webpack_exports__, __webpack_require__) => {

// ESM COMPAT FLAG
__webpack_require__.r(__webpack_exports__);

// EXPORTS
__webpack_require__.d(__webpack_exports__, {
  assets: () => (/* binding */ assets),
  contentTitle: () => (/* binding */ contentTitle),
  "default": () => (/* binding */ MDXContent),
  frontMatter: () => (/* binding */ frontMatter),
  metadata: () => (/* reexport */ site_docs_working_with_scripts_script_purposes_md_cc5_namespaceObject),
  toc: () => (/* binding */ toc)
});

;// ./.docusaurus/docusaurus-plugin-content-docs/default/site-docs-working-with-scripts-script-purposes-md-cc5.json
const site_docs_working_with_scripts_script_purposes_md_cc5_namespaceObject = /*#__PURE__*/JSON.parse('{"id":"working-with-scripts/script-purposes","title":"Script Purposes","description":"One of the arguments every Plutus script receives is the script context, containing information about the transaction the script is validating.","source":"@site/docs/working-with-scripts/script-purposes.md","sourceDirName":"working-with-scripts","slug":"/working-with-scripts/script-purposes","permalink":"/pr-preview/docs/pr-7541/working-with-scripts/script-purposes","draft":false,"unlisted":false,"editUrl":"https://github.com/IntersectMBO/plutus/edit/master/doc/docusaurus/docs/working-with-scripts/script-purposes.md","tags":[],"version":"current","sidebarPosition":2,"frontMatter":{"sidebar_position":2},"sidebar":"tutorialSidebar","previous":{"title":"Plutus Ledger Language Version (Plutus V1/V2/V3)","permalink":"/pr-preview/docs/pr-7541/working-with-scripts/ledger-language-version"},"next":{"title":"Producing a Plutus contract blueprint","permalink":"/pr-preview/docs/pr-7541/working-with-scripts/producing-a-blueprint"}}');
// EXTERNAL MODULE: ./node_modules/react/jsx-runtime.js
var jsx_runtime = __webpack_require__(4848);
// EXTERNAL MODULE: ./node_modules/@mdx-js/react/lib/index.js
var lib = __webpack_require__(8453);
;// ./docs/working-with-scripts/script-purposes.md


const frontMatter = {
	sidebar_position: 2
};
const contentTitle = 'Script Purposes';

const assets = {

};



const toc = [{
  "value": "Spending",
  "id": "spending",
  "level": 2
}, {
  "value": "Minting",
  "id": "minting",
  "level": 2
}, {
  "value": "Rewarding",
  "id": "rewarding",
  "level": 2
}, {
  "value": "Certifying",
  "id": "certifying",
  "level": 2
}, {
  "value": "Voting",
  "id": "voting",
  "level": 2
}, {
  "value": "Proposing",
  "id": "proposing",
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
    ...(0,lib/* useMDXComponents */.R)(),
    ...props.components
  };
  return (0,jsx_runtime.jsxs)(jsx_runtime.Fragment, {
    children: [(0,jsx_runtime.jsx)(_components.header, {
      children: (0,jsx_runtime.jsx)(_components.h1, {
        id: "script-purposes",
        children: "Script Purposes"
      })
    }), "\n", (0,jsx_runtime.jsx)(_components.p, {
      children: "One of the arguments every Plutus script receives is the script context, containing information about the transaction the script is validating.\nOne of the fields of script context is the script purpose.\nSince a transaction may do multiple things, each of which is validated by a separate  script, the script purpose informs a script what exactly it is supposed to validate."
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["Plutus V1 and V2 share the same ", (0,jsx_runtime.jsx)(_components.a, {
        href: "https://plutus.cardano.intersectmbo.org/haddock/master/plutus-ledger-api/PlutusLedgerApi-V1-Contexts.html#t:ScriptPurpose",
        children: (0,jsx_runtime.jsx)(_components.code, {
          children: "ScriptPurpose"
        })
      }), " type with four variants: spending, minting, rewarding and certifying.\nPlutus V3's ", (0,jsx_runtime.jsx)(_components.a, {
        href: "https://plutus.cardano.intersectmbo.org/haddock/master/plutus-ledger-api/PlutusLedgerApi-V3-Contexts.html#t:ScriptPurpose",
        children: (0,jsx_runtime.jsx)(_components.code, {
          children: "ScriptPurpose"
        })
      }), " has two additional variants: voting and proposing.\nNext we go over and explain all these different script purposes."]
    }), "\n", (0,jsx_runtime.jsx)(_components.h2, {
      id: "spending",
      children: "Spending"
    }), "\n", (0,jsx_runtime.jsx)(_components.p, {
      children: "A spending script validates the spending of a UTXO.\nA UTXO can have either a public key address or a script address.\nTo spend a UTXO with a script address, the script whose hash matches the script address must be included in the transaction (either directly, or as a reference script), and is executed to validate it."
    }), "\n", (0,jsx_runtime.jsx)(_components.p, {
      children: "The script can make the decision based on the datum attached in the UTXO being spent, if any (datum is mandatory for Plutus V1 and V2, i.e., a UTXO with a Plutus V1 or V2 script address but without a datum cannot be spent; datum is optional for Plutus V3), the redeemer included in the transaction, as well as other fields of the transaction."
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["The ", (0,jsx_runtime.jsx)(_components.code, {
        children: "Spending"
      }), " constructor of ", (0,jsx_runtime.jsx)(_components.code, {
        children: "ScriptPurpose"
      }), " includes a ", (0,jsx_runtime.jsx)(_components.code, {
        children: "TxOutRef"
      }), " field that references the UTXO the script is validating, which is also one of the UTXOs the transaction attempts to spend."]
    }), "\n", (0,jsx_runtime.jsx)(_components.h2, {
      id: "minting",
      children: "Minting"
    }), "\n", (0,jsx_runtime.jsx)(_components.p, {
      children: "Minting scripts, sometimes also referred to as minting policies, are used to approve or reject minting of new assets."
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["In Cardano, we can uniquely identify an asset by its ", (0,jsx_runtime.jsx)(_components.code, {
        children: "CurrencySymbol"
      }), " and ", (0,jsx_runtime.jsx)(_components.code, {
        children: "TokenName"
      }), ".\nIf a transaction attempts to mint some new assets, then for each unique ", (0,jsx_runtime.jsx)(_components.code, {
        children: "CurrencySymbol"
      }), " in the new assets, the script whose hash matches the ", (0,jsx_runtime.jsx)(_components.code, {
        children: "CurrencySymbol"
      }), " must be included in the transaction, and is executed to validate the minting of that ", (0,jsx_runtime.jsx)(_components.code, {
        children: "CurrencySymbol"
      }), ".\nThis is the reason why the ", (0,jsx_runtime.jsx)(_components.code, {
        children: "Minting"
      }), " constructor of ", (0,jsx_runtime.jsx)(_components.code, {
        children: "ScriptPurpose"
      }), " contains a ", (0,jsx_runtime.jsx)(_components.code, {
        children: "CurrencySymbol"
      }), " field."]
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["A minting script should pay attention to the fact that the transaction may attempt to mint multiple assets with the same ", (0,jsx_runtime.jsx)(_components.code, {
        children: "CurrencySymbol"
      }), " but different ", (0,jsx_runtime.jsx)(_components.code, {
        children: "TokenNames"
      }), ".\nIn general all these assets with the same ", (0,jsx_runtime.jsx)(_components.code, {
        children: "CurrencySymbol"
      }), " should be checked."]
    }), "\n", (0,jsx_runtime.jsx)(_components.h2, {
      id: "rewarding",
      children: "Rewarding"
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["As previously stated, a UTXO's address can be either a public key address or a script address.\nBoth kinds of addresses can optionally have a staking credential.\nA UTXO may contain Ada, and the Ada it contains can be delegated to an SPO to earn staking rewards.\nStaking rewards are deposited into a reward account", (0,jsx_runtime.jsx)(_components.sup, {
        children: (0,jsx_runtime.jsx)(_components.a, {
          href: "#user-content-fn-1",
          id: "user-content-fnref-1",
          "data-footnote-ref": true,
          "aria-describedby": "footnote-label",
          children: "1"
        })
      }), " corresponding to the staking credential."]
    }), "\n", (0,jsx_runtime.jsx)(_components.p, {
      children: "A staking credential can contain either a public key hash or a script hash.\nTo withdraw rewards from a reward account corresponding to a staking credential that contains a script hash, the script with that particular hash must be included in the transaction, and is executed to validate the withdrawal."
    }), "\n", (0,jsx_runtime.jsx)(_components.p, {
      children: "The script might set conditions on reward distribution, such as ensuring that any withdrawal are deposited into one of the designated addresses."
    }), "\n", (0,jsx_runtime.jsx)(_components.h2, {
      id: "certifying",
      children: "Certifying"
    }), "\n", (0,jsx_runtime.jsx)(_components.p, {
      children: "A certifying script can validate a number of certificate-related transactions, such as: (1) registering a staking credential, and in doing so, creating a reward account associated with the staking credential; (2) de-registering a staking credential, and in doing so, terminating the reward account; (3) delegating a staking credential to a particular delegatee."
    }), "\n", (0,jsx_runtime.jsx)(_components.p, {
      children: "In all these cases except registration, if the staking credential in question contains a script hash (as opposed to a public key hash), the script with that hash must be included in the transaction, and is executed to validate the action."
    }), "\n", (0,jsx_runtime.jsx)(_components.p, {
      children: "Such a script may, for instance, check that certain signatures be provided for de-registration and delegation, or that the delegatee must be among the allowed delegatees."
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["In Conway and all previous eras, including the associated script for registering a staking credential in a transaction is optional. This is due to the availability of two different certificates for registering staking credentials: ", (0,jsx_runtime.jsx)(_components.code, {
        children: "stake_registration"
      }), ", which does not require a witness, and ", (0,jsx_runtime.jsx)(_components.code, {
        children: "reg_cert"
      }), ", which does require the script credential as a witness. When using ", (0,jsx_runtime.jsx)(_components.code, {
        children: "reg_cert"
      }), ", the script must be included in the transaction. In the era following Conway, the ", (0,jsx_runtime.jsx)(_components.code, {
        children: "stake_registration"
      }), " certificate, which allows for the registration of script credentials without a script witness, will be deprecated. After this change, all stake credential registration transactions will require the script associated with a script hash to be included in the transaction, aligning them with the behavior of all other certificate-related transactions."]
    }), "\n", (0,jsx_runtime.jsx)(_components.h2, {
      id: "voting",
      children: "Voting"
    }), "\n", (0,jsx_runtime.jsx)(_components.p, {
      children: "A voting script validates votes cast by a Delegated Representative (DRep) or a constitutional committee member (CCM) in a transaction.\nA DRep or a CCM can be associated with a script hash.\nIf a transaction contains one or more votes from a DRep or a constitution committee member associated with a script hash, the script with that hash must be included in the transaction, and is executed to approve or reject the vote."
    }), "\n", (0,jsx_runtime.jsx)(_components.h2, {
      id: "proposing",
      children: "Proposing"
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["A proposing script, also known as constitution script or guardrail script, validates two kinds of ", (0,jsx_runtime.jsx)(_components.a, {
        href: "https://plutus.cardano.intersectmbo.org/haddock/master/plutus-ledger-api/PlutusLedgerApi-V3-Contexts.html#t:ScriptContext",
        children: "governance actions"
      }), ": ", (0,jsx_runtime.jsx)(_components.code, {
        children: "ParameterChange"
      }), " and ", (0,jsx_runtime.jsx)(_components.code, {
        children: "TreasuryWithdrawals"
      }), "."]
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["There is a key distinction between proposing scripts and other kinds of scripts: proposing scripts are not written by regular users.\nAt any given point in time, there is exactly one active proposing script being used by the entire chain.\nThis proposing script must be included in transactions that propose ", (0,jsx_runtime.jsx)(_components.code, {
        children: "ParameterChange"
      }), " or ", (0,jsx_runtime.jsx)(_components.code, {
        children: "TreasuryWithdrawals"
      }), ".\nThe ledger enforces that no other proposing script is accepted.\nThe proposing script is updated only when there is a change to the constitution, via the ", (0,jsx_runtime.jsx)(_components.code, {
        children: "NewConstitution"
      }), " governance action."]
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["Note that what the proposing script decides is whether the ", (0,jsx_runtime.jsx)(_components.em, {
        children: "proposal"
      }), " of a governance action is allowed to go through, rather than whether the governance action will be enacted.\nAfter a proposal goes through, it will need to meet the appropriate criteria (such as gathering enough votes from constitution committee members, DReps and/or SPOs) in order to be enacted."]
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
            children: ["Reward accounts are distinct from UTXOs, and are more akin to accounts in account-based blockchains.\nThey are used for accumulating staking rewards, rather than using UTXOs, in order to avoid creating a large number of UTXOs with tiny values.\nReward accounts are special on Cardano and cannot be created arbitrarily.\nEach reward account is associated with a staking credential, and is created automatically when the staking credential is registered. ", (0,jsx_runtime.jsx)(_components.a, {
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