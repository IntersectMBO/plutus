"use strict";
(self["webpackChunkdocusaurus"] = self["webpackChunkdocusaurus"] || []).push([[8041],{

/***/ 4814:
/***/ ((__unused_webpack_module, __webpack_exports__, __webpack_require__) => {

// ESM COMPAT FLAG
__webpack_require__.r(__webpack_exports__);

// EXPORTS
__webpack_require__.d(__webpack_exports__, {
  assets: () => (/* binding */ assets),
  contentTitle: () => (/* binding */ contentTitle),
  "default": () => (/* binding */ MDXContent),
  frontMatter: () => (/* binding */ frontMatter),
  metadata: () => (/* reexport */ site_docs_working_with_scripts_optimizing_scripts_with_as_data_md_270_namespaceObject),
  toc: () => (/* binding */ toc)
});

;// ./.docusaurus/docusaurus-plugin-content-docs/default/site-docs-working-with-scripts-optimizing-scripts-with-as-data-md-270.json
const site_docs_working_with_scripts_optimizing_scripts_with_as_data_md_270_namespaceObject = /*#__PURE__*/JSON.parse('{"id":"working-with-scripts/optimizing-scripts-with-asData","title":"Optimizing Scripts with asData","description":"The Plutus libraries contain a PlutusTx.asData module that contains Template Haskell (TH) code for encoding algebraic data types (ADTs) as Data objects in Plutus Core, as opposed to sums-of-products terms.","source":"@site/docs/working-with-scripts/optimizing-scripts-with-asData.md","sourceDirName":"working-with-scripts","slug":"/working-with-scripts/optimizing-scripts-with-asData","permalink":"/pr-preview/docs/pr-7417/working-with-scripts/optimizing-scripts-with-asData","draft":false,"unlisted":false,"editUrl":"https://github.com/IntersectMBO/plutus/edit/master/doc/docusaurus/docs/working-with-scripts/optimizing-scripts-with-asData.md","tags":[],"version":"current","sidebarPosition":20,"frontMatter":{"sidebar_position":20},"sidebar":"tutorialSidebar","previous":{"title":"Producing a Plutus contract blueprint","permalink":"/pr-preview/docs/pr-7417/working-with-scripts/producing-a-blueprint"},"next":{"title":"Simplifying Code Before Compilation","permalink":"/pr-preview/docs/pr-7417/working-with-scripts/simplifying-before-compilation"}}');
// EXTERNAL MODULE: ./node_modules/react/jsx-runtime.js
var jsx_runtime = __webpack_require__(4848);
// EXTERNAL MODULE: ./node_modules/@mdx-js/react/lib/index.js
var lib = __webpack_require__(8453);
;// ./docs/working-with-scripts/optimizing-scripts-with-asData.md


const frontMatter = {
	sidebar_position: 20
};
const contentTitle = 'Optimizing Scripts with asData';

const assets = {

};



const toc = [{
  "value": "Purpose",
  "id": "purpose",
  "level": 2
}, {
  "value": "Choice of two approaches",
  "id": "choice-of-two-approaches",
  "level": 2
}, {
  "value": "Approach one: proactively do all of the parsing",
  "id": "approach-one-proactively-do-all-of-the-parsing",
  "level": 3
}, {
  "value": "Approach two: only do the parsing if and when necessary",
  "id": "approach-two-only-do-the-parsing-if-and-when-necessary",
  "level": 3
}, {
  "value": "<code>Data</code>-backed Plinth standard library",
  "id": "data-backed-plinth-standard-library",
  "level": 2
}, {
  "value": "Using <code>asData</code>",
  "id": "using-asdata",
  "level": 2
}, {
  "value": "Nested fields",
  "id": "nested-fields",
  "level": 3
}, {
  "value": "Writing optimal code using <code>asData</code>",
  "id": "writing-optimal-code-using-asdata",
  "level": 3
}, {
  "value": "Choosing an approach",
  "id": "choosing-an-approach",
  "level": 2
}, {
  "value": "Data-backed <code>ScriptContext</code>",
  "id": "data-backed-scriptcontext",
  "level": 2
}];
function _createMdxContent(props) {
  const _components = {
    a: "a",
    code: "code",
    em: "em",
    h1: "h1",
    h2: "h2",
    h3: "h3",
    header: "header",
    li: "li",
    ol: "ol",
    p: "p",
    pre: "pre",
    ul: "ul",
    ...(0,lib/* useMDXComponents */.R)(),
    ...props.components
  }, {LiteralInclude} = _components;
  if (!LiteralInclude) _missingMdxReference("LiteralInclude", true);
  return (0,jsx_runtime.jsxs)(jsx_runtime.Fragment, {
    children: [(0,jsx_runtime.jsx)(_components.header, {
      children: (0,jsx_runtime.jsxs)(_components.h1, {
        id: "optimizing-scripts-with-asdata",
        children: ["Optimizing Scripts with ", (0,jsx_runtime.jsx)(_components.code, {
          children: "asData"
        })]
      })
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["The Plutus libraries contain a ", (0,jsx_runtime.jsx)(_components.code, {
        children: "PlutusTx.asData"
      }), " module that contains Template Haskell (TH) code for encoding algebraic data types (ADTs) as ", (0,jsx_runtime.jsx)(_components.code, {
        children: "Data"
      }), " objects in Plutus Core, as opposed to sums-of-products terms.\nIn general, ", (0,jsx_runtime.jsx)(_components.code, {
        children: "asData"
      }), " pushes the burden of a computation nearer to where a value is used, in a crude sense making the evaluation less strict and more lazy.\nThis is intended for expert Plutus developers."]
    }), "\n", (0,jsx_runtime.jsx)(_components.h2, {
      id: "purpose",
      children: "Purpose"
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["Values stored in datums or redeemers need to be encoded into ", (0,jsx_runtime.jsx)(_components.code, {
        children: "Data"
      }), " objects.\nWhen writing and optimizing a Plutus script, one of the challenges is finding the right approach to handling ", (0,jsx_runtime.jsx)(_components.code, {
        children: "Data"
      }), " objects and how expensive that method will be.\nTo make an informed decision, you may need to benchmark and profile your smart contract code to measure its actual resource consumption.\nThe primary purpose of ", (0,jsx_runtime.jsx)(_components.code, {
        children: "asData"
      }), " is to give you more options for how you want to handle ", (0,jsx_runtime.jsx)(_components.code, {
        children: "Data"
      }), "."]
    }), "\n", (0,jsx_runtime.jsx)(_components.h2, {
      id: "choice-of-two-approaches",
      children: "Choice of two approaches"
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["When handling ", (0,jsx_runtime.jsx)(_components.code, {
        children: "Data"
      }), " objects, you have a choice of two pathways.\nIt is up to you to determine which pathway to use depending on your particular use case.\nThere are trade offs in performance and where errors occur."]
    }), "\n", (0,jsx_runtime.jsx)(_components.h3, {
      id: "approach-one-proactively-do-all-of-the-parsing",
      children: "Approach one: proactively do all of the parsing"
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["The first approach is to parse the object immediately (using ", (0,jsx_runtime.jsx)(_components.code, {
        children: "fromBuiltinData"
      }), ") into a native Plutus Core datatype, which will also identify any problems with the structuring of the object.\nHowever, this performs all the work up front."]
    }), "\n", (0,jsx_runtime.jsx)(_components.p, {
      children: "This is the normal style that has been promoted in the past."
    }), "\n", (0,jsx_runtime.jsx)(_components.h3, {
      id: "approach-two-only-do-the-parsing-if-and-when-necessary",
      children: "Approach two: only do the parsing if and when necessary"
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["In the second approach, the script doesn't do any parsing work immediately, and instead does it later, when it needs to.\nIt might be that this saves you a lot of work, because you may never need to parse the entire object.\nInstead, the script will just carry the item around as a ", (0,jsx_runtime.jsx)(_components.code, {
        children: "Data"
      }), " object."]
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["Using this method, every time the script uses the object, it will look at it to find out if it has the right shape.\nIf it does have the right shape, it will deconstruct the ", (0,jsx_runtime.jsx)(_components.code, {
        children: "Data"
      }), " object and do its processing; if\nnot, it will throw an error.\nThis work may be repeated depending on how your script is written.\nIn some cases, you might do less work, in some cases you might do more work, depending on your specific use case."]
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["The Plinth library provides some helper types and functions to make this second style easier to do, in the form of the \"data-backed\" standard types and the ", (0,jsx_runtime.jsx)(_components.code, {
        children: "asData"
      }), " function."]
    }), "\n", (0,jsx_runtime.jsxs)(_components.h2, {
      id: "data-backed-plinth-standard-library",
      children: [(0,jsx_runtime.jsx)(_components.code, {
        children: "Data"
      }), "-backed Plinth standard library"]
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["The Plinth standard library provides some common types which are already defined as ", (0,jsx_runtime.jsx)(_components.code, {
        children: "Data"
      }), " objects under the hood.\nWe refer to such types as being ", (0,jsx_runtime.jsx)(_components.em, {
        children: "data-backed"
      }), "."]
    }), "\n", (0,jsx_runtime.jsxs)(_components.ul, {
      children: ["\n", (0,jsx_runtime.jsxs)(_components.li, {
        children: [(0,jsx_runtime.jsx)(_components.a, {
          href: "https://plutus.cardano.intersectmbo.org/haddock/master/plutus-tx/PlutusTx-Data-List.html#t:List",
          children: "PlutusTx.Data.List.List"
        }), ", a data-backed version of the regular Plinth ", (0,jsx_runtime.jsx)(_components.code, {
          children: "[]"
        }), " type."]
      }), "\n", (0,jsx_runtime.jsxs)(_components.li, {
        children: [(0,jsx_runtime.jsx)(_components.a, {
          href: "https://plutus.cardano.intersectmbo.org/haddock/master/plutus-tx/PlutusTx-Data-AssocMap.html#t:Map",
          children: "PlutusTx.Data.AssocMap.Map"
        }), ", which is the data-backed version of ", (0,jsx_runtime.jsx)(_components.code, {
          children: "PlutusTx.AssocMap.Map"
        }), "."]
      }), "\n"]
    }), "\n", (0,jsx_runtime.jsx)(_components.p, {
      children: "These types provide similar APIs to their regular Plinth counterparts."
    }), "\n", (0,jsx_runtime.jsx)(_components.p, {
      children: "There are also conversion functions between the two representations, and it is up to the developer to decide when or whether to convert to the regular representation or to use the data-backed API.\nIt depends on a case-by-case basis whether the data-backed or the regular versions perform the best."
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["It is, however, recommended to use them instead of the regular Plinth types when they are part of other types defined using ", (0,jsx_runtime.jsx)(_components.code, {
        children: "asData"
      }), "."]
    }), "\n", (0,jsx_runtime.jsxs)(_components.h2, {
      id: "using-asdata",
      children: ["Using ", (0,jsx_runtime.jsx)(_components.code, {
        children: "asData"
      })]
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["The ", (0,jsx_runtime.jsx)(_components.code, {
        children: "asData"
      }), " function takes the definition of a data type and replaces it with an equivalent definition whose representation uses ", (0,jsx_runtime.jsx)(_components.code, {
        children: "Data"
      }), " directly."]
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["For example, if we wanted to use it on the types from the ", (0,jsx_runtime.jsx)(_components.a, {
        href: "/pr-preview/docs/pr-7417/auction-smart-contract/on-chain-code",
        children: "auction example"
      }), ", we would put the datatype declarations inside a Template Haskell quote and call ", (0,jsx_runtime.jsx)(_components.code, {
        children: "asData"
      }), " on it."]
    }), "\n", (0,jsx_runtime.jsx)(LiteralInclude, {
      file: "AuctionValidator.hs",
      language: "haskell",
      title: "",
      start: "-- BLOCK9",
      end: "-- BLOCK10"
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["This is normal Template Haskell that just generates new Haskell source, so you can see the code that it generates with ", (0,jsx_runtime.jsx)(_components.code, {
        children: "{-# OPTIONS_GHC-ddump-splices #-}"
      }), " but it will look something like this:"]
    }), "\n", (0,jsx_runtime.jsx)(_components.pre, {
      children: (0,jsx_runtime.jsx)(_components.code, {
        children: "PlutusTx.asData\n[d| data Bid'\n        = Bid' {bBidder' :: PubKeyHash, bAmount' :: Lovelace}\n        deriving newtype (Eq, Ord, ToBuitinData, FromBuiltinData, UnsafeFromBuiltinData)\n    data AuctionRedeemer' = NewBid' Bid | Payout'\n        deriving newtype (Eq, Ord, ToBuitinData, FromBuiltinData, UnsafeFromBuiltinData) |]\n\n======>\n\nnewtype Bid' = Bid'2 BuiltinData\nderiving newtype (Eq, Ord, PlutusTx.ToData, FromData, UnsafeFromData)\n\n{-# COMPLETE Bid' #-}\npattern Bid' :: PubKeyHash -> Lovelace -> Bid'\npattern Bid' ...\n\nnewtype AuctionRedeemer' = AuctionRedeemer'2 BuiltinData\nderiving newtype (Eq, Ord, PlutusTx.ToData, FromData, UnsafeFromData)\n\n{-# COMPLETE NewBid', Payout' #-}\npattern NewBid' :: Bid -> AuctionRedeemer'\npattern NewBid' ...\npattern Payout' :: AuctionRedeemer'\npattern Payout' ...\n"
      })
    }), "\n", (0,jsx_runtime.jsx)(_components.p, {
      children: "That is:"
    }), "\n", (0,jsx_runtime.jsxs)(_components.ul, {
      children: ["\n", (0,jsx_runtime.jsxs)(_components.li, {
        children: ["It creates a newtype wrapper around ", (0,jsx_runtime.jsx)(_components.code, {
          children: "BuiltinData"
        })]
      }), "\n", (0,jsx_runtime.jsx)(_components.li, {
        children: "It creates pattern synonyms corresponding to each of the constructors you wrote"
      }), "\n"]
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["This lets you write code \"as if\" you were using the original declaration that you wrote, while in fact the pattern synonyms are handling conversion to/from ", (0,jsx_runtime.jsx)(_components.code, {
        children: "Data"
      }), " for you.\nBut any values of this type actually are represented with ", (0,jsx_runtime.jsx)(_components.code, {
        children: "Data"
      }), ".\nThat means that when we newtype-derive the instances for converting to and from ", (0,jsx_runtime.jsx)(_components.code, {
        children: "Data"
      }), " we get\nthe instances for ", (0,jsx_runtime.jsx)(_components.code, {
        children: "BuiltinData"
      }), " - which are free!"]
    }), "\n", (0,jsx_runtime.jsx)(_components.h3, {
      id: "nested-fields",
      children: "Nested fields"
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["The most important caveat to using ", (0,jsx_runtime.jsx)(_components.code, {
        children: "asData"
      }), " is that ", (0,jsx_runtime.jsx)(_components.code, {
        children: "Data"
      }), " objects encoding datatypes must also encode the ", (0,jsx_runtime.jsx)(_components.em, {
        children: "fields"
      }), " of the datatype as ", (0,jsx_runtime.jsx)(_components.code, {
        children: "Data"
      }), ".\nHowever, ", (0,jsx_runtime.jsx)(_components.code, {
        children: "asData"
      }), " tries to make the generated code a drop-in replacement for the original code, which means that when using the pattern synonyms they try to give you the fields as they were originally defined, which means ", (0,jsx_runtime.jsx)(_components.em, {
        children: "not"
      }), " encoded as ", (0,jsx_runtime.jsx)(_components.code, {
        children: "Data"
      }), "."]
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["For example, in the ", (0,jsx_runtime.jsx)(_components.code, {
        children: "Bid"
      }), " case above the ", (0,jsx_runtime.jsx)(_components.code, {
        children: "bAmount"
      }), " field is originally defined to have type ", (0,jsx_runtime.jsx)(_components.code, {
        children: "Lovelace"
      }), " which is a newtype around a Plutus Core builtin integer.\nHowever, since we are using ", (0,jsx_runtime.jsx)(_components.code, {
        children: "asData"
      }), ", we need to encode the field into ", (0,jsx_runtime.jsx)(_components.code, {
        children: "Data"
      }), " in order to store it.\nThat means that when you construct a ", (0,jsx_runtime.jsx)(_components.code, {
        children: "Bid"
      }), " object you must take the ", (0,jsx_runtime.jsx)(_components.code, {
        children: "Integer"
      }), " that you start with and convert it to ", (0,jsx_runtime.jsx)(_components.code, {
        children: "Data"
      }), ", and when you pattern match on a ", (0,jsx_runtime.jsx)(_components.code, {
        children: "Bid"
      }), " object you do the reverse conversion."]
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["These conversions are potentially expensive!\nIf the ", (0,jsx_runtime.jsx)(_components.code, {
        children: "bAmount"
      }), " field was a complex data structure, then every time we constructed or deconstructed a ", (0,jsx_runtime.jsx)(_components.code, {
        children: "Bid"
      }), " object we would need to convert that datastructure to or from ", (0,jsx_runtime.jsx)(_components.code, {
        children: "Data"
      }), ".\nWhether or not this is a problem depends on the precise situation, but in general:"]
    }), "\n", (0,jsx_runtime.jsxs)(_components.ul, {
      children: ["\n", (0,jsx_runtime.jsx)(_components.li, {
        children: "If the field is a builtin integer or bytestring or a wrapper around those, it is probably cheap"
      }), "\n", (0,jsx_runtime.jsxs)(_components.li, {
        children: ["If the field is a datatype which is itself defined with ", (0,jsx_runtime.jsx)(_components.code, {
          children: "asData"
        }), " then it is free (since it's already ", (0,jsx_runtime.jsx)(_components.code, {
          children: "Data"
        }), ")"]
      }), "\n", (0,jsx_runtime.jsx)(_components.li, {
        children: "If the field is a list or a map, and are defined using the data-backed versions of list and map, then it is free"
      }), "\n", (0,jsx_runtime.jsx)(_components.li, {
        children: "If the field is any other kind of complex or large datatype, then it is potentially expensive"
      }), "\n"]
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["Therefore ", (0,jsx_runtime.jsx)(_components.code, {
        children: "asData"
      }), " tends to work best when you use it for a type and also for all the types of its fields."]
    }), "\n", (0,jsx_runtime.jsxs)(_components.h3, {
      id: "writing-optimal-code-using-asdata",
      children: ["Writing optimal code using ", (0,jsx_runtime.jsx)(_components.code, {
        children: "asData"
      })]
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["Consider the following type encoded using ", (0,jsx_runtime.jsx)(_components.code, {
        children: "asData"
      }), ", and two functions which produce equivalent results:"]
    }), "\n", (0,jsx_runtime.jsx)(_components.pre, {
      children: (0,jsx_runtime.jsx)(_components.code, {
        children: "PlutusTx.asData\n    [d|\n        data Point =\n            Point\n                { x :: Int\n                , y :: Int\n                , z :: Int\n                }\n    |]\n\nfoo1 :: Point -> Int\nfoo1 point = x point + y point\n\nfoo2 :: Point -> Int\nfoo2 Point {x, y} = x + y\n"
      })
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["The second function, ", (0,jsx_runtime.jsx)(_components.code, {
        children: "foo2"
      }), ", matches on the ", (0,jsx_runtime.jsx)(_components.code, {
        children: "Point"
      }), " argument using record patterns.\nThis ensures that both fields are extracted at the same time from the underlying ", (0,jsx_runtime.jsx)(_components.code, {
        children: "Data"
      }), " object.\nIn ", (0,jsx_runtime.jsx)(_components.code, {
        children: "foo1"
      }), ", which uses field accessors instead, this will only be the case if the compiler detects that ", (0,jsx_runtime.jsx)(_components.code, {
        children: "x point"
      }), " and ", (0,jsx_runtime.jsx)(_components.code, {
        children: "y point"
      }), " both contain a common subexpression which can be factored out.\nDepending on this compiler optimisation is unreliable, therefore the approach illustrated in ", (0,jsx_runtime.jsx)(_components.code, {
        children: "foo2"
      }), " is preferred."]
    }), "\n", (0,jsx_runtime.jsx)(_components.h2, {
      id: "choosing-an-approach",
      children: "Choosing an approach"
    }), "\n", (0,jsx_runtime.jsx)(_components.p, {
      children: "There are a number of tradeoffs to consider:"
    }), "\n", (0,jsx_runtime.jsxs)(_components.ol, {
      children: ["\n", (0,jsx_runtime.jsxs)(_components.li, {
        children: ["Plinth's datatypes are faster to work with and easier to optimize than ", (0,jsx_runtime.jsx)(_components.code, {
          children: "Data"
        }), ", so if the resulting object is going to be processed in its entirety (or have parts of it repeatedly processed) then it can be better to parse it up-front."]
      }), "\n", (0,jsx_runtime.jsx)(_components.li, {
        children: "If it is important to check that the entire structure is well-formed, then it is better to parse it up-front, since the conversion will check the entire structure for well-formedness immediately, rather than checking only the parts that are used when they are used."
      }), "\n", (0,jsx_runtime.jsxs)(_components.li, {
        children: ["If you do not want to use ", (0,jsx_runtime.jsx)(_components.code, {
          children: "asData"
        }), " for the types of the fields, then it may be better to not use it at all in order to avoid conversion penalties at the use sites."]
      }), "\n"]
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["Which approach is better is an empirical question and may vary in different cases.\nA single script may wish to use different approaches in different places.\nFor example, your datum might contain a large state object which is usually only inspected in part (a good candidate for ", (0,jsx_runtime.jsx)(_components.code, {
        children: "asData"
      }), "), whereas your redeemer might be a small object which is inspected frequently to determine what to do (a good candidate for a native Plinth datatype)."]
    }), "\n", (0,jsx_runtime.jsxs)(_components.h2, {
      id: "data-backed-scriptcontext",
      children: ["Data-backed ", (0,jsx_runtime.jsx)(_components.code, {
        children: "ScriptContext"
      })]
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["The ", (0,jsx_runtime.jsx)(_components.a, {
        href: "/pr-preview/docs/pr-7417/working-with-scripts/ledger-language-version#scriptcontext",
        children: "ScriptContext"
      }), " is one type which can massively benefit from the ", (0,jsx_runtime.jsx)(_components.code, {
        children: "asData"
      }), " approach."]
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["Plinth scripts receive information from the ledger in the form of a ", (0,jsx_runtime.jsx)(_components.code, {
        children: "BuiltinData"
      }), " argument.\nThis argument can be very large, especially in the case of ", (0,jsx_runtime.jsx)(_components.a, {
        href: "/pr-preview/docs/pr-7417/working-with-scripts/ledger-language-version#plutus-v3",
        children: "V3"
      }), " scripts.\nTherefore, upfront parsing of this ", (0,jsx_runtime.jsx)(_components.code, {
        children: "BuiltinData"
      }), " object into a native Plinth datatype may sometimes constitute wasted effort if the script does not make use of most of the information inside the script context.\nThis effort translates into high evaluation fees which could be avoided if the script would parse only what it needs from the script context."]
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["For this use-case, we provide a version of the ledger API in which the ", (0,jsx_runtime.jsx)(_components.code, {
        children: "ScriptContext"
      }), " types are data-backed, i.e. they are defined using this ", (0,jsx_runtime.jsx)(_components.code, {
        children: "asData"
      }), " approach, and so are all the types on which the script contexts depend on as fields."]
    }), "\n", (0,jsx_runtime.jsx)(_components.p, {
      children: "The module naming scheme is as follows:"
    }), "\n", (0,jsx_runtime.jsxs)(_components.ul, {
      children: ["\n", (0,jsx_runtime.jsxs)(_components.li, {
        children: ["the ", (0,jsx_runtime.jsx)(_components.code, {
          children: "PlutusLedgerApi/Data/"
        }), " directory contains the data-backed versions of the top-level ", (0,jsx_runtime.jsx)(_components.code, {
          children: "V1"
        }), ", ", (0,jsx_runtime.jsx)(_components.code, {
          children: "V2"
        }), " and ", (0,jsx_runtime.jsx)(_components.code, {
          children: "V3"
        }), " modules"]
      }), "\n", (0,jsx_runtime.jsxs)(_components.li, {
        children: ["inside each of the ", (0,jsx_runtime.jsx)(_components.code, {
          children: "PlutusLedgerApi/Vn"
        }), " directories, where ", (0,jsx_runtime.jsx)(_components.code, {
          children: "n"
        }), " represents the language version number, there is a ", (0,jsx_runtime.jsx)(_components.code, {
          children: "Data/"
        }), " directory with the data-backed versions of modules specific to each language version."]
      }), "\n"]
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["Using this version of the ledger API can be as simple as modifying the relevant imports; for example, importing ", (0,jsx_runtime.jsx)(_components.a, {
        href: "https://plutus.cardano.intersectmbo.org/haddock/master/plutus-ledger-api/PlutusLedgerApi-Data-V3.html",
        children: "PlutusLedgerApi.Data.V3"
      }), " instead of ", (0,jsx_runtime.jsx)(_components.a, {
        href: "https://plutus.cardano.intersectmbo.org/haddock/master/plutus-ledger-api/PlutusLedgerApi-V3.html",
        children: "PlutusLedgerApi.V3"
      }), ", and so on."]
    }), "\n", (0,jsx_runtime.jsx)(_components.p, {
      children: "If your script is slightly more complex, and it operates on those fields of the script context which are represented as lists or maps, then you will need to also import the respective data-backed collection type from the Plinth standard library."
    }), "\n", (0,jsx_runtime.jsxs)(_components.p, {
      children: ["It is recommended to use record patterns to extract all necessary fields of the ", (0,jsx_runtime.jsx)(_components.code, {
        children: "ScriptContext"
      }), " at the beginning of a function.\nThe reasoning behind this is briefly explained ", (0,jsx_runtime.jsx)(_components.a, {
        href: "#writing-optimal-code-using-asdata",
        children: "above"
      }), "."]
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