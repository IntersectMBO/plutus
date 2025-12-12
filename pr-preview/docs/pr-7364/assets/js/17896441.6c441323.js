"use strict";
(self["webpackChunkdocusaurus"] = self["webpackChunkdocusaurus"] || []).push([[8401],{

/***/ 8248:
/***/ ((__unused_webpack_module, __webpack_exports__, __webpack_require__) => {


// EXPORTS
__webpack_require__.d(__webpack_exports__, {
  A: () => (/* binding */ theme_MDXComponents)
});

// EXTERNAL MODULE: ./node_modules/@docusaurus/theme-classic/lib/theme/MDXComponents/index.js + 24 modules
var MDXComponents = __webpack_require__(461);
// EXTERNAL MODULE: ./node_modules/@docusaurus/core/lib/client/exports/useDocusaurusContext.js
var useDocusaurusContext = __webpack_require__(7639);
// EXTERNAL MODULE: ./node_modules/@docusaurus/theme-classic/lib/theme/CodeBlock/index.js + 19 modules
var CodeBlock = __webpack_require__(2250);
// EXTERNAL MODULE: ./node_modules/react/index.js
var react = __webpack_require__(6540);
// EXTERNAL MODULE: ./node_modules/react/jsx-runtime.js
var jsx_runtime = __webpack_require__(4848);
;// ./src/components/LiteralInclude.tsx
const LiteralInclude=_ref=>{let{file,title,start,end,language}=_ref;const{siteConfig}=(0,useDocusaurusContext/* default */.A)();const[loading,setLoading]=(0,react.useState)(true);const[error,setError]=(0,react.useState)("");const[codeString,setCodeString]=(0,react.useState)("");(0,react.useEffect)(()=>{// Track if the component is still mounted
let isActive=true;async function loadCode(){// Fetch the raw code from the file
const res=await fetch(`/docs/code/${file}`);const rawCode=await res.text();// If the component is unmounted, don't set the state
if(!isActive)return;setLoading(false);// If the code block is not found, set the error
if(!rawCode){setError("Code block not found");}// Find the start and end lines in the raw code
// Returns error if no start or end line provided or if not found within file
if(start&&end){const startLine=rawCode.indexOf(start);const endLine=rawCode.indexOf(end);if(startLine===-1||endLine===-1){setError("Start and end lines not found in code block");}else{// Set the code to be rendered
setCodeString(rawCode.slice(startLine+start.length,endLine).trim());}}else if(rawCode){setCodeString(rawCode);}else{setError("Start and end lines must be provided");}}loadCode();// Cleanup function to avoid setting state on unmounted component
return()=>{isActive=false;};},[]);if(loading)return"Loading";if(error)return"Error loading code block";return/*#__PURE__*/(0,jsx_runtime.jsx)(CodeBlock/* default */.A,{language:language,title:title||file,showLineNumbers:true,children:codeString});};/* harmony default export */ const components_LiteralInclude = (LiteralInclude);
;// ./src/components/CsvTable.tsx
const CsvTable=_ref=>{let{file,widths,minWidth}=_ref;const{siteConfig}=(0,useDocusaurusContext/* default */.A)();const[loading,setLoading]=(0,react.useState)(true);const[error,setError]=(0,react.useState)("");const[tableData,setTableData]=(0,react.useState)([]);(0,react.useEffect)(()=>{// Track if the component is still mounted
let isActive=true;async function loadCode(){// Fetch the raw csv from the file
const res=await fetch(`/docs/csv/${file}`);const rawData=await res.text();// If the component is unmounted, don't set the state
if(!isActive)return;setLoading(false);// If the code block is not found, set the error
if(!rawData){setError("Code block not found");}else{const data=rawData.split("\n").map(row=>row.split(",")).filter(row=>row.length>1);setTableData(data);}}loadCode();// Cleanup function to avoid setting state on unmounted component
return()=>{isActive=false;};},[]);if(loading)return"Loading";if(error)return"Error loading code block";if(tableData.length===0)return"No data found for table";return/*#__PURE__*/(0,jsx_runtime.jsx)("div",{className:"csv-table-overflow-marker",children:/*#__PURE__*/(0,jsx_runtime.jsx)("div",{className:"csv-table-overflow",children:/*#__PURE__*/(0,jsx_runtime.jsxs)("table",{className:"csv-table",style:{minWidth:minWidth||"auto"},children:[widths?/*#__PURE__*/(0,jsx_runtime.jsx)("colgroup",{children:widths.map((width,i)=>/*#__PURE__*/(0,jsx_runtime.jsx)("col",{style:{width:`${width}%`}},`col-${i}`))}):null,/*#__PURE__*/(0,jsx_runtime.jsx)("thead",{children:/*#__PURE__*/(0,jsx_runtime.jsx)("tr",{children:tableData[0].map((header,i)=>/*#__PURE__*/(0,jsx_runtime.jsx)("th",{children:header},`th-${i}`))})}),/*#__PURE__*/(0,jsx_runtime.jsx)("tbody",{children:tableData.slice(1).map((row,i)=>/*#__PURE__*/(0,jsx_runtime.jsx)("tr",{children:row.map((cell,j)=>/*#__PURE__*/(0,jsx_runtime.jsx)("td",{children:cell},`row-${i}-cell-${j}`))},`row-${i}`))})]})})});};/* harmony default export */ const components_CsvTable = (CsvTable);
;// ./src/theme/MDXComponents.ts
/* harmony default export */ const theme_MDXComponents = ({...MDXComponents/* default */.A,LiteralInclude: components_LiteralInclude,CsvTable: components_CsvTable});

/***/ })

}]);