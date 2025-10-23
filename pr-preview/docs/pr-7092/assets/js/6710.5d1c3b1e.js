"use strict";
(self["webpackChunkdocusaurus"] = self["webpackChunkdocusaurus"] || []).push([[6710],{

/***/ 3861:
/***/ ((__unused_webpack___webpack_module__, __webpack_exports__, __webpack_require__) => {

/* harmony export */ __webpack_require__.d(__webpack_exports__, {
/* harmony export */   S: () => (/* binding */ populateCommonDb)
/* harmony export */ });
/* harmony import */ var _chunk_VIW5F6AA_mjs__WEBPACK_IMPORTED_MODULE_0__ = __webpack_require__(6936);


// src/diagrams/common/populateCommonDb.ts
function populateCommonDb(ast, db) {
  if (ast.accDescr) {
    db.setAccDescription?.(ast.accDescr);
  }
  if (ast.accTitle) {
    db.setAccTitle?.(ast.accTitle);
  }
  if (ast.title) {
    db.setDiagramTitle?.(ast.title);
  }
}
(0,_chunk_VIW5F6AA_mjs__WEBPACK_IMPORTED_MODULE_0__/* .__name */ .K2)(populateCommonDb, "populateCommonDb");




/***/ }),

/***/ 3004:
/***/ ((__unused_webpack___webpack_module__, __webpack_exports__, __webpack_require__) => {

/* harmony export */ __webpack_require__.d(__webpack_exports__, {
/* harmony export */   P: () => (/* binding */ setupViewPortForSVG)
/* harmony export */ });
/* harmony import */ var _chunk_VIW5F6AA_mjs__WEBPACK_IMPORTED_MODULE_0__ = __webpack_require__(6936);


// src/rendering-util/setupViewPortForSVG.ts
var setupViewPortForSVG = /* @__PURE__ */ (0,_chunk_VIW5F6AA_mjs__WEBPACK_IMPORTED_MODULE_0__/* .__name */ .K2)((svg, padding, cssDiagram, useMaxWidth) => {
  svg.attr("class", cssDiagram);
  const { width, height, x, y } = calculateDimensionsWithPadding(svg, padding);
  (0,_chunk_VIW5F6AA_mjs__WEBPACK_IMPORTED_MODULE_0__/* .configureSvgSize */ .a$)(svg, height, width, useMaxWidth);
  const viewBox = createViewBox(x, y, width, height, padding);
  svg.attr("viewBox", viewBox);
  _chunk_VIW5F6AA_mjs__WEBPACK_IMPORTED_MODULE_0__/* .log */ .Rm.debug(`viewBox configured: ${viewBox} with padding: ${padding}`);
}, "setupViewPortForSVG");
var calculateDimensionsWithPadding = /* @__PURE__ */ (0,_chunk_VIW5F6AA_mjs__WEBPACK_IMPORTED_MODULE_0__/* .__name */ .K2)((svg, padding) => {
  const bounds = svg.node()?.getBBox() || { width: 0, height: 0, x: 0, y: 0 };
  return {
    width: bounds.width + padding * 2,
    height: bounds.height + padding * 2,
    x: bounds.x,
    y: bounds.y
  };
}, "calculateDimensionsWithPadding");
var createViewBox = /* @__PURE__ */ (0,_chunk_VIW5F6AA_mjs__WEBPACK_IMPORTED_MODULE_0__/* .__name */ .K2)((x, y, width, height, padding) => {
  return `${x - padding} ${y - padding} ${width} ${height}`;
}, "createViewBox");




/***/ }),

/***/ 6710:
/***/ ((__unused_webpack___webpack_module__, __webpack_exports__, __webpack_require__) => {

/* harmony export */ __webpack_require__.d(__webpack_exports__, {
/* harmony export */   diagram: () => (/* binding */ diagram)
/* harmony export */ });
/* harmony import */ var _chunk_NRVI72HA_mjs__WEBPACK_IMPORTED_MODULE_0__ = __webpack_require__(3004);
/* harmony import */ var _chunk_7RNWAQOT_mjs__WEBPACK_IMPORTED_MODULE_1__ = __webpack_require__(5828);
/* harmony import */ var _chunk_ANTBXLJU_mjs__WEBPACK_IMPORTED_MODULE_2__ = __webpack_require__(3861);
/* harmony import */ var _chunk_U37J5Y7L_mjs__WEBPACK_IMPORTED_MODULE_3__ = __webpack_require__(8045);
/* harmony import */ var _chunk_T57MJCP2_mjs__WEBPACK_IMPORTED_MODULE_4__ = __webpack_require__(163);
/* harmony import */ var _chunk_VIW5F6AA_mjs__WEBPACK_IMPORTED_MODULE_5__ = __webpack_require__(6936);
/* harmony import */ var _mermaid_js_parser__WEBPACK_IMPORTED_MODULE_6__ = __webpack_require__(8731);
/* harmony import */ var d3__WEBPACK_IMPORTED_MODULE_7__ = __webpack_require__(451);







// src/diagrams/treemap/db.ts
var TreeMapDB = class {
  constructor() {
    this.nodes = [];
    this.levels = /* @__PURE__ */ new Map();
    this.outerNodes = [];
    this.classes = /* @__PURE__ */ new Map();
    this.setAccTitle = _chunk_VIW5F6AA_mjs__WEBPACK_IMPORTED_MODULE_5__/* .setAccTitle */ .SV;
    this.getAccTitle = _chunk_VIW5F6AA_mjs__WEBPACK_IMPORTED_MODULE_5__/* .getAccTitle */ .iN;
    this.setDiagramTitle = _chunk_VIW5F6AA_mjs__WEBPACK_IMPORTED_MODULE_5__/* .setDiagramTitle */ .ke;
    this.getDiagramTitle = _chunk_VIW5F6AA_mjs__WEBPACK_IMPORTED_MODULE_5__/* .getDiagramTitle */ .ab;
    this.getAccDescription = _chunk_VIW5F6AA_mjs__WEBPACK_IMPORTED_MODULE_5__/* .getAccDescription */ .m7;
    this.setAccDescription = _chunk_VIW5F6AA_mjs__WEBPACK_IMPORTED_MODULE_5__/* .setAccDescription */ .EI;
  }
  static {
    (0,_chunk_VIW5F6AA_mjs__WEBPACK_IMPORTED_MODULE_5__/* .__name */ .K2)(this, "TreeMapDB");
  }
  getNodes() {
    return this.nodes;
  }
  getConfig() {
    const defaultConfig = _chunk_VIW5F6AA_mjs__WEBPACK_IMPORTED_MODULE_5__/* .defaultConfig_default */ .UI;
    const userConfig = (0,_chunk_VIW5F6AA_mjs__WEBPACK_IMPORTED_MODULE_5__/* .getConfig */ .zj)();
    return (0,_chunk_U37J5Y7L_mjs__WEBPACK_IMPORTED_MODULE_3__/* .cleanAndMerge */ .$t)({
      ...defaultConfig.treemap,
      ...userConfig.treemap ?? {}
    });
  }
  addNode(node, level) {
    this.nodes.push(node);
    this.levels.set(node, level);
    if (level === 0) {
      this.outerNodes.push(node);
      this.root ??= node;
    }
  }
  getRoot() {
    return { name: "", children: this.outerNodes };
  }
  addClass(id, _style) {
    const styleClass = this.classes.get(id) ?? { id, styles: [], textStyles: [] };
    const styles = _style.replace(/\\,/g, "\xA7\xA7\xA7").replace(/,/g, ";").replace(/§§§/g, ",").split(";");
    if (styles) {
      styles.forEach((s) => {
        if ((0,_chunk_7RNWAQOT_mjs__WEBPACK_IMPORTED_MODULE_1__/* .isLabelStyle */ .KX)(s)) {
          if (styleClass?.textStyles) {
            styleClass.textStyles.push(s);
          } else {
            styleClass.textStyles = [s];
          }
        }
        if (styleClass?.styles) {
          styleClass.styles.push(s);
        } else {
          styleClass.styles = [s];
        }
      });
    }
    this.classes.set(id, styleClass);
  }
  getClasses() {
    return this.classes;
  }
  getStylesForClass(classSelector) {
    return this.classes.get(classSelector)?.styles ?? [];
  }
  clear() {
    (0,_chunk_VIW5F6AA_mjs__WEBPACK_IMPORTED_MODULE_5__/* .clear */ .IU)();
    this.nodes = [];
    this.levels = /* @__PURE__ */ new Map();
    this.outerNodes = [];
    this.classes = /* @__PURE__ */ new Map();
    this.root = void 0;
  }
};

// src/diagrams/treemap/parser.ts


// src/diagrams/treemap/utils.ts
function buildHierarchy(items) {
  if (!items.length) {
    return [];
  }
  const root = [];
  const stack = [];
  items.forEach((item) => {
    const node = {
      name: item.name,
      children: item.type === "Leaf" ? void 0 : []
    };
    node.classSelector = item?.classSelector;
    if (item?.cssCompiledStyles) {
      node.cssCompiledStyles = [item.cssCompiledStyles];
    }
    if (item.type === "Leaf" && item.value !== void 0) {
      node.value = item.value;
    }
    while (stack.length > 0 && stack[stack.length - 1].level >= item.level) {
      stack.pop();
    }
    if (stack.length === 0) {
      root.push(node);
    } else {
      const parent = stack[stack.length - 1].node;
      if (parent.children) {
        parent.children.push(node);
      } else {
        parent.children = [node];
      }
    }
    if (item.type !== "Leaf") {
      stack.push({ node, level: item.level });
    }
  });
  return root;
}
(0,_chunk_VIW5F6AA_mjs__WEBPACK_IMPORTED_MODULE_5__/* .__name */ .K2)(buildHierarchy, "buildHierarchy");

// src/diagrams/treemap/parser.ts
var populate = /* @__PURE__ */ (0,_chunk_VIW5F6AA_mjs__WEBPACK_IMPORTED_MODULE_5__/* .__name */ .K2)((ast, db) => {
  (0,_chunk_ANTBXLJU_mjs__WEBPACK_IMPORTED_MODULE_2__/* .populateCommonDb */ .S)(ast, db);
  const items = [];
  for (const row of ast.TreemapRows ?? []) {
    if (row.$type === "ClassDefStatement") {
      db.addClass(row.className ?? "", row.styleText ?? "");
    }
  }
  for (const row of ast.TreemapRows ?? []) {
    const item = row.item;
    if (!item) {
      continue;
    }
    const level = row.indent ? parseInt(row.indent) : 0;
    const name = getItemName(item);
    const styles = item.classSelector ? db.getStylesForClass(item.classSelector) : [];
    const cssCompiledStyles = styles.length > 0 ? styles.join(";") : void 0;
    const itemData = {
      level,
      name,
      type: item.$type,
      value: item.value,
      classSelector: item.classSelector,
      cssCompiledStyles
    };
    items.push(itemData);
  }
  const hierarchyNodes = buildHierarchy(items);
  const addNodesRecursively = /* @__PURE__ */ (0,_chunk_VIW5F6AA_mjs__WEBPACK_IMPORTED_MODULE_5__/* .__name */ .K2)((nodes, level) => {
    for (const node of nodes) {
      db.addNode(node, level);
      if (node.children && node.children.length > 0) {
        addNodesRecursively(node.children, level + 1);
      }
    }
  }, "addNodesRecursively");
  addNodesRecursively(hierarchyNodes, 0);
}, "populate");
var getItemName = /* @__PURE__ */ (0,_chunk_VIW5F6AA_mjs__WEBPACK_IMPORTED_MODULE_5__/* .__name */ .K2)((item) => {
  return item.name ? String(item.name) : "";
}, "getItemName");
var parser = {
  // @ts-expect-error - TreeMapDB is not assignable to DiagramDB
  parser: { yy: void 0 },
  parse: /* @__PURE__ */ (0,_chunk_VIW5F6AA_mjs__WEBPACK_IMPORTED_MODULE_5__/* .__name */ .K2)(async (text) => {
    try {
      const parseFunc = _mermaid_js_parser__WEBPACK_IMPORTED_MODULE_6__/* .parse */ .qg;
      const ast = await parseFunc("treemap", text);
      _chunk_VIW5F6AA_mjs__WEBPACK_IMPORTED_MODULE_5__/* .log */ .Rm.debug("Treemap AST:", ast);
      const db = parser.parser?.yy;
      if (!(db instanceof TreeMapDB)) {
        throw new Error(
          "parser.parser?.yy was not a TreemapDB. This is due to a bug within Mermaid, please report this issue at https://github.com/mermaid-js/mermaid/issues."
        );
      }
      populate(ast, db);
    } catch (error) {
      _chunk_VIW5F6AA_mjs__WEBPACK_IMPORTED_MODULE_5__/* .log */ .Rm.error("Error parsing treemap:", error);
      throw error;
    }
  }, "parse")
};

// src/diagrams/treemap/renderer.ts

var DEFAULT_INNER_PADDING = 10;
var SECTION_INNER_PADDING = 10;
var SECTION_HEADER_HEIGHT = 25;
var draw = /* @__PURE__ */ (0,_chunk_VIW5F6AA_mjs__WEBPACK_IMPORTED_MODULE_5__/* .__name */ .K2)((_text, id, _version, diagram2) => {
  const treemapDb = diagram2.db;
  const config = treemapDb.getConfig();
  const treemapInnerPadding = config.padding ?? DEFAULT_INNER_PADDING;
  const title = treemapDb.getDiagramTitle();
  const root = treemapDb.getRoot();
  const { themeVariables } = (0,_chunk_VIW5F6AA_mjs__WEBPACK_IMPORTED_MODULE_5__/* .getConfig */ .zj)();
  if (!root) {
    return;
  }
  const titleHeight = title ? 30 : 0;
  const svg = (0,_chunk_T57MJCP2_mjs__WEBPACK_IMPORTED_MODULE_4__/* .selectSvgElement */ .D)(id);
  const width = config.nodeWidth ? config.nodeWidth * SECTION_INNER_PADDING : 960;
  const height = config.nodeHeight ? config.nodeHeight * SECTION_INNER_PADDING : 500;
  const svgWidth = width;
  const svgHeight = height + titleHeight;
  svg.attr("viewBox", `0 0 ${svgWidth} ${svgHeight}`);
  (0,_chunk_VIW5F6AA_mjs__WEBPACK_IMPORTED_MODULE_5__/* .configureSvgSize */ .a$)(svg, svgHeight, svgWidth, config.useMaxWidth);
  let valueFormat;
  try {
    const formatStr = config.valueFormat || ",";
    if (formatStr === "$0,0") {
      valueFormat = /* @__PURE__ */ (0,_chunk_VIW5F6AA_mjs__WEBPACK_IMPORTED_MODULE_5__/* .__name */ .K2)((value) => "$" + (0,d3__WEBPACK_IMPORTED_MODULE_7__/* .format */ .GPZ)(",")(value), "valueFormat");
    } else if (formatStr.startsWith("$") && formatStr.includes(",")) {
      const precision = /\.\d+/.exec(formatStr);
      const precisionStr = precision ? precision[0] : "";
      valueFormat = /* @__PURE__ */ (0,_chunk_VIW5F6AA_mjs__WEBPACK_IMPORTED_MODULE_5__/* .__name */ .K2)((value) => "$" + (0,d3__WEBPACK_IMPORTED_MODULE_7__/* .format */ .GPZ)("," + precisionStr)(value), "valueFormat");
    } else if (formatStr.startsWith("$")) {
      const restOfFormat = formatStr.substring(1);
      valueFormat = /* @__PURE__ */ (0,_chunk_VIW5F6AA_mjs__WEBPACK_IMPORTED_MODULE_5__/* .__name */ .K2)((value) => "$" + (0,d3__WEBPACK_IMPORTED_MODULE_7__/* .format */ .GPZ)(restOfFormat || "")(value), "valueFormat");
    } else {
      valueFormat = (0,d3__WEBPACK_IMPORTED_MODULE_7__/* .format */ .GPZ)(formatStr);
    }
  } catch (error) {
    _chunk_VIW5F6AA_mjs__WEBPACK_IMPORTED_MODULE_5__/* .log */ .Rm.error("Error creating format function:", error);
    valueFormat = (0,d3__WEBPACK_IMPORTED_MODULE_7__/* .format */ .GPZ)(",");
  }
  const colorScale = (0,d3__WEBPACK_IMPORTED_MODULE_7__/* .scaleOrdinal */ .UMr)().range([
    "transparent",
    themeVariables.cScale0,
    themeVariables.cScale1,
    themeVariables.cScale2,
    themeVariables.cScale3,
    themeVariables.cScale4,
    themeVariables.cScale5,
    themeVariables.cScale6,
    themeVariables.cScale7,
    themeVariables.cScale8,
    themeVariables.cScale9,
    themeVariables.cScale10,
    themeVariables.cScale11
  ]);
  const colorScalePeer = (0,d3__WEBPACK_IMPORTED_MODULE_7__/* .scaleOrdinal */ .UMr)().range([
    "transparent",
    themeVariables.cScalePeer0,
    themeVariables.cScalePeer1,
    themeVariables.cScalePeer2,
    themeVariables.cScalePeer3,
    themeVariables.cScalePeer4,
    themeVariables.cScalePeer5,
    themeVariables.cScalePeer6,
    themeVariables.cScalePeer7,
    themeVariables.cScalePeer8,
    themeVariables.cScalePeer9,
    themeVariables.cScalePeer10,
    themeVariables.cScalePeer11
  ]);
  const colorScaleLabel = (0,d3__WEBPACK_IMPORTED_MODULE_7__/* .scaleOrdinal */ .UMr)().range([
    themeVariables.cScaleLabel0,
    themeVariables.cScaleLabel1,
    themeVariables.cScaleLabel2,
    themeVariables.cScaleLabel3,
    themeVariables.cScaleLabel4,
    themeVariables.cScaleLabel5,
    themeVariables.cScaleLabel6,
    themeVariables.cScaleLabel7,
    themeVariables.cScaleLabel8,
    themeVariables.cScaleLabel9,
    themeVariables.cScaleLabel10,
    themeVariables.cScaleLabel11
  ]);
  if (title) {
    svg.append("text").attr("x", svgWidth / 2).attr("y", titleHeight / 2).attr("class", "treemapTitle").attr("text-anchor", "middle").attr("dominant-baseline", "middle").text(title);
  }
  const g = svg.append("g").attr("transform", `translate(0, ${titleHeight})`).attr("class", "treemapContainer");
  const hierarchyRoot = (0,d3__WEBPACK_IMPORTED_MODULE_7__/* .hierarchy */ .Sk5)(root).sum((d) => d.value ?? 0).sort((a, b) => (b.value ?? 0) - (a.value ?? 0));
  const treemapLayout = (0,d3__WEBPACK_IMPORTED_MODULE_7__/* .treemap */ .hkb)().size([width, height]).paddingTop(
    (d) => d.children && d.children.length > 0 ? SECTION_HEADER_HEIGHT + SECTION_INNER_PADDING : 0
  ).paddingInner(treemapInnerPadding).paddingLeft((d) => d.children && d.children.length > 0 ? SECTION_INNER_PADDING : 0).paddingRight((d) => d.children && d.children.length > 0 ? SECTION_INNER_PADDING : 0).paddingBottom((d) => d.children && d.children.length > 0 ? SECTION_INNER_PADDING : 0).round(true);
  const treemapData = treemapLayout(hierarchyRoot);
  const branchNodes = treemapData.descendants().filter((d) => d.children && d.children.length > 0);
  const sections = g.selectAll(".treemapSection").data(branchNodes).enter().append("g").attr("class", "treemapSection").attr("transform", (d) => `translate(${d.x0},${d.y0})`);
  sections.append("rect").attr("width", (d) => d.x1 - d.x0).attr("height", SECTION_HEADER_HEIGHT).attr("class", "treemapSectionHeader").attr("fill", "none").attr("fill-opacity", 0.6).attr("stroke-width", 0.6).attr("style", (d) => {
    if (d.depth === 0) {
      return "display: none;";
    }
    return "";
  });
  sections.append("clipPath").attr("id", (_d, i) => `clip-section-${id}-${i}`).append("rect").attr("width", (d) => Math.max(0, d.x1 - d.x0 - 12)).attr("height", SECTION_HEADER_HEIGHT);
  sections.append("rect").attr("width", (d) => d.x1 - d.x0).attr("height", (d) => d.y1 - d.y0).attr("class", (_d, i) => {
    return `treemapSection section${i}`;
  }).attr("fill", (d) => colorScale(d.data.name)).attr("fill-opacity", 0.6).attr("stroke", (d) => colorScalePeer(d.data.name)).attr("stroke-width", 2).attr("stroke-opacity", 0.4).attr("style", (d) => {
    if (d.depth === 0) {
      return "display: none;";
    }
    const styles = (0,_chunk_7RNWAQOT_mjs__WEBPACK_IMPORTED_MODULE_1__/* .styles2String */ .GX)({ cssCompiledStyles: d.data.cssCompiledStyles });
    return styles.nodeStyles + ";" + styles.borderStyles.join(";");
  });
  sections.append("text").attr("class", "treemapSectionLabel").attr("x", 6).attr("y", SECTION_HEADER_HEIGHT / 2).attr("dominant-baseline", "middle").text((d) => d.depth === 0 ? "" : d.data.name).attr("font-weight", "bold").attr("style", (d) => {
    if (d.depth === 0) {
      return "display: none;";
    }
    const labelStyles = "dominant-baseline: middle; font-size: 12px; fill:" + colorScaleLabel(d.data.name) + "; white-space: nowrap; overflow: hidden; text-overflow: ellipsis;";
    const styles = (0,_chunk_7RNWAQOT_mjs__WEBPACK_IMPORTED_MODULE_1__/* .styles2String */ .GX)({ cssCompiledStyles: d.data.cssCompiledStyles });
    return labelStyles + styles.labelStyles.replace("color:", "fill:");
  }).each(function(d) {
    if (d.depth === 0) {
      return;
    }
    const self = (0,d3__WEBPACK_IMPORTED_MODULE_7__/* .select */ .Ltv)(this);
    const originalText = d.data.name;
    self.text(originalText);
    const totalHeaderWidth = d.x1 - d.x0;
    const labelXPosition = 6;
    let spaceForTextContent;
    if (config.showValues !== false && d.value) {
      const valueEndsAtXRelative = totalHeaderWidth - 10;
      const estimatedValueTextActualWidth = 30;
      const gapBetweenLabelAndValue = 10;
      const labelMustEndBeforeX = valueEndsAtXRelative - estimatedValueTextActualWidth - gapBetweenLabelAndValue;
      spaceForTextContent = labelMustEndBeforeX - labelXPosition;
    } else {
      const labelOwnRightPadding = 6;
      spaceForTextContent = totalHeaderWidth - labelXPosition - labelOwnRightPadding;
    }
    const minimumWidthToDisplay = 15;
    const actualAvailableWidth = Math.max(minimumWidthToDisplay, spaceForTextContent);
    const textNode = self.node();
    const currentTextContentLength = textNode.getComputedTextLength();
    if (currentTextContentLength > actualAvailableWidth) {
      const ellipsis = "...";
      let currentTruncatedText = originalText;
      while (currentTruncatedText.length > 0) {
        currentTruncatedText = originalText.substring(0, currentTruncatedText.length - 1);
        if (currentTruncatedText.length === 0) {
          self.text(ellipsis);
          if (textNode.getComputedTextLength() > actualAvailableWidth) {
            self.text("");
          }
          break;
        }
        self.text(currentTruncatedText + ellipsis);
        if (textNode.getComputedTextLength() <= actualAvailableWidth) {
          break;
        }
      }
    }
  });
  if (config.showValues !== false) {
    sections.append("text").attr("class", "treemapSectionValue").attr("x", (d) => d.x1 - d.x0 - 10).attr("y", SECTION_HEADER_HEIGHT / 2).attr("text-anchor", "end").attr("dominant-baseline", "middle").text((d) => d.value ? valueFormat(d.value) : "").attr("font-style", "italic").attr("style", (d) => {
      if (d.depth === 0) {
        return "display: none;";
      }
      const labelStyles = "text-anchor: end; dominant-baseline: middle; font-size: 10px; fill:" + colorScaleLabel(d.data.name) + "; white-space: nowrap; overflow: hidden; text-overflow: ellipsis;";
      const styles = (0,_chunk_7RNWAQOT_mjs__WEBPACK_IMPORTED_MODULE_1__/* .styles2String */ .GX)({ cssCompiledStyles: d.data.cssCompiledStyles });
      return labelStyles + styles.labelStyles.replace("color:", "fill:");
    });
  }
  const leafNodes = treemapData.leaves();
  const cell = g.selectAll(".treemapLeafGroup").data(leafNodes).enter().append("g").attr("class", (d, i) => {
    return `treemapNode treemapLeafGroup leaf${i}${d.data.classSelector ? ` ${d.data.classSelector}` : ""}x`;
  }).attr("transform", (d) => `translate(${d.x0},${d.y0})`);
  cell.append("rect").attr("width", (d) => d.x1 - d.x0).attr("height", (d) => d.y1 - d.y0).attr("class", "treemapLeaf").attr("fill", (d) => {
    return d.parent ? colorScale(d.parent.data.name) : colorScale(d.data.name);
  }).attr("style", (d) => {
    const styles = (0,_chunk_7RNWAQOT_mjs__WEBPACK_IMPORTED_MODULE_1__/* .styles2String */ .GX)({ cssCompiledStyles: d.data.cssCompiledStyles });
    return styles.nodeStyles;
  }).attr("fill-opacity", 0.3).attr("stroke", (d) => {
    return d.parent ? colorScale(d.parent.data.name) : colorScale(d.data.name);
  }).attr("stroke-width", 3);
  cell.append("clipPath").attr("id", (_d, i) => `clip-${id}-${i}`).append("rect").attr("width", (d) => Math.max(0, d.x1 - d.x0 - 4)).attr("height", (d) => Math.max(0, d.y1 - d.y0 - 4));
  const leafLabels = cell.append("text").attr("class", "treemapLabel").attr("x", (d) => (d.x1 - d.x0) / 2).attr("y", (d) => (d.y1 - d.y0) / 2).attr("style", (d) => {
    const labelStyles = "text-anchor: middle; dominant-baseline: middle; font-size: 38px;fill:" + colorScaleLabel(d.data.name) + ";";
    const styles = (0,_chunk_7RNWAQOT_mjs__WEBPACK_IMPORTED_MODULE_1__/* .styles2String */ .GX)({ cssCompiledStyles: d.data.cssCompiledStyles });
    return labelStyles + styles.labelStyles.replace("color:", "fill:");
  }).attr("clip-path", (_d, i) => `url(#clip-${id}-${i})`).text((d) => d.data.name);
  leafLabels.each(function(d) {
    const self = (0,d3__WEBPACK_IMPORTED_MODULE_7__/* .select */ .Ltv)(this);
    const nodeWidth = d.x1 - d.x0;
    const nodeHeight = d.y1 - d.y0;
    const textNode = self.node();
    const padding = 4;
    const availableWidth = nodeWidth - 2 * padding;
    const availableHeight = nodeHeight - 2 * padding;
    if (availableWidth < 10 || availableHeight < 10) {
      self.style("display", "none");
      return;
    }
    let currentLabelFontSize = parseInt(self.style("font-size"), 10);
    const minLabelFontSize = 8;
    const originalValueRelFontSize = 28;
    const valueScaleFactor = 0.6;
    const minValueFontSize = 6;
    const spacingBetweenLabelAndValue = 2;
    while (textNode.getComputedTextLength() > availableWidth && currentLabelFontSize > minLabelFontSize) {
      currentLabelFontSize--;
      self.style("font-size", `${currentLabelFontSize}px`);
    }
    let prospectiveValueFontSize = Math.max(
      minValueFontSize,
      Math.min(originalValueRelFontSize, Math.round(currentLabelFontSize * valueScaleFactor))
    );
    let combinedHeight = currentLabelFontSize + spacingBetweenLabelAndValue + prospectiveValueFontSize;
    while (combinedHeight > availableHeight && currentLabelFontSize > minLabelFontSize) {
      currentLabelFontSize--;
      prospectiveValueFontSize = Math.max(
        minValueFontSize,
        Math.min(originalValueRelFontSize, Math.round(currentLabelFontSize * valueScaleFactor))
      );
      if (prospectiveValueFontSize < minValueFontSize && currentLabelFontSize === minLabelFontSize) {
        break;
      }
      self.style("font-size", `${currentLabelFontSize}px`);
      combinedHeight = currentLabelFontSize + spacingBetweenLabelAndValue + prospectiveValueFontSize;
      if (prospectiveValueFontSize <= minValueFontSize && combinedHeight > availableHeight) {
      }
    }
    self.style("font-size", `${currentLabelFontSize}px`);
    if (textNode.getComputedTextLength() > availableWidth || currentLabelFontSize < minLabelFontSize || availableHeight < currentLabelFontSize) {
      self.style("display", "none");
    }
  });
  if (config.showValues !== false) {
    const leafValues = cell.append("text").attr("class", "treemapValue").attr("x", (d) => (d.x1 - d.x0) / 2).attr("y", function(d) {
      return (d.y1 - d.y0) / 2;
    }).attr("style", (d) => {
      const labelStyles = "text-anchor: middle; dominant-baseline: hanging; font-size: 28px;fill:" + colorScaleLabel(d.data.name) + ";";
      const styles = (0,_chunk_7RNWAQOT_mjs__WEBPACK_IMPORTED_MODULE_1__/* .styles2String */ .GX)({ cssCompiledStyles: d.data.cssCompiledStyles });
      return labelStyles + styles.labelStyles.replace("color:", "fill:");
    }).attr("clip-path", (_d, i) => `url(#clip-${id}-${i})`).text((d) => d.value ? valueFormat(d.value) : "");
    leafValues.each(function(d) {
      const valueTextElement = (0,d3__WEBPACK_IMPORTED_MODULE_7__/* .select */ .Ltv)(this);
      const parentCellNode = this.parentNode;
      if (!parentCellNode) {
        valueTextElement.style("display", "none");
        return;
      }
      const labelElement = (0,d3__WEBPACK_IMPORTED_MODULE_7__/* .select */ .Ltv)(parentCellNode).select(".treemapLabel");
      if (labelElement.empty() || labelElement.style("display") === "none") {
        valueTextElement.style("display", "none");
        return;
      }
      const finalLabelFontSize = parseFloat(labelElement.style("font-size"));
      const originalValueFontSize = 28;
      const valueScaleFactor = 0.6;
      const minValueFontSize = 6;
      const spacingBetweenLabelAndValue = 2;
      const actualValueFontSize = Math.max(
        minValueFontSize,
        Math.min(originalValueFontSize, Math.round(finalLabelFontSize * valueScaleFactor))
      );
      valueTextElement.style("font-size", `${actualValueFontSize}px`);
      const labelCenterY = (d.y1 - d.y0) / 2;
      const valueTopActualY = labelCenterY + finalLabelFontSize / 2 + spacingBetweenLabelAndValue;
      valueTextElement.attr("y", valueTopActualY);
      const nodeWidth = d.x1 - d.x0;
      const nodeTotalHeight = d.y1 - d.y0;
      const cellBottomPadding = 4;
      const maxValueBottomY = nodeTotalHeight - cellBottomPadding;
      const availableWidthForValue = nodeWidth - 2 * 4;
      if (valueTextElement.node().getComputedTextLength() > availableWidthForValue || valueTopActualY + actualValueFontSize > maxValueBottomY || actualValueFontSize < minValueFontSize) {
        valueTextElement.style("display", "none");
      } else {
        valueTextElement.style("display", null);
      }
    });
  }
  const diagramPadding = config.diagramPadding ?? 8;
  (0,_chunk_NRVI72HA_mjs__WEBPACK_IMPORTED_MODULE_0__/* .setupViewPortForSVG */ .P)(svg, diagramPadding, "flowchart", config?.useMaxWidth || false);
}, "draw");
var getClasses = /* @__PURE__ */ (0,_chunk_VIW5F6AA_mjs__WEBPACK_IMPORTED_MODULE_5__/* .__name */ .K2)(function(_text, diagramObj) {
  return diagramObj.db.getClasses();
}, "getClasses");
var renderer = { draw, getClasses };

// src/diagrams/treemap/styles.ts
var defaultTreemapStyleOptions = {
  sectionStrokeColor: "black",
  sectionStrokeWidth: "1",
  sectionFillColor: "#efefef",
  leafStrokeColor: "black",
  leafStrokeWidth: "1",
  leafFillColor: "#efefef",
  labelColor: "black",
  labelFontSize: "12px",
  valueFontSize: "10px",
  valueColor: "black",
  titleColor: "black",
  titleFontSize: "14px"
};
var getStyles = /* @__PURE__ */ (0,_chunk_VIW5F6AA_mjs__WEBPACK_IMPORTED_MODULE_5__/* .__name */ .K2)(({
  treemap: treemap2
} = {}) => {
  const options = (0,_chunk_U37J5Y7L_mjs__WEBPACK_IMPORTED_MODULE_3__/* .cleanAndMerge */ .$t)(defaultTreemapStyleOptions, treemap2);
  return `
  .treemapNode.section {
    stroke: ${options.sectionStrokeColor};
    stroke-width: ${options.sectionStrokeWidth};
    fill: ${options.sectionFillColor};
  }
  .treemapNode.leaf {
    stroke: ${options.leafStrokeColor};
    stroke-width: ${options.leafStrokeWidth};
    fill: ${options.leafFillColor};
  }
  .treemapLabel {
    fill: ${options.labelColor};
    font-size: ${options.labelFontSize};
  }
  .treemapValue {
    fill: ${options.valueColor};
    font-size: ${options.valueFontSize};
  }
  .treemapTitle {
    fill: ${options.titleColor};
    font-size: ${options.titleFontSize};
  }
  `;
}, "getStyles");
var styles_default = getStyles;

// src/diagrams/treemap/diagram.ts
var diagram = {
  parser,
  get db() {
    return new TreeMapDB();
  },
  renderer,
  styles: styles_default
};



/***/ })

}]);