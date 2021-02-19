/*eslint-env node*/
"use strict";

var JSONbig = require("json-bigint");

exports.createBlocklyInstance_ = function () {
  return require("node-blockly/browser");
};
exports.debugBlockly_ = function debugBlockly_ (name, state) {
  if (typeof window.blockly === 'undefined') {
    window.blockly = {};
  }
  window.blockly[name] = state
}
exports.getElementById_ = function (id) {
  return document.getElementById(id);
};

exports.createWorkspace_ = function (blockly, workspaceDiv, config) {
  var workspace = blockly.inject(workspaceDiv, config);
  blockly.svgResize(workspace);
  return workspace;
};

exports.resizeBlockly_ = function (blockly, workspace) {
  blockly.svgResize(workspace);
  workspace.render();
};

function removeUndefinedFields(obj) {
  for (var propName in obj) {
    if (obj[propName] === undefined) {
      delete obj[propName];
    }
  }
}

function removeEmptyArrayFields(obj) {
  for (var propName in obj) {
    if (Array.isArray(obj[propName]) && obj[propName].length == 0) {
      delete obj[propName];
    }
  }
}

exports.addBlockType_ = function (blockly, name, block) {
  // we really don't want to be mutating the input object, it is not supposed to be state
  var clone = JSONbig.parse(JSONbig.stringify(block));
  removeUndefinedFields(clone);
  removeEmptyArrayFields(clone);
  blockly.Blocks[name] = {
    init: function () {
      this.jsonInit(clone);
    },
  };
};

exports.initializeWorkspace_ = function (blockly, workspace) {
  // QUESTION: Shouldn't we pass the id element as a parameter? this does not
  // affect having multiple Blockly instances? (currently Actus and BlocklyEditor)
  var workspaceBlocks = document.getElementById("workspaceBlocks");
  blockly.Xml.domToWorkspace(workspaceBlocks, workspace);
  workspace.getAllBlocks()[0].setDeletable(false);
};

exports.render_ = function (workspace) {
  workspace.render();
};

exports.getBlockById_ = function (just, nothing, workspace, id) {
  var result = workspace.getBlockById(id);
  if (result) {
    return just(result);
  } else {
    return nothing;
  }
};

exports.workspaceXML_ = function (blockly, workspace) {
  const isEmpty = workspace.getAllBlocks()[0].getChildren().length == 0;
  if (isEmpty) {
    return "";
  } else {
    var dom = blockly.Xml.workspaceToDom(workspace);
    return blockly.utils.xml.domToText(dom);
  }
};

exports.loadWorkspace_ = function (blockly, workspace, xml) {
  var dom = blockly.utils.xml.textToDomDocument(xml);
  blockly.Xml.clearWorkspaceAndLoadFromXml(dom.childNodes[0], workspace);
  workspace.getAllBlocks()[0].setDeletable(false);
};

exports.addChangeListener_ = function (workspace, listener) {
  workspace.addChangeListener(listener);
};

exports.removeChangeListener_ = function (workspace, listener) {
  workspace.removeChangeListener(listener);
};

exports.workspaceToDom_ = function (blockly, workspace) {
  return blockly.Xml.workspaceToDom(workspace);
};
