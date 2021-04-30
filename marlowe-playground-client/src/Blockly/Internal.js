/*eslint-env node*/
"use strict";

var JSONbig = require("json-bigint");

exports.createBlocklyInstance_ = function () {
  return require("blockly");
};
exports.debugBlockly_ = function debugBlockly_(name, state) {
  if (typeof window.blockly === 'undefined') {
    window.blockly = {};
  }
  window.blockly[name] = state
}
exports.getElementById_ = function (id) {
  return document.getElementById(id);
};

exports.createWorkspace_ = function (blockly, workspaceDiv, config) {

  /* Disable disabling blocks */
  blockly.ContextMenuRegistry.registry.unregister('blockDisable');

  /* Disable comments */
  blockly.ContextMenuRegistry.registry.unregister('blockComment');

  /* Register extensions */
  /* Silently clean if already registered */
  try { blockly.Extensions.register('timeout_validator', function () { }); } catch(err) { }
  blockly.Extensions.unregister('timeout_validator');

  /* Timeout extension (advanced validation for the timeout field) */
  blockly.Extensions.register('timeout_validator',
    function () {
      var thisBlock = this;

      /* Validator for timeout */
      var timeoutValidator = function (input) {
        if (thisBlock.getFieldValue('timeout_type') == 'slot') {
          var cleanedInput = input.replace(new RegExp('[,]+', 'g'), '').trim();
          if ((new RegExp('^(-[0-9])?[0-9]*$', 'g')).test(cleanedInput)) {
            return BigInt(cleanedInput).toString();
          } else {
            return null;
          }
        } else {
          return input;
        }
      };
      
      thisBlock.getField('timeout').setValidator(timeoutValidator);

      /* This sets the timeout to zero when switching to slot in the dropdown */
      this.setOnChange(function (event) {
        if (event.blockId == thisBlock.id &&
          event.name == 'timeout_type' &&
          event.element == 'field' &&
          event.oldValue != event.newValue) {
          if (timeoutValidator(thisBlock.getFieldValue('timeout')) === null) {
              thisBlock.setFieldValue('0', 'timeout');
          }
        }
      });
    });

  /* Inject workspace */
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

exports.select_ = function (block) {
  block.select();
}

exports.centerOnBlock_ = function (workspace, blockId) {
  workspace.centerOnBlock(blockId);
}

exports.hideChaff_ = function (blockly) {
  blockly.hideChaff();
}

exports.getBlockType_ = function (block) {
  return block.type;
}

exports.updateToolbox_ = function (toolboxJson, workspace) {
  workspace.updateToolbox(toolboxJson);
}


