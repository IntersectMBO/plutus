/*eslint-env node*/
'use strict';

var JSONbig = require('json-bigint');

exports.createBlocklyInstance_ = function () {
    return require('node-blockly/browser');
}

exports.getElementById_ = function (id) {
    return document.getElementById(id);
}

exports.createWorkspace_ = function (blockly, workspaceDiv, config) {
    var workspace = blockly.inject(workspaceDiv, config);
    blockly.svgResize(workspace);
    return workspace;

}

exports.resizeBlockly_ = function (blockly, workspaceRef) {
    return function () {
        var workspace = workspaceRef.value;
        blockly.svgResize(workspace);
        workspace.render();
    }
}

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

exports.addBlockType_ = function (blocklyRef, name, block) {
    return function () {
        var blockly = blocklyRef.value;
        // we really don't want to be mutating the input object, it is not supposed to be state
        var clone = JSONbig.parse(JSONbig.stringify(block));
        removeUndefinedFields(clone);
        removeEmptyArrayFields(clone);
        blockly.Blocks[name] = {
            init: function () {
                this.jsonInit(clone);
            }
        }
    };
}

exports.initializeWorkspace_ = function (blockly, workspaceRef) {
    return function () {
        var workspace = workspaceRef.value;
        var workspaceBlocks = document.getElementById("workspaceBlocks");
        blockly.Xml.domToWorkspace(workspaceBlocks, workspace);
        workspace.getAllBlocks()[0].setDeletable(false);
    };
}

exports.render_ = function (workspaceRef) {
    return function () {
        var workspace = workspaceRef.value;
        workspace.render();
    };
}

exports.getBlockById_ = function (just, nothing, workspace, id) {
    var result = workspace.getBlockById(id);
    if (result) {
        return just(result);
    } else {
        return nothing;
    }
}

exports.workspaceXML_ = function (blockly, workspace) {
    const isEmpty = workspace.getAllBlocks()[0].getChildren().length == 0;
    if (isEmpty) {
        return "";
    } else {
        var dom = blockly.Xml.workspaceToDom(workspace);
        return blockly.utils.xml.domToText(dom);
    }
}

exports.loadWorkspace_ = function (blockly, workspaceRef, xml) {
    return function () {
        var workspace = workspaceRef.value;
        var dom = blockly.utils.xml.textToDomDocument(xml);
        blockly.Xml.clearWorkspaceAndLoadFromXml(dom.childNodes[0], workspace);
        workspace.getAllBlocks()[0].setDeletable(false);
    }
}