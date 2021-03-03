/*eslint-env node*/
'use strict';

exports.createBlocklyInstance_ = function() {
    return require('blockly/blockly-node');
}

exports.createWorkspace_ = function(blockly) {
    return new blockly.Workspace;
}

exports.initializeWorkspace_ = function(blockly, workspace) {
    var xmlText = '<xml id="workspaceBlocks" style="display:none"><block type="BaseContractType" x="13" y="187" id="root_contract"></block></xml>';
    var workspaceBlocks = blockly.Xml.textToDom(xmlText);
    blockly.Xml.domToWorkspace(workspaceBlocks, workspace);
    workspace.getAllBlocks()[0].setDeletable(false);
}

exports.newBlock_ = function (workspace, name) {
    return workspace.newBlock(name);
}
