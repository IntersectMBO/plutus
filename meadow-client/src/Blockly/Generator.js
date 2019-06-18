/*eslint-env node*/
'use strict';

exports.getFieldValue_ = function (left, right, block, key) {
    var result = block.getFieldValue(key);
    if (result) {
        return right(result);
    } else {
        return left("couldn't find field: " + key);
    }
}

exports.statementToCode_ = function (left, right, generator, block, key) {
    var result = generator.statementToCode(block, key);
    if (result) {
        // Blockly adds some whitespace for some reason
        return right(result.trim());
    } else {
        return left("couldn't find statement: " + key);
    }
}

exports.valueToCode_ = function (left, right, generator, block, key, order) {
    var result = generator.valueToCode(block, key, order);
    if (result) {
        // Blockly adds some whitespace for some reason
        return right(result.trim());
    } else {
        return left("couldn't find value: " + key);
    }
}

exports.mkGenerator_ = function (mkRef, blocklyState, name) {
    var generator = new blocklyState.blockly.Generator(name);
    return mkRef(generator);
}

exports.insertGeneratorFunction_ = function (genRef, key, f) {
    return function () {
        var generator = genRef.value;
        generator[key] = f;
    };
}

exports.workspaceToCode_ = function (left, right, blocklyState, generator) {
    try {
        return right(generator.workspaceToCode(blocklyState.workspace));
    } catch(err) {
        return left(err.message);
    }
}

exports.inputList_ = function (block) {
    return block.inputList;
}

exports.connectToPrevious_ = function (blockRef, input) {
    return function () {
        var block = blockRef.value;
        block.previousConnection.connect(input.connection);
    };
}

exports.connectToOutput_ = function (blockRef, input) {
    return function () {
        var block = blockRef.value;
        block.outputConnection.connect(input.connection);
    };
}

exports.newBlock_ = function (mkRef, workspaceRef, name) {
    var workspace = workspaceRef.value;
    var block = workspace.newBlock(name);
    block.initSvg();
    return mkRef(block);
}

exports.inputName_ = function (input) {
    return input.name;
}

exports.clearWorkspace_ = function (workspaceRef) {
    return function () {
        var workspace = workspaceRef.value;
        workspace.clear()
    };
}

exports.fieldRow_ = function (input) {
    return input.fieldRow;
}

exports.setFieldText_ = function (fieldRef, text) {
    return function () {
        var field = fieldRef.value;
        field.setText(text);
    };
}

exports.fieldName_ = function (field) {
    return field.name;
}

exports.unsafeThrowError_ = function (s) {
    throw new Error(s);
}