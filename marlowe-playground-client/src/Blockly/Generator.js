/*eslint-env node*/
"use strict";

exports.nextBlock_ = function (just, nothing, block) {
  var mBlock = block.getNextBlock();
  if (mBlock == null) {
    return nothing;
  } else {
    return just(mBlock);
  }
};

exports.getType_ = function (block) {
  return block.type;
};

exports.getFieldValue_ = function (left, right, block, key) {
  var result = block.getFieldValue(key);
  if (result == 0 || result) {
    /* For some unknown reason, the xmljs library turns strings into numbers if it can
     * We are always expecting a string and that's what the browser gives us but the
     * tests break without this extra toString()
     */
    return right(result.toString());
  } else {
    // we used to return an error if the field returned null/undefined however
    // this happens if the value is empty. We need to sometimes use empty values
    // and they represent an empty string so now we just return an empty string
    // This is slightly dangerous as it can lead to a bug if you use this function
    // with a key that doesn't exist, instead of getting a run time error you
    // will just get an empty string and may not notice.
    // return left("couldn't find field: " + key);
    return right("");
  }
};

exports.statementToCode_ = function (left, right, generator, block, key) {
  var result = generator.statementToCode(block, key);
  if (result) {
    // Blockly adds some whitespace for some reason
    return right(result.trim());
  } else {
    return left("couldn't find statement: " + key);
  }
};

exports.valueToCode_ = function (left, right, generator, block, key, order) {
  var result = generator.valueToCode(block, key, order);
  if (result) {
    // Blockly adds some whitespace for some reason
    return right(result.trim());
  } else {
    return left("couldn't find value: " + key);
  }
};

exports.mkGenerator_ = function (blockly, name) {
  var generator = new blockly.Generator(name);
  return generator;
};

exports.insertGeneratorFunction_ = function (generator, key, f) {
  generator[key] = f;
};

exports.blockToCode_ = function (left, right, block, generator) {
  try {
    return right(generator.blockToCode(block));
  } catch (err) {
    console.log(block);
    console.log(err.message);
    return left(err.message);
  }
};

exports.inputList_ = function (block) {
  return block.inputList;
};

exports.connectToPrevious_ = function (block, input) {
  block.previousConnection.connect(input.connection);
};
exports.previousConnection_ = function (block) {
  return block.previousConnection;
};

exports.nextConnection_ = function (block) {
  return block.nextConnection;
};

exports.connect_ = function (from, to) {
  from.connect(to);
};

exports.connectToOutput_ = function (block, input) {
  block.outputConnection.connect(input.connection);
};

exports.newBlock_ = function (workspace, name) {
  var block = workspace.newBlock(name);
  block.initSvg();
  return block;
};

exports.inputName_ = function (input) {
  return input.name;
};

exports.inputType_ = function (input) {
  return input.type;
};

exports.clearWorkspace_ = function (workspace) {
  workspace.clear();
};

exports.fieldRow_ = function (input) {
  return input.fieldRow;
};

exports.setFieldText_ = function (field, text) {
  field.setValue(text);
};

exports.fieldName_ = function (field) {
  return field.name;
};

exports.unsafeThrowError_ = function (s) {
  throw new Error(s);
};

exports.getBlockInputConnectedTo_ = function (left, right, input) {
  try {
    var mTargetConnection = input.connection.targetConnection;
    if (mTargetConnection == null) {
      return left("no target connection found");
    }
    var mBlock = mTargetConnection.getSourceBlock();
    if (mBlock == null) {
      return left("no block found");
    }
    return right(mBlock);
  } catch (err) {
    return left(err.message);
  }
};
