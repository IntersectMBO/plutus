console.log("run worker");
/**
 * TODO: I'm sorry but we need to use a global here to force the WASM to load exactly once
 * This will be in a web worker soon anyway
 */
const Module = require('z3w.js');
const WasmModule = require('z3w.wasm');
const Z3 = Module({
    locateFile: function (path) {
        // we can add a condition for when this is run in node that should mean it works in the repl
        if (path.endsWith('.wasm')) {
            console.log("https://localhost:8009/" + WasmModule);
            return WasmModule;
        }
        return path;
    }
});
Z3.onRuntimeInitialized = () => {
    // FIXME: need to somehow wait for this to happen before doing anything else
    // really though this should be in a web worker I think
    // P.S. needs -s BINARYEN_ASYNC_COMPILATION=1 to work
    // If you try sync compilation it fails to load at all
    console.log("WASM loaded");
};
exports.handler = function (e) {
  console.log('Worker: Message received from main script');
  let result = e.data[0] * e.data[1];
  if (isNaN(result)) {
    postMessage('Please write two numbers');
  } else {
    let workerResult = 'Result: ' + result;
    console.log('Worker: Posting message back to main script');
    postMessage(workerResult);
  }
}
exports.registerOnMessage = function (ctx, f) {
ctx.onmessage = function (e) {
  f(e);
};
};

exports.context = function() { return self; };