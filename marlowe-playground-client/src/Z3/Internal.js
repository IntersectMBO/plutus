/*eslint-env node*/
'use strict';
/**
 * TODO: I'm sorry but we need to use a global here to force the WASM to load exactly once
 * This will be in a web worker soon anyway
 */
const Module = require('z3w.js');
const WasmModule = require('z3w.wasm');
var Z3 = Module({
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

const Worker = require('output/worker.js');
const worker = new Worker();
// const W = new Worker('worker.[hash].js');
console.log("post message");
worker.postMessage({ a: 1 });
worker.postMessage({ a: 1 });
console.log("posted message");

exports.createInstance = function () {
    return Z3;
}

exports.mk_config = function (z3) {
    return z3.ccall('Z3_mk_config', 'number', [], []);
}

exports.mk_context = function (z3, cfg) {
    return z3.ccall('Z3_mk_context', 'number', ['number'], [cfg]);
}

exports.del_config = function (z3, cfg) {
    return z3.ccall('Z3_del_config', null, ['number'], [cfg]);
}

exports.del_context = function (z3, ctx) {
    return z3.ccall('Z3_del_context', null, ['number'], [ctx]);
}

exports.mk_solver = function (z3, ctx) {
    return z3.ccall('Z3_mk_solver', 'number', ['number'], [ctx]);
}

exports.mk_string_symbol = function (z3, ctx, name) {
    return z3.ccall('Z3_mk_string_symbol', 'number', ['number', 'string'], [ctx, name]);
}

exports.mk_const = function (z3, ctx, symbol, sort) {
    return z3.ccall('Z3_mk_const', 'number', ['number', 'number', 'number'], [ctx, symbol, sort]);
}

exports.mk_int_sort = function (z3, ctx) {
    return z3.ccall('Z3_mk_int_sort', 'number', ['number'], [ctx]);
}

exports.mk_string_sort = function (z3, ctx) {
    return z3.ccall('Z3_mk_string_sort', 'number', ['number'], [ctx]);
}

exports.mk_bool_sort = function (z3, ctx) {
    return z3.ccall('Z3_mk_bool_sort', 'number', ['number'], [ctx]);
}

exports.mk_int = function (z3, ctx, value, sort) {
    return z3.ccall('Z3_mk_int', 'number', ['number', 'number'], [ctx, value, sort]);
}

exports.mk_string = function (z3, ctx, value) {
    return z3.ccall('Z3_mk_string', 'number', ['number', 'string'], [ctx, value]);
}

exports.mk_true = function (z3, ctx) {
    return z3.ccall('Z3_mk_true', 'number', ['number'], [ctx]);
}

exports.mk_false = function (z3, ctx) {
    return z3.ccall('Z3_mk_false', 'number', ['number'], [ctx]);
}

exports.mk_not = function (z3, ctx, ast) {
    return z3.ccall('Z3_mk_not', 'number', ['number', 'number'], [ctx, ast]);
}

exports.mk_and = function (z3, ctx, x, y) {
    return z3.ccall('Z3_mk_and', 'number', ['number', 'number', 'array'], [ctx, 2, [x, y]]);
}

exports.mk_add = function (z3, ctx, x, y) {
    return z3.ccall('Z3_mk_add', 'number', ['number', 'number', 'array'], [ctx, 2, [x, y]]);
}

exports.mk_mul = function (z3, ctx, x, y) {
    return z3.ccall('Z3_mk_mul', 'number', ['number', 'number', 'array'], [ctx, 2, [x, y]]);
}

exports.mk_sub = function (z3, ctx, x, y) {
    return z3.ccall('Z3_mk_sub', 'number', ['number', 'number', 'array'], [ctx, 2, [x, y]]);
}

exports.mk_or = function (z3, ctx, x, y) {
    return z3.ccall('Z3_mk_or', 'number', ['number', 'number', 'array'], [ctx, 2, [x, y]]);
}

exports.mk_eq = function (z3, ctx, x, y) {
    return z3.ccall('Z3_mk_eq', 'number', ['number', 'number', 'number'], [ctx, x, y]);
}

exports.mk_lt = function (z3, ctx, x, y) {
    return z3.ccall('Z3_mk_lt', 'number', ['number', 'number', 'number'], [ctx, x, y]);
}

exports.mk_le = function (z3, ctx, x, y) {
    return z3.ccall('Z3_mk_le', 'number', ['number', 'number', 'number'], [ctx, x, y]);
}

exports.mk_gt = function (z3, ctx, x, y) {
    return z3.ccall('Z3_mk_gt', 'number', ['number', 'number', 'number'], [ctx, x, y]);
}

exports.mk_ge = function (z3, ctx, x, y) {
    return z3.ccall('Z3_mk_ge', 'number', ['number', 'number', 'number'], [ctx, x, y]);
}

exports.solver_assert = function (z3, ctx, solver, ast) {
    return z3.ccall('Z3_solver_assert', null, ['number', 'number', 'number'], [ctx, solver, ast]);
}

exports.solver_get_model = function (z3, ctx, solver) {
    return z3.ccall('Z3_solver_get_model', 'number', ['number', 'number'], [ctx, solver]);
}

exports.model_inc_ref = function (z3, ctx, model) {
    return z3.ccall('Z3_model_inc_ref', null, ['number', 'number'], [ctx, model]);
}

exports.model_dec_rec = function (z3, ctx, model) {
    return z3.ccall('Z3_model_dec_ref', null, ['number', 'number'], [ctx, model]);
}

exports.model_to_string = function (z3, ctx, model) {
    return z3.ccall('Z3_model_to_string', 'string', ['number', 'number'], [ctx, model]);
}

exports.solver_check = function (z3, ctx, solver) {
    return z3.ccall('Z3_solver_check', 'number', ['number', 'number'], [ctx, solver]);
}

exports.ast_to_string = function (z3, ctx, ast) {
    return z3.ccall('Z3_ast_to_string', 'string', ['number', 'number'], [ctx, ast]);
}

exports.func_decl_to_string = function (z3, ctx, decl) {
    return z3.ccall('Z3_func_decl_to_string', 'number', ['number', 'number'], [ctx, decl]);
}

exports.model_get_const_interp = function (z3, ctx, model, decl) {
    return z3.ccall('Z3_model_get_const_interp', 'number', ['number', 'number', 'number'], [ctx, model, decl]);
}

exports.mk_func_decl = function (z3, ctx, symbol, sort) {
    return z3.ccall('Z3_mk_func_decl', 'number', ['number', 'number', 'number', 'array', 'number'], [ctx, symbol, 0, [], sort]);
}

exports.mk_app = function (z3, ctx, decl) {
    return z3.ccall('Z3_mk_app', 'number', ['number', 'number', 'number', 'array'], [ctx, decl, 0, []]);
}

exports.solver_push = function (z3, ctx, solver) {
    return z3.ccall('Z3_solver_push', null, ['number', 'number'], [ctx, solver]);
}

exports.solver_pop = function (z3, ctx, solver) {
    return z3.ccall('Z3_solver_pop', null, ['number', 'number', 'number'], [ctx, solver, 1]);
}

exports.solver_inc_ref = function (z3, ctx, solver) {
    return z3.ccall('Z3_solver_inc_ref', null, ['number', 'number'], [ctx, solver]);
}

exports.solver_dec_ref = function (z3, ctx, solver) {
    return z3.ccall('Z3_solver_dec_ref', null, ['number', 'number'], [ctx, solver]);
}

exports.eval_smtlib2_string = function (z3, ctx, str) {
    return z3.ccall('Z3_eval_smtlib2_string', 'string', ['number', 'string'], [ctx, str]);
}