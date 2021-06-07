#include <ghcjs/rts.h>

function h$allProps(o) {
    var a = [], i = 0;
    for(var p in o) a[i++] = p;
    return a;
}

function h$listProps(o) {
    var r = HS_NIL;
    for(var p in o) { r = MK_CONS(MK_JSVAL(p), r); }
    return r;
}

function h$listAssocs(o) {
    var r = HS_NIL;
    for(var p in o) { r = MK_CONS(MK_TUP2(MK_JSVAL(p), MK_JSVAL(o[p])), r); }
    return r;
}

function h$isNumber(o) {
    return typeof(o) === 'number';
}

// returns true for null, but not for functions and host objects
function h$isObject(o) {
    return typeof(o) === 'object';
}

function h$isString(o) {
    return typeof(o) === 'string';
}

function h$isSymbol(o) {
    return typeof(o) === 'symbol';
}

function h$isBoolean(o) {
    return typeof(o) === 'boolean';
}

function h$isFunction(o) {
    return typeof(o) === 'function';
}

function h$jsTypeOf(o) {
    var t = typeof(o);
    if(t === 'undefined') return 0;
    if(t === 'object')    return 1;
    if(t === 'boolean')   return 2;
    if(t === 'number')    return 3;
    if(t === 'string')    return 4;
    if(t === 'symbol')    return 5;
    if(t === 'function')  return 6;
    return 7; // other, host object etc
}

/*
        -- 0 - null, 1 - integer,
        -- 2 - float, 3 - bool,
        -- 4 - string, 5 - array
        -- 6 - object
*/
function h$jsonTypeOf(o) {
    if (!(o instanceof Object)) {
        if (o == null) {
            return 0;
        } else if (typeof o == 'number') {
            if (h$isInteger(o)) {
                return 1;
            } else {
                return 2;
            }
        } else if (typeof o == 'boolean') {
            return 3;
        } else {
            return 4;
        }
    } else {
        if (Object.prototype.toString.call(o) == '[object Array]') {
            // it's an array
            return 5;
        } else if (!o) {
            // null 
            return 0;
        } else {
            // it's an object
            return 6;
        }
    }

}

