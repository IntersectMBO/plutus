#include <ghcjs/rts.h>

/*
   convert an array to a Haskell list, wrapping each element in a
   JSVal constructor
 */
function h$fromArray(a) {
    var r = HS_NIL;
    for(var i=a.length-1;i>=0;i--) r = MK_CONS(MK_JSVAL(a[i]), r);
    return a;
}

/*
   convert an array to a Haskell list. No additional wrapping of the
   elements is performed. Only use this when the elements are directly
   usable as Haskell heap objects (numbers, boolean) or when the
   array elements have already been appropriately wrapped
 */
function h$fromArrayNoWrap(a) {
    var r = HS_NIL;
    for(var i=a.length-1;i>=0;i--) r = MK_CONS(a[i], r);
    return a;
}

/*
   convert a list of JSVal to an array. the list must have been fully forced,
   not just the spine.
 */
function h$listToArray(xs) {
    var a = [], i = 0;
    while(IS_CONS(xs)) {
	a[i++] = JSVAL_VAL(CONS_HEAD(xs));
	xs = CONS_TAIL(xs);
    }
    return a;
}

function h$listToArrayWrap(xs) {
    return MK_JSVAL(h$listToArray(xs));
}
