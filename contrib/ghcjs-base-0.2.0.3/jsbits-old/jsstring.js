#include <ghcjs/rts.h>

/*
 * Support code for the Data.JSString module. This code presents a JSString
 * as a sequence of code points and hides the underlying encoding ugliness of
 * the JavaScript strings.
 *
 * Use Data.JSString.Raw for direct access to the JSThis makes the operations more expen
 */

/*
 * Some workarounds here for JS engines that do not support proper
 * code point access
 */

#ifdef GHCJS_TRACE_JSSTRING
#define TRACE_JSSTRING(args...) h$log("jsstring: ", args);
#else
#define TRACE_JSSTRING(args...)
#endif

#define IS_ASTRAL(cp)    ((cp)>=0x10000)
#define IS_HI_SURR(cp)   ((cp|1023)===0xDBFF)
#define IS_LO_SURR(cp)   ((cp|1023)===0xDFFF)
#define FROM_SURR(hi,lo) ((((hi)-0xD800)<<10)+(lo)-0xDC00+0x10000)
#define HI_SURR(cp)      ((((cp)-0x10000)>>>10)+0xDC00)
#define LO_SURR(cp)      (((cp)&0x3FF)+0xD800)

var h$jsstringEmpty = MK_JSVAL('');

var h$jsstringHead, h$jsstringTail, h$jsstringCons,
    h$jsstringSingleton, h$jsstringSnoc, h$jsstringUncons,
    h$jsstringIndex, h$jsstringUncheckedIndex;

var h$fromCodePoint;

if(String.prototype.fromCodePoint) {
    h$fromCodePoint = String.fromCodePoint;
} else {
    // polyfill from https://github.com/mathiasbynens/String.fromCodePoint (MIT-license)
    h$fromCodePoint =
      (function() {
          var stringFromCharCode = String.fromCharCode;
          var floor = Math.floor;
          return function(_) {
              var MAX_SIZE = 0x4000;
              var codeUnits = [];
              var highSurrogate;
              var lowSurrogate;
              var index = -1;
              var length = arguments.length;
              if (!length) {
                  return '';
              }
              var result = '';
              while (++index < length) {
                  var codePoint = Number(arguments[index]);
                  if (
                      !isFinite(codePoint) || // `NaN`, `+Infinity`, or `-Infinity`
                      codePoint < 0 || // not a valid Unicode code point
                      codePoint > 0x10FFFF || // not a valid Unicode code point
                      floor(codePoint) != codePoint // not an integer
                  ) {
                      throw RangeError('Invalid code point: ' + codePoint);
                  }
                  if (codePoint <= 0xFFFF) { // BMP code point
                      codeUnits.push(codePoint);
                  } else { // Astral code point; split in surrogate halves
                      // https://mathiasbynens.be/notes/javascript-encoding#surrogate-formulae
                      codePoint -= 0x10000;
                      highSurrogate = (codePoint >> 10) + 0xD800;
                      lowSurrogate = (codePoint % 0x400) + 0xDC00;
                      codeUnits.push(highSurrogate, lowSurrogate);
                  }
                  if (index + 1 == length || codeUnits.length > MAX_SIZE) {
                      result += stringFromCharCode.apply(null, codeUnits);
                      codeUnits.length = 0;
                  }
              }
              return result;
          }
      })();
}

if(String.prototype.codePointAt) {
    h$jsstringSingleton = function(ch) {
        TRACE_JSSTRING("(codePointAt) singleton: " + ch);
	return String.fromCodePoint(ch);
    }
    h$jsstringHead = function(str) {
        TRACE_JSSTRING("(codePointAt) head: " + str);
	var cp = str.codePointAt(0);
	return (cp === undefined) ? -1 : (cp|0);
    }
    h$jsstringTail = function(str) {
        TRACE_JSSTRING("(codePointAt) tail: " + str);
	var l = str.length;
	if(l===0) return null;
	var ch = str.codePointAt(0);
	if(ch === undefined) return null;
	// string length is at least two if ch comes from a surrogate pair
	return str.substr(IS_ASTRAL(ch)?2:1);
    }
    h$jsstringCons = function(ch, str) {
        TRACE_JSSTRING("(codePointAt) cons: " + ch + " '" + str + "'");
	return String.fromCodePoint(ch)+str;
    }
    h$jsstringSnoc = function(str, ch) {
        TRACE_JSSTRING("(codePointAt) snoc: '" + str + "' " + ch);
	return str+String.fromCodePoint(ch);
    }
    h$jsstringUncons = function(str) {
        TRACE_JSSTRING("(codePointAt) uncons: '" + str + "'");
	var l = str.length;
	if(l===0) {
          RETURN_UBX_TUP2(-1, null);
        }
	var ch = str.codePointAt(0);
        if(ch === undefined) {
  	  RETURN_UBX_TUP2(-1, null);
        }
        RETURN_UBX_TUP2(ch, str.substr(IS_ASTRAL(ch)?2:1));
    }
    // index is the first part of the character
    h$jsstringIndex = function(i, str) {
        TRACE_JSSTRING("(codePointAt) index: " + i + " '" + str + "'");
	var ch = str.codePointAt(i);
	if(ch === undefined) return -1;
	return ch;
    }
    h$jsstringUncheckedIndex = function(i, str) {
        TRACE_JSSTRING("(codePointAt) uncheckedIndex: " + i + " '" + str.length + "'");
	return str.codePointAt(i);
    }
} else {
    h$jsstringSingleton = function(ch) {
        TRACE_JSSTRING("(no codePointAt) singleton: " + ch);
	return (IS_ASTRAL(ch)) ? String.fromCharCode(HI_SURR(ch), LO_SURR(ch))
                               : String.fromCharCode(ch);
    }
    h$jsstringHead = function(str) {
        TRACE_JSSTRING("(no codePointAt) head: " + str);
	var l = str.length;
	if(l===0) return -1;
	var ch = str.charCodeAt(0);
	if(IS_HI_SURR(ch)) {
	    return (l>1) ? FROM_SURR(ch, str.charCodeAt(1)) : -1;
	} else {
	    return ch;
	}
    }
    h$jsstringTail = function(str) {
        TRACE_JSSTRING("(no codePointAt) tail: " + str);
	var l = str.length;
	if(l===0) return null;
	var ch = str.charCodeAt(0);
	if(IS_HI_SURR(ch)) {
	    return (l>1)?str.substr(2):null;
	} else return str.substr(1);
    }
    h$jsstringCons = function(ch, str) {
        TRACE_JSSTRING("(no codePointAt) cons: " + ch + " '" + str + "'");
	return ((IS_ASTRAL(ch)) ? String.fromCharCode(HI_SURR(ch), LO_SURR(ch))
                                : String.fromCharCode(ch))
                                + str;
    }
    h$jsstringSnoc = function(str, ch) {
        TRACE_JSSTRING("(no codePointAt) snoc: '" + str + "' " + ch);
	return str + ((IS_ASTRAL(ch)) ? String.fromCharCode(HI_SURR(ch), LO_SURR(ch))
                                      : String.fromCharCode(ch));
    }
    h$jsstringUncons = function(str) {
        TRACE_JSSTRING("(no codePointAt) uncons: '" + str + "'");
	var l = str.length;
	if(l===0) {
          RETURN_UBX_TUP2(-1, null);
        }
	var ch = str.charCodeAt(0);
	if(IS_HI_SURR(ch)) {
	  if(l > 1) {
 	      RETURN_UBX_TUP2(FROM_SURR(ch, str.charCodeAt(1)), str.substr(2));
	  } else {
  	    RETURN_UBX_TUP2(-1, null);
	  }
	} else {
 	    RETURN_UBX_TUP2(ch, str.substr(1));
	}
    }
    // index is the first part of the character
    h$jsstringIndex = function(i, str) {
        // TRACE_JSSTRING("(no codePointAt) index: " + i + " '" + str + "'");
	var ch = str.charCodeAt(i);
	if(ch != ch) return -1; // NaN test
	return (IS_HI_SURR(ch)) ? FROM_SURR(ch, str.charCodeAt(i+1)) : ch;
    }
    h$jsstringUncheckedIndex = function(i, str) {
        TRACE_JSSTRING("(no codePointAt) uncheckedIndex: " + i + " '" + str.length + "'");
	var ch = str.charCodeAt(i);
	return (IS_HI_SURR(ch)) ? FROM_SURR(ch, str.charCodeAt(i+1)) : ch;
    }
}

function h$jsstringUnsnoc(str) {
  TRACE_JSSTRING("unsnoc: '" + str + "'");
  var l = str.length;
  if(l===0) {
    RETURN_UBX_TUP2(-1, null);
  }
  var ch = str.charCodeAt(l-1);
  if(IS_LO_SURR(ch)) {
    if(l !== 1) {
      RETURN_UBX_TUP2(FROM_SURR(str.charCodeAt(l-2),ch), str.substr(0,l-2));
    } else {
      RETURN_UBX_TUP2(-1, null);
    }
  } else {
    RETURN_UBX_TUP2(ch, str.substr(0,l-1));
  }
}


function h$jsstringPack(xs) {
    var r = '', i = 0, a = [], c;
    while(IS_CONS(xs)) {
	c = CONS_HEAD(xs);
	a[i++] = UNWRAP_NUMBER(c);
	if(i >= 60000) {
	    r += h$fromCodePoint.apply(null, a);
	    a = [];
	    i = 0;
	}
	xs = CONS_TAIL(xs);
    }
    if(i > 0) r += h$fromCodePoint.apply(null, a);
    TRACE_JSSTRING("pack: '" + r + "'");
    return r;
}

function h$jsstringPackReverse(xs) {
    var a = [], i = 0, c;
    while(IS_CONS(xs)) {
	c = CONS_HEAD(xs);
	a[i++] = UNWRAP_NUMBER(c);
	xs = CONS_TAIL(xs);
    }
    if(i===0) return '';
    var r = h$jsstringConvertArray(a.reverse());
    TRACE_JSSTRING("packReverse: '" + r + "'");
    return r;
}

function h$jsstringPackArray(arr) {
    TRACE_JSSTRING("pack array: " + arr);
    return h$jsstringConvertArray(arr);
}

function h$jsstringPackArrayReverse(arr) {
    TRACE_JSSTRING("pack array reverse: " + arr);
    return h$jsstringConvertArray(arr.reverse());
}

function h$jsstringConvertArray(arr) {
    if(arr.length < 60000) {
	return h$fromCodePoint.apply(null, arr);
    } else {
	var r = '';
	for(var i=0; i<arr.length; i+=60000) {
	    r += h$fromCodePoint.apply(null, arr.slice(i, i+60000));
	}
	return r;
    }
}

function h$jsstringInit(str) {
    TRACE_JSSTRING("init: '" + str + "'");
    var l = str.length;
    if(l===0) return null;
    var ch = str.charCodeAt(l-1);
    var o = IS_LO_SURR(ch)?2:1;
    var r = str.substr(0, l-o);
    return r;
}

function h$jsstringLast(str) {
    TRACE_JSSTRING("last: '" + str + "'");
    var l = str.length;
    if(l===0) return -1;
    var ch = str.charCodeAt(l-1);
    if(IS_LO_SURR(ch)) {
	return (l>1) ? FROM_SURR(str.charCodeAt(l-2), ch) : -1;

    } else return ch;
}

// index is the last part of the character
function h$jsstringIndexR(i, str) {
    TRACE_JSSTRING("indexR: " + i + " '" + str + "'");
    if(i < 0 || i > str.length) return -1;
    var ch = str.charCodeAt(i);
    return (IS_LO_SURR(ch)) ? FROM_SURR(str.charCodeAt(i-1), ch) : ch;
}

function h$jsstringNextIndex(i, str) {
    TRACE_JSSTRING("nextIndex: " + i + " '" + str + "'");
    return i + (IS_HI_SURR(str.charCodeAt(i))?2:1);
}

function h$jsstringTake(n, str) {
    TRACE_JSSTRING("take: " + n + " '" + str + "'");
    if(n <= 0) return '';
    var i = 0, l = str.length, ch;
    if(n >= l) return str;
    while(n--) {
	ch = str.charCodeAt(i++);
	if(IS_HI_SURR(ch)) i++;
	if(i >= l) return str;
    }
    return str.substr(0,i);
}

function h$jsstringDrop(n, str) {
    TRACE_JSSTRING("drop: " + n + " '" + str + "'");
    if(n <= 0) return str;
    var i = 0, l = str.length, ch;
    if(n >= l) return '';
    while(n--) {
	ch = str.charCodeAt(i++);
	if(IS_HI_SURR(ch)) i++;
	if(i >= l) return '';
    }
    return str.substr(i);
}

function h$jsstringSplitAt(n, str) {
  TRACE_JSSTRING("splitAt: " + n + " '" + str + "'");
  if(n <= 0) {
    RETURN_UBX_TUP2("", str);
  } else if(n >= str.length) {
    RETURN_UBX_TUP2(str, "");
  }
  var i = 0, l = str.length, ch;
  while(n--) {
    ch = str.charCodeAt(i++);
    if(IS_HI_SURR(ch)) i++;
    if(i >= l) {
      RETURN_UBX_TUP2(str, "");
    }
  }
  RETURN_UBX_TUP2(str.substr(0,i),str.substr(i));
}

function h$jsstringTakeEnd(n, str) {
    TRACE_JSSTRING("takeEnd: " + n + " '" + str + "'");
    if(n <= 0) return '';
    var l = str.length, i = l-1, ch;
    if(n >= l) return str;
    while(n-- && i > 0) {
	ch = str.charCodeAt(i--);
	if(IS_LO_SURR(ch)) i--;
    }
    return (i<0) ? str : str.substr(i+1);
}

function h$jsstringDropEnd(n, str) {
    TRACE_JSSTRING("dropEnd: " + n + " '" + str + "'");
    if(n <= 0) return str;
    var l = str.length, i = l-1, ch;
    if(n >= l) return '';
    while(n-- && i > 0) {
	ch = str.charCodeAt(i--);
	if(IS_LO_SURR(ch)) i--;
    }
    return (i<0) ? '' : str.substr(0,i+1);
}

function h$jsstringIntercalate(x, ys) {
    TRACE_JSSTRING("intercalate: '" + x + "'");
    var a = [], i = 0;
    while(IS_CONS(ys)) {
	if(i) a[i++] = x;
	a[i++] = JSVAL_VAL(CONS_HEAD(ys));
	ys = CONS_TAIL(ys);
    }
    return a.join('');
}

function h$jsstringIntersperse(ch, ys) {
    TRACE_JSSTRING("intersperse: " + ch + " '" + ys + "'");
    var i = 0, l = ys.length, j = 0, a = [], ych;
    if(IS_ASTRAL(ch)) {
	while(j < l) {
	    if(i) a[i++] = ch;
	    ych = ys.charCodeAt(j++);
	    a[i++] = ych;
	    if(IS_HI_SURR(ych)) a[i++] = ys.charCodeAt(j++);
	}
    } else {
	while(j < l) {
	    if(i) a[i++] = ch;
	    ych = ys.charCodeAt(j++);
	    a[i++] = ych;
	    if(IS_HI_SURR(ych)) a[i++] = ys.charCodeAt(j++);
	}
    }
    return h$jsstringConvertArray(a);
}

function h$jsstringConcat(xs) {
    TRACE_JSSTRING("concat");
    var a = [], i = 0;
    while(IS_CONS(xs)) {
	a[i++] = JSVAL_VAL(CONS_HEAD(xs));
	xs     = CONS_TAIL(xs);
    }
    return a.join('');
}

var h$jsstringStripPrefix, h$jsstringStripSuffix,
    h$jsstringIsPrefixOf, h$jsstringIsSuffixOf,
    h$jsstringIsInfixOf;
if(String.prototype.startsWith) {
    h$jsstringStripPrefix = function(p, x) {
	TRACE_JSSTRING("(startsWith) stripPrefix: '" + p + "' '" + x + "'");
	if(x.startsWith(p)) {
	    return MK_JUST(MK_JSVAL(x.substr(p.length)));
	} else {
	    return HS_NOTHING;
	}
    }

    h$jsstringIsPrefixOf = function(p, x) {
	TRACE_JSSTRING("(startsWith) isPrefixOf: '" + p + "' '" + x + "'");
	return x.startsWith(p);
    }

} else {
    h$jsstringStripPrefix = function(p, x) {
	TRACE_JSSTRING("(no startsWith) stripPrefix: '" + p + "' '" + x + "'");
	if(x.indexOf(p) === 0) { // this has worse complexity than it should
	    return MK_JUST(MK_JSVAL(x.substr(p.length)));
	} else {
	  return HS_NOTHING;
	}
    }

    h$jsstringIsPrefixOf = function(p, x) {
	TRACE_JSSTRING("(no startsWith) isPrefixOf: '" + p + "' '" + x + "'");
	return x.indexOf(p) === 0; // this has worse complexity than it should
    }
}

if(String.prototype.endsWith) {
    h$jsstringStripSuffix = function(s, x) {
	TRACE_JSSTRING("(endsWith) stripSuffix: '" + s + "' '" + x + "'");
	if(x.endsWith(s)) {
	    return MK_JUST(MK_JSVAL(x.substr(0,x.length-s.length)));
	} else {
	  return HS_NOTHING;
	}
    }

    h$jsstringIsSuffixOf = function(s, x) {
	TRACE_JSSTRING("(endsWith) isSuffixOf: '" + s + "' '" + x + "'");
	return x.endsWith(s);
    }
} else {
    h$jsstringStripSuffix = function(s, x) {
	TRACE_JSSTRING("(no endsWith) stripSuffix: '" + s + "' '" + x + "'");
	var i = x.lastIndexOf(s); // this has worse complexity than it should
	var l = x.length - s.length;
	if(i !== -1 && i === l) {
	    return MK_JUST(MK_JSVAL(x.substr(0,l)));
	} else {
	  return HS_NOTHING;
	}
    }

      h$jsstringIsSuffixOf = function(s, x) {
	TRACE_JSSTRING("(no endsWith) isSuffixOf: '" + s + "' '" + x + "'");
        var i = x.lastIndexOf(s); // this has worse complexity than it should
	return i !== -1 && i === x.length - s.length;
    }
}

if(String.prototype.includes) {
    h$jsstringIsInfixOf = function(i, x) {
        TRACE_JSSTRING("(includes) isInfixOf: '" + i + "' '" + x + "'");
	return x.includes(i);
    }
} else {
    h$jsstringIsInfixOf = function(i, x) {
        TRACE_JSSTRING("(no includes) isInfixOf: '" + i + "' '" + x + "'");
	return x.indexOf(i) !== -1; // this has worse complexity than it should
    }
}

function h$jsstringCommonPrefixes(x, y) {
    TRACE_JSSTRING("commonPrefixes: '" + x + "' '" + y + "'");
    var lx = x.length, ly = y.length, i = 0, cx;
    var l  = lx <= ly ? lx : ly;
    if(lx === 0 || ly === 0 || x.charCodeAt(0) !== y.charCodeAt(0)) {
      return HS_NOTHING;
    }
    while(++i<l) {
	cx = x.charCodeAt(i);
	if(cx !== y.charCodeAt(i)) {
	    if(IS_LO_SURR(cx)) i--;
	    break;
	}
    }
  if(i===0) return HS_NOTHING;
    return MK_JUST(MK_TUP3( MK_JSVAL((i===lx)?x:((i===ly)?y:x.substr(0,i)))
			, (i===lx) ? h$jsstringEmpty : MK_JSVAL(x.substr(i))
			, (i===ly) ? h$jsstringEmpty : MK_JSVAL(y.substr(i))
		        ));
}

function h$jsstringBreakOn(b, x) {
    TRACE_JSSTRING("breakOn: '" + b + "' '" + x + "'");
    var i = x.indexOf(b);
    if(i===-1) {
        RETURN_UBX_TUP2(x, "");
    }
    if(i===0) {
        RETURN_UBX_TUP2("", x);
    }
    RETURN_UBX_TUP2(x.substr(0,i), x.substr(i));
}

function h$jsstringBreakOnEnd(b, x) {
    TRACE_JSSTRING("breakOnEnd: '" + b + "' '" + x + "'");
    var i = x.lastIndexOf(b);
  if(i===-1) {
    RETURN_UBX_TUP2("", x);

    }
  i += b.length;
    RETURN_UBX_TUP2(x.substr(0,i), x.substr(i));
}

function h$jsstringBreakOnAll1(n, b, x) {
    TRACE_JSSTRING("breakOnAll1: " + n + " '" + b + "' '" + x + "'");
    var i = x.indexOf(b, n);
    if(i===0) {
       RETURN_UBX_TUP3(b.length, "", x);
    }
    if(i===-1) {
       RETURN_UBX_TUP3(-1, null, null);
    }
    RETURN_UBX_TUP3(i+b.length, x.substr(0,i), x.substr(i));
}

function h$jsstringBreakOnAll(pat, src) {
    TRACE_JSSTRING("breakOnAll");
    var a = [], i = 0, n = 0, r = HS_NIL, pl = pat.length;
    while(true) {
	var x = src.indexOf(pat, n);
	if(x === -1) break;
	a[i++] = MK_TUP2(MK_JSVAL(src.substr(0,x)), MK_JSVAL(src.substr(x)));
	n = x + pl;
    }
    while(--i >= 0) r = MK_CONS(a[i], r);
    return r;
}

function h$jsstringSplitOn1(n, p, x) {
    TRACE_JSSTRING("splitOn1: " + n + " '" + p + "' '" + x + "'");
    var i = x.indexOf(p, n);
    if(i === -1) {
        RETURN_UBX_TUP2(-1, null);
    }
    var r1 = (i==n) ? "" : x.substr(n, i-n);
    RETURN_UBX_TUP2(i + p.length, r1);
}

function h$jsstringSplitOn(p, x) {
    TRACE_JSSTRING("splitOn: '" + p + "' '" + x + "'");
    var a = x.split(p);
    var r = HS_NIL, i = a.length;
    while(--i>=0) r = MK_CONS(MK_JSVAL(a[i]), r);
    return r;
}

// returns -1 for end of input, start of next token otherwise
// word in h$ret1
// this function assumes that there are no whitespace characters >= 0x10000
function h$jsstringWords1(n, x) {
    TRACE_JSSTRING("words1: " + n + " '" + x + "'");
    var m = n, s = n, l = x.length;
    if(m >= l) return -1;
    // skip leading spaces
    do {
	if(m >= l) return -1;
    } while(h$isSpace(x.charCodeAt(m++)));
    // found start of word
    s = m - 1;
    while(m < l) {
	if(h$isSpace(x.charCodeAt(m++))) {
	    // found end of word
            var r1 = (m-s<=1) ? "" : x.substr(s,m-s-1);
            RETURN_UBX_TUP2(m, r1);
	}
    }
    // end of string
    if(s < l) {
        var r1 = s === 0 ? x : x.substr(s);
        RETURN_UBX_TUP2(m, r1);
    }
    RETURN_UBX_TUP2(-1, null);
}

function h$jsstringWords(x) {
    TRACE_JSSTRING("words: '" + x + "'");
    var a = null, i = 0, n, s = -1, m = 0, w, l = x.length, r = HS_NIL;
    outer:
    while(m < l) {
	// skip leading spaces
	do {
	    if(m >= l) { s = m; break outer; }
	} while(h$isSpace(x.charCodeAt(m++)));
	// found start of word
	s = m - 1;
	while(m < l) {
	    if(h$isSpace(x.charCodeAt(m++))) {
		// found end of word
		w = (m-s<=1) ? h$jsstringEmpty
                             : MK_JSVAL(x.substr(s,m-s-1));
		if(i) a[i++] = w; else { a = [w]; i = 1; }
		s = m;
		break;
	    }
	}
    }
    // end of string
    if(s !== -1 && s < l) {
	w = MK_JSVAL(s === 0 ? x : x.substr(s));
	if(i) a[i++] = w; else { a = [w]; i = 1; }
    }
    // build resulting list
    while(--i>=0) r = MK_CONS(a[i], r);
    return r;
}

// returns -1 for end of input, start of next token otherwise
// line in h$ret1
function h$jsstringLines1(n, x) {
    TRACE_JSSTRING("lines1: " + n + " '" + x + "'");
    var m = n, l = x.length;
    if(n >= l) return -1;
    while(m < l) {
	if(x.charCodeAt(m++) === 10) {
	    // found newline
	    if(n > 0 && n === l-1) return -1; // it was the last character
            var r1 = (m-n<=1) ? "" : x.substr(n,m-n-1);
            RETURN_UBX_TUP2(m, r1);
	}
    }
    // end of string
    RETURN_UBX_TUP2(m, x.substr(n));
}

function h$jsstringLines(x) {
    TRACE_JSSTRING("lines: '" + x + "'");
    var a = null, m = 0, i = 0, l = x.length, s = 0, r = HS_NIL, w;
    if(l === 0) return HS_NIL;
    outer:
    while(true) {
	s = m;
	do {
	    if(m >= l) break outer;
	} while(x.charCodeAt(m++) !== 10);
	w = (m-s<=1) ? h$jsstringEmpty : MK_JSVAL(x.substr(s,m-s-1));
	if(i) a[i++] = w; else { a = [w]; i = 1; }
    }
    if(s < l) {
	w = MK_JSVAL(x.substr(s));
	if(i) a[i++] = w; else { a = [w]; i = 1; }
    }
    while(--i>=0) r = MK_CONS(a[i], r);
    return r;
}

function h$jsstringGroup(x) {
    TRACE_JSSTRING("group: '" + x + "'");
    var xl = x.length;
    if(xl === 0) return HS_NIL;
    var i = xl-1, si, ch, s=xl, r=HS_NIL;
    var tch = x.charCodeAt(i--);
    if(IS_LO_SURR(tch)) tch = FROM_SURR(x.charCodeAt(i--), tch);
    while(i >= 0) {
	si = i;
	ch = x.charCodeAt(i--);
	if(IS_LO_SURR(ch)) {
	    ch = FROM_SURR(x.charCodeAt(i--), ch);
	}
	if(ch != tch) {
	    tch = ch;
	    r   = MK_CONS(MK_JSVAL(x.substr(si+1,s-si)), r);
	    s   = si;
	}
    }
    return MK_CONS(MK_JSVAL(x.substr(0,s+1)), r);
}

function h$jsstringChunksOf1(n, s, x) {
    TRACE_JSSTRING("chunksOf1: " + n + " " + s + " '" + x + "'");
    var m = s, c = 0, l = x.length, ch;
    if(n <= 0 || l === 0 || s >= l) return -1
    while(++m < l) {
        ch = x.charCodeAt(m - 1);
        if(IS_HI_SURR(ch)) ++m;
        if(++c >= n) break;
    }
    var r1 = (m >= l && s === c) ? x : x.substr(s,m-s);
    RETURN_UBX_TUP2(m, r1);
}

function h$jsstringChunksOf(n, x) {
    TRACE_JSSTRING("chunksOf: " + n + " '" + x + "'");
    var l = x.length;
    if(l===0 || n <= 0)  return HS_NIL;
    if(l <= n) return MK_CONS(MK_JSVAL(x), HS_NIL);
    var a = [], i = 0, s = 0, ch, m = 0, c, r = HS_NIL;
    while(m < l) {
	s = m;
	c = 0;
	while(m < l && ++c <= n) {
	    ch = x.charCodeAt(m++);
	    if(IS_HI_SURR(ch)) ++m;
	}
	if(c) a[i++] = x.substr(s, m-s);
    }
    while(--i>=0) r = MK_CONS(MK_JSVAL(a[i]), r);
    return r;
}

function h$jsstringCount(pat, src) {
    TRACE_JSSTRING("count: '" + pat + "' '" + src + "'");
    var i = 0, n = 0, pl = pat.length, sl = src.length;
    while(i<sl) {
	i = src.indexOf(pat, i);
	if(i===-1) break;
	n++;
	i += pl;
    }
    return n;
}

function h$jsstringReplicate(n, str) {
    TRACE_JSSTRING("replicate: " + n + " '" + str + "'");
    if(n === 0 || str == '') return '';
    if(n === 1) return str;
    var r = '';
    do {
	if(n&1) r+=str;
        str+=str;
        n >>= 1;
    } while(n > 1);
    return r+str;
}

// this does not deal with combining diacritics, Data.Text does not either
var h$jsstringReverse;
if(Array.from) {
    h$jsstringReverse = function(str) {
	TRACE_JSSTRING("(Array.from) reverse: '" + str + "'");
	return Array.from(str).reverse().join('');
    }
} else {
    h$jsstringReverse = function(str) {
	TRACE_JSSTRING("(no Array.from) reverse: '" + str + "'");
	var l = str.length, a = [], o = 0, i = 0, c, c1, s = '';
	while(i < l) {
	    c = str.charCodeAt(i);
	    if(IS_HI_SURR(c)) {
		a[i]   = str.charCodeAt(i+1);
		a[i+1] = c;
		i += 2;
	    } else a[i++] = c;
	    if(i-o > 60000) {
		s = String.fromCharCode.apply(null, a.reverse()) + s;
		o = -i;
		a = [];
	    }
	}
	return (i===0) ? s : String.fromCharCode.apply(null,a.reverse()) + s;
    }
}

function h$jsstringUnpack(str) {
    TRACE_JSSTRING("unpack: '" + str + "'");
    var r = HS_NIL, i = str.length-1, c;
    while(i >= 0) {
	c = str.charCodeAt(i--);
	if(IS_LO_SURR(c)) c = FROM_SURR(str.charCodeAt(i--), c)
	r = MK_CONS(c, r);
    }
    return r;
}



#if __GLASGOW_HASKELL__ >= 800
function h$jsstringDecInteger(val) {
  TRACE_JSSTRING("decInteger");
  if(IS_INTEGER_S(val)) {
    return '' + INTEGER_S_DATA(val);
  } else if(IS_INTEGER_Jp(val)) {
    return h$ghcjsbn_showBase(INTEGER_J_DATA(val), 10);
  } else {
    return '-' + h$ghcjsbn_showBase(INTEGER_J_DATA(val), 10);
  }
}
#else
function h$jsstringDecInteger(val) {
  TRACE_JSSTRING("decInteger");
  if(IS_INTEGER_S(val)) {
    return '' + INTEGER_S_DATA(val);
  } else {
    return INTEGER_J_DATA(val).toString();
  }
}
#endif

function h$jsstringDecI64(hi,lo) {
    TRACE_JSSTRING("decI64: " + hi + " " + lo);
    var lo0 = (lo < 0) ? lo+4294967296:lo;
    if(hi < 0) {
	if(hi === -1) return ''+(lo0-4294967296);
	lo0 = 4294967296 - lo0;
	var hi0 = -1 - hi;
	var x0  = hi0 * 967296;
	var x1  = (lo0 + x0) % 1000000;
	var x2  = hi0*4294+Math.floor((x0+lo0-x1)/1000000);
	return '-' + x2 + h$jsstringDecIPadded6(x1);
    } else {
	if(hi === 0) return ''+lo0;
	var x0  = hi * 967296;
	var x1  = (lo0 + x0) % 1000000;
	var x2  = hi*4294+Math.floor((x0+lo0-x1)/1000000);
	return '' + x2 + h$jsstringDecIPadded6(x1);
    }
}

function h$jsstringDecW64(hi,lo) {
    TRACE_JSSTRING("decW64: " + hi + " " + lo);
    var lo0 = (lo < 0) ? lo+4294967296 : lo;
    if(hi === 0) return ''+lo0;
    var hi0 = (hi < 0) ? hi+4294967296 : hi;
    var x0  = hi0 * 967296;
    var x1  = (lo0 + x0) % 1000000;
    var x2  = hi0*4294+Math.floor((x0+lo0-x1)/1000000);
    return '' + x2 + h$jsstringDecIPadded6(x1);
}

#if __GLASGOW_HASKELL__ >= 800
function h$jsstringHexInteger(val) {
  TRACE_JSSTRING("hexInteger");
  if(IS_INTEGER_S(val)) {
    return '' + INTEGER_S_DATA(val);
  } else {
    // we assume it's nonnegative. this condition is checked by the Haskell code
    return h$ghcjsbn_showBase(INTEGER_J_DATA(val), 16);
  }
}
#else
function h$jsstringHexInteger(val) {
  TRACE_JSSTRING("hexInteger");
  if(IS_INTEGER_S(val)) {
    return '' + INTEGER_S_DATA(val);
  } else {
    return INTEGER_J_DATA(val).toRadix(16);
  }
}
#endif

function h$jsstringHexI64(hi,lo) {
    var lo0 = lo<0 ? lo+4294967296 : lo;
    if(hi === 0) return lo0.toString(16);
    return ((hi<0)?hi+4294967296:hi).toString(16) + h$jsstringHexIPadded8(lo0);
}

function h$jsstringHexW64(hi,lo) {
    var lo0 = lo<0 ? lo+4294967296 : lo;
    if(hi === 0) return lo0.toString(16);
    return ((hi<0)?hi+4294967296:hi).toString(16) + h$jsstringHexIPadded8(lo0);
}

// n in [0, 1000000000)
function h$jsstringDecIPadded9(n) {
    TRACE_JSSTRING("decIPadded9: " + n);
    if(n === 0) return '000000000';
    var pad = (n>=100000000)?'':
              (n>=10000000)?'0':
              (n>=1000000)?'00':
              (n>=100000)?'000':
              (n>=10000)?'0000':
              (n>=1000)?'00000':
              (n>=100)?'000000':
              (n>=10)?'0000000':
                     '00000000';
    return pad+n;
}

// n in [0, 1000000)
function h$jsstringDecIPadded6(n) {
    TRACE_JSSTRING("decIPadded6: " + n);
    if(n === 0) return '000000';
    var pad = (n>=100000)?'':
              (n>=10000)?'0':
              (n>=1000)?'00':
              (n>=100)?'000':
              (n>=10)?'0000':
                     '00000';
    return pad+n;
}

// n in [0, 2147483648)
function h$jsstringHexIPadded8(n) {
    TRACE_JSSTRING("hexIPadded8: " + n);
   if(n === 0) return '00000000';
   var pad = (n>=0x10000000)?'':
             (n>=0x1000000)?'0':
             (n>=0x100000)?'00':
             (n>=0x10000)?'000':
             (n>=0x1000)?'0000':
             (n>=0x100)?'00000':
             (n>=0x10)?'000000':
                      '0000000';
    return pad+n.toString(16);
}

function h$jsstringZeroes(n) {
    var r;
    switch(n&7) {
	case 0: r = ''; break;
	case 1: r = '0'; break;
	case 2: r = '00'; break;
	case 3: r = '000'; break;
	case 4: r = '0000'; break;
	case 5: r = '00000'; break;
	case 6: r = '000000'; break;
	case 7: r = '0000000';
    }
    for(var i=n>>3;i>0;i--) r = r + '00000000';
    return r;
}

function h$jsstringDoubleToFixed(decs, d) {
    if(decs >= 0) {
	if(Math.abs(d) < 1e21) {
	    var r = d.toFixed(Math.min(20,decs));
	    if(decs > 20) r = r + h$jsstringZeroes(decs-20);
	    return r;
	} else {
	    var r = d.toExponential();
	    var ei = r.indexOf('e');
	    var di = r.indexOf('.');
	    var e  = parseInt(r.substr(ei+1));
	    return r.substring(0,di) + r.substring(di,ei) + h$jsstringZeroes(di-ei+e) +
                   ((decs > 0) ? ('.' + h$jsstringZeroes(decs)) : '');
	}
    }
    var r = Math.abs(d).toExponential();
    var ei = r.indexOf('e');
    var e = parseInt(r.substr(ei+1));
    var m = d < 0 ? '-' : '';
    r = r.substr(0,1) + r.substring(2,ei);
    if(e >= 0) {
	return (e > r.length) ? m + r + h$jsstringZeroes(r.length-e-1) + '.0'
	                      : m + r.substr(0,e+1) + '.' + r.substr(e+1);
    } else {
	return m + '0.' + h$jsstringZeroes(-e-1) + r;
    }
}

function h$jsstringDoubleToExponent(decs, d) {
    var r;
    if(decs ===-1) {
	r = d.toExponential().replace('+','');
    } else {
	r = d.toExponential(Math.max(1, Math.min(20,decs))).replace('+','');
    }
    if(r.indexOf('.') === -1) {
	r = r.replace('e', '.0e');
    }
    if(decs > 20) r = r.replace('e', h$jsstringZeroes(decs-20)+'e');
    return r;
}

function h$jsstringDoubleGeneric(decs, d) {
    var r;
    if(decs === -1) {
	r = d.toString(10).replace('+','');
    } else {
	r = d.toPrecision(Math.max(decs+1,1)).replace('+','');
    }
    if(decs !== 0 && r.indexOf('.') === -1) {
	if(r.indexOf('e') !== -1) {
	    r = r.replace('e', '.0e');
	} else {
	    r = r + '.0';
	}
    }
    return r;
}

function h$jsstringAppend(x, y) {
    TRACE_JSSTRING("append: '" + x + "' '" + y + "'");
    return x+y;
}

function h$jsstringCompare(x, y) {
    TRACE_JSSTRING("compare: '" + x + "' '" + y + "'");
    return (x<y)?-1:((x>y)?1:0);
}

function h$jsstringUnlines(xs) {
    var r = '';
    while(IS_CONS(xs)) {
	r = r + JSVAL_VAL(CONS_HEAD(xs)) + '\n';
	xs = CONS_TAIL(xs);
    }
    return r;
}

function h$jsstringUnwords(xs) {
    if(IS_NIL(xs)) return '';
    var r = JSVAL_VAL(CONS_HEAD(xs));
    xs = CONS_TAIL(xs);
    while(IS_CONS(xs)) {
	r = r + ' ' + JSVAL_VAL(CONS_HEAD(xs));
	xs = CONS_TAIL(xs);
    }
    return r;
}

function h$jsstringReplace(pat, rep, src) {
    TRACE_JSSTRING("replace: '" + pat + "' '" + rep + "' '" + src + "'");
    var r = src.replace(pat, rep, 'g');
    // the 'g' flag is not supported everywhere, check and fall back if necessary
    if(r.indexOf(pat) !== -1) {
	r = src.split(pat).join(rep);
    }
    return r;
}

function h$jsstringReplicateChar(n, ch) {
    TRACE_JSSTRING("replicateChar: " + n + " " + ch);
    return h$jsstringReplicate(n, h$jsstringSingleton(ch));
}

function h$jsstringIsInteger(str) {
    return /^-?\d+$/.test(str);
}

function h$jsstringIsNatural(str) {
    return /^\d+$/.test(str);
}

function h$jsstringReadInt(str) {
    if(!/^-?\d+/.test(str)) return null;
    var x = parseInt(str, 10);
    var x0 = x|0;
    return (x===x0) ? x0 : null;
}

function h$jsstringLenientReadInt(str) {
    var x = parseInt(str, 10);
    var x0 = x|0;
    return (x===x0) ? x0 : null;
}

function h$jsstringReadWord(str) {
  if(!/^\d+/.test(str)) return null;
  var x = parseInt(str, 10);
  var x0 = x|0;
  if(x0<0) return (x===x0+2147483648) ? x0 : null;
  else     return (x===x0) ? x0 : null;
}

function h$jsstringReadDouble(str) {
    return parseFloat(str, 10);
}

function h$jsstringLenientReadDouble(str) {
    return parseFloat(str, 10);
}

function h$jsstringReadInteger(str) {
  TRACE_JSSTRING("readInteger: " + str);
  if(!/^(-)?\d+$/.test(str)) {
    return null;
  } else if(str.length <= 9) {
    return MK_INTEGER_S(parseInt(str, 10));
  } else {
#if __GLASGOW_HASKELL__ >= 800
    return h$ghcjsbn_readInteger(str);
#else
    return MK_INTEGER_J(new BigInteger(str, 10));
#endif
  }
}

function h$jsstringReadInt64(str) {
  if(!/^(-)?\d+$/.test(str)) {
      RETURN_UBX_TUP3(0, 0, 0);
  }
  if(str.charCodeAt(0) === 45) { // '-'
    return h$jsstringReadValue64(str, 1, true);
  } else {
    return h$jsstringReadValue64(str, 0, false);
  }
}

function h$jsstringReadWord64(str) {
  if(!/^\d+$/.test(str)) {
    RETURN_UBX_TUP3(0, 0, 0);
  }
  return h$jsstringReadValue64(str, 0, false);
}

var h$jsstringLongs = null;

function h$jsstringReadValue64(str, start, negate) {
  var l = str.length, i = start;
  while(i < l) {
    if(str.charCodeAt(i) !== 48) break;
    i++;
  }
  if(i >= l) RETURN_UBX_TUP3(1, 0, 0); // only zeroes
  if(h$jsstringLongs === null) {
    h$jsstringLongs = [];
    for(var t=10; t<=1000000000; t*=10) {
      h$jsstringLongs.push(goog.math.Long.fromInt(t));
    }
  }
  var li = l-i;
  if(li < 10 && !negate) {
    RETURN_UBX_TUP3(1, 0, parseInt(str.substr(i), 10));
  }
  var r = goog.math.Long.fromInt(parseInt(str.substr(li,9),10));
  li += 9;
  while(li < l) {
    r = r.multiply(h$jsstringLongs[Math.min(l-li-1,8)])
         .add(goog.math.Long.fromInt(parseInt(str.substr(li,9), 10)));
    li += 9;
  }
  if(negate) {
    r = r.negate();
  }
  RETURN_UBX_TUP3(1, r.getHighBits(), r.getLowBits());
}

function h$jsstringExecRE(i, str, re) {
    re.lastIndex = i;
    var m = re.exec(str);
    if(m === null) return -1;
    var a = [], x, j = 1, r = HS_NIL;
    while(true) {
	x = m[j];
	if(typeof x === 'undefined') break;
	a[j-1] = x;
	j++;
    }
    j-=1;
    while(--j>=0) r = MK_CONS(MK_JSVAL(a[j]), r);
    RETURN_UBX_TUP3(m.index, m[0], r);
}

function h$jsstringReplaceRE(pat, replacement, str) {
    return str.replace(pat, replacement);
}

function h$jsstringSplitRE(limit, re, str) {
    re.lastIndex = i;
    var s = (limit < 0) ? str.split(re) : str.split(re, limit);
    var i = s.length, r = HS_NIL;
    while(--i>=0) r = MK_CONS(MK_JSVAL(a[i]), r);
    return r;
}
