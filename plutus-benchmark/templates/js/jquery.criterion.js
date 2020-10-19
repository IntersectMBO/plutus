(function ($) {
  $.zip = function(a,b) {
    var x = Math.min(a.length,b.length);
    var c = new Array(x);
    for (var i = 0; i < x; i++)
      c[i] = [a[i],b[i]];
    return c;
  };

  $.mean = function(ary) {
    var m = 0, i = 0;

    while (i < ary.length) {
      var j = i++;
      m += (ary[j] - m) / i;
    }

    return m;
  };

  $.timeUnits = function(secs) {
    if (secs < 0)           return $.timeUnits(-secs);
    else if (secs >= 1e9)   return [1e-9, "Gs"];
    else if (secs >= 1e6)   return [1e-6, "Ms"];
    else if (secs >= 1)     return [1,    "s"];
    else if (secs >= 1e-3)  return [1e3,  "ms"];
    else if (secs >= 1e-6)  return [1e6,  "\u03bcs"];
    else if (secs >= 1e-9)  return [1e9,  "ns"];
    else if (secs >= 1e-12) return [1e12, "ps"];
    return [1, "s"];
  };

  $.scaleTimes = function(ary) {
    var s = $.timeUnits($.mean(ary));
    return [$.scaleBy(s[0], ary), s[0]];
  };

  $.prepareTime = function(secs) {
    var units = $.timeUnits(secs);
    var scaled = secs * units[0];
    var s = scaled.toPrecision(3);
    var t = scaled.toString();
    return [t.length < s.length ? t : s, units[1]];
  };

  $.scaleBy = function(x, ary) {
    var nary = new Array(ary.length);
    for (var i = 0; i < ary.length; i++)
      nary[i] = ary[i] * x;
    return nary;
  };

  $.renderTime = function(secs) {
    var x = $.prepareTime(secs);
    return x[0] + ' ' + x[1];
  };

  $.unitFormatter = function(scale) {
    var labelname;
    return function(secs,axis) {
        var x = $.prepareTime(secs / scale);
        if (labelname === x[1])
          return x[0];
        else {
          labelname = x[1];
          return x[0] + ' ' + x[1];
        }
    };
  };

  $.addTooltip = function(name, renderText) {
    function showTooltip(x, y, contents) {
	$('<div id="tooltip">' + contents + '</div>').css( {
	    position: 'absolute',
	    display: 'none',
	    top: y + 5,
	    left: x + 5,
	    border: '1px solid #fdd',
	    padding: '2px',
	    'background-color': '#fee',
	    opacity: 0.80
	}).appendTo("body").fadeIn(200);
    };
    var pp = null;
    $(name).bind("plothover", function (event, pos, item) {
	$("#x").text(pos.x.toFixed(2));
	$("#y").text(pos.y.toFixed(2));

	if (item) {
	    if (pp != item.dataIndex) {
		pp = item.dataIndex;

		$("#tooltip").remove();
		var x = item.datapoint[0],
		    y = item.datapoint[1];

		showTooltip(item.pageX, item.pageY, renderText(x,y));
	    }
	}
	else {
	    $("#tooltip").remove();
	    pp = null;
	}
    });
  };
})(jQuery);
