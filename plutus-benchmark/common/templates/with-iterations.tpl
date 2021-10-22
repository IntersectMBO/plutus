<!doctype html>
<html>
<head>
  <meta charset="utf-8"/>
  <title>criterion report</title>
  <script>
    {{{js-chart}}}
  </script>
  <script>  
    (function() {
       /* This is Criterion's `criterion.js` file modified to extend the HTML
          report with the total number of iterations and total time spent
          executing each benchmark.  The original `default.tpl` file includes
          `criterion.js` using microstache via \{\{\{js-criterion\}\}\}.  That
          loads files from a fixed location in the Criterion library using
          `data-files`, so we can't use that to load a modified version.
          Instead we have to include the entire script bodily.  */

       'use strict';

       window.addEventListener('beforeprint', function() {
           for (var id in Chart.instances) {
               Chart.instances[id].resize();
           }
       }, false);

       var errorBarPlugin = (function () {
           function drawErrorBar(chart, ctx, low, high, y, height, color) {
               ctx.save();
               ctx.lineWidth = 3;
               ctx.strokeStyle = color;
               var area = chart.chartArea;
               ctx.rect(area.left, area.top, area.right - area.left, area.bottom - area.top);
               ctx.clip();
               ctx.beginPath();
               ctx.moveTo(low, y - height);
               ctx.lineTo(low, y + height);
               ctx.moveTo(low, y);
               ctx.lineTo(high, y);
               ctx.moveTo(high, y - height);
               ctx.lineTo(high, y + height);
               ctx.stroke();
               ctx.restore();
           }
           // Avoid sudden jumps in error bars when switching
           // between linear and logarithmic scale
           function conservativeError(vx, mx, now, final, scale) {
               var finalDiff = Math.abs(mx - final);
               var diff = Math.abs(vx - now);
               return (diff > finalDiff) ? vx + scale * finalDiff : now;
           }
           return {
               afterDatasetDraw: function(chart, easingOptions) {
                   var ctx = chart.ctx;
                   var easing = easingOptions.easingValue;
                   chart.data.datasets.forEach(function(d, i) {
                       var bars = chart.getDatasetMeta(i).data;
                       var axis = chart.scales[chart.options.scales.xAxes[0].id];
                       bars.forEach(function(b, j) {
                           var value = axis.getValueForPixel(b._view.x);
                           var final = axis.getValueForPixel(b._model.x);
                           var errorBar = d.errorBars[j];
                           var low = axis.getPixelForValue(value - errorBar.minus);
                           var high = axis.getPixelForValue(value + errorBar.plus);
                           var finalLow = axis.getPixelForValue(final - errorBar.minus);
                           var finalHigh = axis.getPixelForValue(final + errorBar.plus);
                           var l = easing === 1 ? finalLow :
                               conservativeError(b._view.x, b._model.x, low,
                                                 finalLow, -1.0);
                           var h = easing === 1 ? finalHigh :
                               conservativeError(b._view.x, b._model.x,
                                                 high, finalHigh, 1.0);
                           drawErrorBar(chart, ctx, l, h, b._view.y, 4, errorBar.color);
                       });
                   });
               },
           };
       })();

       function timeUnits(secs) {
           if (secs < 0)
               return timeUnits(-secs);
           else if (secs >= 1e9)
               return [1e-9, "Gs"];
           else if (secs >= 1e6)
               return [1e-6, "Ms"];
           else if (secs >= 1)
               return [1, "s"];
           else if (secs >= 1e-3)
               return [1e3, "ms"];
           else if (secs >= 1e-6)
               return [1e6, "\u03bcs"];
           else if (secs >= 1e-9)
               return [1e9, "ns"];
           else if (secs >= 1e-12)
               return [1e12, "ps"];
           return [1, "s"];
       }

       function formatUnit(raw, unit, precision) {
           var v = precision ? raw.toPrecision(precision) : Math.round(raw);
           var label = String(v) + ' ' + unit;
           return label;
       }

       function formatTime(value, precision) {
           var units = timeUnits(value);
           var scale = units[0];
           return formatUnit(value * scale, units[1], precision);
       }

       // Formats the ticks on the X-axis on the scatter plot
       var iterFormatter = function() {
           var denom = 0;
           return function(iters, index, values) {
               if (iters == 0) {
                   return '';
               }
               if (index == values.length - 1) {
                   return '';
               }
               var power;
               if (iters >= 1e9) {
                   denom = 1e9;
                   power = '⁹';
               } else if (iters >= 1e6) {
                   denom = 1e6;
                   power = '⁶';
               } else if (iters >= 1e3) {
                   denom = 1e3;
                   power = '³';
               } else {
                   denom = 1;
               }
               if (denom > 1) {
                   var value = (iters / denom).toFixed();
                   return String(value) + '×10' + power;
               } else {
                   return String(iters);
               }
           };
       };

       var colors = ["#edc240", "#afd8f8", "#cb4b4b", "#4da74d", "#9440ed"];
       var errorColors = ["#cda220", "#8fb8d8", "#ab2b2b", "#2d872d", "#7420cd"];


       // Positions tooltips at cursor. Required for overview since the bars may
       // extend past the canvas width.
       Chart.Tooltip.positioners.cursor = function(_elems, position) {
           return position;
       }

       function axisType(logaxis) {
           return logaxis ? 'logarithmic' : 'linear';
       }

       function reportSort(a, b) {
           return a.reportNumber - b.reportNumber;
       }

       // adds groupNumber and group fields to reports;
       // returns list of list of reports, grouped by group
       function groupReports(reports) {

           function reportGroup(report) {
               var parts = report.groups.slice();
               parts.pop();
               return parts.join('/');
           }

           var groups = [];
           reports.forEach(function(report) {
               report.group = reportGroup(report);
               if (groups.length === 0) {
                   groups.push([report]);
               } else {
                   var prevGroup = groups[groups.length - 1];
                   var prevGroupName = prevGroup[0].group;
                   if (prevGroupName === report.group) {
                       prevGroup.push(report);
                   } else {
                       groups.push([report]);
                   }
               }
               report.groupNumber = groups.length - 1;
           });
           return groups;
       }

       // compares 2 arrays lexicographically
       function lex(aParts, bParts) {
           for(var i = 0; i < aParts.length && i < bParts.length; i++) {
               var x = aParts[i];
               var y = bParts[i];
               if (x < y) {
                   return -1;
               }
               if (y < x) {
                   return 1;
               }
           }
           return aParts.length - bParts.length;
       }
       function lexicalSort(a, b) {
           return lex(a.groups, b.groups);
       }

       function reverseLexicalSort(a, b) {
           return lex(a.groups.slice().reverse(), b.groups.slice().reverse());
       }

       function durationSort(a, b) {
           return a.reportAnalysis.anMean.estPoint - b.reportAnalysis.anMean.estPoint;
       }
       function reverseDurationSort(a,b) {
           return -durationSort(a,b);
       }

       // pure function that produces the 'data' object of the overview chart
       function overviewData(state, reports) {
           var order = state.order;
           var sorter = order === 'report-index' ? reportSort
               : order === 'lex'          ? lexicalSort
               : order === 'colex'        ? reverseLexicalSort
               : order === 'duration'     ? durationSort
               : order === 'rev-duration' ? reverseDurationSort
               : reportSort;
           var sortedReports = reports.filter(function(report) {
               return !state.hidden[report.groupNumber];
           }).slice().sort(sorter);
           var data = sortedReports.map(function(report) {
               return report.reportAnalysis.anMean.estPoint;
           });
           var labels = sortedReports.map(function(report) {
               return report.groups.join(' / ');
           });
           var upperBound = function(report) {
               var est = report.reportAnalysis.anMean;
               return est.estPoint + est.estError.confIntUDX;
           };
           var errorBars = sortedReports.map(function(report) {
               var est = report.reportAnalysis.anMean;
               return {
                   minus: est.estError.confIntLDX,
                   plus: est.estError.confIntUDX,
                   color: errorColors[report.groupNumber % errorColors.length]
               };
           });
           var top = sortedReports.map(upperBound).reduce(function(a, b) {
               return Math.max(a, b);
           }, 0);
           var scale = top;
           if(state.activeReport !== null) {
               reports.forEach(function(report) {
                   if(report.reportNumber === state.activeReport) {
                       scale = upperBound(report);
                   }
               });
           }

           return {
               labels: labels,
               top: top,
               max: scale * 1.1,
               reports: sortedReports,
               datasets: [{
                   borderWidth: 1,
                   backgroundColor: sortedReports.map(function(report) {
                       var active = report.reportNumber === state.activeReport;
                       var alpha = active ? 'ff' : 'a0';
                       var color = colors[report.groupNumber % colors.length] + alpha;
                       if (active) {
                           return Chart.helpers.getHoverColor(color);
                       } else {
                           return color;
                       }
                   }),
                   barThickness: 16,
                   barPercentage: 0.8,
                   data: data,
                   errorBars: errorBars,
                   minBarLength: 2,
               }]
           };
       }

       function inside(box, point) {
           return (point.x >= box.left && point.x <= box.right && point.y >= box.top &&
                   point.y <= box.bottom);
       }

       function overviewHover(event, elems) {
           var chart = this;
           var xAxis = chart.scales[chart.options.scales.xAxes[0].id];
           var yAxis = chart.scales[chart.options.scales.yAxes[0].id];
           var point = Chart.helpers.getRelativePosition(event, chart);
           var over =
               (inside(xAxis, point) || inside(yAxis, point) || elems.length > 0);
           if (over) {
               chart.canvas.style.cursor = "pointer";
           } else {
               chart.canvas.style.cursor = "default";
           }
       }

       // Re-renders the overview after clicking/sorting
       function renderOverview(state, reports, chart) {
           var data = overviewData(state, reports);
           var xaxis = chart.options.scales.xAxes[0];
           xaxis.ticks.max = data.max;
           chart.config.data.datasets[0].backgroundColor = data.datasets[0].backgroundColor;
           chart.config.data.datasets[0].errorBars = data.datasets[0].errorBars;
           chart.config.data.datasets[0].data = data.datasets[0].data;
           chart.options.scales.xAxes[0].type = axisType(state.logaxis);
           chart.options.legend.display = state.legend;
           chart.data.labels = data.labels;
           chart.update();
       }

       function overviewClick(state, reports) {
           return function(event, elems) {
               var chart = this;
               var xAxis = chart.scales[chart.options.scales.xAxes[0].id];
               var yAxis = chart.scales[chart.options.scales.yAxes[0].id];
               var point = Chart.helpers.getRelativePosition(event, chart);
               var sorted = overviewData(state, reports).reports;

               function activateBar(index) {
                   // Trying to activate active bar disables instead
                   if (sorted[index].reportNumber === state.activeReport) {
                       state.activeReport = null;
                   } else {
                       state.activeReport = sorted[index].reportNumber;
                   }
               }

               if (inside(xAxis, point)) {
                   state.activeReport = null;
                   state.logaxis = !state.logaxis;
                   renderOverview(state, reports, chart);
               } else if (inside(yAxis, point)) {
                   var index = yAxis.getValueForPixel(point.y);
                   activateBar(index);
                   renderOverview(state, reports, chart);
               } else if (elems.length > 0) {
                   var elem = elems[0];
                   var index = elem._index;
                   activateBar(index);
                   state.logaxis = false;
                   renderOverview(state, reports, chart);
               } else if(inside(chart.chartArea, point)) {
                   state.activeReport = null;
                   renderOverview(state, reports, chart);
               }
           };
       }

       // listener for sort drop-down
       function overviewSort(state, reports, chart) {
           return function(event) {
               state.order = event.currentTarget.value;
               renderOverview(state, reports, chart);
           };
       }

       // Returns a formatter for the ticks on the X-axis of the overview
       function overviewTick(state) {
           return function(value, index, values) {
               var label = formatTime(value);
               if (state.logaxis) {
                   const remain = Math.round(value /
                                             (Math.pow(10, Math.floor(Chart.helpers.log10(value)))));
                   if (index === values.length - 1) {
                       // Draw endpoint if we don't span a full order of magnitude
                       if (values[index] / values[1] < 10) {
                           return label;
                       } else {
                           return '';
                       }
                   }
                   if (remain === 1) {
                       return label;
                   }
                   return '';
               } else {
                   // Don't show the right endpoint
                   if (index === values.length - 1) {
                       return '';
                   }
                   return label;
               }
           }
       }

       function mkOverview(reports) {
           var canvas = document.createElement('canvas');

           var state = {
               logaxis: false,
               activeReport: null,
               order: 'index',
               hidden: {},
               legend: false,
           };


           var data = overviewData(state, reports);
           var chart = new Chart(canvas.getContext('2d'), {
               type: 'horizontalBar',
               data: data,
               plugins: [errorBarPlugin],
               options: {
                   onHover: overviewHover,
                   onClick: overviewClick(state, reports),
                   onResize: function(chart, size) {
                       if (size.width < 800) {
                           chart.options.scales.yAxes[0].ticks.mirror = true;
                           chart.options.scales.yAxes[0].ticks.padding = -10;
                           chart.options.scales.yAxes[0].ticks.fontColor = '#000';
                       } else {
                           chart.options.scales.yAxes[0].ticks.fontColor = '#666';
                           chart.options.scales.yAxes[0].ticks.mirror = false;
                           chart.options.scales.yAxes[0].ticks.padding = 0;
                       }
                   },
                   elements: {
                       rectangle: {
                           borderWidth: 2,
                       },
                   },
                   scales: {
                       yAxes: [{
                           ticks: {
                               // make sure we draw the ticks above the error bars
                               z: 2,
                           }
                       }],
                       xAxes: [{
                           display: true,
                           type: axisType(state.logaxis),
                           ticks: {
                               autoSkip: false,
                               min: 0,
                               max: data.top * 1.1,
                               minRotation: 0,
                               maxRotation: 0,
                               callback: overviewTick(state),
                           }
                       }]
                   },
                   responsive: true,
                   maintainAspectRatio: false,
                   legend: {
                       display: state.legend,
                       position: 'right',
                       onLeave: function() {
                           chart.canvas.style.cursor = 'default';
                       },
                       onHover: function() {
                           chart.canvas.style.cursor = 'pointer';
                       },
                       onClick: function(_event, item) {
                           // toggle hidden
                           state.hidden[item.groupNumber] = !state.hidden[item.groupNumber];
                           renderOverview(state, reports, chart);
                       },
                       labels: {
                           boxWidth: 12,
                           generateLabels: function() {
                               var groups = [];
                               var groupNames = [];
                               reports.forEach(function(report) {
                                   var index = groups.indexOf(report.groupNumber);
                                   if (index === -1) {
                                       groups.push(report.groupNumber);
                                       var groupName = report.groups.slice(0,report.groups.length-1).join(' / ');
                                       groupNames.push(groupName);
                                   }
                               });
                               return groups.map(function(groupNumber, index) {
                                   var color = colors[groupNumber % colors.length];
                                   return {
                                       text: groupNames[index],
                                       fillStyle: color,
                                       hidden: state.hidden[groupNumber],
                                       groupNumber: groupNumber,
                                   };
                               });
                           },
                       },
                   },
                   tooltips: {
                       position: 'cursor',
                       callbacks: {
                           label: function(item) {
                               return formatTime(item.xLabel, 3);
                           },
                       },
                   },
                   title: {
                       display: false,
                       text: 'Chart.js Horizontal Bar Chart'
                   }
               }
           });
           document.getElementById('sort-overview')
               .addEventListener('change', overviewSort(state, reports, chart));
           var toggle = document.getElementById('legend-toggle');
           toggle.addEventListener('mouseup', function () {
               state.legend = !state.legend;
               if(state.legend) {
                   toggle.classList.add('right');
               } else {
                   toggle.classList.remove('right');
               }
               renderOverview(state, reports, chart);
           })
           return canvas;
       }

       function mkKDE(report) {
           var canvas = document.createElement('canvas');
           var mean = report.reportAnalysis.anMean.estPoint;
           var units = timeUnits(mean);
           var scale = units[0];
           var reportKDE = report.reportKDEs[0];
           var data = reportKDE.kdeValues.map(function(time, index) {
               var pdf = reportKDE.kdePDF[index];
               return {
                   x: time * scale,
                   y: pdf
               };
           });
           var chart = new Chart(canvas.getContext('2d'), {
               type: 'line',
               data: {
                   datasets: [{
                       label: 'KDE',
                       borderColor: colors[0],
                       borderWidth: 2,
                       backgroundColor: '#00000000',
                       data: data,
                       hoverBorderWidth: 1,
                       pointHitRadius: 8,
                   },
                              {
                                  label: 'mean'
                              }
                             ],
               },
               plugins: [{
                   afterDraw: function(chart) {
                       var ctx = chart.ctx;
                       var area = chart.chartArea;
                       var axis = chart.scales[chart.options.scales.xAxes[0].id];
                       var value = axis.getPixelForValue(mean * scale);
                       ctx.save();
                       ctx.strokeStyle = colors[1];
                       ctx.lineWidth = 2;
                       ctx.beginPath();
                       ctx.moveTo(value, area.top);
                       ctx.lineTo(value, area.bottom);
                       ctx.stroke();
                       ctx.restore();
                   },
               }],
               options: {
                   title: {
                       display: true,
                       text: report.groups.join(' / ') + ' — time densities',
                   },
                   elements: {
                       point: {
                           radius: 0,
                           hitRadius: 0
                       }
                   },
                   scales: {
                       xAxes: [{
                           display: true,
                           type: 'linear',
                           scaleLabel: {
                               display: false,
                               labelString: 'Time'
                           },
                           ticks: {
                               min: reportKDE.kdeValues[0] * scale,
                               max: reportKDE.kdeValues[reportKDE.kdeValues.length - 1] * scale,
                               callback: function(value, index, values) {
                                   // Don't show endpoints
                                   if (index === 0 || index === values.length - 1) {
                                       return '';
                                   }
                                   var str = String(value) + ' ' + units[1];
                                   return str;
                               },
                           }
                       }],
                       yAxes: [{
                           display: true,
                           type: 'linear',
                           ticks: {
                               min: 0,
                               callback: function() {
                                   return '';
                               },
                           },
                       }]
                   },
                   responsive: true,
                   legend: {
                       display: false,
                       position: 'right',
                   },
                   tooltips: {
                       mode: 'nearest',
                       callbacks: {
                           title: function() {
                               return '';
                           },
                           label: function(
                               item) {
                               return formatUnit(item.xLabel, units[1], 3);
                           },
                       },
                   },
                   hover: {
                       intersect: false
                   },
               }
           });
           return canvas;
       }

       function mkScatter(report) {

           // collect the measured value for a given regression
           function getMeasured(key) {
               var ix = report.reportKeys.indexOf(key);
               return report.reportMeasured.map(function(x) {
                   return x[ix];
               });
           }

           var canvas = document.createElement('canvas');
           var times = getMeasured("time");
           var iters = getMeasured("iters");
           var lastIter = iters[iters.length - 1];
           var olsTime = report.reportAnalysis.anRegress[0].regCoeffs.iters;
           var dataPoints = times.map(function(time, i) {
               return {
                   x: iters[i],
                   y: time
               }
           });
           var formatter = iterFormatter();
           var chart = new Chart(canvas.getContext('2d'), {
               type: 'scatter',
               data: {
                   datasets: [{
                       data: dataPoints,
                       label: 'scatter',
                       borderWidth: 2,
                       pointHitRadius: 8,
                       borderColor: colors[1],
                       backgroundColor: '#fff',
                   },
                              {
                                  data: [
                                      {x: 0, y: 0 },
                                      { x: lastIter, y: olsTime.estPoint * lastIter }
                                  ],
                                  label: 'regression',
                                  type: 'line',
                                  backgroundColor: "#00000000",
                                  borderColor: colors[0],
                                  pointRadius: 0,
                              },
                              {
                                  data: [{
                                      x: 0,
                                      y: 0
                                  }, {
                                      x: lastIter,
                                      y: (olsTime.estPoint - olsTime.estError.confIntLDX) * lastIter,
                                  }],
                                  label: 'lower',
                                  type: 'line',
                                  fill: 1,
                                  borderWidth: 0,
                                  pointRadius: 0,
                                  borderColor: '#00000000',
                                  backgroundColor: colors[0] + '33',
                              },
                              {
                                  data: [{
                                      x: 0,
                                      y: 0
                                  }, {
                                      x: lastIter,
                                      y: (olsTime.estPoint + olsTime.estError.confIntUDX) * lastIter,
                                  }],
                                  label: 'upper',
                                  type: 'line',
                                  fill: 1,
                                  borderWidth: 0,
                                  borderColor: '#00000000',
                                  pointRadius: 0,
                                  backgroundColor: colors[0] + '33',
                              },
                             ],
               },
               options: {
                   title: {
                       display: true,
                       text: report.groups.join(' / ') + ' — time per iteration',
                   },
                   scales: {
                       yAxes: [{
                           display: true,
                           type: 'linear',
                           scaleLabel: {
                               display: false,
                               labelString: 'Time'
                           },
                           ticks: {
                               callback: function(value, index, values) {
                                   return formatTime(value);
                               },
                           }
                       }],
                       xAxes: [{
                           display: true,
                           type: 'linear',
                           scaleLabel: {
                               display: false,
                               labelString: 'Iterations'
                           },
                           ticks: {
                               callback: formatter,
                               max: lastIter,
                           }
                       }],
                   },
                   legend: {
                       display: false,
                   },
                   tooltips: {
                       callbacks: {
                           label: function(ttitem, ttdata) {
                               var iters = ttitem.xLabel;
                               var duration = ttitem.yLabel;
                               return formatTime(duration, 3) + ' / ' +
                                   iters.toLocaleString() + ' iters';
                           },
                       },
                   },
               }
           });
           return canvas;
       }

       // Create an HTML Element with attributes and child nodes
       function elem(tag, props, children) {
           var node = document.createElement(tag);
           if (children) {
               children.forEach(function(child) {
                   if (typeof child === 'string') {
                       var txt = document.createTextNode(child);
                       node.appendChild(txt);
                   } else {
                       node.appendChild(child);
                   }
               });
           }
           Object.assign(node, props);
           return node;
       }

       function bounds(analysis) {
           var mean = analysis.estPoint;
           return {
               low: mean - analysis.estError.confIntLDX,
               mean: mean,
               high: mean + analysis.estError.confIntUDX
           };
       }

       function confidence(level) {
           return String(1 - level) + ' confidence level';
       }

       /* For each benchmark, report the total number of executions and the total
          time taken.  This makes it easier to see if we've got enough data to get
          sensible results (the default time limit is 5 seconds, so if a benchmark
          runs for a long time you may not get very many data points).
       */
       function mkIterations(report) {
           function getMeasured(key) {
               var ix = report.reportKeys.indexOf(key);
               return report.reportMeasured.map(function(x) {
                   return x[ix];
               });
           }

           var totalIters = getMeasured("iters").reduce((a,b) => a+b, 0)
           var totalTime  = getMeasured("time").reduce((a,b) => a+b, 0)
           return elem('div', {className: 'iterations'}, [
               elem('p', {}, [
                   'Total number of executions: ',
                   String(totalIters),
                   elem ('br',[]),
                   'Total time: ',
                   formatTime(totalTime,3)
               ])
           ]);
       }

       function mkOutliers(report) {
           var outliers = report.reportAnalysis.anOutlierVar;
           return elem('div', {className: 'outliers'}, [
               elem('p', {}, [
                   'Outlying measurements have ',
                   outliers.ovDesc,
                   ' (', String((outliers.ovFraction * 100).toPrecision(3)), '%)',
                   ' effect on estimated standard deviation.'
               ])
           ]);
       }

       function mkTable(report) {
           var analysis = report.reportAnalysis;
           var timep4 = function(t) {
               return formatTime(t, 3)
           };
           var idformatter = function(t) {
               return t.toPrecision(3)
           };
           var rows = [
               Object.assign({
                   label: 'OLS regression',
                   formatter: timep4
               },
                             bounds(analysis.anRegress[0].regCoeffs.iters)),
               Object.assign({
                   label: 'R² goodness-of-fit',
                   formatter: idformatter
               },
                             bounds(analysis.anRegress[0].regRSquare)),
               Object.assign({
                   label: 'Mean execution time',
                   formatter: timep4
               },
                             bounds(analysis.anMean)),
               Object.assign({
                   label: 'Standard deviation',
                   formatter: timep4
               },
                             bounds(analysis.anStdDev)),
           ];
           return elem('table', {
               className: 'analysis'
           }, [
               elem('thead', {}, [
                   elem('tr', {}, [
                       elem('th'),
                       elem('th', {
                           className: 'low',
                           title: confidence(analysis.anRegress[0].regCoeffs.iters.estError.confIntCL)
                       }, ['lower bound']),
                       elem('th', {}, ['estimate']),
                       elem('th', {
                           className: 'high',
                           title: confidence(analysis.anRegress[0].regCoeffs.iters.estError.confIntCL)
                       }, ['upper bound']),
                   ])
               ]),
               elem('tbody', {}, rows.map(function(row) {
                   return elem('tr', {}, [
                       elem('td', {}, [row.label]),
                       elem('td', {className: 'low'}, [row.formatter(row.low, 4)]),
                       elem('td', {}, [row.formatter(row.mean)]),
                       elem('td', {className: 'high'}, [row.formatter(row.high, 4)]),
                   ]);
               }))
           ]);
       }
       document.addEventListener('DOMContentLoaded', function() {
           var rawJSON = document.getElementById('report-data').text;
           var reportData = JSON.parse(rawJSON)
               .map(function(report) {
                   report.groups = report.reportName.split('/');
                   return report;
               });
           groupReports(reportData);
           var overview = document.getElementById('overview-chart');
           var overviewLineHeight = 16 * 1.25;
           overview.style.height =
               String(overviewLineHeight * reportData.length + 36) + 'px';
           overview.appendChild(mkOverview(reportData.slice()));
           var reports = document.getElementById('reports');
           reportData.forEach(function(report, i) {
               var id = 'report_' + String(i);
               reports.appendChild(
                   elem('div', {id: id, className: 'report-details'}, [
                       elem('h1', {}, [elem('a', {href: '#' + id}, [report.groups.join(' / ')])]),
                       elem('div', {className: 'kde'}, [mkKDE(report)]),
                       elem('div', {className: 'scatter'}, [mkScatter(report)]),
                       mkIterations(report), mkTable(report), mkOutliers(report)
                   ]));
           });
        }, false);
    })();
  </script>
  <style>
    {{{criterion-css}}}
  </style>
  <script type="application/json" id="report-data">
    {{{json}}}
  </script>
  <meta name="viewport" content="width=device-width, initial-scale=1">
</head>
<body>
  <div class="content">
    <h1 class='title'>criterion performance measurements</h1>
    <p class="no-print"><a href="#grokularation">want to understand this report?</a></p>
    <h1 id="overview"><a href="#overview">overview</a></h1>
    <div class="no-print">
      <select id="sort-overview" class="select">
        <option value="report-index">index</option>
        <option value="lex">lexical</option>
        <option value="colex">colexical</option>
        <option value="duration">time ascending</option>
        <option value="rev-duration">time descending</option>
      </select>
      <span class="overview-info">
        <a href="#controls-explanation" class="info" title="click bar/label to zoom; x-axis to toggle logarithmic scale; background to reset">&#9432;</a>
        <a id="legend-toggle" class="chevron button"></a>
      </span>
    </div>
    <aside id="overview-chart"></aside>
    <main id="reports"></main>
  </div>

  <aside id="controls-explanation" class="explanation no-print">
    <h1><a href="#controls-explanation">controls</a></h1>

    <p>
      The overview chart can be controlled by clicking the following elements:
      <ul>
        <li><em>a bar or its label</em> zooms the x-axis to that bar</li>
        <li><em>the background</em> resets zoom to the entire chart</li>
        <li><em>the x-axis</em> toggles between linear and logarithmic scale</li>
        <li><em>the chevron</em> in the top-right toggles the the legend</li>
        <li><em>a group name in the legend</em> shows/hides that group</li>
      </ul>
    </p>

    <p>
      The overview chart supports the following sort orders:
      <ul>
        <li><em>index</em> order is the order as the benchmarks are defined in criterion</li>
        <li><em>lexical</em> order sorts <a href="https://en.wikipedia.org/wiki/Lexicographic_order#Motivation_and_definition">groups left-to-right</a>, alphabetically</li>
        <li><em>colexical</em> order sorts <a href="https://en.wikipedia.org/wiki/Lexicographic_order#Colexicographic_order">groups right-to-left</a>, alphabetically</li>
        <li><em>time ascending/descending</em> order sorts by the estimated mean execution time</li>
      </ul>
    </p>

  </aside>

  <aside id="grokularation" class="explanation">

    <h1><a>understanding this report</a></h1>

    <p>
      In this report, each function benchmarked by criterion is assigned a section of its own.
      <span class="no-print">The charts in each section are active; if you hover your mouse over data points and annotations, you will see more details.</span>
    </p>

    <ul>
      <li>
        The chart on the left is a <a href="http://en.wikipedia.org/wiki/Kernel_density_estimation">kernel density estimate</a> (also known as a KDE) of time measurements.
        This graphs the probability of any given time measurement occurring.
        A spike indicates that a measurement of a particular time occurred; its height indicates how often that measurement was repeated.
      </li>

      <li>
        The chart on the right is the raw data from which the kernel density estimate is built.
        The <em>x</em>-axis indicates the number of loop iterations, while the <em>y</em>-axis shows measured execution time for the given number of loop iterations.
        The line behind the values is the linear regression estimate of execution time for a given number of iterations.
        Ideally, all measurements will be on (or very near) this line.
        The transparent area behind it shows the confidence interval for the execution time estimate.
      </li>
    </ul>

    <p>
      Under the charts is a small table.
      The first two rows are the results of a linear regression run on the measurements displayed in the right-hand chart.
    </p>

    <ul>
      <li>
        <em>OLS regression</em> indicates the time estimated for a single loop iteration using an ordinary least-squares regression model.
        This number is more accurate than the <em>mean</em> estimate below it, as it more effectively eliminates measurement overhead and other constant factors.
      </li>
      <li>
        <em>R<sup>2</sup>; goodness-of-fit</em> is a measure of how accurately the linear regression model fits the observed measurements.
        If the measurements are not too noisy, R<sup>2</sup>; should lie between 0.99 and 1, indicating an excellent fit.
        If the number is below 0.99, something is confounding the accuracy of the linear model.
      </li>
      <li>
        <em>Mean execution time</em> and <em>standard deviation</em> are statistics calculated from execution time divided by number of iterations.
      </li>
    </ul>

    <p>
      We use a statistical technique called the <a href="http://en.wikipedia.org/wiki/Bootstrapping_(statistics)">bootstrap</a> to provide confidence intervals on our estimates.
      The bootstrap-derived upper and lower bounds on estimates let you see how accurate we believe those estimates to be.
      <span class="no-print">(Hover the mouse over the table headers to see the confidence levels.)</span>
    </p>

    <p>
      A noisy benchmarking environment can cause some or many measurements to fall far from the mean.
      These outlying measurements can have a significant inflationary effect on the estimate of the standard deviation.
      We calculate and display an estimate of the extent to which the standard deviation has been inflated by outliers.
    </p>

  </aside>

  <footer>
    <div class="content">
      <h1 class="colophon-header">colophon</h1>
      <p>
        This report was created using the <a href="http://hackage.haskell.org/package/criterion">criterion</a>
        benchmark execution and performance analysis tool.
      </p>
      <p>
        Criterion is developed and maintained
        by <a href="http://www.serpentine.com/blog/">Bryan O'Sullivan</a>.
      </p>
    </div>
  </footer>
</body>
</html>
