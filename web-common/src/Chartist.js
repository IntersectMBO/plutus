/*global exports, require*/
'use strict';

var Chartist = require('chartist');

exports.tooltipPlugin = Chartist.plugins.tooltip();

exports.axisTitlePlugin = Chartist.plugins.ctAxisTitle;

exports.intAutoScaleAxis = {
    type: Chartist.AutoScaleAxis,
    onlyInteger: true
};

exports._updateData = function (chart, newData) {
    chart.update(newData);
};

// Chartist does a resize when you call update with no new data. I
// find that a bit weird and want to separate those behaviours into
// two separately-named calls in PureScript-space.
exports._resize = function (chart) {
    chart.update();
};

exports._barChart = function (element, options) {
    return new Chartist.Bar(
        element,
        {},
        options,
        {}
    );
};
