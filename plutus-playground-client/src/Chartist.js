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

exports._barChart = function (element, options) {
    return new Chartist.Bar(
        element,
        {},
        options,
        {}
    );
};
