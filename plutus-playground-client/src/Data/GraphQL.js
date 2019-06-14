/*global exports, require*/
'use strict';

var GraphQL = require('graphql');

exports.buildSchemaImpl = function (str) {
    return function () {
        return GraphQL.buildSchema(str);
    };
};

exports.buildClientSchemaImpl = function (str) {
    return function () {
        return GraphQL.buildClientSchema(JSON.parse(str));
    };
};
