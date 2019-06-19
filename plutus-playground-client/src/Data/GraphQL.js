/*global exports, require*/
'use strict';

var GraphQL = require('graphql');

exports.buildClientSchemaImpl = function (onFailure, onSuccess, str) {
    try {
        return onSuccess(GraphQL.buildClientSchema(JSON.parse(str).data));
    } catch (e) {
        return onFailure(e);
    }
};
