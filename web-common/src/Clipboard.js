/*global exports, require*/
'use strict';

exports._copy = function (string) {
    if (navigator && navigator.clipboard) {
        navigator.clipboard.writeText(string);
    };
};
