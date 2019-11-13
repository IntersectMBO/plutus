/*eslint-env node*/
'use strict';

exports.trackEvent_ = function (action, category, label, value) {
    gtag('event', action, {
        'event_category': category,
        'event_label': label,
        'value': value
    });
};
