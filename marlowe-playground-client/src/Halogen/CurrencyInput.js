
exports.setOldValues_ = function(input) {
    input.old_value = input.value;
    input.old_selectionStart = input.selectionStart;
    input.old_selectionEnd = input.selectionEnd;
}

exports.checkChange_ = function(input) {
    if (/^-?[0-9]*(\.[0-9]*)?$/.test(input.value)) {
        exports.setOldValues_(input);
    } else {
        input.value = input.old_value;
        input.selectionStart = input.old_selectionStart;
        input.selectionEnd = input.old_selectionEnd;
    }
}

exports.formatValueString_ = function(text, decimalPlaces) {
    var positionSeparator = text.indexOf(".");
    if (positionSeparator < 0) {
        if (decimalPlaces > 0) {
            text += '.';
            text = text.padEnd(text.length + decimalPlaces, '0');
        }
    } else {
        text = text.substring(0, positionSeparator + decimalPlaces + 1);
        text = text.padEnd(positionSeparator + decimalPlaces + 1, '0');
    }
    if (text == '') {
	text = '0';
    } else if (text[0] == '.') {
        text = '0' + text;
    } else if ((text == '-') || ((text[0] == '-') && (text[1] == '.'))) {
        text = '-0' + text.substring(1);
    }
    return text;
}

exports.formatValue_ = function(input, decimalPlaces) {
    input.value = exports.formatValueString_(input.value, decimalPlaces);
}

exports.setValue_ = function(input, str) {
    input.value = str;
}

exports.onChangeHandler_ = function(input, decimalPlaces) {
    exports.checkChange_(input);
    exports.formatValue_(input, decimalPlaces);
    return input.value;
}
