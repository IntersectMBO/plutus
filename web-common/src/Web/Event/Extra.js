/*global FileReader, exports*/
'use strict';

exports._readFileFromDragEvent = function(onLoad, onError, e) {
    var i, item, files, file, reader;

    files = [];
    if (e.dataTransfer.items) {
        for (i = 0; i < e.dataTransfer.items.length; i++) {
            item = e.dataTransfer.items[i];
            if (item.kind === 'file') {
                files.push(item.getAsFile());
            }
        }
    }

    file = files[0];
    if (file) {
        reader = new FileReader();
        reader.onloadend = function (loadEvent) {
            if (reader.error) {
                onError(reader.error)();
            } else {
                onLoad(loadEvent.target.result)();
            }
        };

        reader.readAsText(file);
    }

    return function canceler (error) {
        reader.abort();
    };
};
