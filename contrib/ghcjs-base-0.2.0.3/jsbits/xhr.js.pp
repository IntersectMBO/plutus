function h$sendXHR(xhr, d, cont) {
    xhr.addEventListener('error', function () {
	cont(2);
    });
    xhr.addEventListener('abort', function() {
	cont(1);
    });
    xhr.addEventListener('load', function() {
	cont(0);
    });
    if(d) {
	xhr.send(d);
    } else {
	xhr.send();
    }
}
