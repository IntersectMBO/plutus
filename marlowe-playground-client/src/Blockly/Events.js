exports._unsafeReadBlocklyEventType = function (nothing, just, name, value) {
    var proto = Object.getPrototypeOf(value);
    if ('type' in proto && proto.type === name) {
      return just(value);
    } else {
      return nothing;
    }
}
