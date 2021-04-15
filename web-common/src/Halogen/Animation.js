exports.getAnimations_ = function (element) {
  // If the browser does not implement the Web Animation API
  // we return an empty array instead of failing.
  if ("getAnimations" in element) {
    return element.getAnimations();
  } else {
    return [];
  }
};

exports.getAnimationName = function (animation) {
  return animation.animationName;
};

exports.setOnFinishHandler_ = function (animation, cb) {
  animation.onfinish = cb;
};
