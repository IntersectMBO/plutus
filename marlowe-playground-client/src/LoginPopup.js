exports._openLoginPopup = function () {
  const height = 620;
  const width = 600;

  // TODO: move to PS
  const top = window.outerHeight / 2 - height / 2;
  const left = window.outerWidth / 2 - width / 2;

  console.log("Open login popout", width, height, top, left); // TODO: remove
  return new Promise(function (resolve) {
    // TODO: move to PS
    window.open(
      "/api/oauth/github",
      "_blank",
      `width=${width},height=${height},top=${top},left=${left},menubar=no,status=no,location=no`
    );

    const listener = function (ev) {
      console.log("openLoginPopup Event listener ", ev);
      if (ev.data === "GithubUser") {
        console.log("Resolving true");
        window.removeEventListener("message", listener);
        resolve(true);
      } else if (ev.data === "Anonymous") {
        console.log("Resolving false");
        window.removeEventListener("message", listener);
        resolve(false);
      }
    };
    window.addEventListener("message", listener);
  });
};
