import "./index.css";
import "./carousel.css";
import $ from "jquery";
import { activateAnalytics } from "./analytics";

function initializeFaqComponent() {
  const faqElements = document.getElementsByClassName("faq");
  for (const faqComponent of faqElements) {
    faqComponent.addEventListener("click", () => faqComponent.classList.toggle("expanded"));
  }
}

function initializeBackToTopComponent() {
  const backToTopComponent = document.getElementById("back-to-top");

  var myScrollFunc = function () {
    var y = window.scrollY;
    if (y >= 400) {
      backToTopComponent.className = "show select-none";
    } else {
      backToTopComponent.className = "hide";
    }
  };

  window.addEventListener("scroll", myScrollFunc);
}

// This function adds smooth scrolling for the internal links.
// It is using some deprecated features from jQuery which adds 80kb to the build.
// TODO: maybe refactor to use native JS.
function initializeSmoothScrolling() {
  // Select all links with hashes
  $('a[href*="#"]')
    // Remove links that don't actually link to anything
    .not('[href="#"]')
    .not('[href="#0"]')
    .click(function (event) {
      // On-page links
      if (
        location.pathname.replace(/^\//, "") == this.pathname.replace(/^\//, "") &&
        location.hostname == this.hostname
      ) {
        // Figure out element to scroll to
        var target = $(this.hash);
        target = target.length ? target : $("[name=" + this.hash.slice(1) + "]");
        // Does a scroll target exist?
        if (target.length) {
          // Only prevent default if animation is actually gonna happen
          event.preventDefault();
          $("html, body").animate(
            {
              scrollTop: target.offset().top,
            },
            500,
            function () {
              // Callback after animation
              // Must change focus!
              var $target = $(target);
              $target.focus();
              if ($target.is(":focus")) {
                // Checking if the target was focused
                return false;
              } else {
                $target.attr("tabindex", "-1"); // Adding tabindex for elements not focusable
                $target.focus(); // Set focus again
              }
            }
          );
        }
      }
    });
}

function initializeMobileMenu() {
  const drawer = document.getElementById("menu-drawer");
  const menu = document.getElementById("mobile-menu");
  const mobileMenuClose = document.getElementById("mobile-menu-close");
  function closeOnEscape(evt) {
    if (evt.key == "Escape") {
      closeMenu();
    }
  }

  function openMenu() {
    menu.classList.remove("hidden");
    // We need to add this class to the body so that the menu does not
    // let the user scroll.
    document.body.classList.add("overflow-hidden");
    // Allow the menu to be closed with the Escape key.
    document.addEventListener("keydown", closeOnEscape);
  }

  function closeMenu() {
    menu.classList.add("hidden");
    document.body.classList.remove("overflow-hidden");
    document.removeEventListener("keydown", closeOnEscape);
  }
  drawer.onclick = openMenu;
  mobileMenuClose.onclick = closeMenu;
  $("#mobile-menu a").on("click", closeMenu);
}

function initializeContractCarousel() {
  const carousel = document.getElementById("contract-carousel");

  const selectors = Array.from(document.getElementById("carousel-selectors").children);
  const items = Array.from(document.getElementById("carousel-items").children);

  let selectedItem = 0;
  function select(index) {
    selectors[selectedItem].classList.remove("active");
    selectors[index].classList.add("active");
    items[selectedItem].classList.remove("active");
    items[index].classList.add("active");
    selectedItem = index;
  }

  selectors.forEach((elm, i) => {
    elm.onclick = function () {
      select(i);
    };
  });

  function startRotation() {
    return setInterval(function () {
      select((selectedItem + 1) % 3);
    }, 3500);
  }

  let rotateSubscription = startRotation();
  carousel.onmouseenter = function () {
    clearInterval(rotateSubscription);
  };
  carousel.onmouseleave = function () {
    rotateSubscription = startRotation();
  };
}

function fixCrossLinks() {
  const env = window.location.hostname.split(".")[0];

  if (env == "localhost" || env == "marlowe-finance") {
    return;
  }

  const urls = {
    run: "https://" + env + ".marlowe-dash.iohkdev.io",
    play: "https://" + env + ".marlowe.iohkdev.io",
  };

  const crossLinks = document.querySelectorAll("a[data-marlowe-component]");
  for (const crossLink of crossLinks) {
    crossLink.href = urls[crossLink.dataset.marloweComponent];
  }
}

function activateYoutube() {
  $(".video-container iframe").each((_, elm) => {
    elm.setAttribute("src", elm.getAttribute("data-src"));
    elm.classList.remove("hidden");
  });
  $(".video-container p").each((_, elm) => {
    elm.classList.add("hidden");
    elm.classList.remove("flex");
  });
}
function activateTypeform() {
  var script = document.createElement("script");
  script.type = "text/javascript";
  script.async = !0;
  script.src = "//embed.typeform.com/next/embed.js";
  var node = document.getElementsByTagName("script")[0];
  node.parentNode.insertBefore(script, node);
}

function initializeGDPR() {
  function activateComponentsWithCookies() {
    activateAnalytics();
    activateYoutube();
    activateTypeform();
  }
  const gdprConsent = localStorage.getItem("gdpr-consent");
  if (gdprConsent === "agree") {
    activateComponentsWithCookies();
    $("#gdpr-banner").addClass("hidden");
  } else {
    // Show the banner
    $("#gdpr-banner").removeClass("hidden");
    $(".agreeGDPR").on("click", () => {
      localStorage.setItem("gdpr-consent", "agree");
      activateComponentsWithCookies();
      $("#gdpr-banner").addClass("hidden");
    });
    $(".cancelGDPR").on("click", () => {
      $("#gdpr-banner").addClass("hidden");
    });
  }
}

window.onload = function () {
  initializeGDPR();
  initializeFaqComponent();
  initializeBackToTopComponent();
  initializeSmoothScrolling();
  initializeMobileMenu();
  initializeContractCarousel();
  fixCrossLinks();
};
