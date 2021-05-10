import "./index.css";

window.onload = function () {
  const elements = document.getElementsByClassName("faq");
  for (const faqComponent of elements) {
    faqComponent.addEventListener("click", () => faqComponent.classList.toggle("expanded"));
  }
};
