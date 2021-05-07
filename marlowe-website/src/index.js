import "./index.css";

window.onload = function () {
  console.log("Placeholder");
  const elements = document.getElementsByClassName("faq");
  for (const faqComponent of elements) {
    faqComponent.addEventListener("click", () => faqComponent.classList.toggle("expanded"));
  }
  console.log(elements);
};
