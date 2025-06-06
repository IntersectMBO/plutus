import React from "react";
import useBaseUrl from "@docusaurus/useBaseUrl";

export default function Footer(props) {
  return (
    <footer className="footer">
      <div className="footer-container">
        <div className="footer-left">
          <img
            className="footer-logo"
            src={useBaseUrl("/img/logo-footer.svg")}
            alt="Plutus"
          />
          <span>
            Copyright ©{new Date().getFullYear()} IOHK. Built with Docusaurus.
          </span>
        </div>
        <div className="footer-right">
          <a href={useBaseUrl("/")}>User Guide</a>
          <a
            href="https://github.com/IntersectMBO/plutus"
            class="github-link"
            target="_blank"
            aria-label="Github"
          ></a>
        </div>
      </div>
    </footer>
  );
}
