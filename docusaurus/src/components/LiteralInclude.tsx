import useDocusaurusContext from "@docusaurus/useDocusaurusContext";
import CodeBlock from "@theme/CodeBlock";
import { useEffect, useState } from "react";
const LiteralInclude = ({
  file,
  title,
  start,
  end,
  language,
}: {
  file: string;
  title?: string;
  start: string;
  end: string;
  language: string;
}) => {
  const { siteConfig } = useDocusaurusContext();

  const [loading, setLoading] = useState(true);
  const [error, setError] = useState("");
  const [codeString, setCodeString] = useState("");

  useEffect(() => {
    // Track if the component is still mounted
    let isActive = true;

    async function loadCode() {
      // Fetch the raw code from the file
      const res = await fetch(`/plutus/master/docs/code/${file}`);
      const rawCode = await res.text();

      // If the component is unmounted, don't set the state
      if (!isActive) return;
      setLoading(false);

      // If the code block is not found, set the error
      if (!rawCode) {
        setError("Code block not found");
      }

      // Find the start and end lines in the raw code
      // Returns error if no start or end line provided or if not found within file
      if (start && end) {
        const startLine = rawCode.indexOf(start);
        const endLine = rawCode.indexOf(end);
        if (startLine === -1 || endLine === -1) {
          setError("Start and end lines not found in code block");
        } else {
          // Set the code to be rendered
          setCodeString(
            rawCode.slice(startLine + start.length, endLine).trim()
          );
        }
      } else if (rawCode) {
        setCodeString(rawCode);
      } else {
        setError("Start and end lines must be provided");
      }
    }

    loadCode();

    // Cleanup function to avoid setting state on unmounted component
    return () => {
      isActive = false;
    };
  }, []);

  if (loading) return "Loading";
  if (error) return "Error loading code block";

  return (
    <CodeBlock language={language} title={title || file} showLineNumbers>
      {codeString}
    </CodeBlock>
  );
};

export default LiteralInclude;
