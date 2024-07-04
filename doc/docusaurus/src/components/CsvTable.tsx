import useDocusaurusContext from "@docusaurus/useDocusaurusContext";
import { useEffect, useState } from "react";
const CsvTable = ({
  file,
  widths,
  minWidth,
}: {
  file: string;
  widths?: number[];
  minWidth?: number;
}) => {
  const { siteConfig } = useDocusaurusContext();

  const [loading, setLoading] = useState(true);
  const [error, setError] = useState("");
  const [tableData, setTableData] = useState<string[][]>([]);

  useEffect(() => {
    // Track if the component is still mounted
    let isActive = true;

    async function loadCode() {
      // Fetch the raw csv from the file
      const res = await fetch(`/docs/csv/${file}`);
      const rawData = await res.text();

      // If the component is unmounted, don't set the state
      if (!isActive) return;
      setLoading(false);

      // If the code block is not found, set the error
      if (!rawData) {
        setError("Code block not found");
      } else {
        const data = rawData
          .split("\n")
          .map((row) => row.split(","))
          .filter((row) => row.length > 1);
        setTableData(data);
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

  if (tableData.length === 0) return "No data found for table";

  return (
    <div className="csv-table-overflow-marker">
      <div className="csv-table-overflow">
        <table className="csv-table" style={{ minWidth: minWidth || "auto" }}>
          {widths ? (
            <colgroup>
              {widths.map((width, i) => (
                <col key={`col-${i}`} style={{ width: `${width}%` }} />
              ))}
            </colgroup>
          ) : null}
          <thead>
            <tr>
              {tableData[0].map((header, i) => (
                <th key={`th-${i}`}>{header}</th>
              ))}
            </tr>
          </thead>
          <tbody>
            {tableData.slice(1).map((row, i) => (
              <tr key={`row-${i}`}>
                {row.map((cell, j) => (
                  <td key={`row-${i}-cell-${j}`}>{cell}</td>
                ))}
              </tr>
            ))}
          </tbody>
        </table>
      </div>
    </div>
  );
};

export default CsvTable;
