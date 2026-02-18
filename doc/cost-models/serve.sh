#!/usr/bin/env python3
"""Dev server for cost model docs with CORS disabled."""

import http.server
import os
import sys

PORT = int(sys.argv[1]) if len(sys.argv) > 1 else 8080

REPO_ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
DOC_ROOT = os.path.join(REPO_ROOT, "doc", "cost-models")
DATA_DIR = os.path.join(REPO_ROOT, "plutus-core", "cost-model", "data")


class Handler(http.server.SimpleHTTPRequestHandler):
    def translate_path(self, path):
        if path.startswith("/data/") or path == "/data":
            rel = path[len("/data"):]
            return os.path.join(DATA_DIR, rel.lstrip("/"))
        return super().translate_path(path)

    def end_headers(self):
        self.send_header("Access-Control-Allow-Origin", "*")
        self.send_header("Access-Control-Allow-Methods", "*")
        self.send_header("Access-Control-Allow-Headers", "*")
        super().end_headers()

    def do_OPTIONS(self):
        self.send_response(200)
        self.end_headers()


os.chdir(DOC_ROOT)
print(f"Serving docs from {DOC_ROOT}")
print(f"Serving data from {DATA_DIR} at /data")
print(f"http://localhost:{PORT}")
http.server.HTTPServer(("", PORT), Handler).serve_forever()
