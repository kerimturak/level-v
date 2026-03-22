"""MkDocs hooks: sync generated test dashboard into docs/ before build."""

from __future__ import annotations

import shutil
from pathlib import Path

_PLACEHOLDER = """<!DOCTYPE html>
<html lang="en">
<head>
  <meta charset="UTF-8"/>
  <meta name="viewport" content="width=device-width, initial-scale=1.0"/>
  <title>Level Test Dashboard — no data</title>
  <style>
    body { font-family: system-ui, sans-serif; max-width: 42rem; margin: 3rem auto; padding: 0 1rem;
           color: #1a1a2e; background: #f5f7fa; line-height: 1.5; }
    code { background: #e2e8f0; padding: 0.15em 0.4em; border-radius: 4px; }
    h1 { font-size: 1.35rem; }
  </style>
</head>
<body>
  <h1>Test dashboard not generated yet</h1>
  <p>Run <code>make dashboard</code> (or <code>make html</code>) from the repository root, then build the docs again.
     The dashboard reads <code>results/logs/&lt;sim&gt;/</code> and writes <code>results/logs/dashboard.html</code>.</p>
  <p>On CI without simulation logs, this placeholder is expected.</p>
</body>
</html>
"""


def on_pre_build(config):
    root = Path(config.config_file_path).resolve().parent
    docs_dir = Path(config.docs_dir).resolve()
    src = root / "results" / "logs" / "dashboard.html"
    dst = docs_dir / "dashboard.html"

    if src.is_file():
        shutil.copy2(src, dst)
    else:
        dst.write_text(_PLACEHOLDER, encoding="utf-8")
