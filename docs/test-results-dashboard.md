# Test results dashboard

The HTML dashboard summarizes Verilator (or other simulator) test runs under `results/logs/<sim>/`. It is produced by the same generator the Makefile uses for `make dashboard`.

## Generate data

From the repository root:

```bash
make dashboard
# or
make html
```

Output file: `results/logs/dashboard.html`.

## View in MkDocs

When you run `mkdocs build` or `mkdocs serve`, a **pre-build hook** copies `results/logs/dashboard.html` into the docs tree as `dashboard.html`. If that file does not exist yet, a short placeholder page is written instead so links do not break.

- **Embedded** (below): interactive dashboard when real data was present at build time.
- **Full page**: [Open dashboard.html](dashboard.html){ .md-button }

!!! note "GitHub Pages / CI"
    Published sites often build without `results/logs/`. You will see the placeholder until you generate a dashboard locally (or extend CI to run tests and `make dashboard` before `mkdocs build`).

---

<div class="md-typeset" markdown="0">
<iframe
  src="../dashboard.html"
  title="Level test dashboard"
  width="100%"
  height="920"
  style="border: 1px solid var(--md-default-fg-color--lighter); border-radius: 6px; background: var(--md-default-bg-color);"
></iframe>
</div>
