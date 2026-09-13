"""Publish the main theorem's native Lean axiom output."""

from html import escape
from pathlib import Path
from urllib.request import Request, urlopen
import json
import os
import re

root = Path(__file__).resolve().parents[1]
statements = (root / "verified-statements.txt").read_text(encoding="utf-8")
native_output = re.search(
    r"'Universality\.affine_orbit_universality_explicit' depends on axioms:\s*\[[^\]]*\]",
    statements,
)
if native_output is None:
    raise SystemExit("Lean's native axiom output is missing.")
axioms = native_output.group(0)
repository = os.environ["GITHUB_REPOSITORY"]
source = f"https://github.com/{repository}/blob/{os.environ['GITHUB_SHA']}/Universality/MainTheorem.lean"
editor = f"https://codespaces.new/{repository}?quickstart=1"
api = os.environ.get("GITHUB_API_URL", "https://api.github.com")
run_id = os.environ["GITHUB_RUN_ID"]
attempt = os.environ["GITHUB_RUN_ATTEMPT"]
headers = {"Accept": "application/vnd.github+json"}
if token := os.environ.get("GITHUB_TOKEN"):
    headers["Authorization"] = f"Bearer {token}"
request = Request(
    f"{api}/repos/{repository}/actions/runs/{run_id}/attempts/{attempt}/jobs?per_page=100",
    headers=headers,
)
with urlopen(request, timeout=30) as response:
    jobs = json.load(response)["jobs"]
job = next(job for job in jobs if job["name"] == "Build and verify")
steps = {step["name"]: step for step in job["steps"]}
checks = {
    "build": ("Latest verified build", "Build the pinned Lean project"),
    "axioms": ("Axiom audit", "Check the main theorem and audit its axioms"),
}
links = {}
for route, (_, step_name) in checks.items():
    step = steps[step_name]
    if step["conclusion"] != "success":
        raise SystemExit(f"Verification step did not pass: {step_name}")
    links[route] = f"{job['html_url']}#step:{step['number']}:1"
title = "Every finitely presented affine scheme over a commutative ring is an affine-linear section of a smooth relative square-zero nilpotent orbit and its closed affine Lagrangian cell."
output = root / "_site"
output.mkdir(exist_ok=True)
(output / "index.html").write_text(f'''<!doctype html>
<html lang="en"><head><meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>{escape(title)}</title>
<style>
body{{max-width:960px;margin:48px auto;padding:0 24px;color:#172333;font:16px/1.6 system-ui,sans-serif}}
h1{{font-size:26px;font-weight:600;line-height:1.4}}h2{{font-size:18px;margin-top:32px}}
nav{{display:flex;flex-wrap:wrap;gap:24px}}a{{color:#174c83;text-underline-offset:3px}}
pre{{font:14px/1.7 ui-monospace,Consolas,monospace;white-space:pre-wrap;overflow-wrap:anywhere}}
</style></head><body>
<h1>{escape(title)}</h1>
<nav><a href="{escape(editor)}">Build in Lean</a><a href="{escape(links['build'])}">Latest verified build</a><a href="{escape(links['axioms'])}">Axioms</a><a href="{escape(source)}">Source</a></nav>
<h2>Axioms</h2><pre>{escape(axioms)}</pre>
</body></html>''', encoding="utf-8")
(output / ".nojekyll").touch()

for route, (label, _) in checks.items():
    destination = output / route
    destination.mkdir(exist_ok=True)
    (destination / "index.html").write_text(f'''<!doctype html>
<html lang="en"><head><meta charset="utf-8">
<title>{escape(label)}</title>
<meta http-equiv="refresh" content="0;url={escape(links[route])}">
</head><body><a href="{escape(links[route])}">{escape(label)}</a></body></html>
''', encoding="utf-8")
