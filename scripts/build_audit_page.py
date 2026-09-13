"""Publish Lean's checked statement and axiom output as a static audit report."""

from html import escape
from pathlib import Path
import json
import os
import re

root = Path(__file__).resolve().parents[1]
statements = (root / "verified-statements.txt").read_text(encoding="utf-8")
axioms = (root / "lean-axiom-audit.log").read_text(encoding="utf-8")
version = (root / "lean-version.txt").read_text(encoding="utf-8").strip()
if "PASS: all 18 audited declarations" not in axioms:
    raise SystemExit("The required Lean axiom audit did not pass.")
if "Universality.affine_orbit_universality" not in statements:
    raise SystemExit("Lean's main theorem statement is missing.")

repository = os.environ["GITHUB_REPOSITORY"]
commit = os.environ["GITHUB_SHA"]
run = os.environ["GITHUB_RUN_ID"]
if not re.fullmatch(r"[0-9a-f]{40}", commit):
    raise SystemExit("A complete checked commit identifier is required.")
repo_url = f"https://github.com/{repository}"
run_url = f"{repo_url}/actions/runs/{run}"
source_url = f"{repo_url}/blob/{commit}"
editor_url = f"https://codespaces.new/{repository}?quickstart=1"
first_statement = statements.split("\nstructure ", 1)[0].strip()
output = root / "_site"
output.mkdir(exist_ok=True)
(output / "statements.txt").write_text(statements, encoding="utf-8")
(output / "axioms.txt").write_text(axioms, encoding="utf-8")
(output / "verification.json").write_text(json.dumps({
    "repository": repository, "commit": commit, "run_url": run_url,
    "lean_version": version,
    "mathlib_commit": "5450b53e5ddc75d46418fabb605edbf36bd0beb6",
    "axiom_audit": "passed", "audited_declarations": 18,
    "allowed_axioms": ["propext", "Classical.choice", "Quot.sound"],
}, indent=2) + "\n", encoding="utf-8")

page = f'''<!doctype html>
<html lang="en"><head><meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<meta name="description" content="Verified Lean statements and axiom dependencies for affine scheme universality.">
<title>Affine Scheme Universality — Lean Verification</title>
<style>
:root{{color-scheme:light;--ink:#172333;--muted:#566477;--line:#dbe2ea;--blue:#174c83;--green:#17643a}}
*{{box-sizing:border-box}}body{{margin:0;background:#fff;color:var(--ink);font:16px/1.65 system-ui,-apple-system,BlinkMacSystemFont,"Segoe UI",sans-serif}}
main{{max-width:1060px;margin:0 auto;padding:48px 28px 64px}}a{{color:var(--blue);text-underline-offset:3px}}a:hover{{color:#092d54}}
.eyebrow{{font-size:12px;font-weight:700;letter-spacing:.12em;text-transform:uppercase;color:var(--muted)}}h1{{font:normal clamp(32px,5vw,48px)/1.15 Georgia,serif;margin:13px 0 20px;max-width:850px}}
.intro{{font-size:18px;max-width:860px}}nav{{display:flex;flex-wrap:wrap;gap:12px 24px;margin:26px 0 34px;font-size:14px}}
.verification{{border:1px solid var(--line);border-left:4px solid var(--green);padding:17px 22px;background:#f8fbf9;margin:0 0 36px}}
.verification strong{{color:var(--green)}}.meta{{font-size:13px;color:var(--muted);margin:4px 0 0;overflow-wrap:anywhere}}
h2{{font-size:22px;letter-spacing:-.02em;margin:36px 0 10px}}p{{margin:10px 0}}code,pre{{font-family:ui-monospace,SFMono-Regular,Consolas,"Liberation Mono",monospace}}
code{{font-size:.9em}}pre{{font-size:13px;line-height:1.65;background:#f5f7fa;border:1px solid var(--line);border-radius:5px;padding:20px;overflow:auto;tab-size:2}}
details{{border-top:1px solid var(--line);margin-top:24px;padding-top:17px}}summary{{cursor:pointer;font-weight:600;padding:4px 0}}details pre{{max-height:720px}}
.links{{font-size:14px}}footer{{margin-top:42px;padding-top:18px;border-top:1px solid var(--line);font-size:12px;color:var(--muted)}}
@media(max-width:600px){{main{{padding:30px 18px}}pre{{padding:14px;font-size:11px}}nav{{gap:10px 18px}}}}
</style></head><body><main>
<header><div class="eyebrow">Lean verification</div><h1>Affine Scheme Universality</h1>
<p class="intro">Every finitely presented affine scheme over a field is an affine-linear section of a smooth square-zero nilpotent orbit and its closed affine Lagrangian cell.</p>
<nav aria-label="Audit navigation"><a href="#statements">Verified statements</a><a href="#axioms">Axiom dependencies</a><a href="{escape(source_url)}/Universality/Main.lean">Lean source</a><a href="{escape(editor_url)}">Open in Lean</a></nav></header>
<section class="verification" aria-label="Verification result"><strong>Build and axiom audit passed</strong>
<p class="meta">Checked commit <a href="{escape(repo_url)}/commit/{commit}">{commit[:12]}</a> · <a href="{escape(run_url)}">GitHub verification run</a></p></section>
<section id="statements"><h2>Verified theorem</h2>
<p>This is Lean's printed type of the main theorem. The realization certificate specifies the exact scheme isomorphism, both fiber products, smoothness, dimensions, closed immersions, and symplectic structure.</p>
<pre>{escape(first_statement)}</pre>
<p class="links"><a href="statements.txt">Complete Lean statement output</a> · <a href="{escape(source_url)}/Universality/Statements.lean">Statement inspection commands</a></p>
<details><summary>Complete realization certificate and geometric statements</summary><pre>{escape(statements)}</pre></details></section>
<section id="axioms"><h2>Axiom dependencies</h2>
<p>Lean reports only <code>propext</code>, <code>Classical.choice</code>, and <code>Quot.sound</code>. No additional axioms occur in the 18 audited declarations.</p>
<pre>{escape(axioms)}</pre>
<p class="links"><a href="axioms.txt">Download Lean's axiom output</a> · <a href="{escape(source_url)}/Universality/Audit.lean">Audit source</a></p></section>
<footer><p>{escape(version)}<br>Mathlib <code>5450b53e5ddc75d46418fabb605edbf36bd0beb6</code></p>
<p>This report is generated from successful compiler output for the identified commit. <a href="verification.json">Verification metadata</a> · <a href="{escape(repo_url)}">Repository</a></p></footer>
</main></body></html>'''
(output / "index.html").write_text(page, encoding="utf-8")
(output / ".nojekyll").touch()
print(f"Generated audit report for {commit}.")
