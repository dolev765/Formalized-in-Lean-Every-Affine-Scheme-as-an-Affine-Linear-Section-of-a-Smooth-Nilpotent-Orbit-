"""Check trusted project sources against an immutable reference with upstream Comparator."""

import argparse
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]


def run(args, cwd, env=None, stdout=None):
    subprocess.run([str(arg) for arg in args], cwd=cwd, env=env, stdout=stdout, check=True)


def checkout(url, revision, destination):
    if not (destination / ".git").exists():
        run(["git", "clone", "--no-checkout", url, destination], ROOT)
        run(["git", "checkout", "--detach", revision], destination)
    actual = subprocess.check_output(
        ["git", "rev-parse", "HEAD"], cwd=destination, text=True
    ).strip()
    changes = subprocess.check_output(
        ["git", "status", "--porcelain", "--untracked-files=no"], cwd=destination, text=True
    ).strip()
    if actual != revision or changes:
        raise SystemExit(f"Expected a clean checkout at {revision}: {destination}")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--project", type=Path, default=ROOT)
    parser.add_argument("--work-dir", type=Path)
    args = parser.parse_args()
    project = args.project.resolve()
    work = (args.work_dir or project / ".lake" / "comparator").resolve()
    work.mkdir(parents=True, exist_ok=True)
    config_path = ROOT / "verification" / "comparator.json"
    config = json.loads(config_path.read_text())
    print(f"Reference commit: {config['reference_commit']}", flush=True)
    tools = work / "tools"
    reference = work / "reference"
    checkout("https://github.com/leanprover/comparator.git", config["comparator_commit"], tools)
    checkout(config["reference_repository"], config["reference_commit"], reference)

    toolchain = (project / "lean-toolchain").read_text().strip()
    for directory in (tools, reference):
        if (directory / "lean-toolchain").read_text().strip() != toolchain:
            raise SystemExit(f"Lean toolchain mismatch: {directory}")
    run(["lake", "build", "comparator", "lean4export"], tools)

    # Reference sources and dependencies come from the fixed commit, never the candidate.
    for directory, module in (
        (reference, config["challenge_module"]), (project, config["solution_module"])
    ):
        print(f"Building {module} in {directory}", flush=True)
        mathlib_cache = directory / ".lake/packages/mathlib/.lake/build/lib/lean/Mathlib.olean"
        if not mathlib_cache.exists():
            run(["lake", "exe", "cache", "get"], directory)
        run(["lake", "build", module], directory)

    env = os.environ.copy()
    env["LEAN_NUM_THREADS"] = "1"
    env["COMPARATOR_CONFIG"] = str(config_path)
    env["COMPARATOR_TARGETS"] = str(work / "targets.json")
    env["COMPARATOR_REFERENCE_EXPORT"] = str(work / "reference.ndjson")
    env["COMPARATOR_SOLUTION_EXPORT"] = str(work / "solution.ndjson")
    # Comparator's pinned CLI context uses `which git`, also available with Git for Windows.
    if os.name == "nt":
        git = Path(shutil.which("git") or "")
        unix_tools = git.parent.parent / "usr" / "bin"
        if unix_tools.is_dir():
            env["PATH"] = str(unix_tools) + os.pathsep + env["PATH"]
    tool_env = env.copy()
    tool_env.update(json.loads(subprocess.check_output(
        ["lake", "env", sys.executable, "-c",
         "import json,os; print(json.dumps({k:os.environ[k] for k in "
         "('LEAN_PATH','PATH','LD_LIBRARY_PATH','DYLD_LIBRARY_PATH') if k in os.environ}))"],
        cwd=tools, env=env, text=True,
    )))
    # Both upstream executables have a module named Main; select Comparator's Main.
    tool_env["LEAN_PATH"] = (
        str(tools / ".lake" / "build" / "lib" / "lean") + os.pathsep + tool_env["LEAN_PATH"]
    )
    driver = ["lean", "-j1", "-M16384", ROOT / "verification" / "Compare.lean"]
    tool_env["COMPARATOR_MODE"] = "targets"
    run(driver, tools, tool_env)
    targets = json.loads((work / "targets.json").read_text())
    exporter = tools / ".lake" / "packages" / "lean4export" / ".lake" / "build" / "bin" / (
        "lean4export.exe" if os.name == "nt" else "lean4export"
    )
    for directory, module, output in (
        (reference, config["challenge_module"], work / "reference.ndjson"),
        (project, config["solution_module"], work / "solution.ndjson"),
    ):
        print(f"Exporting {output.name}", flush=True)
        with output.open("wb") as stream:
            run(["lake", "env", exporter, module, "--", *targets], directory, env, stream)
    print("Comparing the specification and replaying the proof", flush=True)
    tool_env["COMPARATOR_MODE"] = "verify"
    run(driver, tools, tool_env)


if __name__ == "__main__":
    main()
