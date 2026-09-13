#!/usr/bin/env bash
set -euo pipefail

project_dir="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
cd -- "$project_dir"

mkdir -p .lake
exec > >(tee .lake/browser-check.log) 2>&1

printf 'Checking the complete repository using its pinned Lean and mathlib versions.\n'
lean --version
lake exe cache get
lake build
lake env lean Universality/Audit.lean
printf '\nSUCCESS: lake build and the theorem audit both completed.\n'
printf 'Full log: .lake/browser-check.log\n'
