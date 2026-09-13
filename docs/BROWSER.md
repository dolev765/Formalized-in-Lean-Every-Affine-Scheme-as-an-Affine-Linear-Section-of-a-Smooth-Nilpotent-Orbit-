# Online Lean proof checking

This repository provides a public compiler audit on GitHub Actions and an
interactive Lean editor through GitHub Codespaces. Both use the pinned Lean
toolchain and Mathlib revision committed with the proof.

## View the public compiler audit

Open **[Lean kernel build and axiom audit](https://github.com/dolev765/Formalized-in-Lean-Every-Affine-Scheme-as-an-Affine-Linear-Section-of-a-Smooth-Nilpotent-Orbit-/actions/workflows/lean.yml)**
and select the latest successful run for `main`. Its summary identifies the
exact checked commit, compiler versions, and all 18 declarations' axiom
dependencies. The complete axiom log is also attached to the run.

The check runs automatically after every push and pull request. Maintainers can
use **Run workflow → Run workflow** to request a fresh server-side check. This
uses the actual Lean compiler; viewing an editor or an AI's assessment is not
the verification procedure.

## Open the interactive Lean editor

1. Click **[Open proof in browser](https://codespaces.new/dolev765/Formalized-in-Lean-Every-Affine-Scheme-as-an-Affine-Linear-Section-of-a-Smooth-Nilpotent-Orbit-?quickstart=1)**.
2. Alternatively, on the repository page choose **Code → Codespaces → Create codespace**.
   Sign in and confirm creation when GitHub asks. The first setup downloads the
   toolchain and dependency cache, so it is not an instantaneous proof check.
3. Wait for the development-container setup to finish. Its post-create command
   runs `.devcontainer/check-project.sh`, which checks the cache, the complete
   build, and the axiom audit.
4. Open `Universality/Main.lean` in the browser editor. The main declaration is
   `Universality.affine_orbit_universality`. Use Lean's infoview to inspect its
   type and the fields of `AffineOrbitRealization`.

GitHub documents the repository creation links and quick-start behavior in
[Facilitating codespace creation](https://docs.github.com/en/codespaces/setting-up-your-project-for-codespaces/setting-up-your-repository/facilitating-quick-creation-and-resumption-of-codespaces).

## Check the result and rerun

The automatic script writes its output to `.lake/browser-check.log`. Success
requires all commands to finish with exit code zero and the final line:

```text
SUCCESS: lake build and the theorem audit both completed.
```

The axiom audit also prints its own `PASS` message. An error in a Lean proof,
an absent audit declaration, or an axiom outside the allowed standard basis
causes the command to fail. An editor displaying a file is not itself evidence
that the whole repository passed these checks.

To rerun everything in the browser terminal:

```sh
bash .devcontainer/check-project.sh
```

Or run the portable commands individually from the repository root:

```sh
lake exe cache get
lake build
lake env lean Universality/Audit.lean
```

The GitHub Actions result is a separate remote check. Use its commit identifier
to determine exactly which revision was checked.

The README contains working repository-specific audit and Codespaces links.
The Codespaces quick-start page lets the user create or resume a Codespace and
opens it in the web editor, as described in the GitHub documentation above.

## About single-file web editors

A link that merely loads `Main.lean` into a generic Lean web editor is
insufficient: this proof imports several local modules and pinned Mathlib
dependencies. Lean4Web's
[project documentation](https://github.com/leanprover-community/lean4web/blob/main/doc/Projects.md)
describes server-configured projects. Codespaces is the supplied workflow for
checking this complete repository directly after GitHub upload.
