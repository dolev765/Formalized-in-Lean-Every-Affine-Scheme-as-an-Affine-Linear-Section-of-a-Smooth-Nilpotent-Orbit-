# Verification

The [theorem and axiom audit](https://dolev765.github.io/Formalized-in-Lean-Every-Affine-Scheme-as-an-Affine-Linear-Section-of-a-Smooth-Nilpotent-Orbit-/)
presents the Lean statements and their permitted classical axioms.

To reproduce the check from the repository root:

```sh
lake exe cache get
lake build
lake env lean Universality/Audit.lean
```

The pinned Lean toolchain and Lake dependency manifest determine the versions.
[Audit.lean](../Universality/Audit.lean) rejects any transitive axiom outside
`propext`, `Classical.choice`, and `Quot.sound`. Both the build and audit must
finish successfully.

For interactive browser use, open the repository's **Code → Codespaces** menu.
The development container runs the same checks and provides the Lean editor.
Open [Main.lean](../Universality/Main.lean) to inspect the theorem and its
certificates. The check log is `.lake/browser-check.log`.

GitHub Actions runs the build and audit for the source commit shown in each
workflow run.
