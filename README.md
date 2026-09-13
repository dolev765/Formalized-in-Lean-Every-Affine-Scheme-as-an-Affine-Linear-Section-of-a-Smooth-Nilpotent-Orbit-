# Every Affine Scheme as an Affine-Linear Section of a Smooth Square-Zero Nilpotent Orbit

[![Lean kernel build and axiom audit](https://github.com/dolev765/Formalized-in-Lean-Every-Affine-Scheme-as-an-Affine-Linear-Section-of-a-Smooth-Nilpotent-Orbit-/actions/workflows/lean.yml/badge.svg?branch=main)](https://github.com/dolev765/Formalized-in-Lean-Every-Affine-Scheme-as-an-Affine-Linear-Section-of-a-Smooth-Nilpotent-Orbit-/actions/workflows/lean.yml)
[![Open proof in browser](https://github.com/codespaces/badge.svg)](https://codespaces.new/dolev765/Formalized-in-Lean-Every-Affine-Scheme-as-an-Affine-Linear-Section-of-a-Smooth-Nilpotent-Orbit-?quickstart=1)

**[View the Lean build and axiom audit](https://github.com/dolev765/Formalized-in-Lean-Every-Affine-Scheme-as-an-Affine-Linear-Section-of-a-Smooth-Nilpotent-Orbit-/actions/workflows/lean.yml)** · **[Open the proof in a browser Lean editor](https://codespaces.new/dolev765/Formalized-in-Lean-Every-Affine-Scheme-as-an-Affine-Linear-Section-of-a-Smooth-Nilpotent-Orbit-?quickstart=1)** · **[Read the main theorem](Universality/Main.lean)**

The audit link opens the public GitHub Actions result for this repository. A
green run means the pinned Lean compiler built the full proof and the axiom
audit passed for that commit. Each successful run includes a readable summary
and downloadable axiom-audit log. No local installation is needed to inspect
the result. Repository maintainers can request a fresh check with **Run workflow**.
The browser editor uses GitHub Codespaces and requires GitHub sign-in.

This Lean project proves the theorem in the supplied **NOP.png**: every finitely
presented affine scheme over a field is a scheme-theoretic affine-linear section
of a smooth maximal-rank square-zero orbit, contained in its closed affine
Lagrangian cell.

The entry point is
[`Universality.affine_orbit_universality`](Universality/Main.lean).
It returns a fully proved `AffineOrbitRealization k A` for every field `k` and
finitely presented commutative `k`-algebra `A`. The same witness supplies a positive
integer `N`, an affine-linear closed subscheme `L` of the space of `2N × 2N`
matrices, an orbit `O`, and a closed affine cell `U`, with

```text
Spec A ≅ L ×_(matrix space) U ≅ L ×_(matrix space) O.
```

The intersection certificates are actual `IsPullback` proofs in Mathlib's
category of schemes. The coordinate algebra is preserved exactly, including
nilpotents; no radical or extra affine factor is introduced. The witness also
contains smooth relative dimensions `2 * N^2` and `N^2`, orbit irreducibility,
the closed-immersion certificates, a compatible closed perfect symplectic atlas,
and the cell's zero pullback linked to its actual chart morphism.

[Proof-to-image traceability](docs/PROOF.md) maps the three parts of NOP.png to
the declarations. [Source identification](docs/SOURCE.md) records the original
image's location and SHA-256 digest.

## Check the project

Install [elan](https://github.com/leanprover/elan), clone this repository, and run
these commands from its root:

```sh
lake exe cache get
lake build
lake env lean Universality/Audit.lean
```

The project pins Lean **v4.30.0-rc2** and Mathlib commit
`5450b53e5ddc75d46418fabb605edbf36bd0beb6`. The committed Lake manifest pins the
dependency revisions. A fresh clone uses the Git dependency in `lakefile.toml`;
it does not need the original author's local Mathlib directory.

`lake build` checks the exported proof. The separate
[`Universality/Audit.lean`](Universality/Audit.lean) command checks transitive
axiom dependencies of the main theorem and selected supporting results. It
fails on any axiom outside `propext`, `Classical.choice`, and `Quot.sound`, so an
admitted proof in those dependencies fails the audit. Successful execution ends
with the audit's `PASS` message and exit code zero. Routine unused-argument or
unused-simp warnings do not constitute proof failures.

The final local direct build, theorem entry point, and all 18 declarations in
the axiom audit have passed. A standard `lake build` also passed in an isolated
temporary checkout (2,860 jobs), using the committed dependency pins and no
prebuilt project artifacts. Every audited declaration used only the three
standard axioms listed above. For the original Windows development environment,
`Check.ps1` can reuse an existing package cache. It is optional; the commands
above are the portable checking interface.

## Check in a browser after upload

The repository includes a GitHub Codespaces development container and a GitHub
Actions workflow. After uploading the repository, open **Code → Codespaces →
Create codespace**. The container installs the pinned toolchain and runs the
cache, build, and axiom-audit commands. Open `Universality/Main.lean` to inspect
the theorem in the Lean editor. Detailed steps and the expected success marker
are in [docs/BROWSER.md](docs/BROWSER.md).

GitHub Actions checks each push and pull request and also supports a manual
run. The badge above reports the current status; the run's commit identifies
the exact source checked. Codespaces provides a separate interactive editor
and automatically runs the same proof build and axiom audit on initial setup.

## Source organization

| File | Role |
| --- | --- |
| [`Universality.lean`](Universality.lean) | Public import of the theorem module. |
| [`Universality/Main.lean`](Universality/Main.lean) | The image's theorem, packaged with one common witness. |
| [`Universality/Construction.lean`](Universality/Construction.lean) | Circuit-to-matrix construction, exact coordinate quotients, and categorical intersection proofs. |
| [`Universality/MatrixOrbit.lean`](Universality/MatrixOrbit.lean) | Matrix identities, maximal-rank orbit classification, and tangent calculations. |
| [`Universality/Circuit.lean`](Universality/Circuit.lean) | Arithmetic circuits, unique reconstruction of auxiliary wires, and affine constraints. |
| [`Universality/Scheme.lean`](Universality/Scheme.lean) | Actual schemes, principal-open charts, smoothness, dimensions, irreducibility, and closed immersions. |
| [`Universality/Symplectic.lean`](Universality/Symplectic.lean) | KKS form, closed perfect local forms, compatibility on actual overlaps, and cell isotropy. |
| [`Universality/Audit.lean`](Universality/Audit.lean) | Executable axiom-dependency audit. |

The implementation proves orbit smoothness and the regular symplectic form by
explicit affine charts. This is an alternative to the homogeneous-space and
Maurer–Cartan route used in the image; it proves the same conclusions needed by
the theorem. The precise construction is explained in the proof guide.

Additional checked declarations include a finite-diagram extension and
coefficient/support-size bounds. They are separate results, rather than part of
the NOP.png theorem. This project makes no polynomial-time complexity-class
completeness claim. The ignored `trash/` directory contains development history
and abandoned prototypes; it is outside the supported proof/build target.
