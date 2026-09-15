# Every Affine Scheme as an Affine-Linear Section of a Smooth Nilpotent Orbit

For every commutative ring $k$ and finitely presented affine $k$-scheme $X$, there are
an integer $N \ge 1$, an affine-linear closed subscheme $L \subset M_{2N}$,
a smooth relative maximal-rank square-zero orbit $O_N$, and a closed affine Lagrangian
cell $U_N \cong \mathbb A_k^{N^2} \subset O_N$, such that

$$
X \cong L \times_{M_{2N}} U_N \cong L \times_{M_{2N}} O_N.
$$

[Main theorem](Universality/MainTheorem.lean)
· [Build in Lean](https://codespaces.new/dolev765/Formalized-in-Lean-Every-Affine-Scheme-as-an-Affine-Linear-Section-of-a-Smooth-Nilpotent-Orbit-?quickstart=1)
· [Latest Lean build (GitHub Actions)](https://github.com/dolev765/Formalized-in-Lean-Every-Affine-Scheme-as-an-Affine-Linear-Section-of-a-Smooth-Nilpotent-Orbit-/actions/runs/34961812447/job/104356914326#step:3:1)
· [Axiom audit](https://github.com/dolev765/Formalized-in-Lean-Every-Affine-Scheme-as-an-Affine-Linear-Section-of-a-Smooth-Nilpotent-Orbit-/actions/runs/34961812457/job/104356913847#step:4:1)

```sh
lake exe cache get
lake build
lake env lean Universality/MainTheorem.lean
```

Main results formalized from the [main paper](https://papers.ssrn.com/sol3/papers.cfm?abstract_id=7199240).

[Related paper](https://papers.ssrn.com/sol3/papers.cfm?abstract_id=7249658).
