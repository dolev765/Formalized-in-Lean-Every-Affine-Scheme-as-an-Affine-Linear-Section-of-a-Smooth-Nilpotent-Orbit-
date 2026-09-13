# Proof guide

The entry point is `Universality.affine_orbit_universality` in
[Main.lean](../Universality/Main.lean). It constructs
`AffineOrbitRealization k A` for every finitely presented commutative algebra
over a field. All certificates refer to the same circuit, matrix size, and
section scheme.

| Conclusion | Certificate |
| --- | --- |
| Positive matrix size | `positive_size` |
| Exact coordinate algebra and induced scheme isomorphism | `coordinateIso`, `schemeIso`, `schemeIso_from_coordinate` |
| Affine-linear closed subscheme | `affine_degree`, `affine_closed` |
| Scheme-theoretic intersections with the orbit and cell | `orbit_intersection`, `cell_intersection` |
| Closed cell in the orbit | `cell_closed_in_orbit` |
| Smooth orbit of dimension `2 * N^2` | `orbit_smooth_dimension` |
| Irreducible orbit | `orbit_irreducible` |
| Affine cell of dimension `N^2` | `AffineOrbitRealization.cell`, `cell_smooth_dimension` |
| Compatible closed perfect symplectic form | `symplectic` |
| Vanishing pullback along the actual cell immersion | `cell_chart_factorization`, `cell_isotropic` |

The two intersection fields are `IsPullback` certificates in Mathlib's category
of schemes, preserving nonreduced structure.

The construction has three stages:

1. [Circuit.lean](../Universality/Circuit.lean) encodes polynomial equations
   using uniquely determined auxiliary wires. The quotient-algebra
   equivalences in [Construction.lean](../Universality/Construction.lean)
   identify the resulting matrix section with the original algebra.
2. The block map `(A,B) ↦ [[A,I],[-B,-A]]` turns `B = A*A` into the
   square-zero equations. Equality of equation ideals and categorical pullback
   proofs establish the exact intersections.
3. [Scheme.lean](../Universality/Scheme.lean) covers the maximal-rank orbit by
   explicit affine charts. [Symplectic.lean](../Universality/Symplectic.lean)
   constructs the KKS form as compatible closed perfect forms on these charts
   and proves cell isotropy. Smoothness and the half-dimension calculation
   complete the Lagrangian conclusion.

The affine-chart argument proves the required geometry directly; it is an
alternative to a homogeneous-space quotient proof.
