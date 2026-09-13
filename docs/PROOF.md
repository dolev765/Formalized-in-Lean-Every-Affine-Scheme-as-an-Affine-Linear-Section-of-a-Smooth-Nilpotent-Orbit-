# NOP.png: proof-to-declaration guide

The public theorem is `Universality.affine_orbit_universality` in
[`Main.lean`](../Universality/Main.lean). Its result is
`Nonempty (AffineOrbitRealization k A)`, under exactly the field, commutative
algebra, and finite-presentation assumptions displayed in that declaration.
The result structure contains certificates; the theorem constructs every one.
It does not take the desired geometry as an assumption.

An affine scheme in the image is represented by `Spec A`. The coordinate
isomorphism is a `k`-algebra equivalence, and `schemeIso_from_coordinate` records
that the stored scheme isomorphism is precisely the induced `Spec` isomorphism.

## The final statement uses one witness

For `r : AffineOrbitRealization k A`, the following fields concern the same
`r.circuit`, wire and gate types, and size. `r.size` is the integer `N`;
`r.cell` is literally the spectrum of a polynomial algebra on `N^2` entries.

| Claim in the first paragraph of the image | Field or declaration |
| --- | --- |
| `N ≥ 1` | `positive_size`; `AffineOrbitRealization.size_pos`. |
| `L` is affine-linear and closed in the ambient matrix space | `affine_degree`, `affine_closed`; the equations are `circuit.orbitAffinePolynomials`. |
| `X ≅ L ∩ O`, scheme-theoretically | `coordinateIso`, `schemeIso`, `schemeIso_from_coordinate`, `orbit_intersection`. |
| `X ≅ L ∩ U`, scheme-theoretically | The same isomorphisms, together with `cell_intersection`. |
| The section and cell are closed in the orbit | `section_closed_in_orbit`, `cell_closed_in_orbit`. |
| The orbit is smooth of dimension `2N²` | `orbit_smooth_dimension`. |
| The cell is affine space of dimension `N²` | `AffineOrbitRealization.cell`, `cell_smooth_dimension`. |
| The orbit is symplectic and the cell is isotropic | `symplectic`, `cell_chart_factorization`, `cell_isotropic`. |
| The cell is Lagrangian | The closed immersion, isotropy, and two smooth dimension certificates above; also the direct self-orthogonality theorem below. |

`orbit_intersection` and `cell_intersection` have type `IsPullback` in `Scheme`.
They use the actual closed affine inclusion and the actual orbit/cell maps to
the ambient matrix scheme, rather than an equality of sets of rational points.

## 1. Encode equations by `B = A²`

The arithmetic compiler in [`Circuit.lean`](../Universality/Circuit.lean)
introduces wires for the expressions of a finite polynomial presentation.
`ExpressionPresentation.wire_forced` proves that every auxiliary wire is
determined by the original inputs. `ExpressionPresentation.solutionEquiv`
provides the inverse reconstruction over arbitrary commutative test algebras.

The matrix encoding is `GateSystem.assemble`: one diagonal block for wire
values and a `2 × 2` block for each multiplication gate. Its size is
`|Wire| + 2 * |Gate|`, as recorded by `GateSystem.card_index`.
`GateSystem.linearSection_square_iff` gives the exact equation-level
correspondence with `B = A*A`.

The stronger scheme-level statements are the quotient-algebra equivalences:

- `ExpressionPresentation.coordinateAlgEquiv` in
  [`Scheme.lean`](../Universality/Scheme.lean).
- `GateSystem.matrixCoordinateAlgEquiv` and
  `GateSystem.orbitCoordinateAlgEquiv` in
  [`Construction.lean`](../Universality/Construction.lean).
- `finitePresentation_orbitSection`, which supplies the exact algebra
  equivalence and a positive size for every finitely presented algebra.

Thus the construction retains the entire coordinate algebra, including its
nonreduced scheme structure.

## 2. Pass to the square-zero orbit and actual intersections

`Universality.iota` is the image's block map

```text
(A,B) ↦ [[A,I],[-B,-A]].
```

`iota_square_iff` proves that its square vanishes exactly when `B = A*A`.
`iota_square_entryIdeal` and `universal_iota_square_ideal` in
[`Scheme.lean`](../Universality/Scheme.lean) prove the corresponding equality
of equation ideals, without replacing them by radicals.
`GateSystem.orbitSectionIdeal_eq` and `orbitSectionIdeal_eq_squareZero` apply
this equality to the compiler's actual ambient coordinates.

The actual orbit scheme is `SquareZeroGeometry.maximalRankScheme`, the rank-`N`
open subscheme of the scheme defined by the entries of `Z*Z`.
`inJordanOrbit_iff_square_zero_rank` identifies its field-valued maximal-rank
matrices with the conjugacy orbit of the standard Jordan matrix.
`chart_orbit_iff` and `Symplectic.chartUnits_conjugate_jordan` prove the displayed
cell conjugation identity. `cellMorphism` is the actual scheme morphism induced
by that cell, and `cellMorphism_isClosedImmersion` proves closedness in the orbit.

The image's final fibre-product assertions are discharged by
`GateSystem.sectionToOrbit_isPullback` and
`GateSystem.sectionToCell_isPullback`. These are the declarations stored in the
two intersection fields of the public theorem.

## 3. Smoothness, symplectic form, and Lagrangian cell

The implementation uses an explicit chart proof for this part. When the upper
right block `T` is invertible, the square-zero matrix is uniquely

```text
[[T*A, T],[-A*T*A,-A*T]].
```

`SquareZeroGeometry.chartAlgEquiv` and `topRightChartIso` give actual coordinate
algebra and scheme isomorphisms with the localization of `k[A,T]` at `det T`.
`permutationOpen_cover` proves that the permuted versions cover the whole
maximal-rank scheme, by passing every scheme point to its residue field.
`maximalRankScheme_dimension` then proves smooth relative dimension `2N²`.
This establishes the smooth orbit required in NOP.png through charts, rather
than by constructing the quotient `GL/H` used in the image's proof.

The KKS pairing is `Symplectic.traceForm`; `traceForm_eq` proves its trace
identity. `omegaBilin` is the descended bilinear form on the commutator tangent
module, and `omegaBilin_alternating` and `omegaBilin_nondegenerate` prove its
basic properties. `tangent_eq_linearizedKernel` identifies that module with
the linearization of the square-zero equations.

On each actual chart, `AffineForms.canonicalTrace` is the regular form
`tr(dT ∧ dA)`. Closedness is proved using the six-term Cartan exterior derivative
on algebraic derivations, in `canonicalTrace_closed`.
`canonicalTrace_localized_equiv` constructs a linear equivalence from the
derivation module to its dual using a localized Kähler-differential basis.
Thus the local form is perfect over the coefficient ring, not merely
nondegenerate on field-valued points.

`GlobalSymplectic.orbitSymplecticAtlas` assembles these forms on the actual
scheme open cover. Its overlap rings are the actual double-principal
localizations. The methods `left_transition_is_restriction` and
`right_transition_is_restriction` identify the coordinate maps with the actual
scheme restrictions; `overlap_pullback_forms_compatible` proves equality of the
forms there. This is the standard compatible-affine-chart description of a
regular algebraic two-form. Its use avoids requiring a separately implemented
global differential-form sheaf API.

For the cell, `cellChartEval_T` sends `T` to the identity matrix.
`cell_pullback_form_zero` therefore proves vanishing of the regular form, and
`AlgebraicSymplecticAtlas.cellMorphism_factors_identity` ties that coordinate
pullback to the actual cell immersion. The field-valued tangent assertion is
also proved directly: `Symplectic.lowerSubspace_chart_selfOrthogonal` says that
the cell tangent equals its own symplectic orthogonal. Together with the smooth
dimension certificates, these prove the Lagrangian conclusion.

The chart construction proves the image's required conclusions. It does not
reproduce its auxiliary homogeneous-space quotient and Maurer–Cartan argument
as named constructions, and those alternative steps are not hypotheses of the
public theorem.
