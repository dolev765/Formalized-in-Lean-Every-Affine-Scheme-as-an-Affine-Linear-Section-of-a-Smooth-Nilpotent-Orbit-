import Universality.Construction

/-!
# Exact affine-linear universality in the square-zero orbit

`affine_orbit_universality` is the main theorem. Its witness uses one circuit,
one positive matrix size, and one
section scheme throughout. The two intersection fields are categorical
pullback certificates in `Scheme`, including nonreduced scheme structure.

The symplectic certificate consists of regular alternating, closed, perfect
forms on an actual open atlas, with compatibility on actual intersections.
The cell's zero pullback is linked to that atlas by its displayed factorization.
-/

namespace Universality

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MvPolynomial

universe u

/-- A complete realization of `Spec A` as an affine-linear orbit section.
All certificates concern the same compiler witness and therefore the same
ambient matrix space, orbit, cell, and affine-linear closed subscheme. -/
structure AffineOrbitRealization (k A : Type u) [CommRing k] [CommRing A] [Algebra k A] where
  Wire : Type u
  Gate : Type u
  Equation : Type u
  [wireFinite : Fintype Wire]
  [gateFinite : Fintype Gate]
  [equationFinite : Fintype Equation]
  [wireDecidable : DecidableEq Wire]
  [gateDecidable : DecidableEq Gate]
  circuit : GateSystem k Wire Gate Equation
  positive_size : 0 < Fintype.card (GateSystem.Index Wire Gate)
  coordinateIso : A ≃ₐ[k]
    (MvPolynomial (GateSystem.OrbitCoord Wire Gate) k ⧸ equationIdeal circuit.orbitPolynomials)
  schemeIso : Spec (.of A) ≅ Spec (.of
    (MvPolynomial (GateSystem.OrbitCoord Wire Gate) k ⧸ equationIdeal circuit.orbitPolynomials))
  schemeIso_from_coordinate :
    schemeIso = Scheme.Spec.mapIso coordinateIso.symm.toRingEquiv.toCommRingCatIso.op
  affine_degree : ∀ q, (circuit.orbitAffinePolynomials q).totalDegree ≤ 1
  affine_closed : IsClosedImmersion circuit.affineInclusion
  orbit_intersection : IsPullback circuit.sectionToAffine circuit.sectionToOrbit
    circuit.affineInclusion
    ((SquareZeroGeometry.maximalRankOpen k (GateSystem.Index Wire Gate)).ι ≫
      SquareZeroGeometry.squareZeroClosedImmersion k (GateSystem.Index Wire Gate))
  cell_intersection : IsPullback circuit.sectionToAffine circuit.sectionToCell
    circuit.affineInclusion
    (SquareZeroGeometry.cellMorphism k (GateSystem.Index Wire Gate) ≫
      (SquareZeroGeometry.maximalRankOpen k (GateSystem.Index Wire Gate)).ι ≫
        SquareZeroGeometry.squareZeroClosedImmersion k (GateSystem.Index Wire Gate))
  section_closed_in_orbit : IsClosedImmersion circuit.sectionToOrbit
  section_closed_in_cell : IsClosedImmersion circuit.sectionToCell
  cell_closed_in_orbit :
    IsClosedImmersion (SquareZeroGeometry.cellMorphism k (GateSystem.Index Wire Gate))
  orbit_smooth_dimension : SmoothOfRelativeDimension
    (2 * Fintype.card (GateSystem.Index Wire Gate) ^ 2)
    (SquareZeroGeometry.maximalRankStructureMap k (GateSystem.Index Wire Gate))
  orbit_irreducible : IsField k →
    IrreducibleSpace (SquareZeroGeometry.maximalRankScheme k (GateSystem.Index Wire Gate))
  cell_smooth_dimension : SmoothOfRelativeDimension
    (Fintype.card (GateSystem.Index Wire Gate) ^ 2)
    (Spec.map (CommRingCat.ofHom
      (algebraMap k (MvPolynomial (GateSystem.Index Wire Gate × GateSystem.Index Wire Gate) k))))
  symplectic : GlobalSymplectic.AlgebraicSymplecticAtlas k (GateSystem.Index Wire Gate)
  cell_chart_factorization : SquareZeroGeometry.cellMorphism k (GateSystem.Index Wire Gate) =
    Spec.map (CommRingCat.ofHom
      (SquareZeroGeometry.cellChartEval k (GateSystem.Index Wire Gate)).toRingHom) ≫
      (symplectic.orbitChartIso (Equiv.refl _)).inv ≫
        (SquareZeroGeometry.orbitChartOpen k (GateSystem.Index Wire Gate) (Equiv.refl _)).ι
  cell_isotropic : AffineForms.canonicalTrace (R := k)
    ((SquareZeroGeometry.chartT k (GateSystem.Index Wire Gate)).map
      (SquareZeroGeometry.cellChartEval k (GateSystem.Index Wire Gate)))
    ((SquareZeroGeometry.chartA k (GateSystem.Index Wire Gate)).map
      (SquareZeroGeometry.cellChartEval k (GateSystem.Index Wire Gate))) = 0

attribute [instance] AffineOrbitRealization.wireFinite AffineOrbitRealization.gateFinite
  AffineOrbitRealization.equationFinite AffineOrbitRealization.wireDecidable
  AffineOrbitRealization.gateDecidable

/-- Every finitely presented affine `k`-scheme has an exact affine-linear realization:
one positive-size smooth square-zero orbit, its closed affine Lagrangian cell,
and an affine-linear closed subscheme whose two intersections are `Spec A`. -/
theorem affine_orbit_universality (k A : Type u) [CommRing k] [CommRing A] [Algebra k A]
    [Algebra.FinitePresentation k A] : Nonempty (AffineOrbitRealization k A) := by
  obtain ⟨W, G, E, hW, hG, hE, dW, dG, C, hpos, ⟨e⟩⟩ :=
    finitePresentation_orbitSection k A
  exact ⟨{
    Wire := W
    Gate := G
    Equation := E
    wireFinite := hW
    gateFinite := hG
    equationFinite := hE
    wireDecidable := dW
    gateDecidable := dG
    circuit := C
    positive_size := hpos
    coordinateIso := e
    schemeIso := Scheme.Spec.mapIso e.symm.toRingEquiv.toCommRingCatIso.op
    schemeIso_from_coordinate := rfl
    affine_degree := by
      cases subsingleton_or_nontrivial k with
      | inl h =>
        letI := h
        intro q
        rw [show C.orbitAffinePolynomials q = 0 from Subsingleton.elim _ _]
        simp
      | inr h =>
        letI := h
        exact C.orbitAffinePolynomials_totalDegree
    affine_closed := IsClosedImmersion.spec_of_surjective
      (CommRingCat.ofHom (Ideal.Quotient.mk (equationIdeal C.orbitAffinePolynomials)))
      Ideal.Quotient.mk_surjective
    orbit_intersection := C.sectionToOrbit_isPullback
    cell_intersection := C.sectionToCell_isPullback
    section_closed_in_orbit := C.sectionToOrbit_isClosedImmersion
    section_closed_in_cell := C.sectionToCell_isClosedImmersion
    cell_closed_in_orbit := SquareZeroGeometry.cellMorphism_isClosedImmersion k _
    orbit_smooth_dimension := SquareZeroGeometry.maximalRankScheme_dimension k _
    orbit_irreducible := fun h => by
      letI := h.toField
      exact SquareZeroGeometry.maximalRankScheme_irreducible _
    cell_smooth_dimension := SquareZeroGeometry.cellSource_dimension k _
    symplectic := GlobalSymplectic.orbitSymplecticAtlas k _
    cell_chart_factorization :=
      (GlobalSymplectic.orbitSymplecticAtlas k _).cellMorphism_factors_identity
    cell_isotropic := GlobalSymplectic.cell_pullback_form_zero k _ }⟩

namespace AffineOrbitRealization

variable {k A : Type u} [CommRing k] [CommRing A] [Algebra k A]

/-- The integer `N` appearing in the statement. -/
def size (r : AffineOrbitRealization k A) : ℕ :=
  Fintype.card (GateSystem.Index r.Wire r.Gate)

theorem size_pos (r : AffineOrbitRealization k A) : 0 < r.size := r.positive_size

/-- The closed affine cell is literally affine space on `N²` matrix coordinates. -/
def cell (r : AffineOrbitRealization k A) : Scheme :=
  Spec (.of (MvPolynomial
    (GateSystem.Index r.Wire r.Gate × GateSystem.Index r.Wire r.Gate) k))

def orbit (r : AffineOrbitRealization k A) : Scheme :=
  SquareZeroGeometry.maximalRankScheme k (GateSystem.Index r.Wire r.Gate)

def affineSection (r : AffineOrbitRealization k A) : Scheme :=
  Spec (.of (MvPolynomial (GateSystem.OrbitCoord r.Wire r.Gate) k ⧸
    equationIdeal r.circuit.orbitAffinePolynomials))

end AffineOrbitRealization

end
end Universality
