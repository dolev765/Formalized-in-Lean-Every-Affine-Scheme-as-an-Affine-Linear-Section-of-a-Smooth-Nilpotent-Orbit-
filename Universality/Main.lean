import Universality.Construction

/-!
# Affine-linear realizations of finitely presented algebras

`AffineOrbitRealization` records equations and scheme maps independently of their construction.
`affine_orbit_universality` constructs a realization over every commutative base ring.
-/

namespace Universality
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MvPolynomial
open SquareZeroGeometry
universe u

/-- An intrinsic affine-linear realization of an algebra in a square-zero orbit. -/
structure AffineOrbitRealization (k A : Type u) [CommRing k] [CommRing A] [Algebra k A] where
  Index : Type u
  Equation : Type u
  [indexFinite : Fintype Index]
  [indexDecidable : DecidableEq Index]
  [equationFinite : Fintype Equation]
  affineEquations : Equation → AmbientRing k Index
  sectionIdeal : Ideal (AmbientRing k Index)
  ideal_eq : sectionIdeal = equationIdeal affineEquations ⊔ squareZeroIdeal k Index
  positive_size : 0 < Fintype.card Index
  affine_degree : ∀ q, (affineEquations q).totalDegree ≤ 1
  coordinateIso : A ≃ₐ[k] (AmbientRing k Index ⧸ sectionIdeal)
  sectionToAffine : Spec (.of (AmbientRing k Index ⧸ sectionIdeal)) ⟶
    Spec (.of (AmbientRing k Index ⧸ equationIdeal affineEquations))
  sectionToOrbit : Spec (.of (AmbientRing k Index ⧸ sectionIdeal)) ⟶ maximalRankScheme k Index
  sectionToCell : Spec (.of (AmbientRing k Index ⧸ sectionIdeal)) ⟶
    Spec (.of (MvPolynomial (Index × Index) k))
  orbit_intersection : IsPullback sectionToAffine sectionToOrbit
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (equationIdeal affineEquations))))
    ((maximalRankOpen k Index).ι ≫ squareZeroClosedImmersion k Index)
  cell_intersection : IsPullback sectionToAffine sectionToCell
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (equationIdeal affineEquations))))
    (cellMorphism k Index ≫ (maximalRankOpen k Index).ι ≫ squareZeroClosedImmersion k Index)
  sectionToOrbit_eq : sectionToOrbit = sectionToCell ≫ cellMorphism k Index
  sectionToAmbient : sectionToAffine ≫
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (equationIdeal affineEquations))) =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk sectionIdeal))

attribute [instance] AffineOrbitRealization.indexFinite AffineOrbitRealization.indexDecidable
  AffineOrbitRealization.equationFinite

namespace AffineOrbitRealization
variable {k A : Type u} [CommRing k] [CommRing A] [Algebra k A]
variable (r : AffineOrbitRealization k A)

def size : ℕ := Fintype.card r.Index
theorem size_pos : 0 < r.size := r.positive_size

def ambient : Scheme := Spec (.of (AmbientRing k r.Index))
def sectionScheme : Scheme := Spec (.of (AmbientRing k r.Index ⧸ r.sectionIdeal))
def affineSection : Scheme := Spec (.of (AmbientRing k r.Index ⧸ equationIdeal r.affineEquations))
def orbit : Scheme := maximalRankScheme k r.Index
def cell : Scheme := Spec (.of (MvPolynomial (r.Index × r.Index) k))

def affineInclusion : r.affineSection ⟶ r.ambient :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (equationIdeal r.affineEquations)))

/-- The scheme isomorphism is induced by the coordinate algebra isomorphism. -/
def schemeIso : Spec (.of A) ≅ r.sectionScheme :=
  Scheme.Spec.mapIso r.coordinateIso.symm.toRingEquiv.toCommRingCatIso.op

@[simp] theorem schemeIso_from_coordinate : r.schemeIso =
    Scheme.Spec.mapIso r.coordinateIso.symm.toRingEquiv.toCommRingCatIso.op := rfl

theorem affine_closed : IsClosedImmersion r.affineInclusion :=
  IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective

theorem section_closed_in_orbit : IsClosedImmersion r.sectionToOrbit :=
  MorphismProperty.of_isPullback (P := @IsClosedImmersion) r.orbit_intersection r.affine_closed

theorem section_closed_in_cell : IsClosedImmersion r.sectionToCell :=
  MorphismProperty.of_isPullback (P := @IsClosedImmersion) r.cell_intersection r.affine_closed

theorem cell_closed_in_orbit : IsClosedImmersion (cellMorphism k r.Index) :=
  cellMorphism_isClosedImmersion k r.Index

theorem orbit_smooth_dimension : SmoothOfRelativeDimension (2 * Fintype.card r.Index ^ 2)
    (maximalRankStructureMap k r.Index) := maximalRankScheme_dimension k r.Index

theorem orbit_irreducible (h : IsField k) : IrreducibleSpace r.orbit := by
  letI := h.toField
  exact maximalRankScheme_irreducible r.Index

theorem cell_smooth_dimension : SmoothOfRelativeDimension (Fintype.card r.Index ^ 2)
    (Spec.map (CommRingCat.ofHom (algebraMap k (MvPolynomial (r.Index × r.Index) k)))) :=
  cellSource_dimension k r.Index

def symplectic : GlobalSymplectic.AlgebraicSymplecticAtlas k r.Index :=
  GlobalSymplectic.orbitSymplecticAtlas k r.Index

theorem cell_chart_factorization : cellMorphism k r.Index =
    Spec.map (CommRingCat.ofHom (cellChartEval k r.Index).toRingHom) ≫
      (r.symplectic.orbitChartIso (Equiv.refl _)).inv ≫
        (orbitChartOpen k r.Index (Equiv.refl _)).ι :=
  r.symplectic.cellMorphism_factors_identity

theorem cell_isotropic : AffineForms.canonicalTrace (R := k)
    ((chartT k r.Index).map (cellChartEval k r.Index))
    ((chartA k r.Index).map (cellChartEval k r.Index)) = 0 :=
  GlobalSymplectic.cell_pullback_form_zero k r.Index

end AffineOrbitRealization

/-- Every finitely presented algebra admits an exact affine-linear orbit realization. -/
theorem affine_orbit_universality (k A : Type u) [CommRing k] [CommRing A] [Algebra k A]
    [Algebra.FinitePresentation k A] : Nonempty (AffineOrbitRealization k A) := by
  obtain ⟨W, G, E, hW, hG, hE, dW, dG, C, hpos, ⟨e⟩⟩ := finitePresentation_orbitSection k A
  exact ⟨{
    Index := GateSystem.Index W G
    Equation := GateSystem.OrbitAffineEquation W G E
    affineEquations := C.orbitAffinePolynomials
    sectionIdeal := equationIdeal C.orbitPolynomials
    ideal_eq := by
      simpa only [squareZeroIdeal, genericMatrix, GateSystem.orbitMatrix] using
        C.orbitSectionIdeal_eq
    positive_size := hpos
    affine_degree := C.orbitAffinePolynomials_totalDegree
    coordinateIso := e
    sectionToAffine := C.sectionToAffine
    sectionToOrbit := C.sectionToOrbit
    sectionToCell := C.sectionToCell
    orbit_intersection := C.sectionToOrbit_isPullback
    cell_intersection := C.sectionToCell_isPullback
    sectionToOrbit_eq := rfl
    sectionToAmbient := C.sectionToOrbit_isPullback.w.trans C.sectionToOrbit_ambient }⟩

end
end Universality
