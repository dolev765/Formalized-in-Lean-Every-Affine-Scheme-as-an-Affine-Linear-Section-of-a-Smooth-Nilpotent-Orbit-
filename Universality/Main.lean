import Universality.Construction

/-!
# Affine-linear realizations of finitely presented algebras

A finitely presented algebra over a commutative ring is the coordinate algebra
of an affine-linear section of a maximal-rank square-zero orbit.
-/

namespace Universality
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MvPolynomial
open SquareZeroGeometry
universe u

/-- An affine-linear section of a square-zero orbit with coordinate algebra `A`. -/
structure AffineOrbitRealization (k A : Type u) [CommRing k] [CommRing A] [Algebra k A] where
  Index : Type u
  Equation : Type u
  [indexFinite : Fintype Index]
  [indexDecidable : DecidableEq Index]
  [equationFinite : Fintype Equation]
  affineEquations : Equation → AmbientRing k Index
  sectionIdeal : Ideal (AmbientRing k Index)
  ideal_eq : sectionIdeal = equationIdeal affineEquations ⊔ squareZeroIdeal k Index
  card_index_pos : 0 < Fintype.card Index
  affineEquations_totalDegree : ∀ q, (affineEquations q).totalDegree ≤ 1
  coordinateEquiv : A ≃ₐ[k] (AmbientRing k Index ⧸ sectionIdeal)
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
  sectionToAffine_comp : sectionToAffine ≫
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (equationIdeal affineEquations))) =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk sectionIdeal))

attribute [instance] AffineOrbitRealization.indexFinite AffineOrbitRealization.indexDecidable
  AffineOrbitRealization.equationFinite

namespace AffineOrbitRealization
variable {k A : Type u} [CommRing k] [CommRing A] [Algebra k A]
variable (r : AffineOrbitRealization k A)

def ambient : Scheme := Spec (.of (AmbientRing k r.Index))
def sectionScheme : Scheme := Spec (.of (AmbientRing k r.Index ⧸ r.sectionIdeal))
def affineSection : Scheme := Spec (.of (AmbientRing k r.Index ⧸ equationIdeal r.affineEquations))

def affineInclusion : r.affineSection ⟶ r.ambient :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (equationIdeal r.affineEquations)))

/-- The scheme isomorphism is induced by the coordinate algebra isomorphism. -/
def schemeIso : Spec (.of A) ≅ r.sectionScheme :=
  Scheme.Spec.mapIso r.coordinateEquiv.symm.toRingEquiv.toCommRingCatIso.op

@[simp] theorem schemeIso_eq : r.schemeIso =
    Scheme.Spec.mapIso r.coordinateEquiv.symm.toRingEquiv.toCommRingCatIso.op := rfl

theorem affineInclusion_isClosedImmersion : IsClosedImmersion r.affineInclusion :=
  IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective

theorem sectionToOrbit_isClosedImmersion : IsClosedImmersion r.sectionToOrbit :=
  MorphismProperty.of_isPullback (P := @IsClosedImmersion)
    r.orbit_intersection r.affineInclusion_isClosedImmersion

theorem sectionToCell_isClosedImmersion : IsClosedImmersion r.sectionToCell :=
  MorphismProperty.of_isPullback (P := @IsClosedImmersion)
    r.cell_intersection r.affineInclusion_isClosedImmersion

end AffineOrbitRealization

/-- Every finitely presented algebra admits an exact affine-linear orbit realization. -/
theorem AffineOrbitRealization.nonempty (k A : Type u) [CommRing k] [CommRing A] [Algebra k A]
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
    card_index_pos := hpos
    affineEquations_totalDegree := C.orbitAffinePolynomials_totalDegree
    coordinateEquiv := e
    sectionToAffine := C.sectionToAffine
    sectionToOrbit := C.sectionToOrbit
    sectionToCell := C.sectionToCell
    orbit_intersection := C.sectionToOrbit_isPullback
    cell_intersection := C.sectionToCell_isPullback
    sectionToOrbit_eq := rfl
    sectionToAffine_comp := C.sectionToOrbit_isPullback.w.trans C.sectionToOrbit_ambient }⟩

end
end Universality
