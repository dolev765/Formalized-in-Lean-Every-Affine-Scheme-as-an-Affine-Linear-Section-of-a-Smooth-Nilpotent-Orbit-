import Universality.Circuit
import Universality.MatrixOrbit
import Universality.Scheme
import Universality.Symplectic
import Mathlib.LinearAlgebra.AffineSpace.AffineMap
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring
import Mathlib.RingTheory.FinitePresentation
import Mathlib.Algebra.MvPolynomial.CommRing

/-! Exact reconstruction inside the nilpotent orbit, over every test algebra. -/

namespace Universality

section Chart
variable {S n : Type*} [CommRing S] [Fintype n] [DecidableEq n]

/-- Equations defining the fixed affine chart inside the ambient matrix space. -/
def InFixedChart (Z : Matrix (n ⊕ n) (n ⊕ n) S) : Prop :=
  Z.toBlocks₁₂ = 1 ∧ Z.toBlocks₂₂ = -Z.toBlocks₁₁

theorem iota_inFixedChart (A B : Matrix n n S) : InFixedChart (iota A B) := by
  simp [InFixedChart, iota]

theorem fixedChart_reconstruct (Z : Matrix (n ⊕ n) (n ⊕ n) S)
    (h : InFixedChart Z) : iota Z.toBlocks₁₁ (-Z.toBlocks₂₁) = Z := by
  unfold iota
  rw [neg_neg, ← h.1, ← h.2]
  exact Matrix.fromBlocks_toBlocks Z

def chartResidualLinear : Matrix (n ⊕ n) (n ⊕ n) S →ₗ[S]
    (Matrix n n S × Matrix n n S) where
  toFun Z := (Z.toBlocks₁₂, Z.toBlocks₂₂ + Z.toBlocks₁₁)
  map_add' X Y := by
    apply Prod.ext
    · rfl
    · change (X.toBlocks₂₂ + Y.toBlocks₂₂) + (X.toBlocks₁₁ + Y.toBlocks₁₁) =
        (X.toBlocks₂₂ + X.toBlocks₁₁) + (Y.toBlocks₂₂ + Y.toBlocks₁₁)
      abel
  map_smul' a X := by
    apply Prod.ext
    · rfl
    · change a • X.toBlocks₂₂ + a • X.toBlocks₁₁ = a • (X.toBlocks₂₂ + X.toBlocks₁₁)
      exact (smul_add _ _ _).symm

/-- The fixed chart is the zero fiber of an actual affine map. -/
def fixedChartAffine : Matrix (n ⊕ n) (n ⊕ n) S →ᵃ[S]
    (Matrix n n S × Matrix n n S) :=
  chartResidualLinear.toAffineMap + AffineMap.const S _ (-1, 0)

theorem fixedChartAffine_eq_zero_iff (Z : Matrix (n ⊕ n) (n ⊕ n) S) :
    fixedChartAffine Z = 0 ↔ InFixedChart Z := by
  change (Z.toBlocks₁₂ + -1, Z.toBlocks₂₂ + Z.toBlocks₁₁ + 0) = (0, 0) ↔ _
  simp [InFixedChart, add_eq_zero_iff_eq_neg]

def chartExtractLinear : Matrix (n ⊕ n) (n ⊕ n) S →ₗ[S]
    (Matrix n n S × Matrix n n S) where
  toFun Z := (Z.toBlocks₁₁, -Z.toBlocks₂₁)
  map_add' X Y := by
    apply Prod.ext
    · rfl
    · change -(X.toBlocks₂₁ + Y.toBlocks₂₁) = -X.toBlocks₂₁ + -Y.toBlocks₂₁
      exact neg_add _ _
  map_smul' a X := by
    apply Prod.ext
    · rfl
    · change -(a • X.toBlocks₂₁) = a • (-X.toBlocks₂₁)
      exact (smul_neg _ _).symm

end Chart

namespace GateSystem
variable {R S W G E : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [Fintype W] [DecidableEq W] [Fintype G] [DecidableEq G]

/-- The ambient affine equations, together with membership in the conjugacy orbit.
The affine equations only constrain block entries and the compiler's linear wiring. -/
def OrbitSection (C : GateSystem R W G E)
    (Z : Matrix (Index W G ⊕ Index W G) (Index W G ⊕ Index W G) S) : Prop :=
  InFixedChart Z ∧ C.LinearSection Z.toBlocks₁₁ (-Z.toBlocks₂₁) ∧ InJordanOrbit Z

/-- Actual ambient affine equations for the orbit realization. -/
def orbitAffineConstraints (C : GateSystem R W G E) :
    Matrix (Index W G ⊕ Index W G) (Index W G ⊕ Index W G) S →ᵃ[S]
      ((Matrix (Index W G) (Index W G) S × Matrix (Index W G) (Index W G) S) ×
       (Matrix (Index W G) (Index W G) S × ((E → S) × (G → S)))) :=
  (fixedChartAffine (S := S)).prod
    ((C.residualAffine (S := S)).comp chartExtractLinear.toAffineMap)

theorem orbitAffineConstraints_eq_zero_iff (C : GateSystem R W G E)
    (Z : Matrix (Index W G ⊕ Index W G) (Index W G ⊕ Index W G) S) :
    C.orbitAffineConstraints (S := S) Z = 0 ↔
      InFixedChart Z ∧ C.LinearSection Z.toBlocks₁₁ (-Z.toBlocks₂₁) := by
  change (fixedChartAffine Z, C.residualAffine (S := S) (Z.toBlocks₁₁, -Z.toBlocks₂₁)) = (0, 0) ↔ _
  rw [Prod.mk.injEq, fixedChartAffine_eq_zero_iff, residualAffine_eq_zero_iff]

theorem orbitSection_iff (C : GateSystem R W G E)
    (Z : Matrix (Index W G ⊕ Index W G) (Index W G ⊕ Index W G) S) :
    C.OrbitSection Z ↔ C.orbitAffineConstraints (S := S) Z = 0 ∧ InJordanOrbit Z := by
  rw [orbitAffineConstraints_eq_zero_iff]
  exact and_assoc.symm

/-- An exact orbit-section realization with an explicit inverse, over all test algebras. -/
noncomputable def orbitSolutionEquiv (C : GateSystem R W G E) :
    {w : W → S // C.Satisfies w} ≃
    {Z : Matrix (Index W G ⊕ Index W G) (Index W G ⊕ Index W G) S //
      C.OrbitSection Z} where
  toFun w :=
    ⟨iota (C.assemble w.val) (C.assemble w.val * C.assemble w.val), by
      refine ⟨iota_inFixedChart _ _, ?_, (chart_orbit_iff _ _).mpr rfl⟩
      simpa [iota] using (C.solutionEquiv w).property.1⟩
  invFun Z := C.solutionEquiv.symm
    ⟨(Z.val.toBlocks₁₁, -Z.val.toBlocks₂₁), Z.property.2.1, by
      apply (chart_orbit_iff _ _).mp
      rw [fixedChart_reconstruct Z.val Z.property.1]
      exact Z.property.2.2⟩
  left_inv w := by
    apply Subtype.ext
    simp [solutionEquiv, iota]
  right_inv Z := by
    apply Subtype.ext
    change iota (C.assemble (wires Z.val.toBlocks₁₁))
      (C.assemble (wires Z.val.toBlocks₁₁) * C.assemble (wires Z.val.toBlocks₁₁)) = Z.val
    have hA := Z.property.2.1.1
    have hB : -Z.val.toBlocks₂₁ = Z.val.toBlocks₁₁ * Z.val.toBlocks₁₁ := by
      apply (chart_orbit_iff _ _).mp
      rw [fixedChart_reconstruct Z.val Z.property.1]
      exact Z.property.2.2
    rw [← hA, ← hB]
    exact fixedChart_reconstruct Z.val Z.property.1

end GateSystem

namespace ExpressionPresentation
variable {R S V Q : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [DecidableEq R] [DecidableEq V] [Fintype V] [Fintype Q]

/-- Matrix size index produced from an arbitrary finite polynomial presentation. -/
abbrev PolynomialIndex (f : Q → MvPolynomial V R) :=
  GateSystem.Index (ofPolynomials f).Wire (ofPolynomials f).Wire

theorem polynomialIndex_card_pos (f : Q → MvPolynomial V R) :
    0 < Fintype.card (PolynomialIndex f) := by
  apply Fintype.card_pos_iff.mpr
  exact ⟨Sum.inl ⟨.const 0, (ofPolynomials f).zero_mem⟩⟩

/-- Every finite polynomial system is exactly an affine section of the fixed
square-zero orbit chart, functorially parametrized over arbitrary test algebras. -/
noncomputable def polynomialOrbitSolutionEquiv (f : Q → MvPolynomial V R) :
    {x : V → S // ∀ q, MvPolynomial.eval₂ (algebraMap R S) x (f q) = 0} ≃
    {Z : Matrix (PolynomialIndex f ⊕ PolynomialIndex f)
        (PolynomialIndex f ⊕ PolynomialIndex f) S // (ofPolynomials f).gates.OrbitSection Z} :=
  (Equiv.subtypeEquivRight (fun x => by
    simp only [← ArithmeticExpr.eval_polynomial, ofPolynomials_roots])).trans
      ((ofPolynomials f).solutionEquiv.trans (ofPolynomials f).gates.orbitSolutionEquiv)

end ExpressionPresentation

noncomputable section
universe u
open MvPolynomial AlgebraicGeometry CategoryTheory

namespace GateSystem
variable {R W G E : Type u} [CommRing R]
  [Fintype W] [DecidableEq W] [Fintype G] [DecidableEq G]

abbrev MatrixCoord (W G : Type u) :=
  (Index W G × Index W G) ⊕ (Index W G × Index W G)
abbrev MatrixEquation (W G E : Type u) :=
  (Index W G × Index W G) ⊕ (E ⊕ (G ⊕ (Index W G × Index W G)))

def decode {S : Type*} (x : MatrixCoord W G → S) : Ambient W G S :=
  ((fun i j => x (Sum.inl (i,j))), fun i j => x (Sum.inr (i,j)))
def encode {S : Type*} (p : Ambient W G S) : MatrixCoord W G → S :=
  Sum.elim (fun ij => p.1 ij.1 ij.2) (fun ij => p.2 ij.1 ij.2)

@[simp] theorem decode_encode {S : Type*} (p : Ambient W G S) : decode (encode p) = p := rfl
@[simp] theorem encode_decode {S : Type*} (x : MatrixCoord W G → S) : encode (decode x) = x := by
  funext ij
  cases ij <;> rfl

variable {S T : Type*} [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]

theorem assemble_map (C : GateSystem R W G E) (φ : S →ₐ[R] T) (w : W → S) :
    (C.assemble w).map φ = C.assemble (fun i => φ (w i)) := by
  ext i j
  rcases i with i | ⟨i,g⟩ <;> rcases j with j | ⟨j,h⟩
  · by_cases hij : i = j <;> simp [assemble, Matrix.map_apply, Matrix.diagonal_apply, hij]
  · simp [assemble, Matrix.map_apply]
  · simp [assemble, Matrix.map_apply]
  · fin_cases i <;> fin_cases j <;> by_cases hgh : g = h <;>
      simp [assemble, Matrix.map_apply, Matrix.blockDiagonal_apply, gateBlock, hgh]

/-- Literal equations in the independent matrix entries: affine rows plus B-A². -/
def matrixPolynomials (C : GateSystem R W G E) :
    MatrixEquation W G E → MvPolynomial (MatrixCoord W G) R :=
  let A : Matrix (Index W G) (Index W G) (MvPolynomial (MatrixCoord W G) R) := (decode X).1
  let B : Matrix (Index W G) (Index W G) (MvPolynomial (MatrixCoord W G) R) := (decode X).2
  Sum.elim (fun ij => (A - C.assemble (wires A)) ij.1 ij.2)
    (Sum.elim (fun q => (C.equations q).eval (wires A))
      (Sum.elim (fun g => wires A (C.output g) - B (Sum.inr (0,g)) (Sum.inr (0,g)))
        (fun ij => (B - A*A) ij.1 ij.2)))

theorem matrixPolynomials_satisfied_iff (C : GateSystem R W G E)
    (x : MatrixCoord W G → S) :
    (∀ q, eval₂ (algebraMap R S) x (C.matrixPolynomials q) = 0) ↔
      C.LinearSection (decode x).1 (decode x).2 ∧
        (decode x).2 = (decode x).1 * (decode x).1 := by
  let A : Matrix (Index W G) (Index W G) (MvPolynomial (MatrixCoord W G) R) := (decode X).1
  let B : Matrix (Index W G) (Index W G) (MvPolynomial (MatrixCoord W G) R) := (decode X).2
  have hA : A.map
      (aeval x) = (decode x).1 := by ext i j; simp [A, decode]
  have hB : B.map
      (aeval x) = (decode x).2 := by ext i j; simp [B, decode]
  have hAsm : (C.assemble (wires A)).map (aeval x) =
      C.assemble (wires (decode x).1) := by
    rw [C.assemble_map]
    congr 1
    funext i
    simp [A, wires, decode]
  simp only [matrixPolynomials, Sum.forall, Sum.elim_inl, Sum.elim_inr]
  constructor
  · rintro ⟨hpat, he, hg, hsq⟩
    refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
    · ext i j
      have h := hpat (i,j)
      change aeval x (A i j - C.assemble (wires A) i j) = 0 at h
      rw [map_sub] at h
      change (A.map (aeval x)) i j - ((C.assemble (wires A)).map (aeval x)) i j = 0 at h
      rw [hA, hAsm, sub_eq_zero] at h
      exact h
    · intro q
      simpa [AffineEquation.eval, A, wires, decode] using he q
    · intro g
      simpa [A, B, wires, decode, sub_eq_zero] using hg g
    · ext i j
      have h := hsq (i,j)
      change aeval x (B i j - (A * A) i j) = 0 at h
      rw [map_sub] at h
      change (B.map (aeval x)) i j - ((A*A).map (aeval x)) i j = 0 at h
      rw [Matrix.map_mul, hB, hA, sub_eq_zero] at h
      exact h
  · rintro ⟨⟨hpat, he, hg⟩, hsq⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · rintro ⟨i,j⟩
      change aeval x (A i j - C.assemble (wires A) i j) = 0
      rw [map_sub]
      change (A.map (aeval x)) i j - ((C.assemble (wires A)).map (aeval x)) i j = 0
      rw [hA, hAsm]
      exact sub_eq_zero.mpr (congrFun (congrFun hpat i) j)
    · intro q
      simpa [AffineEquation.eval, A, wires, decode] using he q
    · intro g
      simpa [A, B, wires, decode, sub_eq_zero] using hg g
    · rintro ⟨i,j⟩
      change aeval x (B i j - (A * A) i j) = 0
      rw [map_sub]
      change (B.map (aeval x)) i j - ((A*A).map (aeval x)) i j = 0
      rw [Matrix.map_mul, hB, hA, hsq, sub_self]


theorem matrixUniversal_satisfies (C : GateSystem R W G E) :
    C.LinearSection (decode (universalSolution C.matrixPolynomials)).1
      (decode (universalSolution C.matrixPolynomials)).2 ∧
    (decode (universalSolution C.matrixPolynomials)).2 =
      (decode (universalSolution C.matrixPolynomials)).1 *
        (decode (universalSolution C.matrixPolynomials)).1 :=
  (C.matrixPolynomials_satisfied_iff _).mp (universalSolution_satisfies _)

def matrixToCircuit (C : GateSystem R W G E) :
    (MvPolynomial (MatrixCoord W G) R ⧸ equationIdeal C.matrixPolynomials) →ₐ[R]
      (MvPolynomial W R ⧸ equationIdeal C.polynomials) :=
  solutionLift C.matrixPolynomials
    (encode (C.assemble (universalSolution C.polynomials),
      C.assemble (universalSolution C.polynomials) * C.assemble (universalSolution C.polynomials)))
    ((C.matrixPolynomials_satisfied_iff _).mpr
      ((C.solutionEquiv ⟨_, C.universal_satisfies⟩).property))

def circuitToMatrix (C : GateSystem R W G E) :
    (MvPolynomial W R ⧸ equationIdeal C.polynomials) →ₐ[R]
      (MvPolynomial (MatrixCoord W G) R ⧸ equationIdeal C.matrixPolynomials) :=
  solutionLift C.polynomials
    (wires (decode (universalSolution C.matrixPolynomials)).1)
    ((C.polynomials_satisfied_iff _).mpr
      ((C.solutionEquiv.symm ⟨_, C.matrixUniversal_satisfies⟩).property))

@[simp] theorem matrixToCircuit_generator (C : GateSystem R W G E) (v : MatrixCoord W G) :
    C.matrixToCircuit (universalSolution C.matrixPolynomials v) =
      encode (C.assemble (universalSolution C.polynomials),
        C.assemble (universalSolution C.polynomials) *
          C.assemble (universalSolution C.polynomials)) v := by
  simp [matrixToCircuit]

@[simp] theorem circuitToMatrix_generator (C : GateSystem R W G E) (w : W) :
    C.circuitToMatrix (universalSolution C.polynomials w) =
      wires (decode (universalSolution C.matrixPolynomials)).1 w := by
  simp [circuitToMatrix]

theorem matrixToCircuit_circuitToMatrix (C : GateSystem R W G E) :
    C.matrixToCircuit.comp C.circuitToMatrix = AlgHom.id R _ := by
  apply quotientAlgHom_ext C.polynomials
  intro w
  simp [wires, decode, encode, assemble]

theorem circuitToMatrix_matrixToCircuit (C : GateSystem R W G E) :
    C.circuitToMatrix.comp C.matrixToCircuit = AlgHom.id R _ := by
  apply quotientAlgHom_ext C.matrixPolynomials
  intro v
  have ha := C.matrixUniversal_satisfies.1.1
  have hb := C.matrixUniversal_satisfies.2
  have hm : (C.assemble (universalSolution C.polynomials)).map C.circuitToMatrix =
      (decode (universalSolution C.matrixPolynomials)).1 := by
    rw [C.assemble_map]
    simp only [circuitToMatrix_generator]
    exact ha.symm
  rcases v with ⟨i,j⟩ | ⟨i,j⟩
  · simp only [AlgHom.comp_apply, matrixToCircuit_generator, encode, Sum.elim_inl,
      AlgHom.id_apply]
    change ((C.assemble (universalSolution C.polynomials)).map C.circuitToMatrix) i j = _
    rw [hm]
    rfl
  · simp only [AlgHom.comp_apply, matrixToCircuit_generator, encode, Sum.elim_inr,
      AlgHom.id_apply]
    change ((C.assemble (universalSolution C.polynomials) *
      C.assemble (universalSolution C.polynomials)).map C.circuitToMatrix) i j = _
    rw [Matrix.map_mul, hm, ← hb]
    rfl

/-- The literal affine matrix-section quotient is the circuit coordinate algebra. -/
def matrixCoordinateAlgEquiv (C : GateSystem R W G E) :
    (MvPolynomial W R ⧸ equationIdeal C.polynomials) ≃ₐ[R]
      (MvPolynomial (MatrixCoord W G) R ⧸ equationIdeal C.matrixPolynomials) :=
  AlgEquiv.ofAlgHom C.circuitToMatrix C.matrixToCircuit
    C.circuitToMatrix_matrixToCircuit C.matrixToCircuit_circuitToMatrix

end GateSystem

namespace ExpressionPresentation
variable {R V Q : Type u} [CommRing R] [DecidableEq R] [DecidableEq V]
  [Fintype V] [Fintype Q]

/-- The full coordinate-ring form of graph-of-squaring universality. -/
def polynomialMatrixCoordinateAlgEquiv (f : Q → MvPolynomial V R) :
    (MvPolynomial V R ⧸ equationIdeal f) ≃ₐ[R]
      (MvPolynomial (GateSystem.MatrixCoord (ofPolynomials f).Wire (ofPolynomials f).Wire) R ⧸
        equationIdeal (ofPolynomials f).gates.matrixPolynomials) :=
  (polynomialCoordinateAlgEquiv f).trans (ofPolynomials f).gates.matrixCoordinateAlgEquiv

/-- Every finite polynomial affine scheme is exactly an affine section of one
matrix-square graph, with its full quotient ring and nilpotent structure. -/
def polynomialMatrixSectionSchemeIso (f : Q → MvPolynomial V R) :
    AlgebraicGeometry.Spec (.of (MvPolynomial V R ⧸ equationIdeal f)) ≅
      AlgebraicGeometry.Spec (.of
        (MvPolynomial (GateSystem.MatrixCoord (ofPolynomials f).Wire (ofPolynomials f).Wire) R ⧸
          equationIdeal (ofPolynomials f).gates.matrixPolynomials)) :=
  AlgebraicGeometry.Scheme.Spec.mapIso
    (polynomialMatrixCoordinateAlgEquiv f).symm.toRingEquiv.toCommRingCatIso.op

end ExpressionPresentation

/-- Every finitely presented commutative algebra, with no supplied choice of equations,
is the complete coordinate algebra of an affine matrix-square section. -/
theorem finitePresentation_matrixSection
    (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
    [Algebra.FinitePresentation R A] :
    ∃ (W G E : Type u) (_ : Fintype W) (_ : Fintype G) (_ : Fintype E)
      (_ : DecidableEq W) (_ : DecidableEq G) (C : GateSystem R W G E),
      0 < Fintype.card (GateSystem.Index W G) ∧
      Nonempty (A ≃ₐ[R]
        (MvPolynomial (GateSystem.MatrixCoord W G) R ⧸ equationIdeal C.matrixPolynomials)) := by
  classical
  have hfp : Algebra.FinitePresentation R A := inferInstance
  obtain ⟨(V : Type u), hV, φ, hsurj, hfg⟩ :=
    (Algebra.FinitePresentation.iff_quotient_mvPolynomial' (R := R) (A := A)).mp hfp
  letI := hV
  obtain ⟨s, hs⟩ := hfg
  let f : s → MvPolynomial V R := fun q => q.val
  have hI : equationIdeal f = RingHom.ker φ.toRingHom := by
    change Ideal.span (Set.range (fun q : s => q.val)) = _
    have hr : Set.range (fun q : s => q.val) = (s : Set (MvPolynomial V R)) := by
      ext q
      simp
    rw [hr]
    exact hs
  let P := ExpressionPresentation.ofPolynomials f
  refine ⟨P.Wire, P.Wire, P.Wire ⊕ s, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, P.gates, ?_⟩
  refine ⟨?_, ⟨(Ideal.quotientKerAlgEquivOfSurjective hsurj).symm.trans
    ((Ideal.quotientEquivAlgOfEq R hI.symm).trans
      (ExpressionPresentation.polynomialMatrixCoordinateAlgEquiv f))⟩⟩
  exact Fintype.card_pos_iff.mpr ⟨Sum.inl P.zeroWire⟩

/-- Scheme form of universality for every finitely presented affine coordinate algebra. -/
theorem finitePresentation_matrixSectionScheme
    (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
    [Algebra.FinitePresentation R A] :
    ∃ (W G E : Type u) (_ : Fintype W) (_ : Fintype G) (_ : Fintype E)
      (_ : DecidableEq W) (_ : DecidableEq G) (C : GateSystem R W G E),
      0 < Fintype.card (GateSystem.Index W G) ∧
      Nonempty (AlgebraicGeometry.Spec (.of A) ≅
        AlgebraicGeometry.Spec (.of
          (MvPolynomial (GateSystem.MatrixCoord W G) R ⧸ equationIdeal C.matrixPolynomials))) := by
  obtain ⟨W, G, E, hW, hG, hE, dW, dG, C, hpos, ⟨e⟩⟩ := finitePresentation_matrixSection R A
  exact ⟨W, G, E, hW, hG, hE, dW, dG, C, hpos,
    ⟨AlgebraicGeometry.Scheme.Spec.mapIso e.symm.toRingEquiv.toCommRingCatIso.op⟩⟩


namespace GateSystem
variable {R W G E : Type u} [CommRing R]
  [Fintype W] [DecidableEq W] [Fintype G] [DecidableEq G]

abbrev OrbitCoord (W G : Type u) :=
  (Index W G ⊕ Index W G) × (Index W G ⊕ Index W G)
abbrev OrbitEquation (W G E : Type u) :=
  (Index W G × Index W G) ⊕ ((Index W G × Index W G) ⊕ MatrixEquation W G E)

def orbitMatrix {S : Type*} (x : OrbitCoord W G → S) :
    Matrix (Index W G ⊕ Index W G) (Index W G ⊕ Index W G) S := fun i j => x (i,j)

def orbitExtract {S : Type*} [Neg S] (x : OrbitCoord W G → S) : Ambient W G S :=
  ((orbitMatrix x).toBlocks₁₁, -(orbitMatrix x).toBlocks₂₁)

theorem orbitExtract_iota {S : Type*} [CommRing S]
    (A B : Matrix (Index W G) (Index W G) S) :
    orbitExtract (fun ij => iota A B ij.1 ij.2) = (A,B) := by
  apply Prod.ext
  · ext i j
    rfl
  · ext i j
    simp [orbitExtract, orbitMatrix, iota, Matrix.toBlocks₂₁]

def extractionPolynomial : MvPolynomial (MatrixCoord W G) R →ₐ[R]
    MvPolynomial (OrbitCoord W G) R :=
  aeval (encode (orbitExtract X))

variable {S : Type*} [CommRing S] [Algebra R S]

theorem extractionPolynomial_eval (x : OrbitCoord W G → S)
    (p : MvPolynomial (MatrixCoord W G) R) :
    aeval x (extractionPolynomial p) = aeval (encode (orbitExtract x)) p := by
  have h : (aeval x).comp (extractionPolynomial (R := R) (W := W) (G := G)) =
      aeval (encode (orbitExtract x)) := by
    apply MvPolynomial.algHom_ext
    rintro (⟨i,j⟩ | ⟨i,j⟩) <;>
      simp [extractionPolynomial, encode, orbitExtract, orbitMatrix,
        Matrix.toBlocks₁₁, Matrix.toBlocks₂₁]
  exact DFunLike.congr_fun h p

/-- Literal equations in all entries of Z: fixed affine chart equations, followed
by the compiler equations after the affine extraction (Z11,-Z21). -/
def orbitPolynomials (C : GateSystem R W G E) :
    OrbitEquation W G E → MvPolynomial (OrbitCoord W G) R :=
  Sum.elim
    (fun ij => X (Sum.inl ij.1, Sum.inr ij.2) -
      MvPolynomial.C ((1 : Matrix (Index W G) (Index W G) R) ij.1 ij.2))
    (Sum.elim
      (fun ij => X (Sum.inr ij.1, Sum.inr ij.2) + X (Sum.inl ij.1, Sum.inl ij.2))
      (fun q => extractionPolynomial (C.matrixPolynomials q)))

theorem orbitPolynomials_satisfied_iff (C : GateSystem R W G E)
    (x : OrbitCoord W G → S) :
    (∀ q, eval₂ (algebraMap R S) x (C.orbitPolynomials q) = 0) ↔
      InFixedChart (orbitMatrix x) ∧
      C.LinearSection (orbitExtract x).1 (orbitExtract x).2 ∧
      (orbitExtract x).2 = (orbitExtract x).1 * (orbitExtract x).1 := by
  rw [Sum.forall]
  simp only [orbitPolynomials, Sum.elim_inl, Sum.elim_inr]
  rw [Sum.forall]
  simp only [Sum.elim_inl, Sum.elim_inr]
  constructor
  · rintro ⟨h12, h22, hrest⟩
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · ext i j
      have h := h12 (i,j)
      by_cases hij : i = j <;>
        simpa [orbitMatrix, Matrix.one_apply, hij, sub_eq_zero] using h
    · ext i j
      have h := h22 (i,j)
      simpa [orbitMatrix, add_eq_zero_iff_eq_neg] using h
    · apply (C.matrixPolynomials_satisfied_iff (encode (orbitExtract x))).mp
      intro q
      have h := hrest q
      change aeval x (extractionPolynomial (C.matrixPolynomials q)) = 0 at h
      rw [extractionPolynomial_eval] at h
      exact h
  · rintro ⟨⟨h12, h22⟩, hrest⟩
    refine ⟨?_, ?_, ?_⟩
    · rintro ⟨i,j⟩
      have h := congrFun (congrFun h12 i) j
      by_cases hij : i = j <;>
        simpa [orbitMatrix, Matrix.one_apply, hij, sub_eq_zero] using h
    · rintro ⟨i,j⟩
      have h := congrFun (congrFun h22 i) j
      simpa [orbitMatrix, add_eq_zero_iff_eq_neg] using h
    · intro q
      change aeval x (extractionPolynomial (C.matrixPolynomials q)) = 0
      rw [extractionPolynomial_eval]
      exact (C.matrixPolynomials_satisfied_iff (encode (orbitExtract x))).mpr hrest q

/-- These literal polynomial equations are exactly the affine ambient constraints
together with square-zero, over every test algebra. -/
theorem orbitPolynomials_affine_square (C : GateSystem R W G E)
    (x : OrbitCoord W G → S) :
    (∀ q, eval₂ (algebraMap R S) x (C.orbitPolynomials q) = 0) ↔
      C.orbitAffineConstraints (S := S) (orbitMatrix x) = 0 ∧
      orbitMatrix x * orbitMatrix x = 0 := by
  rw [orbitPolynomials_satisfied_iff, orbitAffineConstraints_eq_zero_iff]
  constructor
  · rintro ⟨hc, hl, hs⟩
    refine ⟨⟨hc, hl⟩, ?_⟩
    rw [← fixedChart_reconstruct _ hc]
    exact (iota_square_iff _ _).mpr hs
  · rintro ⟨⟨hc, hl⟩, hs⟩
    refine ⟨hc, hl, ?_⟩
    apply (iota_square_iff _ _).mp
    unfold orbitExtract
    rw [fixedChart_reconstruct _ hc]
    exact hs

theorem orbitUniversal_satisfies (C : GateSystem R W G E) :
    InFixedChart (orbitMatrix (universalSolution C.orbitPolynomials)) ∧
      C.LinearSection (orbitExtract (universalSolution C.orbitPolynomials)).1
        (orbitExtract (universalSolution C.orbitPolynomials)).2 ∧
      (orbitExtract (universalSolution C.orbitPolynomials)).2 =
        (orbitExtract (universalSolution C.orbitPolynomials)).1 *
          (orbitExtract (universalSolution C.orbitPolynomials)).1 :=
  (C.orbitPolynomials_satisfied_iff _).mp (universalSolution_satisfies _)

/-- The literal closed subscheme is contained in the orbit on every test algebra,
including its universal, potentially nonreduced coordinate algebra. -/
theorem orbitPolynomials_orbit_iff (C : GateSystem R W G E)
    (x : OrbitCoord W G → S) :
    (∀ q, eval₂ (algebraMap R S) x (C.orbitPolynomials q) = 0) ↔
      C.OrbitSection (orbitMatrix x) := by
  rw [orbitPolynomials_satisfied_iff]
  constructor
  · rintro ⟨hc, hl, hs⟩
    refine ⟨hc, hl, ?_⟩
    rw [← fixedChart_reconstruct _ hc]
    exact (chart_orbit_iff _ _).mpr hs
  · rintro ⟨hc, hl, ho⟩
    refine ⟨hc, hl, ?_⟩
    apply (chart_orbit_iff _ _).mp
    unfold orbitExtract
    rw [fixedChart_reconstruct _ hc]
    exact ho

theorem orbitUniversal_inJordanOrbit (C : GateSystem R W G E) :
    InJordanOrbit (orbitMatrix (universalSolution C.orbitPolynomials)) :=
  ((C.orbitPolynomials_orbit_iff _).mp (universalSolution_satisfies _)).2.2


def orbitToMatrix (C : GateSystem R W G E) :
    (MvPolynomial (OrbitCoord W G) R ⧸ equationIdeal C.orbitPolynomials) →ₐ[R]
      (MvPolynomial (MatrixCoord W G) R ⧸ equationIdeal C.matrixPolynomials) :=
  solutionLift C.orbitPolynomials
    (fun ij => iota (decode (universalSolution C.matrixPolynomials)).1
      (decode (universalSolution C.matrixPolynomials)).2 ij.1 ij.2)
    ((C.orbitPolynomials_satisfied_iff _).mpr (by
      refine ⟨iota_inFixedChart _ _, ?_⟩
      rw [orbitExtract_iota]
      exact C.matrixUniversal_satisfies))

def matrixToOrbit (C : GateSystem R W G E) :
    (MvPolynomial (MatrixCoord W G) R ⧸ equationIdeal C.matrixPolynomials) →ₐ[R]
      (MvPolynomial (OrbitCoord W G) R ⧸ equationIdeal C.orbitPolynomials) :=
  solutionLift C.matrixPolynomials
    (encode (orbitExtract (universalSolution C.orbitPolynomials)))
    ((C.matrixPolynomials_satisfied_iff _).mpr C.orbitUniversal_satisfies.2)

@[simp] theorem orbitToMatrix_generator (C : GateSystem R W G E) (v : OrbitCoord W G) :
    C.orbitToMatrix (universalSolution C.orbitPolynomials v) =
      iota (decode (universalSolution C.matrixPolynomials)).1
        (decode (universalSolution C.matrixPolynomials)).2 v.1 v.2 := by
  simp [orbitToMatrix]

@[simp] theorem matrixToOrbit_generator (C : GateSystem R W G E) (v : MatrixCoord W G) :
    C.matrixToOrbit (universalSolution C.matrixPolynomials v) =
      encode (orbitExtract (universalSolution C.orbitPolynomials)) v := by
  simp [matrixToOrbit]

theorem orbitToMatrix_matrixToOrbit (C : GateSystem R W G E) :
    C.orbitToMatrix.comp C.matrixToOrbit = AlgHom.id R _ := by
  apply quotientAlgHom_ext C.matrixPolynomials
  rintro (⟨i,j⟩ | ⟨i,j⟩) <;>
    simp [orbitExtract, orbitMatrix, encode, decode, iota, Matrix.toBlocks₁₁, Matrix.toBlocks₂₁]

theorem matrixToOrbit_orbitToMatrix (C : GateSystem R W G E) :
    C.matrixToOrbit.comp C.orbitToMatrix = AlgHom.id R _ := by
  have ha : ((decode (universalSolution C.matrixPolynomials)).1).map C.matrixToOrbit =
      (orbitExtract (universalSolution C.orbitPolynomials)).1 := by
    ext i j
    simp [decode, encode]
  have hb : ((decode (universalSolution C.matrixPolynomials)).2).map C.matrixToOrbit =
      (orbitExtract (universalSolution C.orbitPolynomials)).2 := by
    ext i j
    simp [decode, encode]
  have hm : (iota (decode (universalSolution C.matrixPolynomials)).1
      (decode (universalSolution C.matrixPolynomials)).2).map C.matrixToOrbit =
      orbitMatrix (universalSolution C.orbitPolynomials) := by
    have hmap : (iota (decode (universalSolution C.matrixPolynomials)).1
        (decode (universalSolution C.matrixPolynomials)).2).map C.matrixToOrbit =
        iota (((decode (universalSolution C.matrixPolynomials)).1).map C.matrixToOrbit)
          (((decode (universalSolution C.matrixPolynomials)).2).map C.matrixToOrbit) :=
      Universality.map_iota C.matrixToOrbit.toRingHom _ _
    rw [hmap, ha, hb]
    exact fixedChart_reconstruct _ C.orbitUniversal_satisfies.1
  apply quotientAlgHom_ext C.orbitPolynomials
  rintro ⟨i,j⟩
  simp only [AlgHom.comp_apply, orbitToMatrix_generator, AlgHom.id_apply]
  exact congrFun (congrFun hm i) j

/-- Literal ambient-Z coordinate reconstruction, not merely a point bijection. -/
def orbitCoordinateAlgEquiv (C : GateSystem R W G E) :
    (MvPolynomial (MatrixCoord W G) R ⧸ equationIdeal C.matrixPolynomials) ≃ₐ[R]
      (MvPolynomial (OrbitCoord W G) R ⧸ equationIdeal C.orbitPolynomials) :=
  AlgEquiv.ofAlgHom C.matrixToOrbit C.orbitToMatrix
    C.matrixToOrbit_orbitToMatrix C.orbitToMatrix_matrixToOrbit

end GateSystem

/-- Every finitely presented algebra is an exact affine section in literal ambient
square-zero matrix coordinates. The universal matrix lies in the fixed orbit chart. -/
theorem finitePresentation_orbitSection
    (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
    [Algebra.FinitePresentation R A] :
    ∃ (W G E : Type u) (_ : Fintype W) (_ : Fintype G) (_ : Fintype E)
      (_ : DecidableEq W) (_ : DecidableEq G) (C : GateSystem R W G E),
      0 < Fintype.card (GateSystem.Index W G) ∧
      Nonempty (A ≃ₐ[R]
        (MvPolynomial (GateSystem.OrbitCoord W G) R ⧸ equationIdeal C.orbitPolynomials)) := by
  obtain ⟨W, G, E, hW, hG, hE, dW, dG, C, hpos, ⟨e⟩⟩ := finitePresentation_matrixSection R A
  exact ⟨W, G, E, hW, hG, hE, dW, dG, C, hpos, ⟨e.trans C.orbitCoordinateAlgEquiv⟩⟩

/-- Scheme-theoretic universality in the actual ambient endomorphism space. -/
theorem finitePresentation_orbitSectionScheme
    (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
    [Algebra.FinitePresentation R A] :
    ∃ (W G E : Type u) (_ : Fintype W) (_ : Fintype G) (_ : Fintype E)
      (_ : DecidableEq W) (_ : DecidableEq G) (C : GateSystem R W G E),
      0 < Fintype.card (GateSystem.Index W G) ∧
      Nonempty (AlgebraicGeometry.Spec (.of A) ≅
        AlgebraicGeometry.Spec (.of
          (MvPolynomial (GateSystem.OrbitCoord W G) R ⧸ equationIdeal C.orbitPolynomials))) := by
  obtain ⟨W, G, E, hW, hG, hE, dW, dG, C, hpos, ⟨e⟩⟩ := finitePresentation_orbitSection R A
  exact ⟨W, G, E, hW, hG, hE, dW, dG, C, hpos,
    ⟨AlgebraicGeometry.Scheme.Spec.mapIso e.symm.toRingEquiv.toCommRingCatIso.op⟩⟩


theorem equationIdeal_le_iff_eval {R V Q : Type u} [CommRing R]
    (f : Q → MvPolynomial V R) (J : Ideal (MvPolynomial V R)) :
    equationIdeal f ≤ J ↔
      ∀ q, eval₂ (algebraMap R (MvPolynomial V R ⧸ J))
        (fun v => Ideal.Quotient.mk J (X v)) (f q) = 0 := by
  have heval (q : Q) : eval₂ (algebraMap R (MvPolynomial V R ⧸ J))
      (fun v => Ideal.Quotient.mk J (X v)) (f q) = (Ideal.Quotient.mkₐ R J) (f q) :=
    eval₂_algHom (Ideal.Quotient.mkₐ R J) (f q)
  simp only [heval]
  rw [equationIdeal, Ideal.span_le]
  constructor
  · intro h q
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (h ⟨q, rfl⟩)
  · intro h p hp
    obtain ⟨q, rfl⟩ := hp
    exact Ideal.Quotient.eq_zero_iff_mem.mp (h q)

namespace GateSystem
variable {R W G E : Type u} [CommRing R]
  [Fintype W] [DecidableEq W] [Fintype G] [DecidableEq G]

abbrev OrbitAffineEquation (W G E : Type u) := (Index W G × Index W G) ⊕
  ((Index W G × Index W G) ⊕ ((Index W G × Index W G) ⊕ (E ⊕ G)))

/-- Only affine equations; the matrix-square equations are deliberately excluded. -/
def orbitAffinePolynomials (C : GateSystem R W G E) :
    OrbitAffineEquation W G E → MvPolynomial (OrbitCoord W G) R :=
  let A : Matrix (Index W G) (Index W G) (MvPolynomial (OrbitCoord W G) R) := (orbitExtract X).1
  let B : Matrix (Index W G) (Index W G) (MvPolynomial (OrbitCoord W G) R) := (orbitExtract X).2
  Sum.elim (fun ij => X (Sum.inl ij.1, Sum.inr ij.2) -
      MvPolynomial.C ((1 : Matrix (Index W G) (Index W G) R) ij.1 ij.2))
    (Sum.elim (fun ij => X (Sum.inr ij.1, Sum.inr ij.2) + X (Sum.inl ij.1, Sum.inl ij.2))
      (Sum.elim (fun ij => (A - C.assemble (wires A)) ij.1 ij.2)
        (Sum.elim (fun q => (C.equations q).eval (wires A))
          (fun g => wires A (C.output g) - B (Sum.inr (0,g)) (Sum.inr (0,g))))))

theorem orbitAffinePolynomials_satisfied_iff {S : Type*} [CommRing S] [Algebra R S]
    (C : GateSystem R W G E) (x : OrbitCoord W G → S) :
    (∀ q, eval₂ (algebraMap R S) x (C.orbitAffinePolynomials q) = 0) ↔
      C.orbitAffineConstraints (S := S) (orbitMatrix x) = 0 := by
  let A : Matrix (Index W G) (Index W G) (MvPolynomial (OrbitCoord W G) R) := (orbitExtract X).1
  have hA : A.map (aeval x) = (orbitExtract x).1 := by
    ext i j
    simp [A, orbitExtract, orbitMatrix, Matrix.toBlocks₁₁]
  have hAsm : (C.assemble (wires A)).map (aeval x) = C.assemble (wires (orbitExtract x).1) := by
    rw [C.assemble_map]
    congr 1
    funext i
    simp [A, wires, orbitExtract, orbitMatrix, Matrix.toBlocks₁₁]
  rw [orbitAffineConstraints_eq_zero_iff]
  simp only [orbitAffinePolynomials, Sum.forall, Sum.elim_inl, Sum.elim_inr]
  constructor
  · rintro ⟨h12, h22, hpat, he, hg⟩
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_, ?_⟩⟩
    · ext i j
      have h := h12 (i,j)
      by_cases hij : i = j <;> simpa [orbitMatrix, Matrix.one_apply, hij, sub_eq_zero] using h
    · ext i j
      simpa [orbitMatrix, add_eq_zero_iff_eq_neg] using h22 (i,j)
    · ext i j
      have h := hpat (i,j)
      change aeval x (A i j - C.assemble (wires A) i j) = 0 at h
      rw [map_sub] at h
      change (A.map (aeval x)) i j - ((C.assemble (wires A)).map (aeval x)) i j = 0 at h
      rw [hA, hAsm, sub_eq_zero] at h
      exact h
    · intro q
      simpa [AffineEquation.eval, A, wires, orbitExtract, orbitMatrix, Matrix.toBlocks₁₁] using he q
    · intro g
      simpa [wires, orbitExtract, orbitMatrix, Matrix.toBlocks₁₁, Matrix.toBlocks₂₁,
        sub_eq_zero, add_eq_zero_iff_eq_neg] using hg g
  · rintro ⟨⟨h12, h22⟩, ⟨hpat, he, hg⟩⟩
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rintro ⟨i,j⟩
      have h := congrFun (congrFun h12 i) j
      by_cases hij : i = j <;> simpa [orbitMatrix, Matrix.one_apply, hij, sub_eq_zero] using h
    · rintro ⟨i,j⟩
      simpa [orbitMatrix, add_eq_zero_iff_eq_neg] using congrFun (congrFun h22 i) j
    · rintro ⟨i,j⟩
      change aeval x (A i j - C.assemble (wires A) i j) = 0
      rw [map_sub]
      change (A.map (aeval x)) i j - ((C.assemble (wires A)).map (aeval x)) i j = 0
      rw [hA, hAsm]
      exact sub_eq_zero.mpr (congrFun (congrFun hpat i) j)
    · intro q
      simpa [AffineEquation.eval, A, wires, orbitExtract, orbitMatrix, Matrix.toBlocks₁₁] using he q
    · intro g
      simpa [wires, orbitExtract, orbitMatrix, Matrix.toBlocks₁₁, Matrix.toBlocks₂₁,
        sub_eq_zero, add_eq_zero_iff_eq_neg] using hg g

/-- The actual scheme intersection ideal, with no passage to a radical. -/
theorem orbitSectionIdeal_eq (C : GateSystem R W G E) :
    equationIdeal C.orbitPolynomials = equationIdeal C.orbitAffinePolynomials ⊔
      matrixEntryIdeal (orbitMatrix (X : OrbitCoord W G → MvPolynomial (OrbitCoord W G) R) *
        orbitMatrix X) := by
  have h (J : Ideal (MvPolynomial (OrbitCoord W G) R)) :
      equationIdeal C.orbitPolynomials ≤ J ↔
      equationIdeal C.orbitAffinePolynomials ⊔
        matrixEntryIdeal (orbitMatrix (X : OrbitCoord W G → MvPolynomial (OrbitCoord W G) R) *
          orbitMatrix X) ≤ J := by
    rw [sup_le_iff, equationIdeal_le_iff_eval, equationIdeal_le_iff_eval,
      C.orbitPolynomials_affine_square, C.orbitAffinePolynomials_satisfied_iff,
      matrixEntryIdeal_le_iff, Matrix.map_mul]
    rfl
  exact le_antisymm ((h _).mpr le_rfl) ((h _).mp le_rfl)

def sectionCellCoordinates (C : GateSystem R W G E) :
    MvPolynomial (Index W G × Index W G) R →ₐ[R]
      (MvPolynomial (OrbitCoord W G) R ⧸ equationIdeal C.orbitPolynomials) :=
  aeval (fun ij => (orbitMatrix (universalSolution C.orbitPolynomials)).toBlocks₁₁ ij.1 ij.2)

theorem orbitUniversal_cell (C : GateSystem R W G E) :
    iota (orbitMatrix (universalSolution C.orbitPolynomials)).toBlocks₁₁
      ((orbitMatrix (universalSolution C.orbitPolynomials)).toBlocks₁₁ *
        (orbitMatrix (universalSolution C.orbitPolynomials)).toBlocks₁₁) =
      orbitMatrix (universalSolution C.orbitPolynomials) := by
  have hs := C.orbitUniversal_satisfies.2.2
  change -(orbitMatrix (universalSolution C.orbitPolynomials)).toBlocks₂₁ =
    (orbitMatrix (universalSolution C.orbitPolynomials)).toBlocks₁₁ *
      (orbitMatrix (universalSolution C.orbitPolynomials)).toBlocks₁₁ at hs
  rw [← hs]
  exact fixedChart_reconstruct _ C.orbitUniversal_satisfies.1

/-- The actual morphism from the section scheme to affine cell coordinates. -/
def sectionToCell (C : GateSystem R W G E) :
    Spec (.of (MvPolynomial (OrbitCoord W G) R ⧸ equationIdeal C.orbitPolynomials)) ⟶
      Spec (.of (MvPolynomial (Index W G × Index W G) R)) :=
  Spec.map (CommRingCat.ofHom C.sectionCellCoordinates.toRingHom)

theorem sectionCellCoordinates_comp_cellCoordinateMap (C : GateSystem R W G E) :
    C.sectionCellCoordinates.toRingHom.comp (cellCoordinateMap (R := R) (Index W G)) =
      Ideal.Quotient.mk (equationIdeal C.orbitPolynomials) := by
  have ha : (SquareZeroGeometry.cellSourceMatrix R (Index W G)).map C.sectionCellCoordinates =
      (orbitMatrix (universalSolution C.orbitPolynomials)).toBlocks₁₁ := by
    ext i j
    simp [SquareZeroGeometry.cellSourceMatrix, sectionCellCoordinates]
  have hm : (iota (SquareZeroGeometry.cellSourceMatrix R (Index W G))
      (SquareZeroGeometry.cellSourceMatrix R (Index W G) *
        SquareZeroGeometry.cellSourceMatrix R (Index W G))).map C.sectionCellCoordinates =
      orbitMatrix (universalSolution C.orbitPolynomials) := by
    calc
      _ = iota ((SquareZeroGeometry.cellSourceMatrix R (Index W G)).map C.sectionCellCoordinates)
          ((SquareZeroGeometry.cellSourceMatrix R (Index W G) *
            SquareZeroGeometry.cellSourceMatrix R (Index W G)).map C.sectionCellCoordinates) :=
        Universality.map_iota C.sectionCellCoordinates.toRingHom _ _
      _ = iota (orbitMatrix (universalSolution C.orbitPolynomials)).toBlocks₁₁
          ((orbitMatrix (universalSolution C.orbitPolynomials)).toBlocks₁₁ *
            (orbitMatrix (universalSolution C.orbitPolynomials)).toBlocks₁₁) := by
        rw [Matrix.map_mul, ha]
      _ = _ := C.orbitUniversal_cell
  apply MvPolynomial.ringHom_ext
  · intro r
    simp [cellCoordinateMap, iotaCoordinateMap, graphEval, sectionCellCoordinates]
    rfl
  · intro ij
    rw [RingHom.comp_apply, SquareZeroGeometry.cellCoordinateMap_X]
    exact congrFun (congrFun hm ij.1) ij.2

theorem sectionCellCoordinates_surjective (C : GateSystem R W G E) :
    Function.Surjective C.sectionCellCoordinates := by
  intro y
  obtain ⟨p, hp⟩ := Ideal.Quotient.mk_surjective y
  refine ⟨cellCoordinateMap (R := R) (Index W G) p, ?_⟩
  change (C.sectionCellCoordinates.toRingHom.comp (cellCoordinateMap (R := R) (Index W G))) p = y
  rw [sectionCellCoordinates_comp_cellCoordinateMap]
  exact hp

theorem sectionToCell_isClosedImmersion (C : GateSystem R W G E) :
    IsClosedImmersion C.sectionToCell :=
  IsClosedImmersion.spec_of_surjective _ C.sectionCellCoordinates_surjective

/-- The actual factorization of the universal affine section into the smooth orbit scheme. -/
def sectionToOrbit (C : GateSystem R W G E) :
    Spec (.of (MvPolynomial (OrbitCoord W G) R ⧸ equationIdeal C.orbitPolynomials)) ⟶
      SquareZeroGeometry.maximalRankScheme R (Index W G) :=
  C.sectionToCell ≫ SquareZeroGeometry.cellMorphism R (Index W G)

theorem sectionToOrbit_isClosedImmersion (C : GateSystem R W G E) :
    IsClosedImmersion C.sectionToOrbit := by
  letI := C.sectionToCell_isClosedImmersion
  letI := SquareZeroGeometry.cellMorphism_isClosedImmersion R (Index W G)
  unfold sectionToOrbit
  infer_instance

theorem sectionToOrbit_ambient (C : GateSystem R W G E) :
    C.sectionToOrbit ≫ (SquareZeroGeometry.maximalRankOpen R (Index W G)).ι ≫
      SquareZeroGeometry.squareZeroClosedImmersion R (Index W G) =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (equationIdeal C.orbitPolynomials))) := by
  unfold sectionToOrbit sectionToCell
  rw [Category.assoc, SquareZeroGeometry.cellMorphism_ambient,
    ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  exact congrArg (fun φ : MvPolynomial (OrbitCoord W G) R →+*
      (MvPolynomial (OrbitCoord W G) R ⧸ equationIdeal C.orbitPolynomials) =>
        Spec.map (CommRingCat.ofHom φ))
    C.sectionCellCoordinates_comp_cellCoordinateMap

theorem assemble_totalDegree_le {V : Type u} (C : GateSystem R W G E)
    (w : W → MvPolynomial V R) (hw : ∀ i, (w i).totalDegree ≤ 1)
    (i j : Index W G) : (C.assemble w i j).totalDegree ≤ 1 := by
  rcases i with i | ⟨i,g⟩ <;> rcases j with j | ⟨j,h⟩
  · by_cases hij : i = j <;> simp [assemble, Matrix.diagonal_apply, hij, hw]
  · simp [assemble]
  · simp [assemble]
  · fin_cases i <;> fin_cases j <;> by_cases hgh : g = h <;>
      simp [assemble, Matrix.blockDiagonal_apply, gateBlock, hgh, hw]

theorem affineEquation_totalDegree_le {V : Type u} (e : AffineEquation R W)
    (w : W → MvPolynomial V R) (hw : ∀ i, (w i).totalDegree ≤ 1) :
    (e.eval w).totalDegree ≤ 1 := by
  unfold AffineEquation.eval
  apply (totalDegree_add _ _).trans
  apply max_le
  · simp [MvPolynomial.algebraMap_eq]
  · apply totalDegree_finsetSum_le
    intro i _
    exact (totalDegree_mul _ _).trans (by simpa [MvPolynomial.algebraMap_eq] using hw i)

/-- Every advertised affine equation is a literal polynomial of total degree at most one. -/
theorem orbitAffinePolynomials_totalDegree [Nontrivial R] (C : GateSystem R W G E)
    (q : OrbitAffineEquation W G E) : (C.orbitAffinePolynomials q).totalDegree ≤ 1 := by
  let A : Matrix (Index W G) (Index W G) (MvPolynomial (OrbitCoord W G) R) := (orbitExtract X).1
  let B : Matrix (Index W G) (Index W G) (MvPolynomial (OrbitCoord W G) R) := (orbitExtract X).2
  have hA (i j) : (A i j).totalDegree ≤ 1 := by
    simp [A, orbitExtract, orbitMatrix, Matrix.toBlocks₁₁]
  have hB (i j) : (B i j).totalDegree ≤ 1 := by
    simp [B, orbitExtract, orbitMatrix, Matrix.toBlocks₂₁]
  have hw (i : W) : (wires A i).totalDegree ≤ 1 := hA _ _
  rcases q with ij | ij | ij | e | g
  · exact (totalDegree_sub _ _).trans (by simp [orbitAffinePolynomials])
  · exact (totalDegree_add _ _).trans (by simp [orbitAffinePolynomials])
  · change (A ij.1 ij.2 - C.assemble (wires A) ij.1 ij.2).totalDegree ≤ 1
    exact (totalDegree_sub _ _).trans (max_le (hA _ _) (C.assemble_totalDegree_le _ hw _ _))
  · exact affineEquation_totalDegree_le (C.equations e) (wires A) hw
  · change (wires A (C.output g) - B (Sum.inr (0,g)) (Sum.inr (0,g))).totalDegree ≤ 1
    exact (totalDegree_sub _ _).trans (max_le (hw _) (hB _ _))

end GateSystem

/-- Every finitely presented affine k-scheme is an exact affine-linear section
of the closed affine Lagrangian cell in the smooth maximal square-zero orbit.
The coordinate algebra is preserved, the embedding is an actual closed immersion,
and the algebraic symplectic atlas and cell isotropy are proved on this same host. -/
theorem lagrangian_squareZero_orbit_universality
    (k A : Type u) [Field k] [CommRing A] [Algebra k A]
    [Algebra.FinitePresentation k A] :
    ∃ (W G E : Type u) (_ : Fintype W) (_ : Fintype G) (_ : Fintype E)
      (_ : DecidableEq W) (_ : DecidableEq G) (C : GateSystem k W G E)
      (_ : A ≃ₐ[k] (MvPolynomial (GateSystem.OrbitCoord W G) k ⧸ equationIdeal C.orbitPolynomials)),
      0 < Fintype.card (GateSystem.Index W G) ∧
      Nonempty (Spec (.of A) ≅ Spec (.of
        (MvPolynomial (GateSystem.OrbitCoord W G) k ⧸ equationIdeal C.orbitPolynomials))) ∧
      equationIdeal C.orbitPolynomials = equationIdeal C.orbitAffinePolynomials ⊔
        SquareZeroGeometry.squareZeroIdeal k (GateSystem.Index W G) ∧
      (∀ q, (C.orbitAffinePolynomials q).totalDegree ≤ 1) ∧
      IsClosedImmersion C.sectionToOrbit ∧
      (C.sectionToOrbit ≫ (SquareZeroGeometry.maximalRankOpen k (GateSystem.Index W G)).ι ≫
        SquareZeroGeometry.squareZeroClosedImmersion k (GateSystem.Index W G) =
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (equationIdeal C.orbitPolynomials)))) ∧
      SmoothOfRelativeDimension (2 * Fintype.card (GateSystem.Index W G) ^ 2)
        (SquareZeroGeometry.maximalRankStructureMap k (GateSystem.Index W G)) ∧
      IrreducibleSpace (SquareZeroGeometry.maximalRankScheme k (GateSystem.Index W G)) ∧
      IsClosedImmersion (SquareZeroGeometry.cellMorphism k (GateSystem.Index W G)) ∧
      SmoothOfRelativeDimension (Fintype.card (GateSystem.Index W G) ^ 2)
        (Spec.map (CommRingCat.ofHom
          (algebraMap k (MvPolynomial (GateSystem.Index W G × GateSystem.Index W G) k)))) ∧
      (∃ ω : GlobalSymplectic.AlgebraicSymplecticAtlas k (GateSystem.Index W G),
        SquareZeroGeometry.cellMorphism k (GateSystem.Index W G) =
          Spec.map (CommRingCat.ofHom
            (SquareZeroGeometry.cellChartEval k (GateSystem.Index W G)).toRingHom) ≫
            (ω.orbitChartIso (Equiv.refl _)).inv ≫
              (SquareZeroGeometry.orbitChartOpen k (GateSystem.Index W G) (Equiv.refl _)).ι) ∧
      AffineForms.canonicalTrace (R := k)
        ((SquareZeroGeometry.chartT k (GateSystem.Index W G)).map
          (SquareZeroGeometry.cellChartEval k (GateSystem.Index W G)))
        ((SquareZeroGeometry.chartA k (GateSystem.Index W G)).map
          (SquareZeroGeometry.cellChartEval k (GateSystem.Index W G))) = 0 := by
  obtain ⟨W, G, E, hW, hG, hE, dW, dG, C, hpos, ⟨e⟩⟩ := finitePresentation_orbitSection k A
  refine ⟨W, G, E, hW, hG, hE, dW, dG, C, e, hpos,
    ⟨Scheme.Spec.mapIso e.symm.toRingEquiv.toCommRingCatIso.op⟩, ?_, C.orbitAffinePolynomials_totalDegree,
    C.sectionToOrbit_isClosedImmersion, C.sectionToOrbit_ambient,
    SquareZeroGeometry.maximalRankScheme_dimension k (GateSystem.Index W G),
    inferInstance,
    SquareZeroGeometry.cellMorphism_isClosedImmersion k (GateSystem.Index W G),
    SquareZeroGeometry.cellSource_dimension k (GateSystem.Index W G),
    ⟨GlobalSymplectic.orbitSymplecticAtlas k (GateSystem.Index W G),
      (GlobalSymplectic.orbitSymplecticAtlas k (GateSystem.Index W G)).cellMorphism_factors_identity⟩,
    GlobalSymplectic.cell_pullback_form_zero k (GateSystem.Index W G)⟩
  simpa only [SquareZeroGeometry.squareZeroIdeal, SquareZeroGeometry.genericMatrix,
    GateSystem.orbitMatrix] using C.orbitSectionIdeal_eq


namespace GateSystem
variable {R S W G E : Type u} [CommRing R] [CommRing S] [Algebra R S]
  [Fintype W] [DecidableEq W] [Fintype G] [DecidableEq G] [Fintype E]

/-- Exact algebraic feasibility equivalence for the affine orbit section. -/
theorem feasibility_reduction (C : GateSystem R W G E) :
    (∃ w : W → S, C.Satisfies w) ↔
      ∃ Z : Matrix (Index W G ⊕ Index W G) (Index W G ⊕ Index W G) S,
        C.orbitAffineConstraints (S := S) Z = 0 ∧ InJordanOrbit Z := by
  constructor
  · rintro ⟨w, hw⟩
    let z := C.orbitSolutionEquiv ⟨w, hw⟩
    exact ⟨z.val, (C.orbitSection_iff z.val).mp z.property⟩
  · rintro ⟨z, hz⟩
    let w := C.orbitSolutionEquiv.symm ⟨z, (C.orbitSection_iff z).mpr hz⟩
    exact ⟨w.val, w.property⟩

/-- The compiler uses N=s+2m, and its literal ambient matrix has exactly 4N² entries. -/
theorem orbit_variable_count : Fintype.card (OrbitCoord W G) =
    4 * (Fintype.card W + 2 * Fintype.card G) ^ 2 := by
  simp only [OrbitCoord, Fintype.card_prod, Fintype.card_sum, card_index, Fintype.card_fin]
  ring

/-- Exact count of the affine rows: two chart blocks, one wiring block, input rows and gates. -/
theorem orbit_affine_equation_count : Fintype.card (OrbitAffineEquation W G E) =
    3 * (Fintype.card W + 2 * Fintype.card G) ^ 2 + Fintype.card E + Fintype.card G := by
  simp only [OrbitAffineEquation, Fintype.card_sum, Fintype.card_prod, card_index, Fintype.card_fin]
  ring

/-- The independent graph equations add N² more rows. -/
theorem orbit_total_equation_count : Fintype.card (OrbitEquation W G E) =
    4 * (Fintype.card W + 2 * Fintype.card G) ^ 2 + Fintype.card E + Fintype.card G := by
  simp only [OrbitEquation, MatrixEquation, Fintype.card_sum, Fintype.card_prod, card_index, Fintype.card_fin]
  ring

/-- Each wiring entry is zero or a copy of one input wire; no scalar arithmetic is hidden here. -/
theorem assemble_entry_zero_or_wire (C : GateSystem R W G E) (w : W → S)
    (i j : Index W G) : C.assemble w i j = 0 ∨ ∃ a, C.assemble w i j = w a := by
  have hw (a : W) : w a = 0 ∨ ∃ b, w a = w b := Or.inr ⟨a, rfl⟩
  rcases i with i | ⟨i,g⟩ <;> rcases j with j | ⟨j,h⟩
  · by_cases hij : i = j <;> simp [assemble, Matrix.diagonal_apply, hij, hw]
  · simp [assemble]
  · simp [assemble]
  · fin_cases i <;> fin_cases j <;> by_cases hgh : g = h <;>
      simp [assemble, Matrix.blockDiagonal_apply, gateBlock, hgh, hw]

theorem polynomial_support_card_add {V : Type u} (p q : MvPolynomial V R) :
    (p + q).support.card ≤ p.support.card + q.support.card := by
  classical
  exact (Finset.card_le_card MvPolynomial.support_add).trans (Finset.card_union_le _ _)

theorem polynomial_support_card_sub {V : Type u} (p q : MvPolynomial V R) :
    (p - q).support.card ≤ p.support.card + q.support.card := by
  simpa only [sub_eq_add_neg, MvPolynomial.support_neg] using polynomial_support_card_add p (-q)

theorem polynomial_support_card_C {V : Type u} (c : R) :
    (MvPolynomial.C c : MvPolynomial V R).support.card ≤ 1 := by
  classical
  by_cases hc : c = 0 <;> simp [MvPolynomial.support_C, hc]

theorem polynomial_support_card_C_mul_X {V : Type u} (c : R) (v : V) :
    (MvPolynomial.C c * X v : MvPolynomial V R).support.card ≤ 1 := by
  classical
  rw [MvPolynomial.C_mul_X_eq_monomial]
  exact (Finset.card_le_card MvPolynomial.support_monomial_subset).trans (by simp)

theorem polynomial_support_card_sum {V I : Type u} (s : Finset I) (p : I → MvPolynomial V R) :
    (∑ i ∈ s, p i).support.card ≤ ∑ i ∈ s, (p i).support.card := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact (polynomial_support_card_add _ _).trans (Nat.add_le_add_left ih _)

/-- Input rows retain their original coefficients literally. The indicator sum
also describes cancellation without assuming distinct monomials. -/
theorem orbitAffinePolynomials_input_coeff (C : GateSystem R W G E) (e : E)
    (d : OrbitCoord W G →₀ ℕ) :
    MvPolynomial.coeff d (C.orbitAffinePolynomials (.inr (.inr (.inr (.inl e))))) =
      (if d = 0 then (C.equations e).constant else 0) +
      ∑ i : W, (C.equations e).coeff i *
        (if Finsupp.single (Sum.inl (Sum.inl i), Sum.inl (Sum.inl i)) 1 = d then 1 else 0) := by
  classical
  simp [orbitAffinePolynomials, AffineEquation.eval, wires, orbitExtract, orbitMatrix,
    Matrix.toBlocks₁₁, MvPolynomial.coeff_sum, MvPolynomial.coeff_X', MvPolynomial.coeff_C, eq_comm]

/-- Each literal affine output row has at most `|W|+2` nonzero monomials.
This counts the actual polynomial after duplicate monomials cancel. -/
theorem orbitAffinePolynomials_support_card [Nontrivial R] (C : GateSystem R W G E)
    (q : OrbitAffineEquation W G E) :
    (C.orbitAffinePolynomials q).support.card ≤ Fintype.card W + 2 := by
  classical
  have hx (v : OrbitCoord W G) : (X v : MvPolynomial (OrbitCoord W G) R).support.card ≤ 1 := by
    simp [MvPolynomial.support_X]
  have hw (i : W) : (wires (orbitExtract (W := W) (G := G) (X (R := R))).1 i).support.card ≤ 1 := hx _
  have ha (i j : Index W G) :
      (C.assemble (wires (orbitExtract (W := W) (G := G) (X (R := R))).1) i j).support.card ≤ 1 := by
    rcases C.assemble_entry_zero_or_wire (wires (orbitExtract (W := W) (G := G) (X (R := R))).1) i j with h | ⟨a,h⟩
    · rw [h]; simp
    · rw [h]; exact hw a
  rcases q with ij | ij | ij | e | g
  · exact (polynomial_support_card_sub _ _).trans
      ((Nat.add_le_add (hx _) (polynomial_support_card_C _)).trans (by omega))
  · exact (polynomial_support_card_add _ _).trans
      ((Nat.add_le_add (hx _) (hx _)).trans (by omega))
  · exact (polynomial_support_card_sub _ _).trans
      ((Nat.add_le_add (hx _) (ha ij.1 ij.2)).trans (by omega))
  · change (MvPolynomial.C (C.equations e).constant +
        ∑ i : W, MvPolynomial.C ((C.equations e).coeff i) *
          wires (orbitExtract (W := W) (G := G) (X (R := R))).1 i).support.card ≤ _
    apply (polynomial_support_card_add _ _).trans
    have hs : (∑ i : W, MvPolynomial.C ((C.equations e).coeff i) *
        wires (orbitExtract (W := W) (G := G) (X (R := R))).1 i).support.card ≤ Fintype.card W := by
      apply (polynomial_support_card_sum _ _).trans
      calc
        _ ≤ ∑ _i : W, 1 := Finset.sum_le_sum (fun i _ => polynomial_support_card_C_mul_X _ _)
        _ = _ := by simp
    exact (Nat.add_le_add (polynomial_support_card_C _) hs).trans (by omega)
  · change (wires (orbitExtract (W := W) (G := G) (X (R := R))).1 (C.output g) -
        (orbitExtract (W := W) (G := G) (X (R := R))).2 (Sum.inr (0,g)) (Sum.inr (0,g))).support.card ≤ _
    apply (polynomial_support_card_sub _ _).trans
    have hb : ((orbitExtract (W := W) (G := G) (X (R := R))).2 (Sum.inr (0,g)) (Sum.inr (0,g))).support.card ≤ 1 := by
      simpa only [orbitExtract, Matrix.neg_apply, MvPolynomial.support_neg] using hx
        (Sum.inr (Sum.inr (0,g)), Sum.inl (Sum.inr (0,g)))
    exact (Nat.add_le_add (hw _) hb).trans (by omega)

/-- Polynomial sparse output-size bound for all literal affine rows. -/
theorem orbitAffinePolynomials_sparse_size [Nontrivial R] (C : GateSystem R W G E) :
    (∑ q, (C.orbitAffinePolynomials q).support.card) ≤
      (3 * (Fintype.card W + 2 * Fintype.card G) ^ 2 + Fintype.card E + Fintype.card G) *
        (Fintype.card W + 2) := by
  calc
    _ ≤ ∑ _q : OrbitAffineEquation W G E, (Fintype.card W + 2) :=
      Finset.sum_le_sum (fun q _ => C.orbitAffinePolynomials_support_card q)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul,
      orbit_affine_equation_count]

theorem coefficient_X_zero_or_one {V : Type u} (v : V) (d : V →₀ ℕ) :
    MvPolynomial.coeff d (X v : MvPolynomial V R) = 0 ∨
      MvPolynomial.coeff d (X v : MvPolynomial V R) = 1 := by
  classical
  simp only [MvPolynomial.coeff_X']
  split_ifs <;> simp

theorem coefficient_sub_binary {V : Type u} (p q : MvPolynomial V R) (d : V →₀ ℕ)
    (hp : MvPolynomial.coeff d p = 0 ∨ MvPolynomial.coeff d p = 1)
    (hq : MvPolynomial.coeff d q = 0 ∨ MvPolynomial.coeff d q = 1) :
    MvPolynomial.coeff d (p-q) = 0 ∨ MvPolynomial.coeff d (p-q) = 1 ∨
      MvPolynomial.coeff d (p-q) = -1 := by
  rw [MvPolynomial.coeff_sub]
  rcases hp with hp | hp <;> rcases hq with hq | hq <;> simp [hp,hq]

theorem coefficient_X_add_distinct {V : Type u} (a b : V) (hab : a ≠ b) (d : V →₀ ℕ) :
    MvPolynomial.coeff d (X a + X b : MvPolynomial V R) = 0 ∨
      MvPolynomial.coeff d (X a + X b : MvPolynomial V R) = 1 := by
  classical
  simp only [MvPolynomial.coeff_add, MvPolynomial.coeff_X']
  by_cases ha : Finsupp.single a 1 = d
  · have hb : Finsupp.single b 1 ≠ d := fun hb =>
      hab (Finsupp.single_left_injective (one_ne_zero : (1 : ℕ) ≠ 0) (ha.trans hb.symm))
    simp [ha,hb]
  · split_ifs <;> simp_all

/-- Injective wire coordinates prevent coefficient aggregation in original input rows. -/
theorem orbitAffinePolynomials_input_provenance (C : GateSystem R W G E) (e : E)
    (d : OrbitCoord W G →₀ ℕ) :
    let c := MvPolynomial.coeff d (C.orbitAffinePolynomials (.inr (.inr (.inr (.inl e)))))
    c = 0 ∨ c = (C.equations e).constant ∨ ∃ i, c = (C.equations e).coeff i := by
  classical
  dsimp only
  rw [C.orbitAffinePolynomials_input_coeff]
  by_cases hd : d = 0
  · simp [hd]
  · by_cases hi : ∃ i : W, Finsupp.single
        ((Sum.inl (Sum.inl i), Sum.inl (Sum.inl i)) : OrbitCoord W G) 1 = d
    · obtain ⟨i, rfl⟩ := hi
      right; right
      refine ⟨i, ?_⟩
      simp [Finsupp.single_left_inj (one_ne_zero : (1 : ℕ) ≠ 0)]
    · left
      simp only [hd, if_false, zero_add]
      apply Finset.sum_eq_zero
      intro i _
      simp [show Finsupp.single ((Sum.inl (Sum.inl i), Sum.inl (Sum.inl i)) : OrbitCoord W G) 1 ≠ d
        from fun h => hi ⟨i,h⟩]

/-- Every coefficient is either `0,1,-1` or an unchanged original affine
coefficient/constant. The proof includes duplicate-wire cancellation. -/
theorem orbitAffinePolynomials_coefficient_provenance (C : GateSystem R W G E)
    (q : OrbitAffineEquation W G E) (d : OrbitCoord W G →₀ ℕ) :
    let c := MvPolynomial.coeff d (C.orbitAffinePolynomials q)
    c = 0 ∨ c = 1 ∨ c = -1 ∨
      ∃ e, c = (C.equations e).constant ∨ ∃ i, c = (C.equations e).coeff i := by
  classical
  dsimp only
  have lift {c : R} (h : c = 0 ∨ c = 1 ∨ c = -1) :
      c = 0 ∨ c = 1 ∨ c = -1 ∨ ∃ e, c = (C.equations e).constant ∨ ∃ i, c = (C.equations e).coeff i := by
    rcases h with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
  rcases q with ij | ij | ij | e | g
  · apply lift
    apply coefficient_sub_binary _ _ _ (coefficient_X_zero_or_one _ _)
    by_cases hij : ij.1 = ij.2 <;> by_cases hd : (0 : OrbitCoord W G →₀ ℕ) = d <;>
      simp [Matrix.one_apply, hij, MvPolynomial.coeff_one, hd]
  · apply lift
    have h := coefficient_X_add_distinct (R := R)
      ((Sum.inr ij.1, Sum.inr ij.2) : OrbitCoord W G)
      (Sum.inl ij.1, Sum.inl ij.2) (by simp) d
    exact h.imp_right Or.inl
  · apply lift
    apply coefficient_sub_binary _ _ _ (coefficient_X_zero_or_one _ _)
    rcases C.assemble_entry_zero_or_wire
        (wires (orbitExtract (W := W) (G := G) (X (R := R))).1) ij.1 ij.2 with h | ⟨a,h⟩
    · rw [h]; simp
    · rw [h]; exact coefficient_X_zero_or_one _ _
  · rcases C.orbitAffinePolynomials_input_provenance e d with h | h | ⟨i,h⟩
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inr ⟨e, Or.inl h⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨e, Or.inr ⟨i,h⟩⟩))
  · apply lift
    have h := coefficient_X_add_distinct (R := R)
      ((Sum.inl (Sum.inl (C.output g)), Sum.inl (Sum.inl (C.output g))) : OrbitCoord W G)
      (Sum.inr (Sum.inr (0,g)), Sum.inl (Sum.inr (0,g))) (by simp) d
    simpa [orbitAffinePolynomials, wires, orbitExtract, Matrix.toBlocks₁₁,
      Matrix.toBlocks₂₁, orbitMatrix, sub_neg_eq_add] using h.imp_right Or.inl

/-- A coefficient-size bound for any chosen scalar encoding measure. -/
theorem orbitAffinePolynomials_coefficient_size (C : GateSystem R W G E)
    (size : R → ℕ) (B : ℕ) (h0 : size 0 ≤ B) (h1 : size 1 ≤ B) (hm : size (-1) ≤ B)
    (hc : ∀ e, size (C.equations e).constant ≤ B)
    (ha : ∀ e i, size ((C.equations e).coeff i) ≤ B)
    (q : OrbitAffineEquation W G E) (d : OrbitCoord W G →₀ ℕ) :
    size (MvPolynomial.coeff d (C.orbitAffinePolynomials q)) ≤ B := by
  rcases C.orbitAffinePolynomials_coefficient_provenance q d with h | h | h | ⟨e,h | ⟨i,h⟩⟩
  · simpa only [h] using h0
  · simpa only [h] using h1
  · simpa only [h] using hm
  · simpa only [h] using hc e
  · simpa only [h] using ha e i

/-- Binary digits of the reduced numerator and denominator, including a sign bit.
Zero is allocated one numerator digit. -/
def rationalCoefficientBitSize (r : ℚ) : ℕ := r.num.natAbs.log2 + r.den.log2 + 3

/-- The rational coefficients have no bit-size growth beyond the input bound
and the three bits allocated to `0,1,-1`. This is an encoding-size statement,
not a machine-runtime assertion. -/
theorem orbitAffinePolynomials_rational_bitSize
    (W G E : Type) [Fintype W] [DecidableEq W] [Fintype G] [DecidableEq G] [Fintype E]
    (C : GateSystem ℚ W G E) (B : ℕ) (hB : 3 ≤ B)
    (hc : ∀ e, rationalCoefficientBitSize (C.equations e).constant ≤ B)
    (ha : ∀ e i, rationalCoefficientBitSize ((C.equations e).coeff i) ≤ B)
    (q : OrbitAffineEquation W G E) (d : OrbitCoord W G →₀ ℕ) :
    rationalCoefficientBitSize (MvPolynomial.coeff d (C.orbitAffinePolynomials q)) ≤ B := by
  apply C.orbitAffinePolynomials_coefficient_size rationalCoefficientBitSize B
  · simpa [rationalCoefficientBitSize] using hB
  · simpa [rationalCoefficientBitSize] using hB
  · simpa [rationalCoefficientBitSize] using hB
  · exact hc
  · exact ha

end GateSystem
end
end Universality

namespace Universality.FiniteDiagram.CircuitDiagram
noncomputable section
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry MvPolynomial
universe u
variable {J R S : Type u} [Category.{u} J] [Fintype J]
  [∀ i j : J, Fintype (i ⟶ j)] [CommRing R] [DecidableEq R]
  [CommRing S] [Algebra R S] {V Q : J → Type u}
  [∀ j, DecidableEq (V j)] [∀ j, Fintype (V j)] [∀ j, Fintype (Q j)]
variable (D : CircuitDiagram (J := J) (R := R) (V := V) (Q := Q))

abbrev MatrixIndex (i : J) := GateSystem.Index (D.Wire i) (D.Wire i)
abbrev AmbientMatrix (i : J) (S : Type u) :=
  Matrix (D.MatrixIndex i ⊕ D.MatrixIndex i) (D.MatrixIndex i ⊕ D.MatrixIndex i) S
abbrev OrbitRing (i : J) :=
  MvPolynomial (GateSystem.OrbitCoord (D.Wire i) (D.Wire i)) R ⧸
    equationIdeal (D.gates i).orbitPolynomials

/-- The actual linear arrow on all four blocks of the full ambient matrix space. -/
def ambientMap {i j} (α : i ⟶ j) : D.AmbientMatrix i S →ₗ[S] D.AmbientMatrix j S :=
  matrixBlockLift (D.matrixMap α)

@[simp] theorem ambientMap_id (i : J) : D.ambientMap (S := S) (𝟙 i) = LinearMap.id := by
  simp [ambientMap, matrixBlockLift_id]

@[simp] theorem ambientMap_comp {i j k} (α : i ⟶ j) (β : j ⟶ k) :
    (D.ambientMap (S := S) β).comp (D.ambientMap α) = D.ambientMap (α ≫ β) := by
  rw [ambientMap, ambientMap, matrixBlockLift_comp, matrixMap_comp]
  rfl

theorem ambientMap_assemble {i j} (α : i ⟶ j) (w : D.Wire i → S) :
    D.ambientMap α (iota ((D.gates i).assemble w)
      ((D.gates i).assemble w * (D.gates i).assemble w)) =
      iota ((D.gates j).assemble (projection S (fun j => (D.presentation j).Wire) α w))
        ((D.gates j).assemble (projection S (fun j => (D.presentation j).Wire) α w) *
          (D.gates j).assemble (projection S (fun j => (D.presentation j).Wire) α w)) := by
  rw [ambientMap, matrixBlockLift_iota _ (D.matrixMap_one α),
    matrixMap_assemble, matrixMap_assemble_square]

theorem ambientMap_preserves {i j} (α : i ⟶ j) (Z : D.AmbientMatrix i S)
    (hZ : (D.gates i).OrbitSection Z) : (D.gates j).OrbitSection (D.ambientMap α Z) := by
  let w := (D.gates i).orbitSolutionEquiv.symm ⟨Z, hZ⟩
  have hz : iota ((D.gates i).assemble w.val)
      ((D.gates i).assemble w.val * (D.gates i).assemble w.val) = Z :=
    congrArg Subtype.val ((D.gates i).orbitSolutionEquiv.apply_symm_apply ⟨Z,hZ⟩)
  rw [← hz, D.ambientMap_assemble]
  exact ((D.gates j).orbitSolutionEquiv
    ⟨_, D.projection_satisfies α w.val w.property⟩).property

theorem ambientMap_natural {T : Type u} [CommRing T] [Algebra R T]
    (φ : S →ₐ[R] T) {i j} (α : i ⟶ j) (Z : D.AmbientMatrix i S) :
    (D.ambientMap α Z).map φ = D.ambientMap α (Z.map φ) := by
  exact matrixBlockLift_map φ.toRingHom (D.matrixMap α) (D.matrixMap α)
    (fun A => GateSystem.matrixPullback_map φ.toRingHom _ _ A) Z

/-- The restriction to the literal section coordinate rings. -/
def orbitMap {i j} (α : i ⟶ j) : D.OrbitRing j →ₐ[R] D.OrbitRing i :=
  solutionLift (D.gates j).orbitPolynomials
    (fun ij => D.ambientMap α
      (GateSystem.orbitMatrix (universalSolution (D.gates i).orbitPolynomials)) ij.1 ij.2)
    (((D.gates j).orbitPolynomials_orbit_iff _).mpr
      (D.ambientMap_preserves α _ (((D.gates i).orbitPolynomials_orbit_iff _).mp
        (universalSolution_satisfies _))))

@[simp] theorem orbitMap_generator {i j} (α : i ⟶ j)
    (v : GateSystem.OrbitCoord (D.Wire j) (D.Wire j)) :
    D.orbitMap α (universalSolution (D.gates j).orbitPolynomials v) =
      D.ambientMap α (GateSystem.orbitMatrix
        (universalSolution (D.gates i).orbitPolynomials)) v.1 v.2 := by
  simp [orbitMap]

theorem orbitUniversal_map {i j} (α : i ⟶ j) :
    (GateSystem.orbitMatrix (universalSolution (D.gates j).orbitPolynomials)).map (D.orbitMap α) =
      D.ambientMap α (GateSystem.orbitMatrix (universalSolution (D.gates i).orbitPolynomials)) := by
  ext a b
  exact D.orbitMap_generator α (a,b)

@[simp] theorem orbitMap_id (i : J) : D.orbitMap (𝟙 i) = AlgHom.id R (D.OrbitRing i) := by
  apply quotientAlgHom_ext (D.gates i).orbitPolynomials
  intro v
  simp [GateSystem.orbitMatrix]

@[simp] theorem orbitMap_comp {i j k} (α : i ⟶ j) (β : j ⟶ k) :
    (D.orbitMap α).comp (D.orbitMap β) = D.orbitMap (α ≫ β) := by
  apply quotientAlgHom_ext (D.gates k).orbitPolynomials
  intro v
  simp only [AlgHom.comp_apply, orbitMap_generator]
  have h := D.ambientMap_natural (D.orbitMap α) β
    (GateSystem.orbitMatrix (universalSolution (D.gates j).orbitPolynomials))
  rw [D.orbitUniversal_map] at h
  have hc := DFunLike.congr_fun (D.ambientMap_comp (S := D.OrbitRing i) α β)
    (GateSystem.orbitMatrix (universalSolution (D.gates i).orbitPolynomials))
  exact congrFun (congrFun (h.trans hc) v.1) v.2

abbrev AmbientRing (i : J) := MvPolynomial (GateSystem.OrbitCoord (D.Wire i) (D.Wire i)) R

/-- The coordinate pullback of the full ambient linear arrow. -/
def ambientPolynomialMap {i j} (α : i ⟶ j) : D.AmbientRing j →ₐ[R] D.AmbientRing i :=
  aeval (fun ij => D.ambientMap α (GateSystem.orbitMatrix X) ij.1 ij.2)

theorem ambientPolynomialMap_matrix {i j} (α : i ⟶ j) :
    (GateSystem.orbitMatrix (X : _ → D.AmbientRing j)).map (D.ambientPolynomialMap α) =
      D.ambientMap α (GateSystem.orbitMatrix (X : _ → D.AmbientRing i)) := by
  ext a b
  simp [ambientPolynomialMap, GateSystem.orbitMatrix]

@[simp] theorem ambientPolynomialMap_id (i : J) :
    D.ambientPolynomialMap (𝟙 i) = AlgHom.id R (D.AmbientRing i) := by
  ext v
  simp [ambientPolynomialMap, GateSystem.orbitMatrix]

@[simp] theorem ambientPolynomialMap_comp {i j k} (α : i ⟶ j) (β : j ⟶ k) :
    (D.ambientPolynomialMap α).comp (D.ambientPolynomialMap β) =
      D.ambientPolynomialMap (α ≫ β) := by
  apply MvPolynomial.algHom_ext
  intro v
  simp only [AlgHom.comp_apply, ambientPolynomialMap, aeval_X]
  have h := D.ambientMap_natural (D.ambientPolynomialMap α) β
    (GateSystem.orbitMatrix (X : _ → D.AmbientRing j))
  rw [D.ambientPolynomialMap_matrix] at h
  have hc := DFunLike.congr_fun (D.ambientMap_comp (S := D.AmbientRing i) α β)
    (GateSystem.orbitMatrix (X : _ → D.AmbientRing i))
  exact congrFun (congrFun (h.trans hc) v.1) v.2

/-- The scheme inclusion square commutes as an equality of coordinate algebra maps. -/
theorem orbitMap_quotient {i j} (α : i ⟶ j) :
    (D.orbitMap α).comp (Ideal.Quotient.mkₐ R (equationIdeal (D.gates j).orbitPolynomials)) =
      (Ideal.Quotient.mkₐ R (equationIdeal (D.gates i).orbitPolynomials)).comp
        (D.ambientPolynomialMap α) := by
  ext v
  change D.orbitMap α (universalSolution (D.gates j).orbitPolynomials v) = _
  rw [D.orbitMap_generator]
  simp only [AlgHom.comp_apply, ambientPolynomialMap, aeval_X]
  have h := D.ambientMap_natural
    (Ideal.Quotient.mkₐ R (equationIdeal (D.gates i).orbitPolynomials)) α
      (GateSystem.orbitMatrix (X : _ → D.AmbientRing i))
  exact (congrFun (congrFun h v.1) v.2).symm

def orbitAlgebraFunctor : Jᵒᵖ ⥤ CommAlgCat R where
  obj i := CommAlgCat.of R (D.OrbitRing i.unop)
  map α := CommAlgCat.ofHom (D.orbitMap α.unop)
  map_id i := by
    apply CommAlgCat.hom_ext
    exact D.orbitMap_id i.unop
  map_comp α β := by
    apply CommAlgCat.hom_ext
    exact (D.orbitMap_comp β.unop α.unop).symm

def ambientAlgebraFunctor : Jᵒᵖ ⥤ CommAlgCat R where
  obj i := CommAlgCat.of R (D.AmbientRing i.unop)
  map α := CommAlgCat.ofHom (D.ambientPolynomialMap α.unop)
  map_id i := by
    apply CommAlgCat.hom_ext
    exact D.ambientPolynomialMap_id i.unop
  map_comp α β := by
    apply CommAlgCat.hom_ext
    exact (D.ambientPolynomialMap_comp β.unop α.unop).symm

/-- A natural closed section inclusion for the whole finite diagram. -/
def quotientNatTrans : D.ambientAlgebraFunctor ⟶ D.orbitAlgebraFunctor where
  app i := CommAlgCat.ofHom (Ideal.Quotient.mkₐ R (equationIdeal (D.gates i.unop).orbitPolynomials))
  naturality := by
    intro i j α
    apply CommAlgCat.hom_ext
    exact (D.orbitMap_quotient α.unop).symm

def gateOrbitAlgEquiv (i : J) :
    (MvPolynomial (D.Wire i) R ⧸ equationIdeal (D.gates i).polynomials) ≃ₐ[R] D.OrbitRing i :=
  (D.gates i).matrixCoordinateAlgEquiv.trans (D.gates i).orbitCoordinateAlgEquiv

@[simp] theorem gateOrbitAlgEquiv_generator (i : J) (w : D.Wire i) :
    D.gateOrbitAlgEquiv i (universalSolution (D.gates i).polynomials w) =
      universalSolution (D.gates i).orbitPolynomials
        (Sum.inl (Sum.inl w), Sum.inl (Sum.inl w)) := by
  simp [gateOrbitAlgEquiv, GateSystem.matrixCoordinateAlgEquiv, GateSystem.orbitCoordinateAlgEquiv,
    GateSystem.wires, GateSystem.decode, GateSystem.encode, GateSystem.orbitExtract,
    GateSystem.orbitMatrix, Matrix.toBlocks₁₁]

theorem gateOrbitAlgEquiv_natural {i j} (α : i ⟶ j) :
    (D.gateOrbitAlgEquiv i).toAlgHom.comp (D.copiedMap α) =
      (D.orbitMap α).comp (D.gateOrbitAlgEquiv j).toAlgHom := by
  apply quotientAlgHom_ext (D.gates j).polynomials
  intro w
  simp only [AlgHom.comp_apply, copiedMap_generator, AlgEquiv.coe_algHom,
    gateOrbitAlgEquiv_generator, orbitMap_generator]
  simp [ambientMap, matrixBlockLift, matrixMap, GateSystem.matrixPullback,
    GateSystem.blockLabel, GateSystem.indexMap, wireMap, copy, GateSystem.orbitMatrix]
  rfl

def orbitSchemeFunctor : J ⥤ Scheme :=
  (D.orbitAlgebraFunctor ⋙ forget₂ (CommAlgCat R) CommRingCat).rightOp ⋙ Scheme.Spec

def ambientSchemeFunctor : J ⥤ Scheme :=
  (D.ambientAlgebraFunctor ⋙ forget₂ (CommAlgCat R) CommRingCat).rightOp ⋙ Scheme.Spec

/-- Actual commuting closed embeddings of section schemes into ambient affine spaces. -/
def sectionInclusion : D.orbitSchemeFunctor ⟶ D.ambientSchemeFunctor :=
  whiskerRight (whiskerRight D.quotientNatTrans (forget₂ (CommAlgCat R) CommRingCat)).rightOp Scheme.Spec

theorem sectionInclusion_isClosedImmersion (i : J) :
    IsClosedImmersion (D.sectionInclusion.app i) := by
  exact IsClosedImmersion.spec_of_surjective
    (CommRingCat.ofHom (Ideal.Quotient.mk (equationIdeal (D.gates i).orbitPolynomials)))
      Ideal.Quotient.mk_surjective

end
end Universality.FiniteDiagram.CircuitDiagram

namespace Universality.FiniteDiagram
noncomputable section
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry MvPolynomial Opposite
universe u
variable {J R : Type u} [Category.{u} J] [Fintype J]
  [∀ i j : J, Fintype (i ⟶ j)] [CommRing R] [DecidableEq R]
variable (F : Jᵒᵖ ⥤ CommAlgCat.{u} R)
  (P : ∀ i : J, FinitePolynomialPresentation R (F.obj (op i)))
  [∀ i, DecidableEq (P i).Variable]

def ofAlgebraDiagramOrbitAlgEquiv (i : J) :
    F.obj (op i) ≃ₐ[R] (ofAlgebraDiagram F P).OrbitRing i :=
  (ofAlgebraDiagramCoordinateAlgEquiv F P i).trans ((ofAlgebraDiagram F P).gateOrbitAlgEquiv i)

theorem ofAlgebraDiagramOrbitAlgEquiv_natural {i j} (α : i ⟶ j) :
    (ofAlgebraDiagramOrbitAlgEquiv F P i).toAlgHom.comp (F.map α.op).hom =
      ((ofAlgebraDiagram F P).orbitMap α).comp
        (ofAlgebraDiagramOrbitAlgEquiv F P j).toAlgHom := by
  let D := ofAlgebraDiagram F P
  change ((D.gateOrbitAlgEquiv i).toAlgHom.comp
    (ofAlgebraDiagramCoordinateAlgEquiv F P i).toAlgHom).comp (F.map α.op).hom = _
  rw [AlgHom.comp_assoc, ofAlgebraDiagramCoordinateAlgEquiv_natural,
    ← AlgHom.comp_assoc, D.gateOrbitAlgEquiv_natural, AlgHom.comp_assoc]
  rfl

/-- An isomorphism of the entire original algebra diagram with its literal orbit sections. -/
def ofAlgebraDiagramOrbitIso : F ≅ (ofAlgebraDiagram F P).orbitAlgebraFunctor :=
  NatIso.ofComponents (fun i => CommAlgCat.isoMk (ofAlgebraDiagramOrbitAlgEquiv F P i.unop)) (by
    intro i j α
    apply CommAlgCat.hom_ext
    exact ofAlgebraDiagramOrbitAlgEquiv_natural F P α.unop)

def algebraDiagramSpec (F : Jᵒᵖ ⥤ CommAlgCat.{u} R) : J ⥤ Scheme :=
  (F ⋙ forget₂ (CommAlgCat R) CommRingCat).rightOp ⋙ Scheme.Spec

/-- The corresponding natural isomorphism of affine scheme diagrams. -/
def ofAlgebraDiagramOrbitSchemeIso :
    algebraDiagramSpec F ≅ (ofAlgebraDiagram F P).orbitSchemeFunctor :=
  isoWhiskerRight
    ((leftOpRightOpEquiv (C := J) (D := CommRingCat)).functor.mapIso
      (isoWhiskerRight (ofAlgebraDiagramOrbitIso F P).symm (forget₂ (CommAlgCat R) CommRingCat)).op)
    Scheme.Spec

/-- Every finite diagram of finitely presented algebras admits an exact simultaneous
orbit-section realization. The ambient arrows are strict linear maps on full matrix
spaces; the isomorphism is natural, and all ambient inclusions are closed immersions. -/
theorem finiteDiagram_orbit_universality
    [∀ i : Jᵒᵖ, Algebra.FinitePresentation R (F.obj i)] :
    ∃ (V Q : J → Type u) (_ : ∀ i, Fintype (V i)) (_ : ∀ i, Fintype (Q i))
      (_ : ∀ i, DecidableEq (V i))
      (D : CircuitDiagram (J := J) (R := R) (V := V) (Q := Q)),
      Nonempty (F ≅ D.orbitAlgebraFunctor) ∧
      Nonempty (algebraDiagramSpec F ≅ D.orbitSchemeFunctor) ∧
      (∀ i, 0 < Fintype.card (D.MatrixIndex i)) ∧
      (∀ i, IsClosedImmersion (D.sectionInclusion.app i)) := by
  classical
  let P : ∀ i : J, FinitePolynomialPresentation R (F.obj (op i)) :=
    fun i => FinitePolynomialPresentation.choose R (F.obj (op i))
  let D := ofAlgebraDiagram F P
  exact ⟨(fun i => (P i).Variable), (fun i => (P i).Relation), inferInstance, inferInstance,
    inferInstance, D, ⟨ofAlgebraDiagramOrbitIso F P⟩, ⟨ofAlgebraDiagramOrbitSchemeIso F P⟩,
    D.index_card_pos, D.sectionInclusion_isClosedImmersion⟩

end
end Universality.FiniteDiagram

namespace Universality
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MvPolynomial
universe u

theorem quotient_eq_sup_isPullback (R : Type u) [CommRing R] (I J K : Ideal R)
    (h : K = I ⊔ J) :
    IsPullback
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor (show I ≤ K by rw [h]; exact le_sup_left))))
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor (show J ≤ K by rw [h]; exact le_sup_right))))
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) := by
  subst K
  exact quotient_sup_isPullback R I J

namespace GateSystem
variable {R W G E : Type u} [CommRing R] [Fintype W] [DecidableEq W]
  [Fintype G] [DecidableEq G] [Fintype E]

theorem orbitSectionIdeal_eq_squareZero (C : GateSystem R W G E) :
    equationIdeal C.orbitPolynomials = equationIdeal C.orbitAffinePolynomials ⊔
      SquareZeroGeometry.squareZeroIdeal R (Index W G) := by
  simpa only [SquareZeroGeometry.squareZeroIdeal, SquareZeroGeometry.genericMatrix, orbitMatrix]
    using C.orbitSectionIdeal_eq

def affineInclusion (C : GateSystem R W G E) :
    Spec (.of (MvPolynomial (OrbitCoord W G) R ⧸ equationIdeal C.orbitAffinePolynomials)) ⟶
      Spec (.of (MvPolynomial (OrbitCoord W G) R)) :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (equationIdeal C.orbitAffinePolynomials)))

def sectionToAffine (C : GateSystem R W G E) :
    Spec (.of (MvPolynomial (OrbitCoord W G) R ⧸ equationIdeal C.orbitPolynomials)) ⟶
      Spec (.of (MvPolynomial (OrbitCoord W G) R ⧸ equationIdeal C.orbitAffinePolynomials)) :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor (show
    equationIdeal C.orbitAffinePolynomials ≤ equationIdeal C.orbitPolynomials by
      rw [C.orbitSectionIdeal_eq_squareZero]; exact le_sup_left)))

def sectionToSquareZero (C : GateSystem R W G E) :
    Spec (.of (MvPolynomial (OrbitCoord W G) R ⧸ equationIdeal C.orbitPolynomials)) ⟶
      SquareZeroGeometry.squareZeroScheme R (Index W G) :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor (show
    SquareZeroGeometry.squareZeroIdeal R (Index W G) ≤ equationIdeal C.orbitPolynomials by
      rw [C.orbitSectionIdeal_eq_squareZero]; exact le_sup_right)))

theorem sectionToSquareZero_ambient (C : GateSystem R W G E) :
    C.sectionToSquareZero ≫ SquareZeroGeometry.squareZeroClosedImmersion R (Index W G) =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (equationIdeal C.orbitPolynomials))) := by
  unfold sectionToSquareZero SquareZeroGeometry.squareZeroClosedImmersion
  exact (Spec.map_comp _ _).symm

theorem sectionToOrbit_squareZero (C : GateSystem R W G E) :
    C.sectionToOrbit ≫ (SquareZeroGeometry.maximalRankOpen R (Index W G)).ι =
      C.sectionToSquareZero := by
  apply (cancel_mono (SquareZeroGeometry.squareZeroClosedImmersion R (Index W G))).mp
  rw [Category.assoc, C.sectionToOrbit_ambient, C.sectionToSquareZero_ambient]

/-- Literal fiber-product semantics of the affine section inside the square-zero scheme. -/
theorem section_squareZero_isPullback (C : GateSystem R W G E) :
    IsPullback C.sectionToAffine C.sectionToSquareZero C.affineInclusion
      (SquareZeroGeometry.squareZeroClosedImmersion R (Index W G)) :=
  quotient_eq_sup_isPullback _ _ _ _ C.orbitSectionIdeal_eq_squareZero

/-- The same exact section is the scheme-theoretic intersection with the smooth orbit. -/
theorem sectionToOrbit_isPullback (C : GateSystem R W G E) :
    IsPullback C.sectionToAffine C.sectionToOrbit C.affineInclusion
      ((SquareZeroGeometry.maximalRankOpen R (Index W G)).ι ≫
        SquareZeroGeometry.squareZeroClosedImmersion R (Index W G)) := by
  let U : (SquareZeroGeometry.squareZeroScheme R (Index W G)).Opens :=
    SquareZeroGeometry.maximalRankOpen R (Index W G)
  letI : IsOpenImmersion U.ι := inferInstance
  letI : Mono U.ι := inferInstance
  let g : Spec (.of (MvPolynomial (OrbitCoord W G) R ⧸ equationIdeal C.orbitPolynomials)) ⟶
      U.toScheme := C.sectionToOrbit
  have h : IsPullback C.sectionToAffine (g ≫ U.ι) C.affineInclusion
      (SquareZeroGeometry.squareZeroClosedImmersion R (Index W G)) := by
    change IsPullback C.sectionToAffine
      (C.sectionToOrbit ≫ (SquareZeroGeometry.maximalRankOpen R (Index W G)).ι)
      C.affineInclusion (SquareZeroGeometry.squareZeroClosedImmersion R (Index W G))
    rw [C.sectionToOrbit_squareZero]
    exact C.section_squareZero_isPullback
  exact isPullback_restrict_mono C.sectionToAffine g U.ι C.affineInclusion
    (SquareZeroGeometry.squareZeroClosedImmersion R (Index W G)) h

/-- It is also the literal fiber product with the closed Lagrangian cell. -/
theorem sectionToCell_isPullback (C : GateSystem R W G E) :
    IsPullback C.sectionToAffine C.sectionToCell C.affineInclusion
      (SquareZeroGeometry.cellMorphism R (Index W G) ≫
        (SquareZeroGeometry.maximalRankOpen R (Index W G)).ι ≫
          SquareZeroGeometry.squareZeroClosedImmersion R (Index W G)) := by
  letI := SquareZeroGeometry.cellMorphism_isClosedImmersion R (Index W G)
  exact isPullback_restrict_mono _ _ _ _ _ C.sectionToOrbit_isPullback

end GateSystem
end
end Universality
