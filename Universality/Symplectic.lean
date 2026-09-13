import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Matrix.Block
import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring
import Mathlib.RingTheory.Derivation.Lie
import Mathlib.RingTheory.Kaehler.Polynomial
import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.RingTheory.Localization.Module
import Universality.MatrixOrbit
import Universality.Scheme

/-!
# The trace form and closed algebraic forms on the orbit charts

The KKS form is constructed on the image of `X ↦ XZ - ZX` over commutative rings.
The lower-cell tangent subspaces are proved equal to their symplectic orthogonals.
On localized polynomial chart algebras, the canonical form on algebraic derivations
is closed under the standard Cartan exterior derivative and gives an equivalence
with the module dual. Its KKS identification yields compatibility under constant
changes of ambient basis. The final namespace assembles these forms on the actual
scheme open cover, using the actual intersection algebras and restriction maps.
-/

namespace Universality
namespace Symplectic

open Matrix

variable {k n : Type*} [CommRing k] [Fintype n] [DecidableEq n]

def comm (X Y : Matrix n n k) : Matrix n n k := X * Y - Y * X

def traceForm (Z X Y : Matrix n n k) : k := Matrix.trace (Z * comm X Y)

omit [DecidableEq n] in
theorem traceForm_eq (Z X Y : Matrix n n k) :
    traceForm Z X Y = Matrix.trace (comm Z X * Y) := by
  simp only [traceForm, comm, mul_sub, sub_mul, trace_sub]
  rw [← Matrix.mul_assoc Z X Y, ← Matrix.mul_assoc Z Y X, Matrix.trace_mul_cycle Z Y X]

omit [DecidableEq n] in
theorem traceForm_alt (Z X : Matrix n n k) : traceForm Z X X = 0 := by
  simp [traceForm, comm]

omit [DecidableEq n] in
theorem traceForm_swap (Z X Y : Matrix n n k) : traceForm Z X Y = -traceForm Z Y X := by
  simp only [traceForm, comm, mul_sub, trace_sub]
  abel

omit [DecidableEq n] in
theorem comm_swap (X Y : Matrix n n k) : comm X Y = -comm Y X := by
  unfold comm
  abel

omit [DecidableEq n] in
theorem traceForm_wellDefined_left (Z X X' Y : Matrix n n k)
    (h : comm X Z = comm X' Z) : traceForm Z X Y = traceForm Z X' Y := by
  rw [traceForm_eq, traceForm_eq, comm_swap Z X, comm_swap Z X', h]

omit [DecidableEq n] in
theorem traceForm_wellDefined_right (Z X Y Y' : Matrix n n k)
    (h : comm Y Z = comm Y' Z) : traceForm Z X Y = traceForm Z X Y' := by
  rw [traceForm_swap Z X Y, traceForm_swap Z X Y']
  rw [traceForm_wellDefined_left Z Y Y' X h]

omit [DecidableEq n] in
theorem traceForm_radical (Z X : Matrix n n k) :
    (∀ Y, traceForm Z X Y = 0) ↔ comm X Z = 0 := by
  constructor
  · intro h
    have hz : comm Z X = 0 := Matrix.ext_iff_trace_mul_right.mpr (by
      intro Y
      simpa only [zero_mul, trace_zero, ← traceForm_eq] using h Y)
    rw [comm_swap, hz, neg_zero]
  · intro h Y
    rw [traceForm_eq, comm_swap Z X, h, neg_zero, zero_mul, trace_zero]

def commLinear (Z : Matrix n n k) : Matrix n n k →ₗ[k] Matrix n n k where
  toFun X := comm X Z
  map_add' X Y := by simp [comm, add_mul, mul_add]; abel
  map_smul' a X := by simp [comm, smul_sub]

abbrev Tangent (Z : Matrix n n k) := LinearMap.range (commLinear Z)

/-- The linearization of the square-zero equations. -/
def squareLinear (Z : Matrix n n k) : Matrix n n k →ₗ[k] Matrix n n k where
  toFun V := Z * V + V * Z
  map_add' V W := by simp [mul_add, add_mul]; abel
  map_smul' a V := by simp [smul_add]

/-- On the orbit, the commutator space is exactly the kernel of the linearized
square equations, over arbitrary commutative coefficient rings. -/
theorem tangent_eq_linearizedKernel {Z : Matrix (n ⊕ n) (n ⊕ n) k}
    (hZ : InJordanOrbit Z) : Tangent Z = LinearMap.ker (squareLinear Z) := by
  ext V
  change (∃ X, X * Z - Z * X = V) ↔ Z * V + V * Z = 0
  exact (orbit_linearized_iff hZ V).symm

def tangent (Z X : Matrix n n k) : Tangent Z := (commLinear Z).rangeRestrict X

noncomputable def representative {Z : Matrix n n k} (v : Tangent Z) : Matrix n n k :=
  v.property.choose

theorem representative_spec {Z : Matrix n n k} (v : Tangent Z) :
    comm (representative v) Z = v.val := v.property.choose_spec

noncomputable def omega (Z : Matrix n n k) (v w : Tangent Z) : k :=
  traceForm Z (representative v) (representative w)

theorem omega_tangent (Z X Y : Matrix n n k) :
    omega Z (tangent Z X) (tangent Z Y) = traceForm Z X Y := by
  unfold omega
  rw [traceForm_wellDefined_left Z _ X _ (representative_spec (tangent Z X))]
  exact traceForm_wellDefined_right Z X _ Y (representative_spec (tangent Z Y))

theorem tangent_representative {Z : Matrix n n k} (v : Tangent Z) :
    tangent Z (representative v) = v := Subtype.ext (representative_spec v)

theorem omega_alternating (Z : Matrix n n k) (v : Tangent Z) : omega Z v v = 0 :=
  traceForm_alt _ _

theorem omega_swap (Z : Matrix n n k) (v w : Tangent Z) : omega Z v w = -omega Z w v :=
  traceForm_swap _ _ _

theorem tangent_add (Z X Y : Matrix n n k) : tangent Z (X + Y) = tangent Z X + tangent Z Y :=
  (commLinear Z).rangeRestrict.map_add X Y

theorem tangent_smul (Z X : Matrix n n k) (a : k) : tangent Z (a • X) = a • tangent Z X :=
  (commLinear Z).rangeRestrict.map_smul a X

theorem omega_add_left (Z : Matrix n n k) (v w u : Tangent Z) :
    omega Z (v + w) u = omega Z v u + omega Z w u := by
  rw [← tangent_representative v, ← tangent_representative w,
    ← tangent_representative u, ← tangent_add]
  simp only [omega_tangent, traceForm, comm, add_mul, mul_add, mul_sub, trace_sub, trace_add]
  abel

theorem omega_smul_left (Z : Matrix n n k) (a : k) (v w : Tangent Z) :
    omega Z (a • v) w = a • omega Z v w := by
  rw [← tangent_representative v, ← tangent_representative w, ← tangent_smul]
  simp [omega_tangent, traceForm, comm, ← smul_sub]

theorem omega_add_right (Z : Matrix n n k) (v w u : Tangent Z) :
    omega Z v (w + u) = omega Z v w + omega Z v u := by
  rw [omega_swap Z v (w + u), omega_add_left, omega_swap Z w v, omega_swap Z u v]
  abel

theorem omega_smul_right (Z : Matrix n n k) (a : k) (v w : Tangent Z) :
    omega Z v (a • w) = a • omega Z v w := by
  rw [omega_swap Z v (a • w), omega_smul_left, omega_swap Z w v]
  simp

/-- The trace pairing descends to an actual bilinear form on the commutator image. -/
noncomputable def omegaBilin (Z : Matrix n n k) : LinearMap.BilinForm k (Tangent Z) where
  toFun v :=
    { toFun := omega Z v
      map_add' := omega_add_right Z v
      map_smul' := fun a w => omega_smul_right Z a v w }
  map_add' v w := by ext u; exact omega_add_left Z v w u
  map_smul' a v := by ext w; exact omega_smul_left Z a v w

theorem omegaBilin_alternating (Z : Matrix n n k) : (omegaBilin Z).IsAlt :=
  omega_alternating Z

theorem omega_separatingLeft (Z : Matrix n n k) (v : Tangent Z)
    (h : ∀ w, omega Z v w = 0) : v = 0 := by
  have hr : comm (representative v) Z = 0 := (traceForm_radical Z _).mp (by
    intro Y
    have hh := h (tangent Z Y)
    rw [← tangent_representative v, omega_tangent] at hh
    exact hh)
  apply Subtype.ext
  exact (representative_spec v).symm.trans hr

theorem omegaBilin_nondegenerate (Z : Matrix n n k) : (omegaBilin Z).Nondegenerate := by
  constructor
  · exact omega_separatingLeft Z
  · intro v h
    apply omega_separatingLeft Z v
    intro w
    rw [omega_swap]
    change -omegaBilin Z w v = 0
    rw [h w, neg_zero]

omit [DecidableEq n] in
theorem comm_jacobi (X Y W : Matrix n n k) :
    comm X (comm Y W) + comm Y (comm W X) + comm W (comm X Y) = 0 := by
  simp only [comm, mul_sub, sub_mul, Matrix.mul_assoc]
  abel

omit [DecidableEq n] in
/-- The Jacobi trace identity used in the invariant-form calculation of `dω`.
This is a matrix identity, not a definition of the scheme exterior derivative. -/
theorem traceForm_jacobi (Z X Y W : Matrix n n k) :
    -(Matrix.trace (Z * (comm X (comm Y W) + comm Y (comm W X) +
      comm W (comm X Y)))) = 0 := by
  rw [comm_jacobi, mul_zero, trace_zero, neg_zero]

def conjugate (g : (Matrix n n k)ˣ) (X : Matrix n n k) : Matrix n n k :=
  (g : Matrix n n k) * X * (↑g⁻¹ : Matrix n n k)

theorem conjugate_comm (g : (Matrix n n k)ˣ) (X Y : Matrix n n k) :
    comm (conjugate g X) (conjugate g Y) = conjugate g (comm X Y) := by
  simp [conjugate, comm, mul_sub, sub_mul, Matrix.mul_assoc]

theorem traceForm_conjugate (g : (Matrix n n k)ˣ) (Z X Y : Matrix n n k) :
    traceForm (conjugate g Z) (conjugate g X) (conjugate g Y) = traceForm Z X Y := by
  rw [traceForm, conjugate_comm]
  simp only [conjugate, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc, Matrix.trace_mul_comm]
  simp [Matrix.mul_assoc, traceForm]
  exact Matrix.trace_mul_comm _ _

theorem traceForm_stabilizer_invariant (g : (Matrix n n k)ˣ) (Z X Y : Matrix n n k)
    (h : conjugate g Z = Z) :
    traceForm Z (conjugate g X) (conjugate g Y) = traceForm Z X Y := by
  simpa only [h] using traceForm_conjugate g Z X Y

theorem conjugate_inv (g : (Matrix n n k)ˣ) (X : Matrix n n k) :
    conjugate g⁻¹ (conjugate g X) = X := by
  simp [conjugate, Matrix.mul_assoc]

def conjugateLinear (g : (Matrix n n k)ˣ) : Matrix n n k ≃ₗ[k] Matrix n n k where
  toFun := conjugate g
  invFun := conjugate g⁻¹
  left_inv := conjugate_inv g
  right_inv X := by simpa using conjugate_inv g⁻¹ X
  map_add' X Y := by simp [conjugate, mul_add, add_mul]
  map_smul' a X := by simp [conjugate]

/-- Tangent spaces and their forms transport along actual matrix conjugation. -/
def tangentConjugate (g : (Matrix n n k)ˣ) (Z : Matrix n n k) :
    Tangent Z ≃ₗ[k] Tangent (conjugate g Z) where
  toFun v := ⟨conjugate g v.val, by
    obtain ⟨X, hX⟩ := v.property
    exact ⟨conjugate g X, by change comm _ _ = _; rw [conjugate_comm, ← hX]; rfl⟩⟩
  invFun v := ⟨conjugate g⁻¹ v.val, by
    obtain ⟨X, hX⟩ := v.property
    refine ⟨conjugate g⁻¹ X, ?_⟩
    change comm _ _ = _
    conv_lhs => rw [← conjugate_inv g Z]
    rw [conjugate_comm, ← hX]
    rfl⟩
  left_inv v := Subtype.ext (conjugate_inv g v.val)
  right_inv v := Subtype.ext (by simpa using conjugate_inv g⁻¹ v.val)
  map_add' v w := Subtype.ext ((conjugateLinear g).map_add v.val w.val)
  map_smul' a v := Subtype.ext ((conjugateLinear g).map_smul a v.val)

theorem tangentConjugate_tangent (g : (Matrix n n k)ˣ) (Z X : Matrix n n k) :
    tangentConjugate g Z (tangent Z X) = tangent (conjugate g Z) (conjugate g X) := by
  apply Subtype.ext
  exact (conjugate_comm g X Z).symm

theorem omegaBilin_conjugate (g : (Matrix n n k)ˣ) (Z : Matrix n n k) (v w : Tangent Z) :
    omegaBilin (conjugate g Z) (tangentConjugate g Z v) (tangentConjugate g Z w) =
      omegaBilin Z v w := by
  rw [← tangent_representative v, ← tangent_representative w]
  simp only [tangentConjugate_tangent]
  change omega _ _ _ = omega _ _ _
  rw [omega_tangent, omega_tangent, traceForm_conjugate]

/-- The Lie algebra element used for the lower-unipotent affine cell. -/
def lowerLie (A : Matrix n n k) : Matrix (n ⊕ n) (n ⊕ n) k :=
  Matrix.fromBlocks 0 0 (-A) 0

def lowerLieLinear : Matrix n n k →ₗ[k] Matrix (n ⊕ n) (n ⊕ n) k where
  toFun := lowerLie
  map_add' A B := by simp [lowerLie, Matrix.fromBlocks_add, add_comm]
  map_smul' a A := by simp [lowerLie, Matrix.fromBlocks_smul]

def lowerTangentLinear (Z : Matrix (n ⊕ n) (n ⊕ n) k) : Matrix n n k →ₗ[k] Tangent Z :=
  (commLinear Z).rangeRestrict.comp lowerLieLinear

def lowerSubspace (Z : Matrix (n ⊕ n) (n ⊕ n) k) : Submodule k (Tangent Z) :=
  LinearMap.range (lowerTangentLinear Z)

omit [DecidableEq n] in
theorem lowerLie_mul (A B : Matrix n n k) : lowerLie A * lowerLie B = 0 := by
  simp [lowerLie, Matrix.fromBlocks_multiply]

omit [DecidableEq n] in
theorem lowerLie_abelian (A B : Matrix n n k) : comm (lowerLie A) (lowerLie B) = 0 := by
  simp [comm, lowerLie_mul]

theorem lowerLie_isotropic (Z : Matrix (n ⊕ n) (n ⊕ n) k) (A B : Matrix n n k) :
    omegaBilin Z (tangent Z (lowerLie A)) (tangent Z (lowerLie B)) = 0 := by
  change omega Z _ _ = 0
  rw [omega_tangent, traceForm, lowerLie_abelian, mul_zero, trace_zero]

omit [DecidableEq n] in
theorem trace_fromBlocks (P Q S T : Matrix n n k) :
    Matrix.trace (Matrix.fromBlocks P Q S T) = Matrix.trace P + Matrix.trace T := by
  simp [Matrix.trace, Matrix.diag, Fintype.sum_sum_type]

theorem traceForm_jordan_lower (X : Matrix (n ⊕ n) (n ⊕ n) k) (A : Matrix n n k) :
    traceForm jordanCell X (lowerLie A) =
      Matrix.trace (A * (X.toBlocks₁₁ - X.toBlocks₂₂)) := by
  obtain ⟨P, Q, S, T, rfl⟩ : ∃ P Q S T, X = Matrix.fromBlocks P Q S T :=
    ⟨_, _, _, _, (Matrix.fromBlocks_toBlocks X).symm⟩
  simp [traceForm, comm, mul_sub, lowerLie, jordanCell, Matrix.fromBlocks_multiply,
    trace_fromBlocks]
  rw [Matrix.trace_mul_comm T A]
  abel

theorem comm_lower_jordan (A : Matrix n n k) :
    comm (lowerLie A) jordanCell = cellLowerParam A := by
  ext (i | i) (j | j) <;>
    simp [comm, lowerLie, jordanCell, cellLowerParam, Matrix.fromBlocks_multiply]

theorem tangent_jordan_eq :
    Tangent (jordanCell : Matrix (n ⊕ n) (n ⊕ n) k) =
      LinearMap.range (cellTangentParam : (Matrix n n k × Matrix n n k) →ₗ[k] _) := by
  ext X
  change (∃ Y, Y * jordanCell - jordanCell * Y = X) ↔ _
  exact cell_commutator_range X

theorem tangent_jordan_finrank {k : Type*} [Field k] :
    Module.finrank k (Tangent (jordanCell : Matrix (n ⊕ n) (n ⊕ n) k)) =
      2 * Fintype.card n ^ 2 := by
  rw [tangent_jordan_eq]
  exact cellTangent_finrank

theorem lowerTangent_jordan_injective : Function.Injective
    (lowerTangentLinear (jordanCell : Matrix (n ⊕ n) (n ⊕ n) k)) := by
  intro A B h
  apply cellLowerParam_injective
  have hv := congrArg Subtype.val h
  change comm (lowerLie A) jordanCell = comm (lowerLie B) jordanCell at hv
  simpa only [comm_lower_jordan] using hv

theorem lowerSubspace_jordan_finrank {k : Type*} [Field k] :
    Module.finrank k (lowerSubspace (jordanCell : Matrix (n ⊕ n) (n ⊕ n) k)) =
      Fintype.card n ^ 2 := by
  rw [lowerSubspace, LinearMap.finrank_range_of_inj lowerTangent_jordan_injective]
  simp [Module.finrank_matrix, pow_two]

/-- The affine cell's tangent space is exactly its symplectic orthogonal at `J`.
Unlike merely counting dimensions, this proves the full linear Lagrangian property. -/
theorem lowerSubspace_jordan_selfOrthogonal :
    (omegaBilin (jordanCell : Matrix (n ⊕ n) (n ⊕ n) k)).orthogonal
      (lowerSubspace jordanCell) = lowerSubspace jordanCell := by
  ext v
  constructor
  · intro h
    let X := representative v
    have hd : X.toBlocks₁₁ - X.toBlocks₂₂ = 0 := Matrix.ext_iff_trace_mul_left.mpr (by
      intro A
      have ha := h (tangent jordanCell (lowerLie A)) ⟨A, rfl⟩
      have hh : omega jordanCell v (tangent jordanCell (lowerLie A)) = 0 := by
        rw [omega_swap]
        change -omegaBilin jordanCell (tangent jordanCell (lowerLie A)) v = 0
        rw [ha, neg_zero]
      rw [← tangent_representative v, omega_tangent, traceForm_jordan_lower] at hh
      simpa using hh)
    refine ⟨-X.toBlocks₂₁, ?_⟩
    apply Subtype.ext
    change comm (lowerLie (-X.toBlocks₂₁)) jordanCell = v.val
    rw [comm_lower_jordan, ← representative_spec v]
    change cellLowerParam (-X.toBlocks₂₁) = X * jordanCell - jordanCell * X
    conv_rhs => rw [← Matrix.fromBlocks_toBlocks X]
    rw [cell_commutator]
    rw [hd]
    simp [cellLowerParam, cellTangentParam]
  · rintro ⟨A, rfl⟩ w ⟨B, rfl⟩
    exact lowerLie_isotropic jordanCell B A

theorem selfOrthogonal_conjugate (g : (Matrix n n k)ˣ) (Z : Matrix n n k)
    (L : Submodule k (Tangent Z)) (hL : (omegaBilin Z).orthogonal L = L) :
    (omegaBilin (conjugate g Z)).orthogonal (L.map (tangentConjugate g Z).toLinearMap) =
      L.map (tangentConjugate g Z).toLinearMap := by
  ext v
  obtain ⟨u, rfl⟩ := (tangentConjugate g Z).surjective v
  constructor
  · intro h
    refine ⟨u, ?_, rfl⟩
    rw [← hL]
    intro w hw
    have hh := h (tangentConjugate g Z w) ⟨w, hw, rfl⟩
    exact (omegaBilin_conjugate g Z w u).symm.trans hh
  · rintro ⟨u', hu', he⟩ w ⟨w', hw', rfl⟩
    have hu : u' = u := (tangentConjugate g Z).injective he
    subst u'
    rw [← hL] at hu'
    exact (omegaBilin_conjugate g Z w' u).trans (hu' w' hw')

theorem lowerSubspace_conjugate
    (g : (Matrix (n ⊕ n) (n ⊕ n) k)ˣ) (Z : Matrix (n ⊕ n) (n ⊕ n) k)
    (h : ∀ A : Matrix n n k, conjugate g (lowerLie A) = lowerLie A) :
    (lowerSubspace Z).map (tangentConjugate g Z).toLinearMap =
      lowerSubspace (conjugate g Z) := by
  ext v
  constructor
  · rintro ⟨u, ⟨A, rfl⟩, rfl⟩
    refine ⟨A, ?_⟩
    change tangent _ (lowerLie A) = tangentConjugate g Z (tangent Z (lowerLie A))
    rw [tangentConjugate_tangent, h]
  · rintro ⟨A, rfl⟩
    refine ⟨lowerTangentLinear Z A, ⟨A, rfl⟩, ?_⟩
    change tangentConjugate g Z (tangent Z (lowerLie A)) = tangent _ (lowerLie A)
    rw [tangentConjugate_tangent, h]

def chartUnits (A : Matrix n n k) : (Matrix (n ⊕ n) (n ⊕ n) k)ˣ where
  val := chartUnit A
  inv := chartUnitInv A
  val_inv := chartUnit_mul_inv A
  inv_val := chartUnit_inv_mul A

theorem chartUnits_conjugate_jordan (A : Matrix n n k) :
    conjugate (chartUnits A) jordanCell = iota A (A * A) := chart_conjugation A

theorem chartUnits_conjugate_lower (A B : Matrix n n k) :
    conjugate (chartUnits A) (lowerLie B) = lowerLie B := by
  change chartUnit A * lowerLie B * chartUnitInv A = lowerLie B
  simp [chartUnit, chartUnitInv, lowerLie, Matrix.fromBlocks_multiply]

/-- At every point of the affine cell, its tangent subspace is Lagrangian. -/
theorem lowerSubspace_chart_selfOrthogonal (A : Matrix n n k) :
    (omegaBilin (iota A (A * A))).orthogonal (lowerSubspace (iota A (A * A))) =
      lowerSubspace (iota A (A * A)) := by
  have h := selfOrthogonal_conjugate (chartUnits A) jordanCell (lowerSubspace jordanCell)
    lowerSubspace_jordan_selfOrthogonal
  rw [lowerSubspace_conjugate _ _ (chartUnits_conjugate_lower A),
    chartUnits_conjugate_jordan] at h
  exact h

theorem tangent_chart_finrank {k : Type*} [Field k] (A : Matrix n n k) :
    Module.finrank k (Tangent (iota A (A * A))) = 2 * Fintype.card n ^ 2 := by
  have h := (tangentConjugate (chartUnits A) jordanCell).finrank_eq
  rw [chartUnits_conjugate_jordan] at h
  rw [← h]
  exact tangent_jordan_finrank

theorem tangent_orbit_finrank {k : Type*} [Field k]
    {Z : Matrix (n ⊕ n) (n ⊕ n) k} (hZ : InJordanOrbit Z) :
    Module.finrank k (Tangent Z) = 2 * Fintype.card n ^ 2 := by
  obtain ⟨P, Q, hPQ, hQP, rfl⟩ := hZ
  let g : (Matrix (n ⊕ n) (n ⊕ n) k)ˣ := ⟨P, Q, hPQ, hQP⟩
  have h := (tangentConjugate g jordanCell).finrank_eq
  change Module.finrank k (Tangent (jordanCell : Matrix (n ⊕ n) (n ⊕ n) k)) =
    Module.finrank k (Tangent (P * jordanCell * Q)) at h
  exact h.symm.trans tangent_jordan_finrank

theorem lowerSubspace_chart_finrank {k : Type*} [Field k] (A : Matrix n n k) :
    Module.finrank k (lowerSubspace (iota A (A * A))) = Fintype.card n ^ 2 := by
  have h := (tangentConjugate (chartUnits A) jordanCell).finrank_map_eq (lowerSubspace jordanCell)
  rw [lowerSubspace_conjugate _ _ (chartUnits_conjugate_lower A),
    chartUnits_conjugate_jordan] at h
  rw [h]
  exact lowerSubspace_jordan_finrank

end Symplectic

namespace AffineForms

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

/-- A regular algebraic two-form, expressed on algebraic vector fields.
For smooth affine algebras this is the derivation description of a Kähler
two-form. The definition uses the coefficient ring's module of derivations,
not vector fields on its set of field-valued points. -/
structure RegularTwoForm where
  bilin : LinearMap.BilinForm S (Derivation R S S)
  alternating : bilin.IsAlt

/-- The standard algebraic Cartan exterior derivative in degree two. -/
def exteriorDerivative2 (ω : LinearMap.BilinForm S (Derivation R S S))
    (D E F : Derivation R S S) : S :=
  D (ω E F) - E (ω D F) + F (ω D E) -
    ω ⁅D, E⁆ F + ω ⁅D, F⁆ E - ω ⁅E, F⁆ D

def IsClosed (ω : LinearMap.BilinForm S (Derivation R S S)) : Prop :=
  ∀ D E F, exteriorDerivative2 ω D E F = 0

/-- The regular two-form `df ∧ dg`. -/
def coordinateForm (f g : S) : LinearMap.BilinForm S (Derivation R S S) where
  toFun D :=
    { toFun E := D f * E g - E f * D g
      map_add' E F := by simp [Derivation.add_apply]; ring
      map_smul' a E := by simp [Derivation.smul_apply, smul_eq_mul]; ring }
  map_add' D E := by ext F; simp [Derivation.add_apply]; ring
  map_smul' a D := by ext E; simp [Derivation.smul_apply, smul_eq_mul]; ring

@[simp] theorem coordinateForm_apply (f g : S) (D E : Derivation R S S) :
    coordinateForm f g D E = D f * E g - E f * D g := rfl

theorem coordinateForm_alternating (f g : S) :
    (coordinateForm (R := R) f g).IsAlt := by
  intro D
  simp

theorem coordinateForm_closed (f g : S) : IsClosed (coordinateForm (R := R) f g) := by
  intro D E F
  simp only [exteriorDerivative2, coordinateForm_apply, map_sub,
    Derivation.leibniz, Derivation.commutator_apply, smul_eq_mul]
  ring

theorem coordinateForm_exact (f g : S) (D E : Derivation R S S) :
    coordinateForm f g D E = D (f * E g) - E (f * D g) - f * ⁅D, E⁆ g := by
  simp only [coordinateForm_apply, Derivation.leibniz, Derivation.commutator_apply, smul_eq_mul]
  ring

theorem closed_zero : IsClosed (0 : LinearMap.BilinForm S (Derivation R S S)) := by
  intro D E F
  simp [exteriorDerivative2]

theorem closed_add (ω η : LinearMap.BilinForm S (Derivation R S S))
    (hω : IsClosed ω) (hη : IsClosed η) : IsClosed (ω + η) := by
  intro D E F
  calc
    exteriorDerivative2 (ω + η) D E F =
        exteriorDerivative2 ω D E F + exteriorDerivative2 η D E F := by
      simp only [exteriorDerivative2, LinearMap.add_apply, map_add]
      ring
    _ = 0 := by rw [hω D E F, hη D E F, add_zero]

theorem closed_sum {I : Type*} (s : Finset I)
    (ω : I → LinearMap.BilinForm S (Derivation R S S))
    (hω : ∀ i ∈ s, IsClosed (ω i)) : IsClosed (∑ i ∈ s, ω i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (closed_zero (R := R) (S := S))
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact closed_add _ _ (hω a (Finset.mem_insert_self _ _))
      (ih (fun i hi => hω i (Finset.mem_insert_of_mem hi)))

variable {n : Type*} [Fintype n]

/-- Canonical cotangent form `tr(dT ∧ dA)`, over any coefficient algebra.
In particular it is defined over the localization at `det T` used for the orbit chart. -/
def canonicalTrace (T A : Matrix n n S) : LinearMap.BilinForm S (Derivation R S S) :=
  ∑ i, ∑ j, coordinateForm (T i j) (A j i)

def derivMatrix (D : Derivation R S S) (A : Matrix n n S) : Matrix n n S :=
  fun i j => D (A i j)

theorem derivMatrix_mul (D : Derivation R S S) (A B : Matrix n n S) :
    derivMatrix D (A * B) = derivMatrix D A * B + A * derivMatrix D B := by
  ext i j
  simp [derivMatrix, Matrix.mul_apply, map_sum, Derivation.leibniz,
    smul_eq_mul, Finset.sum_add_distrib, mul_comm, add_comm]

omit [Fintype n] in
theorem derivMatrix_fromBlocks (D : Derivation R S S) (P Q U V : Matrix n n S) :
    derivMatrix D (Matrix.fromBlocks P Q U V) = Matrix.fromBlocks
      (derivMatrix D P) (derivMatrix D Q) (derivMatrix D U) (derivMatrix D V) := by
  ext (i | i) (j | j) <;> rfl

omit [Fintype n] in
theorem derivMatrix_neg (D : Derivation R S S) (A : Matrix n n S) :
    derivMatrix D (-A) = -derivMatrix D A := by
  ext i j
  simp [derivMatrix]

theorem canonicalTrace_apply (T A : Matrix n n S) (D E : Derivation R S S) :
    canonicalTrace T A D E =
      Matrix.trace (derivMatrix D T * derivMatrix E A - derivMatrix E T * derivMatrix D A) := by
  simp [canonicalTrace, coordinateForm_apply, Matrix.trace, Matrix.diag, Matrix.mul_apply,
    derivMatrix, Finset.sum_sub_distrib]

theorem canonicalTrace_alternating (T A : Matrix n n S) :
    (canonicalTrace (R := R) T A).IsAlt := by
  intro D
  simp [canonicalTrace, coordinateForm_apply]

theorem canonicalTrace_closed (T A : Matrix n n S) :
    IsClosed (canonicalTrace (R := R) T A) := by
  apply closed_sum
  intro i _
  apply closed_sum
  intro j _
  exact coordinateForm_closed _ _

/-- A constructed regular closed algebraic two-form on the affine chart algebra.
Its nondegeneracy and gluing on the entire orbit are separate obligations. -/
def canonicalRegularTwoForm (T A : Matrix n n S) : RegularTwoForm (R := R) (S := S) :=
  ⟨canonicalTrace T A, canonicalTrace_alternating T A⟩

theorem canonicalRegularTwoForm_closed (T A : Matrix n n S) :
    IsClosed (canonicalRegularTwoForm (R := R) T A).bilin := canonicalTrace_closed T A

variable [DecidableEq n]

theorem trace_unit_cycle (T : (Matrix n n S)ˣ) (X Y : Matrix n n S) :
    Matrix.trace ((↑T : Matrix n n S) * (X * (Y * (↑T⁻¹ : Matrix n n S)))) =
      Matrix.trace (X * Y) := by
  rw [← Matrix.mul_assoc X Y, ← Matrix.mul_assoc]
  rw [Matrix.trace_mul_cycle]
  simp

def baseGenerator (T : (Matrix n n S)ˣ) (dA dT : Matrix n n S) :
    Matrix (n ⊕ n) (n ⊕ n) S :=
  Matrix.fromBlocks (dT * (↑T⁻¹ : Matrix n n S)) 0 (-dA) 0

/-- The KKS trace formula in cotangent coordinates, valid over coefficient rings. -/
theorem baseGenerator_trace (T : (Matrix n n S)ˣ) (dA dT eA eT : Matrix n n S) :
    Symplectic.traceForm (Matrix.fromBlocks 0 (↑T : Matrix n n S) 0 0)
      (baseGenerator T dA dT) (baseGenerator T eA eT) =
      Matrix.trace (dT * eA - eT * dA) := by
  simp [Symplectic.traceForm, Symplectic.comm, baseGenerator, mul_sub,
    Matrix.fromBlocks_multiply, Symplectic.trace_fromBlocks,
    Matrix.mul_assoc, trace_unit_cycle, -Matrix.coe_units_inv]
  rw [Matrix.trace_mul_comm dA eT, Matrix.trace_mul_comm eA dT]
  abel

def chartGenerator (A : Matrix n n S) (T : (Matrix n n S)ˣ) (dA dT : Matrix n n S) :
    Matrix (n ⊕ n) (n ⊕ n) S :=
  Symplectic.conjugate (Symplectic.chartUnits A) (baseGenerator T dA dT)

theorem chartGenerator_trace (A : Matrix n n S) (T : (Matrix n n S)ˣ)
    (dA dT eA eT : Matrix n n S) :
    Symplectic.traceForm
      (Symplectic.conjugate (Symplectic.chartUnits A)
        (Matrix.fromBlocks 0 (↑T : Matrix n n S) 0 0))
      (chartGenerator A T dA dT) (chartGenerator A T eA eT) =
      Matrix.trace (dT * eA - eT * dA) := by
  rw [chartGenerator, chartGenerator, Symplectic.traceForm_conjugate]
  exact baseGenerator_trace T dA dT eA eT

theorem generalChart_eq_conjugate (A T : Matrix n n S) :
    generalChart A T = Symplectic.conjugate (Symplectic.chartUnits A)
      (Matrix.fromBlocks 0 T 0 0) := by
  simp [generalChart, Symplectic.conjugate, Symplectic.chartUnits,
    chartUnit, chartUnitInv, Matrix.fromBlocks_multiply]

theorem chartGenerator_blocks (A : Matrix n n S) (T : (Matrix n n S)ˣ)
    (dA dT : Matrix n n S) :
    chartGenerator A T dA dT = Matrix.fromBlocks
      (dT * (↑T⁻¹ : Matrix n n S)) 0 (-A * (dT * (↑T⁻¹ : Matrix n n S)) - dA) 0 := by
  simp [chartGenerator, Symplectic.conjugate, Symplectic.chartUnits,
    chartUnit, chartUnitInv, baseGenerator, Matrix.fromBlocks_multiply, sub_eq_add_neg]

omit [Fintype n] [DecidableEq n] in
theorem fromBlocks_sub (P Q U V P' Q' U' V' : Matrix n n S) :
    Matrix.fromBlocks P Q U V - Matrix.fromBlocks P' Q' U' V' =
      Matrix.fromBlocks (P - P') (Q - Q') (U - U') (V - V') := by
  ext (i | i) (j | j) <;> rfl

theorem chartGenerator_comm (A : Matrix n n S) (T : (Matrix n n S)ˣ)
    (dA dT : Matrix n n S) :
    Symplectic.comm (chartGenerator A T dA dT) (generalChart A (↑T : Matrix n n S)) =
      Matrix.fromBlocks (dT * A + (↑T : Matrix n n S) * dA) dT
        (-(dA * (↑T : Matrix n n S) * A + A * dT * A + A * (↑T : Matrix n n S) * dA))
        (-(dA * (↑T : Matrix n n S) + A * dT)) := by
  simp only [Symplectic.comm, chartGenerator_blocks, generalChart,
    Matrix.fromBlocks_multiply, fromBlocks_sub, Matrix.fromBlocks_inj]
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [Matrix.mul_assoc, mul_sub, sub_mul, -Matrix.coe_units_inv] <;>
    noncomm_ring

omit [DecidableEq n] in
theorem derivMatrix_generalChart (D : Derivation R S S) (A T : Matrix n n S) :
    derivMatrix D (generalChart A T) =
      Matrix.fromBlocks (derivMatrix D T * A + T * derivMatrix D A) (derivMatrix D T)
        (-(derivMatrix D A * T * A + A * derivMatrix D T * A + A * T * derivMatrix D A))
        (-(derivMatrix D A * T + A * derivMatrix D T)) := by
  simp [generalChart, derivMatrix_fromBlocks, derivMatrix_mul, derivMatrix_neg, add_mul]

/-- The generators in the KKS calculation represent the genuine algebraic derivative
of the orbit-chart matrix, entry by entry in the coordinate algebra. -/
theorem chartGenerator_derivative (D : Derivation R S S) (A : Matrix n n S)
    (T : (Matrix n n S)ˣ) :
    Symplectic.comm (chartGenerator A T (derivMatrix D A) (derivMatrix D (↑T : Matrix n n S)))
      (generalChart A (↑T : Matrix n n S)) =
      derivMatrix D (generalChart A (↑T : Matrix n n S)) := by
  rw [chartGenerator_comm, derivMatrix_generalChart]

/-- The closed canonical regular form is the KKS form on the explicit orbit chart. -/
theorem canonicalTrace_eq_KKS (D E : Derivation R S S) (A : Matrix n n S)
    (T : (Matrix n n S)ˣ) :
    Symplectic.traceForm (generalChart A (↑T : Matrix n n S))
      (chartGenerator A T (derivMatrix D A) (derivMatrix D (↑T : Matrix n n S)))
      (chartGenerator A T (derivMatrix E A) (derivMatrix E (↑T : Matrix n n S))) =
      canonicalTrace (↑T : Matrix n n S) A D E := by
  rw [generalChart_eq_conjugate, chartGenerator_trace, canonicalTrace_apply]

theorem derivMatrix_conjugate (D : Derivation R S S)
    (g : (Matrix n n S)ˣ) (Z : Matrix n n S)
    (hg : derivMatrix D (↑g : Matrix n n S) = 0)
    (hgi : derivMatrix D (↑g⁻¹ : Matrix n n S) = 0) :
    derivMatrix D (Symplectic.conjugate g Z) = Symplectic.conjugate g (derivMatrix D Z) := by
  simp only [Symplectic.conjugate, derivMatrix_mul, hg, hgi,
    zero_mul, mul_zero, zero_add, add_zero]

def constantMatrixUnit (g : (Matrix n n R)ˣ) : (Matrix n n S)ˣ :=
  Units.map (algebraMap R S).mapMatrix.toMonoidHom g

theorem constantMatrixUnit_derivatives (g : (Matrix n n R)ˣ) (D : Derivation R S S) :
    derivMatrix D (↑(constantMatrixUnit (S := S) g) : Matrix n n S) = 0 ∧
    derivMatrix D (↑(constantMatrixUnit (S := S) g)⁻¹ : Matrix n n S) = 0 := by
  constructor <;> ext i j <;> simp [constantMatrixUnit, derivMatrix]

theorem chartGenerator_comm_compatible (D : Derivation R S S) (A B : Matrix n n S)
    (T U : (Matrix n n S)ˣ) (g : (Matrix (n ⊕ n) (n ⊕ n) S)ˣ)
    (h : generalChart A (↑T : Matrix n n S) =
      Symplectic.conjugate g (generalChart B (↑U : Matrix n n S)))
    (hg : derivMatrix D (↑g : Matrix (n ⊕ n) (n ⊕ n) S) = 0)
    (hgi : derivMatrix D (↑g⁻¹ : Matrix (n ⊕ n) (n ⊕ n) S) = 0) :
    Symplectic.comm (chartGenerator A T (derivMatrix D A) (derivMatrix D (↑T : Matrix n n S)))
      (generalChart A (↑T : Matrix n n S)) =
    Symplectic.comm (Symplectic.conjugate g
      (chartGenerator B U (derivMatrix D B) (derivMatrix D (↑U : Matrix n n S))))
      (generalChart A (↑T : Matrix n n S)) := by
  rw [chartGenerator_derivative]
  conv_lhs => rw [h, derivMatrix_conjugate D g _ hg hgi]
  conv_rhs => rw [h, Symplectic.conjugate_comm, chartGenerator_derivative]

/-- Actual overlap compatibility: any constant change of ambient basis preserves
the canonical chart forms. This applies in every overlap coefficient algebra,
and follows from the proved derivative identity and KKS well-definedness. -/
theorem canonicalTrace_conjugacy_compatible (A B : Matrix n n S)
    (T U : (Matrix n n S)ˣ) (g : (Matrix (n ⊕ n) (n ⊕ n) S)ˣ)
    (h : generalChart A (↑T : Matrix n n S) =
      Symplectic.conjugate g (generalChart B (↑U : Matrix n n S)))
    (hg : ∀ D : Derivation R S S,
      derivMatrix D (↑g : Matrix (n ⊕ n) (n ⊕ n) S) = 0 ∧
      derivMatrix D (↑g⁻¹ : Matrix (n ⊕ n) (n ⊕ n) S) = 0) :
    canonicalTrace (R := R) (↑T : Matrix n n S) A = canonicalTrace (↑U : Matrix n n S) B := by
  ext D E
  rw [← canonicalTrace_eq_KKS, ← canonicalTrace_eq_KKS]
  rw [Symplectic.traceForm_wellDefined_left _ _ _ _
    (chartGenerator_comm_compatible D A B T U g h (hg D).1 (hg D).2)]
  rw [Symplectic.traceForm_wellDefined_right _ _ _ _
    (chartGenerator_comm_compatible E A B T U g h (hg E).1 (hg E).2)]
  rw [h, Symplectic.traceForm_conjugate]

/-- In particular, chart transition matrices defined over the base ring have
proved compatibility, without an assumed constancy condition. -/
theorem canonicalTrace_baseChange_compatible (A B : Matrix n n S)
    (T U : (Matrix n n S)ˣ) (g : (Matrix (n ⊕ n) (n ⊕ n) R)ˣ)
    (h : generalChart A (↑T : Matrix n n S) =
      Symplectic.conjugate (constantMatrixUnit (S := S) g)
        (generalChart B (↑U : Matrix n n S))) :
    canonicalTrace (R := R) (↑T : Matrix n n S) A = canonicalTrace (↑U : Matrix n n S) B :=
  canonicalTrace_conjugacy_compatible A B T U _ h (constantMatrixUnit_derivatives g)

omit [Fintype n] in
theorem derivMatrix_one (D : Derivation R S S) : derivMatrix D (1 : Matrix n n S) = 0 := by
  ext i j
  simp [derivMatrix, Matrix.one_apply, apply_ite]

/-- The regular canonical form restricts to zero on the affine cell `T = I`. -/
theorem canonicalTrace_one (A : Matrix n n S) :
    canonicalTrace (R := R) (1 : Matrix n n S) A = 0 := by
  ext D E
  rw [canonicalTrace_apply, derivMatrix_one, derivMatrix_one]
  simp

omit [DecidableEq n] in
theorem comm_submatrix (X Y : Matrix n n S) (e : Equiv.Perm n) :
    Symplectic.comm (X.submatrix e e) (Y.submatrix e e) = (Symplectic.comm X Y).submatrix e e := by
  simp [Symplectic.comm, Matrix.submatrix_mul_equiv]
  rfl

omit [DecidableEq n] in
theorem trace_submatrix (X : Matrix n n S) (e : Equiv.Perm n) :
    Matrix.trace (X.submatrix e e) = Matrix.trace X := by
  exact Equiv.sum_comp e (fun i => X i i)

omit [DecidableEq n] in
theorem traceForm_submatrix (Z X Y : Matrix n n S) (e : Equiv.Perm n) :
    Symplectic.traceForm (Z.submatrix e e) (X.submatrix e e) (Y.submatrix e e) =
      Symplectic.traceForm Z X Y := by
  rw [Symplectic.traceForm, comm_submatrix, Matrix.submatrix_mul_equiv, trace_submatrix]
  rfl

theorem chartGenerator_comm_reindex (D : Derivation R S S) (A B : Matrix n n S)
    (T U : (Matrix n n S)ˣ) (e : Equiv.Perm (n ⊕ n))
    (h : generalChart A (↑T : Matrix n n S) = (generalChart B (↑U : Matrix n n S)).submatrix e e) :
    Symplectic.comm (chartGenerator A T (derivMatrix D A) (derivMatrix D (↑T : Matrix n n S)))
      (generalChart A (↑T : Matrix n n S)) =
    Symplectic.comm
      ((chartGenerator B U (derivMatrix D B) (derivMatrix D (↑U : Matrix n n S))).submatrix e e)
      (generalChart A (↑T : Matrix n n S)) := by
  rw [chartGenerator_derivative]
  conv_lhs => rw [h]
  conv_rhs => rw [h, comm_submatrix, chartGenerator_derivative]
  rfl

theorem canonicalTrace_reindex_compatible (A B : Matrix n n S)
    (T U : (Matrix n n S)ˣ) (e : Equiv.Perm (n ⊕ n))
    (h : generalChart A (↑T : Matrix n n S) = (generalChart B (↑U : Matrix n n S)).submatrix e e) :
    canonicalTrace (R := R) (↑T : Matrix n n S) A = canonicalTrace (↑U : Matrix n n S) B := by
  ext D E
  rw [← canonicalTrace_eq_KKS, ← canonicalTrace_eq_KKS]
  rw [Symplectic.traceForm_wellDefined_left _ _ _ _ (chartGenerator_comm_reindex D A B T U e h)]
  rw [Symplectic.traceForm_wellDefined_right _ _ _ _ (chartGenerator_comm_reindex E A B T U e h)]
  rw [h, traceForm_submatrix]

section LocalizedCoordinates

variable {I : Type*} [DecidableEq I]
variable [Algebra (MvPolynomial I R) S] [IsScalarTower R (MvPolynomial I R) S]
variable (M : Submonoid (MvPolynomial I R)) [IsLocalization M S]

noncomputable def coordinate (i : I) : S := algebraMap (MvPolynomial I R) S (MvPolynomial.X i)

/-- Localizing polynomial coordinates preserves their actual Kähler basis. -/
noncomputable def localizedDifferentialBasis : Module.Basis I S (KaehlerDifferential R S) :=
  (KaehlerDifferential.mvPolynomialBasis R I).ofIsLocalizedModule S M
    (KaehlerDifferential.map R R (MvPolynomial I R) S)

omit [DecidableEq I] in
theorem localizedDifferentialBasis_apply (i : I) :
    localizedDifferentialBasis (S := S) M i =
      KaehlerDifferential.D R S (coordinate (R := R) (S := S) i) := by
  simp [localizedDifferentialBasis, coordinate, KaehlerDifferential.mvPolynomialBasis_apply,
    KaehlerDifferential.map_D]

noncomputable def coordinatePartial (i : I) : Derivation R S S :=
  ((localizedDifferentialBasis (S := S) M).coord i).compDer (KaehlerDifferential.D R S)

@[simp] theorem coordinatePartial_coordinate (i j : I) :
    coordinatePartial (S := S) M i (coordinate (R := R) (S := S) j) = if j = i then 1 else 0 := by
  change (localizedDifferentialBasis (S := S) M).coord i
    (KaehlerDifferential.D R S (coordinate (R := R) (S := S) j)) = _
  rw [← localizedDifferentialBasis_apply M]
  simp [Module.Basis.coord_apply, Finsupp.single_apply, eq_comm]

include M in
omit [DecidableEq I] in
theorem derivation_ext_coordinates (D E : Derivation R S S)
    (h : ∀ i : I, D (coordinate (R := R) (S := S) i) = E (coordinate (R := R) (S := S) i)) : D = E := by
  have hl : D.liftKaehlerDifferential = E.liftKaehlerDifferential := by
    apply (localizedDifferentialBasis (S := S) M).ext
    intro i
    rw [localizedDifferentialBasis_apply, Derivation.liftKaehlerDifferential_comp_D,
      Derivation.liftKaehlerDifferential_comp_D, h]
  ext a
  simpa only [Derivation.liftKaehlerDifferential_comp_D] using
    LinearMap.congr_fun hl (KaehlerDifferential.D R S a)

noncomputable def coordinateDerivation (v : I → S) : Derivation R S S :=
  ((localizedDifferentialBasis (S := S) M).constr S v).compDer (KaehlerDifferential.D R S)

omit [DecidableEq I] in
@[simp] theorem coordinateDerivation_coordinate (v : I → S) (i : I) :
    coordinateDerivation M v (coordinate (R := R) (S := S) i) = v i := by
  change (localizedDifferentialBasis (S := S) M).constr S v
    (KaehlerDifferential.D R S (coordinate (R := R) (S := S) i)) = _
  rw [← localizedDifferentialBasis_apply M]
  simp

noncomputable def coordinateDerivationBasis [Fintype I] : Module.Basis I S (Derivation R S S) :=
  (localizedDifferentialBasis (S := S) M).dualBasis.map
    (KaehlerDifferential.linearMapEquivDerivation R S)

@[simp] theorem coordinateDerivationBasis_apply [Fintype I] (i : I) :
    coordinateDerivationBasis (S := S) M i = coordinatePartial M i := by
  simp only [coordinateDerivationBasis, Module.Basis.map_apply, Module.Basis.coe_dualBasis]
  rfl

end LocalizedCoordinates

section LocalizedCotangentChart

variable [Algebra (MvPolynomial ((n × n) ⊕ (n × n)) R) S]
variable [IsScalarTower R (MvPolynomial ((n × n) ⊕ (n × n)) R) S]
variable (M : Submonoid (MvPolynomial ((n × n) ⊕ (n × n)) R)) [IsLocalization M S]

noncomputable def coordinateA : Matrix n n S := fun i j =>
  coordinate (R := R) (I := (n × n) ⊕ (n × n)) (Sum.inl (i, j))
noncomputable def coordinateT : Matrix n n S := fun i j =>
  coordinate (R := R) (I := (n × n) ⊕ (n × n)) (Sum.inr (i, j))

include M

theorem canonicalTrace_partialA (D : Derivation R S S) (i j : n) :
    canonicalTrace (coordinateT (R := R) (S := S) (n := n)) (coordinateA (R := R)) D
      (coordinatePartial M (Sum.inl (j, i))) = D (coordinateT (R := R) i j) := by
  simp [canonicalTrace, coordinateForm_apply, coordinateA, coordinateT,
    coordinatePartial_coordinate, Prod.mk.injEq, ite_and]

theorem canonicalTrace_partialT (D : Derivation R S S) (i j : n) :
    canonicalTrace (coordinateT (R := R) (S := S) (n := n)) (coordinateA (R := R)) D
      (coordinatePartial M (Sum.inr (j, i))) = -D (coordinateA (R := R) i j) := by
  simp [canonicalTrace, coordinateForm_apply, coordinateA, coordinateT,
    coordinatePartial_coordinate, Prod.mk.injEq, ite_and]

theorem canonicalTrace_localized_separatingLeft (D : Derivation R S S)
    (h : ∀ E, canonicalTrace (coordinateT (R := R) (S := S) (n := n))
      (coordinateA (R := R)) D E = 0) : D = 0 := by
  apply derivation_ext_coordinates M D 0
  intro p
  rcases p with ⟨i, j⟩ | ⟨i, j⟩
  · have hh := h (coordinatePartial M (Sum.inr (j, i)))
    rw [canonicalTrace_partialT] at hh
    simpa only [coordinateA, neg_eq_zero, Derivation.zero_apply] using hh
  · have hh := h (coordinatePartial M (Sum.inl (j, i)))
    rw [canonicalTrace_partialA] at hh
    simpa only [coordinateT, Derivation.zero_apply] using hh

/-- The constructed closed form is nondegenerate on the actual derivation module
of any localization of the cotangent coordinate ring, including `det T ≠ 0`. -/
theorem canonicalTrace_localized_nondegenerate :
    (canonicalTrace (R := R) (coordinateT (R := R) (S := S) (n := n))
      (coordinateA (R := R))).Nondegenerate := by
  constructor
  · exact canonicalTrace_localized_separatingLeft M
  · intro D h
    apply canonicalTrace_localized_separatingLeft M D
    intro E
    rw [← (canonicalTrace_alternating (coordinateT (R := R) (S := S) (n := n))
      (coordinateA (R := R))).neg_eq E D]
    rw [h E, neg_zero]

theorem canonicalTrace_localized_surjective : Function.Surjective
    (canonicalTrace (R := R) (coordinateT (R := R) (S := S) (n := n))
      (coordinateA (R := R))) := by
  intro ℓ
  let v : ((n × n) ⊕ (n × n)) → S := fun p => match p with
    | Sum.inl (i, j) => -ℓ (coordinatePartial M (Sum.inr (j, i)))
    | Sum.inr (i, j) => ℓ (coordinatePartial M (Sum.inl (j, i)))
  refine ⟨coordinateDerivation M v, ?_⟩
  apply (coordinateDerivationBasis (S := S) M).ext
  intro p
  rw [coordinateDerivationBasis_apply]
  rcases p with ⟨i, j⟩ | ⟨i, j⟩
  · rw [canonicalTrace_partialA M _ j i]
    simp [coordinateT, v]
  · rw [canonicalTrace_partialT M _ j i]
    simp [coordinateA, v]

/-- Perfectness over the localized coordinate ring: the closed canonical form
gives an actual linear equivalence of vector fields with their module dual. -/
noncomputable def canonicalTrace_localized_equiv :
    Derivation R S S ≃ₗ[S] Module.Dual S (Derivation R S S) :=
  LinearEquiv.ofBijective (canonicalTrace (R := R) (coordinateT (R := R) (S := S) (n := n))
    (coordinateA (R := R)))
    ⟨by
      intro D E h
      apply sub_eq_zero.mp
      apply canonicalTrace_localized_separatingLeft M (D - E)
      intro F
      rw [map_sub, LinearMap.sub_apply, LinearMap.congr_fun h F, sub_self],
      canonicalTrace_localized_surjective M⟩

end LocalizedCotangentChart

end AffineForms

namespace GlobalSymplectic

open AlgebraicGeometry CategoryTheory
open SquareZeroGeometry AffineForms

noncomputable section
universe u
variable (R : Type u) [CommRing R] (n : Type u) [Fintype n] [DecidableEq n]

abbrev ChartIndex := Equiv.Perm (n ⊕ n)

def chartMinor (e : ChartIndex n) : CoordinateRing R n :=
  ((universalMatrix R n).submatrix e e).toBlocks₁₂.det

/-- The coordinate algebra of the actual intersection of two principal orbit charts. -/
abbrev OverlapRing (e f : ChartIndex n) := Localization.Away (chartMinor R n e * chartMinor R n f)

def overlapMatrix (e f : ChartIndex n) : Matrix (n ⊕ n) (n ⊕ n) (OverlapRing R n e f) :=
  (universalMatrix R n).map (algebraMap (CoordinateRing R n) (OverlapRing R n e f))

def overlapT (e f g : ChartIndex n) : Matrix n n (OverlapRing R n e f) :=
  ((overlapMatrix R n e f).submatrix g g).toBlocks₁₂

def overlapA (e f g : ChartIndex n) : Matrix n n (OverlapRing R n e f) :=
  (overlapT R n e f g)⁻¹ * ((overlapMatrix R n e f).submatrix g g).toBlocks₁₁

theorem overlapMatrix_square (e f : ChartIndex n) :
    overlapMatrix R n e f * overlapMatrix R n e f = 0 := by
  rw [overlapMatrix, ← Matrix.map_mul, universalMatrix_square]
  ext i j
  simp

theorem overlapT_det (e f g : ChartIndex n) : (overlapT R n e f g).det =
    algebraMap (CoordinateRing R n) (OverlapRing R n e f) (chartMinor R n g) := by
  symm
  exact (algebraMap (CoordinateRing R n) (OverlapRing R n e f)).map_det _

theorem overlapT_left_isUnit (e f : ChartIndex n) : IsUnit (overlapT R n e f e).det := by
  rw [overlapT_det]
  have h : IsUnit (algebraMap (CoordinateRing R n) (OverlapRing R n e f)
      (chartMinor R n e * chartMinor R n f)) :=
    IsLocalization.Away.algebraMap_isUnit (chartMinor R n e * chartMinor R n f)
  rw [map_mul] at h
  exact isUnit_of_mul_isUnit_left h

theorem overlapT_right_isUnit (e f : ChartIndex n) : IsUnit (overlapT R n e f f).det := by
  rw [overlapT_det]
  have h : IsUnit (algebraMap (CoordinateRing R n) (OverlapRing R n e f)
      (chartMinor R n e * chartMinor R n f)) :=
    IsLocalization.Away.algebraMap_isUnit (chartMinor R n e * chartMinor R n f)
  rw [map_mul] at h
  exact isUnit_of_mul_isUnit_right h

theorem overlap_normalForm (e f g : ChartIndex n) (h : IsUnit (overlapT R n e f g).det) :
    generalChart (overlapA R n e f g) (overlapT R n e f g) =
      (overlapMatrix R n e f).submatrix g g := by
  have hs : (overlapMatrix R n e f).submatrix g g *
      (overlapMatrix R n e f).submatrix g g = 0 := by
    rw [Matrix.submatrix_mul_equiv, overlapMatrix_square]
    rfl
  have hh := square_zero_invertible_block_normalForm
    ((overlapMatrix R n e f).submatrix g g).toBlocks₁₁
    ((overlapMatrix R n e f).submatrix g g).toBlocks₂₁
    ((overlapMatrix R n e f).submatrix g g).toBlocks₂₂
    (overlapT R n e f g) h (by simpa only [overlapT, Matrix.fromBlocks_toBlocks] using hs)
  simpa only [overlapA, overlapT, Matrix.fromBlocks_toBlocks] using hh

def overlapPolynomialMap (e f g : ChartIndex n) :
    ChartPolynomialRing R n →ₐ[R] OverlapRing R n e f :=
  MvPolynomial.aeval (Sum.elim (fun ij => overlapA R n e f g ij.1 ij.2)
    (fun ij => overlapT R n e f g ij.1 ij.2))

theorem overlapPolynomialMap_A (e f g : ChartIndex n) :
    (universalMatrixA n).map (overlapPolynomialMap R n e f g) = overlapA R n e f g := by
  ext i j
  simp [universalMatrixA, overlapPolynomialMap]

theorem overlapPolynomialMap_T (e f g : ChartIndex n) :
    (universalMatrixB n).map (overlapPolynomialMap R n e f g) = overlapT R n e f g := by
  ext i j
  simp [universalMatrixB, overlapPolynomialMap]

theorem overlapPolynomialMap_det (e f g : ChartIndex n) :
    overlapPolynomialMap R n e f g (chartDet R n) = (overlapT R n e f g).det := by
  rw [chartDet, AlgHom.map_det]
  exact congrArg Matrix.det (overlapPolynomialMap_T R n e f g)

def overlapChartMap (e f g : ChartIndex n) (h : IsUnit (overlapT R n e f g).det) :
    ChartRing R n →ₐ[R] OverlapRing R n e f :=
  awayLift R (chartDet R n) (overlapPolynomialMap R n e f g) (by
    rw [overlapPolynomialMap_det]
    exact h)

theorem overlapChartMap_A (e f g : ChartIndex n) (h : IsUnit (overlapT R n e f g).det) :
    (chartA R n).map (overlapChartMap R n e f g h) = overlapA R n e f g := by
  ext i j
  simp [chartA, overlapChartMap, overlapPolynomialMap, universalMatrixA]

theorem overlapChartMap_T (e f g : ChartIndex n) (h : IsUnit (overlapT R n e f g).det) :
    (chartT R n).map (overlapChartMap R n e f g h) = overlapT R n e f g := by
  ext i j
  simp [chartT, overlapChartMap, overlapPolynomialMap, universalMatrixB]

def overlapLeftUnit (e f : ChartIndex n) : (Matrix n n (OverlapRing R n e f))ˣ :=
  Matrix.nonsingInvUnit (overlapT R n e f e) (overlapT_left_isUnit R n e f)

def overlapRightUnit (e f : ChartIndex n) : (Matrix n n (OverlapRing R n e f))ˣ :=
  Matrix.nonsingInvUnit (overlapT R n e f f) (overlapT_right_isUnit R n e f)

/-- Equality of the actual canonical forms in the two coordinate systems on an overlap. -/
theorem overlap_forms_compatible (e f : ChartIndex n) :
    canonicalTrace (R := R) (overlapT R n e f e) (overlapA R n e f e) =
      canonicalTrace (overlapT R n e f f) (overlapA R n e f f) := by
  apply canonicalTrace_reindex_compatible _ _ (overlapLeftUnit R n e f)
    (overlapRightUnit R n e f) (e.trans f.symm)
  change generalChart (overlapA R n e f e) (overlapT R n e f e) =
    (generalChart (overlapA R n e f f) (overlapT R n e f f)).submatrix _ _
  rw [overlap_normalForm _ _ _ _ _ (overlapT_left_isUnit R n e f),
    overlap_normalForm _ _ _ _ _ (overlapT_right_isUnit R n e f)]
  ext i j
  simp [Matrix.submatrix]

/-- Compatibility is expressed through the actual coordinate homomorphisms
from each chart algebra to the overlap algebra. -/
theorem overlap_pullback_forms_compatible (e f : ChartIndex n) :
    canonicalTrace (R := R)
      ((chartT R n).map (overlapChartMap R n e f e (overlapT_left_isUnit R n e f)))
      ((chartA R n).map (overlapChartMap R n e f e (overlapT_left_isUnit R n e f))) =
    canonicalTrace
      ((chartT R n).map (overlapChartMap R n e f f (overlapT_right_isUnit R n e f)))
      ((chartA R n).map (overlapChartMap R n e f f (overlapT_right_isUnit R n e f))) := by
  rw [overlapChartMap_T, overlapChartMap_A, overlapChartMap_T, overlapChartMap_A]
  exact overlap_forms_compatible R n e f

def localForm : LinearMap.BilinForm (ChartRing R n) (Derivation R (ChartRing R n) (ChartRing R n)) :=
  canonicalTrace (chartT R n) (chartA R n)

theorem localForm_alternating : (localForm R n).IsAlt := canonicalTrace_alternating _ _
theorem localForm_closed : IsClosed (localForm R n) := canonicalTrace_closed _ _

def localFormPerfect : Derivation R (ChartRing R n) (ChartRing R n) ≃ₗ[ChartRing R n]
    Module.Dual (ChartRing R n) (Derivation R (ChartRing R n) (ChartRing R n)) :=
  canonicalTrace_localized_equiv (R := R) (S := ChartRing R n) (n := n)
    (Submonoid.powers (chartDet R n))

theorem localFormPerfect_coe : (localFormPerfect R n).toLinearMap = localForm R n := rfl

def overlapOpen (e f : ChartIndex n) : (squareZeroScheme R n).Opens :=
  PrimeSpectrum.basicOpen (chartMinor R n e * chartMinor R n f)

theorem overlapOpen_eq (e f : ChartIndex n) : overlapOpen R n e f =
    PrimeSpectrum.basicOpen (chartMinor R n e) ⊓ PrimeSpectrum.basicOpen (chartMinor R n f) :=
  PrimeSpectrum.basicOpen_mul _ _

/-- The chosen overlap ring is the coordinate ring of the actual intersection open. -/
def overlapSchemeIso (e f : ChartIndex n) : (overlapOpen R n e f).toScheme ≅
    Spec (.of (OverlapRing R n e f)) := basicOpenIsoSpecAway _

theorem overlapChartMap_universal (e f g : ChartIndex n) (h : IsUnit (overlapT R n e f g).det) :
    (universalMatrix R n).map ((overlapChartMap R n e f g h).comp (toChartBase R n)) =
      (overlapMatrix R n e f).submatrix g g := by
  change ((universalMatrix R n).map (toChartBase R n)).map (overlapChartMap R n e f g h) = _
  rw [toChartBase_universal, map_generalChart, overlapChartMap_A, overlapChartMap_T,
    overlap_normalForm _ _ _ _ _ h]

theorem overlapChartMap_toChartBase (e f g : ChartIndex n)
    (h : IsUnit (overlapT R n e f g).det) :
    (overlapChartMap R n e f g h).comp (toChartBase R n) =
      (IsScalarTower.toAlgHom R (CoordinateRing R n) (OverlapRing R n e f)).comp
        (permuteCoordinate R n g).toAlgHom := by
  have hr : (universalMatrix R n).map
      ((IsScalarTower.toAlgHom R (CoordinateRing R n) (OverlapRing R n e f)).comp
        (permuteCoordinate R n g).toAlgHom) = (overlapMatrix R n e f).submatrix g g := by
    change ((universalMatrix R n).map (permuteCoordinate R n g)).map
      (algebraMap (CoordinateRing R n) (OverlapRing R n e f)) = _
    rw [permuteCoordinate_universal]
    rfl
  have hm := (overlapChartMap_universal R n e f g h).trans hr.symm
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro ij
  exact congrFun (congrFun hm ij.1) ij.2

/-- The base-coordinate map for the chart with permuted ambient basis. -/
def chartEmbeddingBase (e : ChartIndex n) : CoordinateRing R n →ₐ[R] ChartRing R n :=
  (toChartBase R n).comp (permuteCoordinate R n e).symm.toAlgHom

theorem chartEmbeddingBase_refl : chartEmbeddingBase R n (Equiv.refl _) = toChartBase R n := by
  have hh : (permuteCoordinate R n (Equiv.refl _)).toAlgHom = AlgHom.id R (CoordinateRing R n) := by
    have hm := permuteCoordinate_universal R n (Equiv.refl _)
    apply Ideal.Quotient.algHom_ext
    apply MvPolynomial.algHom_ext
    intro ij
    exact congrFun (congrFun hm ij.1) ij.2
  ext a
  change toChartBase R n ((permuteCoordinate R n (Equiv.refl _)).symm a) = toChartBase R n a
  apply congrArg (toChartBase R n)
  simpa using (AlgHom.congr_fun hh ((permuteCoordinate R n (Equiv.refl _)).symm a)).symm

theorem overlapChartMap_embedding (e f g : ChartIndex n)
    (h : IsUnit (overlapT R n e f g).det) :
    (overlapChartMap R n e f g h).comp (chartEmbeddingBase R n g) =
      IsScalarTower.toAlgHom R (CoordinateRing R n) (OverlapRing R n e f) := by
  change ((overlapChartMap R n e f g h).comp (toChartBase R n)).comp
    (permuteCoordinate R n g).symm.toAlgHom = _
  rw [overlapChartMap_toChartBase]
  ext a
  simp

/-- The actual overlap-to-chart morphism commutes with the ambient scheme maps. -/
theorem overlapScheme_map_commutes (e f g : ChartIndex n)
    (h : IsUnit (overlapT R n e f g).det) :
    Spec.map (CommRingCat.ofHom (overlapChartMap R n e f g h).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (chartEmbeddingBase R n g).toRingHom) =
    Spec.map (CommRingCat.ofHom (algebraMap (CoordinateRing R n) (OverlapRing R n e f))) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  exact congrArg (fun φ : CoordinateRing R n →ₐ[R] OverlapRing R n e f =>
    Spec.map (CommRingCat.ofHom φ.toRingHom)) (overlapChartMap_embedding R n e f g h)

theorem overlapOpen_eq_permutation (e f : ChartIndex n) :
    overlapOpen R n e f = permutationOpen R n e ⊓ permutationOpen R n f := overlapOpen_eq R n e f

def actualOverlapIso (e f : ChartIndex n) :
    (permutationOpen R n e ⊓ permutationOpen R n f).toScheme ≅
      Spec (.of (OverlapRing R n e f)) :=
  (squareZeroScheme R n).isoOfEq (overlapOpen_eq_permutation R n e f).symm ≪≫ overlapSchemeIso R n e f

theorem actualOverlapIso_ambient (e f : ChartIndex n) :
    (actualOverlapIso R n e f).hom ≫
      Spec.map (CommRingCat.ofHom (algebraMap (CoordinateRing R n) (OverlapRing R n e f))) =
      (permutationOpen R n e ⊓ permutationOpen R n f).ι := by
  have hfac : (overlapSchemeIso R n e f).hom ≫
      Spec.map (CommRingCat.ofHom (algebraMap (CoordinateRing R n) (OverlapRing R n e f))) =
      (overlapOpen R n e f).ι := IsOpenImmersion.isoOfRangeEq_hom_fac
        (Scheme.Opens.ι (X := Spec (.of (CoordinateRing R n)))
          (PrimeSpectrum.basicOpen (chartMinor R n e * chartMinor R n f))) _ (by
            simp only [Scheme.Opens.range_ι]
            exact (PrimeSpectrum.localization_away_comap_range _ _).symm)
  simpa only [actualOverlapIso, Iso.trans_hom, Category.assoc] using
    (congrArg (fun m => ((squareZeroScheme R n).isoOfEq
      (overlapOpen_eq_permutation R n e f).symm).hom ≫ m) hfac).trans
        (Scheme.isoOfEq_hom_ι _ _)

/-- A compatible affine-chart definition of an algebraic symplectic form on
the actual maximal-rank square-zero scheme. The coefficient algebras, actual
open intersections, and concrete transition homomorphisms are part of the
definition. No compatibility or nondegeneracy is assumed in its construction. -/
structure AlgebraicSymplecticAtlas where
  covers : (⨆ e, permutationOpen R n e) = maximalRankOpen R n
  chartIso : ∀ e : ChartIndex n,
    (permutationOpen R n e).toScheme ≅ Spec (.of (ChartRing R n))
  chart_embedding : ∀ e, (chartIso e).inv ≫ (permutationOpen R n e).ι =
    Spec.map (CommRingCat.ofHom (chartEmbeddingBase R n e).toRingHom)
  overlapIso : ∀ e f : ChartIndex n,
    (permutationOpen R n e ⊓ permutationOpen R n f).toScheme ≅ Spec (.of (OverlapRing R n e f))
  overlap_embedding : ∀ e f, (overlapIso e f).hom ≫
      Spec.map (CommRingCat.ofHom (algebraMap (CoordinateRing R n) (OverlapRing R n e f))) =
    (permutationOpen R n e ⊓ permutationOpen R n f).ι
  form : ChartIndex n → LinearMap.BilinForm (ChartRing R n)
    (Derivation R (ChartRing R n) (ChartRing R n))
  local_formula : ∀ e, form e = canonicalTrace (chartT R n) (chartA R n)
  alternating : ∀ e, (form e).IsAlt
  closed : ∀ e, IsClosed (form e)
  perfect : ∀ _e : ChartIndex n, Derivation R (ChartRing R n) (ChartRing R n) ≃ₗ[ChartRing R n]
    Module.Dual (ChartRing R n) (Derivation R (ChartRing R n) (ChartRing R n))
  perfect_form : ∀ e, (perfect e).toLinearMap = form e
  compatible : ∀ e f,
    canonicalTrace (R := R)
      ((chartT R n).map (overlapChartMap R n e f e (overlapT_left_isUnit R n e f)))
      ((chartA R n).map (overlapChartMap R n e f e (overlapT_left_isUnit R n e f))) =
    canonicalTrace
      ((chartT R n).map (overlapChartMap R n e f f (overlapT_right_isUnit R n e f)))
      ((chartA R n).map (overlapChartMap R n e f f (overlapT_right_isUnit R n e f)))

namespace AlgebraicSymplecticAtlas

variable {R n} (ω : AlgebraicSymplecticAtlas R n)

include ω

/-- The atlas covers the actual orbit scheme by actual scheme open immersions. -/
def openCover : (maximalRankScheme R n).OpenCover :=
  (maximalRankScheme R n).openCoverOfIsOpenCover (orbitChartOpen R n) (by
    exact ((maximalRankOpen R n).ι.preimage_iSup (permutationOpen R n)).symm.trans
      ((congrArg (fun U => (maximalRankOpen R n).ι ⁻¹ᵁ U) ω.covers).trans
        (maximalRankOpen R n).ι_preimage_self))

def orbitChartIso (e : ChartIndex n) :
    (SquareZeroGeometry.orbitChartOpen R n e).toScheme ≅ Spec (.of (ChartRing R n)) :=
  orbitChartToPermutationIso R n e ≪≫ ω.chartIso e

theorem orbitChart_embedding (e : ChartIndex n) :
    (ω.orbitChartIso e).inv ≫ (SquareZeroGeometry.orbitChartOpen R n e).ι ≫
      (maximalRankOpen R n).ι = Spec.map (CommRingCat.ofHom (chartEmbeddingBase R n e).toRingHom) := by
  change (ω.chartIso e).inv ≫ (Scheme.Opens.isoOfLE (permutationOpen_le_maximalRank R n e)).inv ≫
    ((maximalRankOpen R n).ι ⁻¹ᵁ permutationOpen R n e).ι ≫ (maximalRankOpen R n).ι = _
  exact (congrArg (fun m => (ω.chartIso e).inv ≫ m)
    (Scheme.Opens.isoOfLE_inv_ι (permutationOpen_le_maximalRank R n e))).trans (ω.chart_embedding e)

/-- The actual affine-cell morphism factors through this atlas's identity chart
using exactly the coordinate map whose pullback form vanishes. -/
theorem cellMorphism_factors_identity : cellMorphism R n =
    Spec.map (CommRingCat.ofHom (cellChartEval R n).toRingHom) ≫
      (ω.orbitChartIso (Equiv.refl _)).inv ≫
        (SquareZeroGeometry.orbitChartOpen R n (Equiv.refl _)).ι := by
  apply (cancel_mono (maximalRankOpen R n).ι).mp
  have hh := congrArg (fun m => Spec.map (CommRingCat.ofHom (cellChartEval R n).toRingHom) ≫ m)
    (ω.orbitChart_embedding (Equiv.refl _))
  rw [chartEmbeddingBase_refl] at hh
  refine Eq.trans ?_ (by simpa only [Category.assoc] using hh.symm)
  change (Spec.map (CommRingCat.ofHom (cellChartEval R n).toRingHom) ≫
    (topRightChartIso R n).inv ≫ (squareZeroScheme R n).homOfLE
      (topRightOpen_le_maximalRank R n)) ≫ (maximalRankOpen R n).ι = _
  exact (Category.assoc _ _ _).trans (congrArg
    (fun m => Spec.map (CommRingCat.ofHom (cellChartEval R n).toRingHom) ≫ m)
    ((Category.assoc _ _ _).trans ((congrArg (fun m => (topRightChartIso R n).inv ≫ m)
      ((squareZeroScheme R n).homOfLE_ι (topRightOpen_le_maximalRank R n))).trans
      (topRightChartIso_inv_ι R n))))

/-- The left coordinate transition is the actual restriction along the open intersection. -/
theorem left_transition_is_restriction (e f : ChartIndex n) :
    (ω.overlapIso e f).hom ≫
      Spec.map (CommRingCat.ofHom (overlapChartMap R n e f e (overlapT_left_isUnit R n e f)).toRingHom) =
    (squareZeroScheme R n).homOfLE (show permutationOpen R n e ⊓ permutationOpen R n f ≤
      permutationOpen R n e from inf_le_left) ≫ (ω.chartIso e).hom := by
  apply (cancel_mono ((ω.chartIso e).inv ≫ (permutationOpen R n e).ι)).mp
  calc
    _ = (ω.overlapIso e f).hom ≫
        Spec.map (CommRingCat.ofHom (algebraMap (CoordinateRing R n) (OverlapRing R n e f))) := by
      simpa only [Category.assoc, ω.chart_embedding] using congrArg
        (fun m => (ω.overlapIso e f).hom ≫ m)
        (overlapScheme_map_commutes R n e f e (overlapT_left_isUnit R n e f))
    _ = _ := by rw [ω.overlap_embedding]; simp

/-- The right coordinate transition is the actual restriction along the open intersection. -/
theorem right_transition_is_restriction (e f : ChartIndex n) :
    (ω.overlapIso e f).hom ≫
      Spec.map (CommRingCat.ofHom (overlapChartMap R n e f f (overlapT_right_isUnit R n e f)).toRingHom) =
    (squareZeroScheme R n).homOfLE (show permutationOpen R n e ⊓ permutationOpen R n f ≤
      permutationOpen R n f from inf_le_right) ≫ (ω.chartIso f).hom := by
  apply (cancel_mono ((ω.chartIso f).inv ≫ (permutationOpen R n f).ι)).mp
  calc
    _ = (ω.overlapIso e f).hom ≫
        Spec.map (CommRingCat.ofHom (algebraMap (CoordinateRing R n) (OverlapRing R n e f))) := by
      simpa only [Category.assoc, ω.chart_embedding] using congrArg
        (fun m => (ω.overlapIso e f).hom ≫ m)
        (overlapScheme_map_commutes R n e f f (overlapT_right_isUnit R n e f))
    _ = _ := by rw [ω.overlap_embedding]; simp

end AlgebraicSymplecticAtlas

/-- The global algebraic symplectic atlas on the actual orbit scheme.
Every local and overlap obligation is discharged by the constructions above. -/
def orbitSymplecticAtlas : AlgebraicSymplecticAtlas R n where
  covers := permutationOpen_cover R n
  chartIso := permutationChartIso R n
  chart_embedding e := by
    simpa only [chartEmbeddingBase, permutationChartEmbedding] using
      permutationChartIso_inv_ι R n e
  overlapIso := actualOverlapIso R n
  overlap_embedding := actualOverlapIso_ambient R n
  form _ := localForm R n
  local_formula _ := rfl
  alternating _ := localForm_alternating R n
  closed _ := localForm_closed R n
  perfect _ := localFormPerfect R n
  perfect_form _ := localFormPerfect_coe R n
  compatible := overlap_pullback_forms_compatible R n

theorem maximalRankScheme_has_symplecticAtlas : Nonempty (AlgebraicSymplecticAtlas R n) :=
  ⟨orbitSymplecticAtlas R n⟩

/-- The regular symplectic form pulls back to zero along the actual affine-cell
morphism, whose coordinate homomorphism sends the cotangent coordinate `T` to `I`. -/
theorem cell_pullback_form_zero :
    canonicalTrace (R := R) ((chartT R n).map (cellChartEval R n))
      ((chartA R n).map (cellChartEval R n)) = 0 := by
  rw [cellChartEval_T]
  exact canonicalTrace_one _

end
end GlobalSymplectic
end Universality
