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
import Mathlib.Topology.Sheaves.LocalPredicate
import Mathlib.LinearAlgebra.SymmetricAlgebra.Basis
import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Mathlib.LinearAlgebra.Alternating.Curry
import Mathlib.LinearAlgebra.BilinearForm.TensorProduct
import Mathlib.AlgebraicGeometry.Modules.Tilde

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

abbrev ChartIndex : Type u := Equiv.Perm (n ⊕ n)

def chartMinor (e : ChartIndex n) : CoordinateRing R n :=
  ((universalMatrix R n).submatrix e e).toBlocks₁₂.det

/-- The coordinate algebra of the actual intersection of two principal orbit charts. -/
abbrev OverlapRing (e f : ChartIndex n) : Type u :=
  Localization.Away (chartMinor R n e * chartMinor R n f)

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

/-- Alternatingness follows from the local formula. -/
theorem alternating (e : ChartIndex n) : (ω.form e).IsAlt := by
  rw [ω.local_formula]
  exact canonicalTrace_alternating _ _

/-- Closedness follows from the local formula. -/
theorem closed (e : ChartIndex n) : IsClosed (ω.form e) := by
  rw [ω.local_formula]
  exact canonicalTrace_closed _ _

/-- The canonical tangent-to-dual equivalence induces the form on each chart. -/
theorem perfect_form (e : ChartIndex n) :
    (localFormPerfect R n).toLinearMap = ω.form e := by
  rw [ω.local_formula]
  exact localFormPerfect_coe R n

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

abbrev CellRing : Type u := MvPolynomial (n × n) R

/-- The coefficient action induced by the actual cell-to-chart morphism. -/
abbrev cellChartAlgebra : Algebra (ChartRing R n) (CellRing R n) :=
  (cellChartEval R n).toAlgebra

attribute [local instance] cellChartAlgebra

local instance cellChartScalarTower : IsScalarTower R (ChartRing R n) (CellRing R n) :=
  IsScalarTower.of_algHom (cellChartEval R n)

/-- The differential of the actual cell chart map, acting on relative derivations. -/
def cellDifferential : Derivation R (CellRing R n) (CellRing R n) →ₗ[CellRing R n]
    Derivation R (ChartRing R n) (CellRing R n) :=
  Derivation.compAlgebraMapL R (ChartRing R n) (CellRing R n) (CellRing R n)

@[simp] theorem cellDifferential_A (D : Derivation R (CellRing R n) (CellRing R n))
    (i j : n) : cellDifferential R n D (chartA R n i j) = D (MvPolynomial.X (i, j)) := by
  change D (cellChartEval R n (chartA R n i j)) = _
  rw [show cellChartEval R n (chartA R n i j) = MvPolynomial.X (i, j) from
    congrFun (congrFun (cellChartEval_A R n) i) j]

@[simp] theorem cellDifferential_T (D : Derivation R (CellRing R n) (CellRing R n))
    (i j : n) : cellDifferential R n D (chartT R n i j) = 0 := by
  change D (cellChartEval R n (chartT R n i j)) = _
  rw [show cellChartEval R n (chartT R n i j) = (1 : Matrix n n (CellRing R n)) i j from
    congrFun (congrFun (cellChartEval_T R n) i) j]
  simp [Matrix.one_apply, apply_ite]

theorem cellDifferential_injective : Function.Injective (cellDifferential R n) := by
  intro D E h
  apply MvPolynomial.derivation_ext
  rintro ⟨i, j⟩
  simpa only [cellDifferential_A] using congrArg (fun d => d (chartA R n i j)) h

/-- Relative tangent vectors along the cell are determined by the chart coordinates. -/
theorem cellTangent_ext (D E : Derivation R (ChartRing R n) (CellRing R n))
    (hA : ∀ i j, D (chartA R n i j) = E (chartA R n i j))
    (hT : ∀ i j, D (chartT R n i j) = E (chartT R n i j)) : D = E := by
  have hl : D.liftKaehlerDifferential = E.liftKaehlerDifferential := by
    apply (localizedDifferentialBasis (R := R) (S := ChartRing R n)
      (Submonoid.powers (chartDet R n))).ext
    intro p
    rw [localizedDifferentialBasis_apply, Derivation.liftKaehlerDifferential_comp_D,
      Derivation.liftKaehlerDifferential_comp_D]
    rcases p with ⟨i, j⟩ | ⟨i, j⟩
    · exact hA i j
    · exact hT i j
  apply DFunLike.ext
  intro a
  simpa only [Derivation.liftKaehlerDifferential_comp_D] using
    LinearMap.congr_fun hl (KaehlerDifferential.D R (ChartRing R n) a)

/-- The tangent image of the cell is exactly `dT = 0`; the reverse inclusion
constructs a derivation of the cell coordinate ring. -/
theorem mem_range_cellDifferential (D : Derivation R (ChartRing R n) (CellRing R n)) :
    D ∈ LinearMap.range (cellDifferential R n) ↔ ∀ i j, D (chartT R n i j) = 0 := by
  constructor
  · rintro ⟨E, rfl⟩ i j
    exact cellDifferential_T R n E i j
  · intro hT
    refine ⟨MvPolynomial.mkDerivation R (fun ij : n × n => D (chartA R n ij.1 ij.2)), ?_⟩
    apply cellTangent_ext R n
    · intro i j
      rw [cellDifferential_A, MvPolynomial.mkDerivation_X]
    · intro i j
      rw [cellDifferential_T, hT]

def cellTangentEval (a : ChartRing R n) :
    Derivation R (ChartRing R n) (CellRing R n) →ₗ[CellRing R n] CellRing R n where
  toFun D := D a
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem cellTangentEval_apply (a : ChartRing R n)
    (D : Derivation R (ChartRing R n) (CellRing R n)) : cellTangentEval R n a D = D a := rfl

/-- The orbit's canonical form with coefficients restricted along `cellChartEval`.
Its arguments remain derivations of the orbit chart, including normal directions. -/
def cellOrbitForm : LinearMap.BilinForm (CellRing R n)
    (Derivation R (ChartRing R n) (CellRing R n)) :=
  ∑ i, ∑ j,
    let F := (LinearMap.mul (CellRing R n) (CellRing R n)).compl₁₂
      (cellTangentEval R n (chartT R n i j)) (cellTangentEval R n (chartA R n j i))
    F - F.flip

theorem cellOrbitForm_apply (D E : Derivation R (ChartRing R n) (CellRing R n)) :
    cellOrbitForm R n D E = ∑ i, ∑ j,
      (D (chartT R n i j) * E (chartA R n j i) -
        E (chartT R n i j) * D (chartA R n j i)) := by
  simp [cellOrbitForm]

/-- Scalar restriction of an actual chart vector field along the cell. -/
def specializeChartDerivation : Derivation R (ChartRing R n) (ChartRing R n) →ₗ[ChartRing R n]
    Derivation R (ChartRing R n) (CellRing R n) :=
  (Algebra.linearMap (ChartRing R n) (CellRing R n)).compDer

@[simp] theorem specializeChartDerivation_apply
    (D : Derivation R (ChartRing R n) (ChartRing R n)) (a : ChartRing R n) :
    specializeChartDerivation R n D a = cellChartEval R n (D a) := rfl

/-- Every tangent vector along the cell is obtained by scalar restriction of a chart vector field. -/
theorem specializeChartDerivation_surjective : Function.Surjective (specializeChartDerivation R n) := by
  intro D
  let lift : CellRing R n → ChartRing R n := fun b => (cellChartEval_surjective R n b).choose
  have lift_spec (b) : cellChartEval R n (lift b) = b := (cellChartEval_surjective R n b).choose_spec
  let v : ((n × n) ⊕ (n × n)) → ChartRing R n := Sum.elim
    (fun ij => lift (D (chartA R n ij.1 ij.2)))
    (fun ij => lift (D (chartT R n ij.1 ij.2)))
  refine ⟨coordinateDerivation (S := ChartRing R n) (Submonoid.powers (chartDet R n)) v, ?_⟩
  apply cellTangent_ext R n
  · intro i j
    rw [specializeChartDerivation_apply]
    have h := coordinateDerivation_coordinate (R := R) (S := ChartRing R n)
      (Submonoid.powers (chartDet R n)) v (Sum.inl (i, j))
    exact (congrArg (cellChartEval R n) h).trans (lift_spec _)
  · intro i j
    rw [specializeChartDerivation_apply]
    have h := coordinateDerivation_coordinate (R := R) (S := ChartRing R n)
      (Submonoid.powers (chartDet R n)) v (Sum.inr (i, j))
    exact (congrArg (cellChartEval R n) h).trans (lift_spec _)

/-- This is the dual of mathlib's map on Kähler differentials for `cellChartEval`. -/
theorem cellDifferential_kaehler (D : Derivation R (CellRing R n) (CellRing R n)) :
    (cellDifferential R n D).liftKaehlerDifferential =
      (D.liftKaehlerDifferential.restrictScalars (ChartRing R n)).comp
        (KaehlerDifferential.map R R (ChartRing R n) (CellRing R n)) := by
  apply Derivation.liftKaehlerDifferential_unique
  apply DFunLike.ext
  intro a
  change (cellDifferential R n D).liftKaehlerDifferential (KaehlerDifferential.D R (ChartRing R n) a) =
    D.liftKaehlerDifferential
      (KaehlerDifferential.map R R (ChartRing R n) (CellRing R n)
        (KaehlerDifferential.D R (ChartRing R n) a))
  rw [Derivation.liftKaehlerDifferential_comp_D, KaehlerDifferential.map_D,
    Derivation.liftKaehlerDifferential_comp_D]
  rfl

/-- The restricted pairing is the scalar extension of the same canonical orbit form. -/
theorem cellOrbitForm_specialize (D E : Derivation R (ChartRing R n) (ChartRing R n)) :
    cellOrbitForm R n (specializeChartDerivation R n D) (specializeChartDerivation R n E) =
      cellChartEval R n (localForm R n D E) := by
  rw [cellOrbitForm_apply]
  change (∑ i, ∑ j, (cellChartEval R n (D (chartT R n i j)) *
      cellChartEval R n (E (chartA R n j i)) -
        cellChartEval R n (E (chartT R n i j)) * cellChartEval R n (D (chartA R n j i)))) = _
  simp [localForm, canonicalTrace, coordinateForm_apply, map_sum, map_sub, map_mul]

theorem cellOrbitForm_partial (D : Derivation R (ChartRing R n) (CellRing R n)) (i j : n) :
    cellOrbitForm R n
      (cellDifferential R n (MvPolynomial.mkDerivation R
        (fun p : n × n => if p = (j, i) then 1 else 0))) D = -D (chartT R n i j) := by
  simp [cellOrbitForm_apply, cellDifferential_T, cellDifferential_A, MvPolynomial.mkDerivation_X,
    Prod.mk.injEq, ite_and]

/-- The image of the actual cell differential equals its symplectic orthogonal,
over every commutative base ring. -/
theorem cellDifferential_selfOrthogonal :
    (cellOrbitForm R n).orthogonal (LinearMap.range (cellDifferential R n)) =
      LinearMap.range (cellDifferential R n) := by
  ext D
  constructor
  · intro h
    apply (mem_range_cellDifferential R n D).mpr
    intro i j
    have hh := h (cellDifferential R n (MvPolynomial.mkDerivation R
      (fun p : n × n => if p = (j, i) then 1 else 0))) ⟨_, rfl⟩
    change cellOrbitForm R n _ D = 0 at hh
    rw [cellOrbitForm_partial] at hh
    exact neg_eq_zero.mp hh
  · intro h E hE
    have hD := (mem_range_cellDifferential R n D).mp h
    have hE' := (mem_range_cellDifferential R n E).mp hE
    change cellOrbitForm R n E D = 0
    simp [cellOrbitForm_apply, hD, hE']


end
end GlobalSymplectic
end Universality

namespace Universality.AffineForms
noncomputable section
open Matrix
variable {R S n : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [Fintype n] [DecidableEq n]

theorem derivMatrix_inv (D : Derivation R S S) (g : (Matrix n n S)ˣ) :
    derivMatrix D g.inv = -(g.inv * derivMatrix D g.val * g.inv) := by
  have h := congrArg (derivMatrix D) g.inv_val
  rw [derivMatrix_mul, derivMatrix_one] at h
  have hm := congrArg (fun M => M * g.inv) h
  simp only [add_mul, mul_assoc, Units.val_inv, mul_one, zero_mul] at hm
  simpa only [mul_assoc] using eq_neg_of_add_eq_zero_left hm

omit [Fintype n] [DecidableEq n] in
theorem derivMatrix_commutator (D E : Derivation R S S) (M : Matrix n n S) :
    derivMatrix ⁅D, E⁆ M = derivMatrix D (derivMatrix E M) - derivMatrix E (derivMatrix D M) := by
  ext i j
  simp [derivMatrix, Derivation.commutator_apply]

def maurerCartan (g : (Matrix n n S)ˣ) (D : Derivation R S S) : Matrix n n S :=
  g.inv * derivMatrix D g.val

/-- The left Maurer–Cartan equation, evaluated on arbitrary algebraic vector fields. -/
theorem maurerCartan_equation (g : (Matrix n n S)ˣ) (D E : Derivation R S S) :
    derivMatrix D (maurerCartan g E) - derivMatrix E (maurerCartan g D) - maurerCartan g ⁅D, E⁆ =
      -Symplectic.comm (maurerCartan g D) (maurerCartan g E) := by
  simp only [maurerCartan, derivMatrix_mul, derivMatrix_inv, derivMatrix_commutator, Symplectic.comm]
  noncomm_ring

def rightMaurerCartan (g : (Matrix n n S)ˣ) (D : Derivation R S S) : Matrix n n S :=
  derivMatrix D g.val * g.inv

theorem rightMaurerCartan_eq_conjugate (g : (Matrix n n S)ˣ) (D : Derivation R S S) :
    rightMaurerCartan g D = Symplectic.conjugate g (maurerCartan g D) := by
  simp [rightMaurerCartan, Symplectic.conjugate, maurerCartan, ← mul_assoc]

/-- Differentiating actual conjugation gives the commutator tangent map. -/
theorem conjugation_derivative (g : (Matrix n n S)ˣ) (J : Matrix n n S)
    (D : Derivation R S S) (hJ : derivMatrix D J = 0) :
    derivMatrix D (Symplectic.conjugate g J) =
      Symplectic.comm (rightMaurerCartan g D) (Symplectic.conjugate g J) := by
  have hi : derivMatrix D (g.val)⁻¹ = -(g.inv * derivMatrix D g.val * g.inv) := by
    simpa only [← Matrix.coe_units_inv] using derivMatrix_inv D g
  simp only [Symplectic.conjugate, derivMatrix_mul, hJ, mul_zero, add_zero,
    Symplectic.comm, rightMaurerCartan]
  simp [mul_assoc, sub_eq_add_neg, hi]

/-- Pullback of the KKS trace formula along conjugation. -/
theorem conjugation_KKS_pullback (g : (Matrix n n S)ˣ) (J : Matrix n n S)
    (D E : Derivation R S S) :
    Symplectic.traceForm (Symplectic.conjugate g J)
      (rightMaurerCartan g D) (rightMaurerCartan g E) =
      Matrix.trace (J * Symplectic.comm (maurerCartan g D) (maurerCartan g E)) := by
  rw [rightMaurerCartan_eq_conjugate, rightMaurerCartan_eq_conjugate, Symplectic.traceForm_conjugate]
  rfl

omit [DecidableEq n] in
theorem derivation_trace (D : Derivation R S S) (M : Matrix n n S) :
    D (Matrix.trace M) = Matrix.trace (derivMatrix D M) := by
  simp [Matrix.trace, Matrix.diag, derivMatrix, map_sum]

def maurerCartanTrace (g : (Matrix n n S)ˣ) (J : Matrix n n S) (D : Derivation R S S) : S :=
  Matrix.trace (J * maurerCartan g D)

/-- `π*ω = -d tr(J g⁻¹dg)`, with the actual conjugation derivative and KKS pairing. -/
theorem conjugation_KKS_exact (g : (Matrix n n S)ˣ) (J : Matrix n n S)
    (D E : Derivation R S S) (hDJ : derivMatrix D J = 0) (hEJ : derivMatrix E J = 0) :
    Symplectic.traceForm (Symplectic.conjugate g J)
      (rightMaurerCartan g D) (rightMaurerCartan g E) =
      -(D (maurerCartanTrace g J E) - E (maurerCartanTrace g J D) - maurerCartanTrace g J ⁅D, E⁆) := by
  rw [conjugation_KKS_pullback]
  have h := congrArg (fun M => Matrix.trace (J * M)) (maurerCartan_equation g D E)
  simp only [mul_sub, mul_neg, Matrix.trace_sub, Matrix.trace_neg] at h
  simp only [maurerCartanTrace, derivation_trace, derivMatrix_mul, hDJ, hEJ, zero_mul, zero_add]
  exact (neg_eq_iff_eq_neg.mp h.symm)

end

noncomputable section
open Matrix
variable {S n : Type*} [CommRing S] [Fintype n] [DecidableEq n]

def infinitesimalA (A : Matrix n n S) (X : Matrix (n ⊕ n) (n ⊕ n) S) : Matrix n n S :=
  -A * X.toBlocks₁₁ - X.toBlocks₂₁ + A * X.toBlocks₁₂ * A + X.toBlocks₂₂ * A

def infinitesimalT (A T : Matrix n n S) (X : Matrix (n ⊕ n) (n ⊕ n) S) : Matrix n n S :=
  X.toBlocks₁₁ * T - X.toBlocks₁₂ * A * T - T * A * X.toBlocks₁₂ - T * X.toBlocks₂₂

omit [DecidableEq n] in
theorem infinitesimal_comm (A T : Matrix n n S) (X : Matrix (n ⊕ n) (n ⊕ n) S) :
    Symplectic.comm X (generalChart A T) =
      Matrix.fromBlocks (infinitesimalT A T X * A + T * infinitesimalA A X) (infinitesimalT A T X)
        (-(infinitesimalA A X * T * A + A * infinitesimalT A T X * A + A * T * infinitesimalA A X))
        (-(infinitesimalA A X * T + A * infinitesimalT A T X)) := by
  conv_lhs => arg 1; rw [← Matrix.fromBlocks_toBlocks X]
  simp only [Symplectic.comm, generalChart, Matrix.fromBlocks_multiply, fromBlocks_sub,
    Matrix.fromBlocks_inj, infinitesimalA, infinitesimalT]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> noncomm_ring

theorem infinitesimalA_generator (A : Matrix n n S) (T : (Matrix n n S)ˣ) (dA dT : Matrix n n S) :
    infinitesimalA A (chartGenerator A T dA dT) = dA := by
  simp [infinitesimalA, chartGenerator_blocks]

theorem infinitesimalT_generator (A : Matrix n n S) (T : (Matrix n n S)ˣ) (dA dT : Matrix n n S) :
    infinitesimalT A T.val (chartGenerator A T dA dT) = dT := by
  simp [infinitesimalT, chartGenerator_blocks, mul_assoc]

end

noncomputable section
variable {S n : Type*} [CommRing S] [Fintype n]

theorem infinitesimalA_add (A : Matrix n n S) (X Y : Matrix (n ⊕ n) (n ⊕ n) S) :
    infinitesimalA A (X + Y) = infinitesimalA A X + infinitesimalA A Y := by
  have h₁ : (X + Y).toBlocks₁₁ = X.toBlocks₁₁ + Y.toBlocks₁₁ := rfl
  have h₂ : (X + Y).toBlocks₁₂ = X.toBlocks₁₂ + Y.toBlocks₁₂ := rfl
  have h₃ : (X + Y).toBlocks₂₁ = X.toBlocks₂₁ + Y.toBlocks₂₁ := rfl
  have h₄ : (X + Y).toBlocks₂₂ = X.toBlocks₂₂ + Y.toBlocks₂₂ := rfl
  simp only [infinitesimalA, h₁, h₂, h₃, h₄, add_mul, mul_add]
  abel

theorem infinitesimalT_add (A T : Matrix n n S) (X Y : Matrix (n ⊕ n) (n ⊕ n) S) :
    infinitesimalT A T (X + Y) = infinitesimalT A T X + infinitesimalT A T Y := by
  have h₁ : (X + Y).toBlocks₁₁ = X.toBlocks₁₁ + Y.toBlocks₁₁ := rfl
  have h₂ : (X + Y).toBlocks₁₂ = X.toBlocks₁₂ + Y.toBlocks₁₂ := rfl
  have h₄ : (X + Y).toBlocks₂₂ = X.toBlocks₂₂ + Y.toBlocks₂₂ := rfl
  simp only [infinitesimalT, h₁, h₂, h₄, add_mul, mul_add]
  abel

theorem infinitesimalA_smul (A : Matrix n n S) (a : S) (X : Matrix (n ⊕ n) (n ⊕ n) S) :
    infinitesimalA A (a • X) = a • infinitesimalA A X := by
  have h₁ : (a • X).toBlocks₁₁ = a • X.toBlocks₁₁ := rfl
  have h₂ : (a • X).toBlocks₁₂ = a • X.toBlocks₁₂ := rfl
  have h₃ : (a • X).toBlocks₂₁ = a • X.toBlocks₂₁ := rfl
  have h₄ : (a • X).toBlocks₂₂ = a • X.toBlocks₂₂ := rfl
  simp only [infinitesimalA, h₁, h₂, h₃, h₄, smul_mul_assoc, mul_smul_comm, smul_add, smul_sub]

theorem infinitesimalT_smul (A T : Matrix n n S) (a : S) (X : Matrix (n ⊕ n) (n ⊕ n) S) :
    infinitesimalT A T (a • X) = a • infinitesimalT A T X := by
  have h₁ : (a • X).toBlocks₁₁ = a • X.toBlocks₁₁ := rfl
  have h₂ : (a • X).toBlocks₁₂ = a • X.toBlocks₁₂ := rfl
  have h₄ : (a • X).toBlocks₂₂ = a • X.toBlocks₂₂ := rfl
  simp only [infinitesimalT, h₁, h₂, h₄, smul_mul_assoc, mul_smul_comm, smul_sub]

end
end Universality.AffineForms

namespace Universality.GlobalSymplectic
noncomputable section
open AffineForms SquareZeroGeometry
universe u
variable (R n : Type u) [CommRing R] [Fintype n] [DecidableEq n]

omit [Fintype n] in
theorem derivMatrix_jordanCell {S : Type u} [CommRing S] [Algebra R S]
    (D : Derivation R S S) : derivMatrix D (jordanCell : Matrix (n ⊕ n) (n ⊕ n) S) = 0 := by
  ext (i | i) (j | j) <;> simp [jordanCell, derivMatrix, Matrix.one_apply, apply_ite]

/-- The computed derivative is that of the coordinate map defining the actual quotient morphism. -/
theorem orbitProjection_derivative (D : Derivation R (GeneralLinearRing R n) (GeneralLinearRing R n)) :
    derivMatrix D ((universalMatrix R n).map (orbitCoordinateMap R n)) =
      Symplectic.comm (rightMaurerCartan (generalLinearUnit R n) D)
        ((universalMatrix R n).map (orbitCoordinateMap R n)) := by
  rw [orbitCoordinateMap_matrix]
  exact conjugation_derivative (generalLinearUnit R n) jordanCell D (derivMatrix_jordanCell R n D)

theorem orbitProjection_KKS_exact
    (D E : Derivation R (GeneralLinearRing R n) (GeneralLinearRing R n)) :
    Symplectic.traceForm ((universalMatrix R n).map (orbitCoordinateMap R n))
      (rightMaurerCartan (generalLinearUnit R n) D) (rightMaurerCartan (generalLinearUnit R n) E) =
      -(D (maurerCartanTrace (generalLinearUnit R n) jordanCell E) -
        E (maurerCartanTrace (generalLinearUnit R n) jordanCell D) -
        maurerCartanTrace (generalLinearUnit R n) jordanCell ⁅D, E⁆) := by
  rw [orbitCoordinateMap_matrix]
  exact conjugation_KKS_exact (generalLinearUnit R n) jordanCell D E
    (derivMatrix_jordanCell R n D) (derivMatrix_jordanCell R n E)

end

noncomputable section
open AffineForms SquareZeroGeometry
universe u
variable (R n : Type u) [CommRing R] [Fintype n] [DecidableEq n]

def chartTangentProjectionFun (X : Matrix (n ⊕ n) (n ⊕ n) (ChartRing R n)) :
    Derivation R (ChartRing R n) (ChartRing R n) :=
  coordinateDerivation (Submonoid.powers (chartDet R n))
    (Sum.elim (fun ij => infinitesimalA (chartA R n) X ij.1 ij.2)
      (fun ij => infinitesimalT (chartA R n) (chartT R n) X ij.1 ij.2))

theorem chartTangentProjection_A (X : Matrix (n ⊕ n) (n ⊕ n) (ChartRing R n)) :
    derivMatrix (chartTangentProjectionFun R n X) (chartA R n) = infinitesimalA (chartA R n) X := by
  ext i j
  exact coordinateDerivation_coordinate _ _ (Sum.inl (i, j))

theorem chartTangentProjection_T (X : Matrix (n ⊕ n) (n ⊕ n) (ChartRing R n)) :
    derivMatrix (chartTangentProjectionFun R n X) (chartT R n) =
      infinitesimalT (chartA R n) (chartT R n) X := by
  ext i j
  exact coordinateDerivation_coordinate _ _ (Sum.inr (i, j))

/-- The local tangent map sends an ambient matrix `X` to the actual derivative `[X,Z]`. -/
theorem chartTangentProjection_derivative (X : Matrix (n ⊕ n) (n ⊕ n) (ChartRing R n)) :
    derivMatrix (chartTangentProjectionFun R n X) (generalChart (chartA R n) (chartT R n)) =
      Symplectic.comm X (generalChart (chartA R n) (chartT R n)) := by
  rw [derivMatrix_generalChart, chartTangentProjection_A, chartTangentProjection_T, infinitesimal_comm]

theorem chartTangentProjection_split (D : Derivation R (ChartRing R n) (ChartRing R n)) :
    chartTangentProjectionFun R n
      (chartGenerator (chartA R n) (chartUnitT R n) (derivMatrix D (chartA R n))
        (derivMatrix D (chartT R n))) = D := by
  apply derivation_ext_coordinates (Submonoid.powers (chartDet R n))
  rintro (ij | ij)
  · have h := chartTangentProjection_A R n
      (chartGenerator (chartA R n) (chartUnitT R n) (derivMatrix D (chartA R n))
        (derivMatrix D (chartT R n)))
    rw [infinitesimalA_generator] at h
    exact congrFun (congrFun h ij.1) ij.2
  · have h := chartTangentProjection_T R n
      (chartGenerator (chartA R n) (chartUnitT R n) (derivMatrix D (chartA R n))
        (derivMatrix D (chartT R n)))
    have hg := infinitesimalT_generator (chartA R n) (chartUnitT R n)
      (derivMatrix D (chartA R n)) (derivMatrix D (chartT R n))
    exact congrFun (congrFun (h.trans hg) ij.1) ij.2

end

noncomputable section
open AffineForms SquareZeroGeometry
universe u
variable (R n : Type u) [CommRing R] [Fintype n] [DecidableEq n]

/-- The commutator map into the actual module of algebraic vector fields on an orbit chart. -/
def chartTangentProjection :
    Matrix (n ⊕ n) (n ⊕ n) (ChartRing R n) →ₗ[ChartRing R n]
      Derivation R (ChartRing R n) (ChartRing R n) where
  toFun := chartTangentProjectionFun R n
  map_add' X Y := by
    apply derivation_ext_coordinates (Submonoid.powers (chartDet R n))
    rintro (ij | ij)
    · have h := (chartTangentProjection_A R n (X + Y)).trans
        ((infinitesimalA_add (chartA R n) X Y).trans
          (congrArg₂ (· + ·) (chartTangentProjection_A R n X).symm (chartTangentProjection_A R n Y).symm))
      exact congrFun (congrFun h ij.1) ij.2
    · have h := (chartTangentProjection_T R n (X + Y)).trans
        ((infinitesimalT_add (chartA R n) (chartT R n) X Y).trans
          (congrArg₂ (· + ·) (chartTangentProjection_T R n X).symm (chartTangentProjection_T R n Y).symm))
      exact congrFun (congrFun h ij.1) ij.2
  map_smul' a X := by
    apply derivation_ext_coordinates (Submonoid.powers (chartDet R n))
    rintro (ij | ij)
    · have h := (chartTangentProjection_A R n (a • X)).trans
        ((infinitesimalA_smul (chartA R n) a X).trans
          (congrArg (a • ·) (chartTangentProjection_A R n X).symm))
      exact congrFun (congrFun h ij.1) ij.2
    · have h := (chartTangentProjection_T R n (a • X)).trans
        ((infinitesimalT_smul (chartA R n) (chartT R n) a X).trans
          (congrArg (a • ·) (chartTangentProjection_T R n X).symm))
      exact congrFun (congrFun h ij.1) ij.2

/-- A linear section of the tangent projection, obtained from explicit lifts of the coordinate basis. -/
def chartTangentSection : Derivation R (ChartRing R n) (ChartRing R n) →ₗ[ChartRing R n]
    Matrix (n ⊕ n) (n ⊕ n) (ChartRing R n) :=
  (coordinateDerivationBasis (S := ChartRing R n) (Submonoid.powers (chartDet R n))).constr
    (ChartRing R n) (fun i =>
      let D := coordinateDerivationBasis (S := ChartRing R n) (Submonoid.powers (chartDet R n)) i
      chartGenerator (chartA R n) (chartUnitT R n)
        (derivMatrix D (chartA R n)) (derivMatrix D (chartT R n)))

set_option maxHeartbeats 800000 in
theorem chartTangentProjection_section :
    (chartTangentProjection R n).comp (chartTangentSection R n) = LinearMap.id := by
  apply (coordinateDerivationBasis (S := ChartRing R n) (Submonoid.powers (chartDet R n))).ext
  intro i
  simp only [LinearMap.comp_apply, LinearMap.id_apply, chartTangentSection, Module.Basis.constr_basis]
  exact chartTangentProjection_split R n _

theorem chartTangentProjection_surjective : Function.Surjective (chartTangentProjection R n) := by
  intro D
  exact ⟨chartTangentSection R n D, LinearMap.congr_fun (chartTangentProjection_section R n) D⟩

end
end Universality.GlobalSymplectic

namespace Universality.AffineForms
noncomputable section
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
universe u
variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]

abbrev PrimeLocalRing (p : PrimeSpectrum A) : Type u := Localization.AtPrime p.asIdeal

def principalToPrime (f : A) (p : PrimeSpectrum A) (hf : p ∈ PrimeSpectrum.basicOpen f) :
    Localization.Away f →+* PrimeLocalRing A p :=
  IsLocalization.Away.lift f (g := algebraMap A (PrimeLocalRing A p))
    (IsLocalization.map_units (M := p.asIdeal.primeCompl) (PrimeLocalRing A p) ⟨f, hf⟩)

@[simp] theorem principalToPrime_algebraMap (f : A) (p : PrimeSpectrum A)
    (hf : p ∈ PrimeSpectrum.basicOpen f) (a : A) :
    principalToPrime A f p hf (algebraMap A (Localization.Away f) a) =
      algebraMap A (PrimeLocalRing A p) a := by
  unfold principalToPrime
  exact IsLocalization.Away.lift_eq _ _ _

def principalToPrimeAlg (f : A) (p : PrimeSpectrum A) (hf : p ∈ PrimeSpectrum.basicOpen f) :
    Localization.Away f →ₐ[A] PrimeLocalRing A p where
  __ := principalToPrime A f p hf
  commutes' := principalToPrime_algebraMap A f p hf

/-- A two-form germ is a bilinear form on derivations of the actual prime localization. -/
abbrev TwoFormGerm (p : PrimeSpectrum A) : Type u :=
  LinearMap.BilinForm (PrimeLocalRing A p) (Derivation R (PrimeLocalRing A p) (PrimeLocalRing A p))

/-- Regular local expressions are finite sums `c da ∧ db`, with coefficients in a principal
localization. Sheafifying this local predicate permits these expressions to vary by neighborhood. -/
def regularTwoFormPrelocal : TopCat.PrelocalPredicate
    (X := PrimeSpectrum.Top A) (TwoFormGerm R A) where
  pred {U} s := ∃ (f : A) (hU : U ≤ PrimeSpectrum.basicOpen f)
      (I : Type u) (_ : Fintype I) (c a b : I → Localization.Away f),
    ∀ p : U, s p = ∑ i, principalToPrime A f p.val (hU p.property) (c i) •
      coordinateForm (R := R)
        (principalToPrime A f p.val (hU p.property) (a i))
        (principalToPrime A f p.val (hU p.property) (b i))
  res i s h := by
    obtain ⟨f, hU, I, hI, c, a, b, hs⟩ := h
    exact ⟨f, i.le.trans hU, I, hI, c, a, b, fun p => hs (i p)⟩

/-- The sheaf of regular algebraic two-forms, expressed on the prime-local derivation modules. -/
def regularTwoFormSheaf : TopCat.Sheaf (Type u) (PrimeSpectrum.Top A) :=
  TopCat.subsheafToTypes (regularTwoFormPrelocal R A).sheafify

end
end Universality.AffineForms

namespace Universality.GlobalSymplectic
noncomputable section
open AffineForms SquareZeroGeometry AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
universe u
variable (R n : Type u) [CommRing R] [Fintype n] [DecidableEq n]

section Coefficients
variable (S : Type u) [CommRing S] [Algebra (CoordinateRing R n) S]

def coefficientMatrix : Matrix (n ⊕ n) (n ⊕ n) S :=
  (universalMatrix R n).map (algebraMap (CoordinateRing R n) S)

def coefficientT (e : Equiv.Perm (n ⊕ n)) : Matrix n n S :=
  ((coefficientMatrix R n S).submatrix e e).toBlocks₁₂

def coefficientA (e : Equiv.Perm (n ⊕ n)) : Matrix n n S :=
  (coefficientT R n S e)⁻¹ * ((coefficientMatrix R n S).submatrix e e).toBlocks₁₁

theorem coefficient_normalForm (e : Equiv.Perm (n ⊕ n)) (h : IsUnit (coefficientT R n S e).det) :
    generalChart (coefficientA R n S e) (coefficientT R n S e) =
      (coefficientMatrix R n S).submatrix e e := by
  have hs : (coefficientMatrix R n S).submatrix e e * (coefficientMatrix R n S).submatrix e e = 0 := by
    rw [Matrix.submatrix_mul_equiv]
    change ((universalMatrix R n).map (algebraMap (CoordinateRing R n) S) *
      (universalMatrix R n).map (algebraMap (CoordinateRing R n) S)).submatrix e e = 0
    rw [← Matrix.map_mul, universalMatrix_square]
    ext i j
    simp
  have hh := square_zero_invertible_block_normalForm
    ((coefficientMatrix R n S).submatrix e e).toBlocks₁₁
    ((coefficientMatrix R n S).submatrix e e).toBlocks₂₁
    ((coefficientMatrix R n S).submatrix e e).toBlocks₂₂
    (coefficientT R n S e) h (by simpa only [coefficientT, Matrix.fromBlocks_toBlocks] using hs)
  simpa only [coefficientA, coefficientT, Matrix.fromBlocks_toBlocks] using hh

theorem coefficientT_det (e : Equiv.Perm (n ⊕ n)) :
    (coefficientT R n S e).det = algebraMap (CoordinateRing R n) S (chartMinor R n e) :=
  ((algebraMap (CoordinateRing R n) S).map_det _).symm

variable [Algebra R S]

theorem coefficient_forms_compatible (e f : Equiv.Perm (n ⊕ n))
    (he : IsUnit (coefficientT R n S e).det) (hf : IsUnit (coefficientT R n S f).det) :
    canonicalTrace (R := R) (coefficientT R n S e) (coefficientA R n S e) =
      canonicalTrace (coefficientT R n S f) (coefficientA R n S f) := by
  apply canonicalTrace_reindex_compatible _ _
    (Matrix.nonsingInvUnit _ he) (Matrix.nonsingInvUnit _ hf) (e.trans f.symm)
  change generalChart (coefficientA R n S e) (coefficientT R n S e) =
    (generalChart (coefficientA R n S f) (coefficientT R n S f)).submatrix _ _
  rw [coefficient_normalForm R n S e he, coefficient_normalForm R n S f hf]
  ext i j
  simp [Matrix.submatrix]

end Coefficients

omit [DecidableEq n] in
theorem coefficientMatrix_map {S B : Type u} [CommRing S] [CommRing B]
    [Algebra (CoordinateRing R n) S] [Algebra (CoordinateRing R n) B]
    (φ : S →ₐ[CoordinateRing R n] B) :
    (coefficientMatrix R n S).map φ = coefficientMatrix R n B := by
  ext i j
  exact φ.commutes _

omit [DecidableEq n] in
theorem coefficientT_map {S B : Type u} [CommRing S] [CommRing B]
    [Algebra (CoordinateRing R n) S] [Algebra (CoordinateRing R n) B]
    (φ : S →ₐ[CoordinateRing R n] B) (e : Equiv.Perm (n ⊕ n)) :
    (coefficientT R n S e).map φ = coefficientT R n B e := by
  have h := coefficientMatrix_map R n φ
  exact congrArg (fun M => (M.submatrix e e).toBlocks₁₂) h

theorem coefficientA_map {S B : Type u} [CommRing S] [CommRing B]
    [Algebra (CoordinateRing R n) S] [Algebra (CoordinateRing R n) B]
    (φ : S →ₐ[CoordinateRing R n] B) (e : Equiv.Perm (n ⊕ n))
    (hS : IsUnit (coefficientT R n S e).det) (hB : IsUnit (coefficientT R n B e).det) :
    (coefficientA R n S e).map φ = coefficientA R n B e := by
  have h := congrArg (fun M => (M.map φ).toBlocks₁₁) (coefficient_normalForm R n S e hS)
  have hm := coefficientMatrix_map R n φ
  have hT := coefficientT_map R n φ e
  change (coefficientT R n S e * coefficientA R n S e).map φ =
    (((coefficientMatrix R n S).map φ).submatrix e e).toBlocks₁₁ at h
  rw [Matrix.map_mul, hT, hm] at h
  have hh := congrArg (fun M => (coefficientT R n B e)⁻¹ * M) h
  simpa only [← mul_assoc, Matrix.nonsing_inv_mul _ hB, one_mul, coefficientA] using hh

theorem prime_coefficientT_isUnit (p : PrimeSpectrum (CoordinateRing R n))
    (e : Equiv.Perm (n ⊕ n)) (he : p ∈ permutationOpen R n e) :
    IsUnit (coefficientT R n (PrimeLocalRing (CoordinateRing R n) p) e).det := by
  rw [coefficientT_det]
  exact IsLocalization.map_units (M := p.asIdeal.primeCompl)
    (PrimeLocalRing (CoordinateRing R n) p) ⟨chartMinor R n e, he⟩

theorem principal_coefficientT_isUnit (e : Equiv.Perm (n ⊕ n)) :
    IsUnit (coefficientT R n (Localization.Away (chartMinor R n e)) e).det := by
  rw [coefficientT_det]
  exact IsLocalization.Away.algebraMap_isUnit _

def primeChartForm (p : PrimeSpectrum (CoordinateRing R n)) (e : Equiv.Perm (n ⊕ n)) :
    TwoFormGerm R (CoordinateRing R n) p :=
  canonicalTrace (coefficientT R n (PrimeLocalRing (CoordinateRing R n) p) e)
    (coefficientA R n (PrimeLocalRing (CoordinateRing R n) p) e)

theorem primeChartForm_eq (p : PrimeSpectrum (CoordinateRing R n)) (e f : Equiv.Perm (n ⊕ n))
    (he : p ∈ permutationOpen R n e) (hf : p ∈ permutationOpen R n f) :
    primeChartForm R n p e = primeChartForm R n p f :=
  coefficient_forms_compatible R n _ e f
    (prime_coefficientT_isUnit R n p e he) (prime_coefficientT_isUnit R n p f hf)

theorem exists_prime_chart (p : maximalRankOpen R n) : ∃ e, p.val ∈ permutationOpen R n e := by
  have hp : p.val ∈ (⨆ e, permutationOpen R n e) := by
    rw [permutationOpen_cover]
    exact p.property
  exact Opens.mem_iSup.mp hp

def orbitFormValue (p : maximalRankOpen R n) : TwoFormGerm R (CoordinateRing R n) p.val :=
  primeChartForm R n p.val (exists_prime_chart R n p).choose

theorem orbitFormValue_eq (p : maximalRankOpen R n) (e : Equiv.Perm (n ⊕ n))
    (he : p.val ∈ permutationOpen R n e) : orbitFormValue R n p = primeChartForm R n p.val e :=
  primeChartForm_eq R n p.val _ e (exists_prime_chart R n p).choose_spec he

/-- A single global section of the regular two-form sheaf on the orbit. -/
def orbitGlobalTwoForm :
    (regularTwoFormSheaf R (CoordinateRing R n)).obj.obj (op (maximalRankOpen R n)) := by
  refine ⟨orbitFormValue R n, ?_⟩
  intro p
  obtain ⟨e, he⟩ := exists_prime_chart R n p
  refine ⟨permutationOpen R n e, he, homOfLE (permutationOpen_le_maximalRank R n e), ?_⟩
  refine ⟨chartMinor R n e, le_rfl, n × n, inferInstance, (fun _ => 1),
    (fun ij => coefficientT R n (Localization.Away (chartMinor R n e)) e ij.1 ij.2),
    (fun ij => coefficientA R n (Localization.Away (chartMinor R n e)) e ij.2 ij.1), ?_⟩
  intro q
  dsimp only
  rw [orbitFormValue_eq R n _ e q.property]
  let φ := principalToPrimeAlg (CoordinateRing R n) (chartMinor R n e) q.val q.property
  have hT := coefficientT_map R n φ e
  have hA := coefficientA_map R n φ e (principal_coefficientT_isUnit R n e)
    (prime_coefficientT_isUnit R n q.val e q.property)
  change canonicalTrace (R := R)
    (coefficientT R n (PrimeLocalRing (CoordinateRing R n) q.val) e)
    (coefficientA R n (PrimeLocalRing (CoordinateRing R n) q.val) e) = _
  rw [← hT, ← hA]
  simp only [canonicalTrace, Fintype.sum_prod_type, map_one, one_smul]
  rfl

theorem orbitGlobalTwoForm_chart (p : maximalRankOpen R n) (e : Equiv.Perm (n ⊕ n))
    (he : p.val ∈ permutationOpen R n e) :
    (orbitGlobalTwoForm R n).val p = primeChartForm R n p.val e :=
  orbitFormValue_eq R n p e he

theorem orbitGlobalTwoForm_alternating (p : maximalRankOpen R n) :
    ((orbitGlobalTwoForm R n).val p).IsAlt :=
  canonicalTrace_alternating _ _

theorem orbitGlobalTwoForm_closed (p : maximalRankOpen R n) :
    IsClosed ((orbitGlobalTwoForm R n).val p) :=
  canonicalTrace_closed _ _

def primeChartEvaluation (p : PrimeSpectrum (CoordinateRing R n)) (e : Equiv.Perm (n ⊕ n))
    (he : p ∈ permutationOpen R n e) : ChartRing R n →ₐ[R] PrimeLocalRing (CoordinateRing R n) p :=
  chartEval R n (coefficientA R n (PrimeLocalRing (CoordinateRing R n) p) e)
    (Matrix.nonsingInvUnit _ (prime_coefficientT_isUnit R n p e he))

theorem primeChartEvaluation_A (p : PrimeSpectrum (CoordinateRing R n)) (e : Equiv.Perm (n ⊕ n))
    (he : p ∈ permutationOpen R n e) :
    (chartA R n).map (primeChartEvaluation R n p e he) =
      coefficientA R n (PrimeLocalRing (CoordinateRing R n) p) e := chartEval_A R n _ _

theorem primeChartEvaluation_T (p : PrimeSpectrum (CoordinateRing R n)) (e : Equiv.Perm (n ⊕ n))
    (he : p ∈ permutationOpen R n e) :
    (chartT R n).map (primeChartEvaluation R n p e he) =
      coefficientT R n (PrimeLocalRing (CoordinateRing R n) p) e :=
  congrArg Units.val (chartEval_T R n _ _)

/-- The chart-to-germ homomorphism is over the actual square-zero coordinate ring. -/
theorem primeChartEvaluation_over (p : PrimeSpectrum (CoordinateRing R n)) (e : Equiv.Perm (n ⊕ n))
    (he : p ∈ permutationOpen R n e) :
    (primeChartEvaluation R n p e he).comp (permutationChartEmbedding R n e) =
      IsScalarTower.toAlgHom R (CoordinateRing R n) (PrimeLocalRing (CoordinateRing R n) p) := by
  have hm : ((universalMatrix R n).map (permutationChartEmbedding R n e)).map
      (primeChartEvaluation R n p e he) = coefficientMatrix R n (PrimeLocalRing (CoordinateRing R n) p) := by
    rw [permutationChartEmbedding_matrix]
    have hchart : (generalChart (chartA R n) (chartT R n)).map (primeChartEvaluation R n p e he) =
        generalChart ((chartA R n).map (primeChartEvaluation R n p e he))
          ((chartT R n).map (primeChartEvaluation R n p e he)) := by
      ext (i | i) (j | j) <;>
        simp [generalChart, Matrix.mul_apply, map_sum, map_mul]
    change ((generalChart (chartA R n) (chartT R n)).map
      (primeChartEvaluation R n p e he)).submatrix e.symm e.symm = _
    rw [hchart, primeChartEvaluation_A, primeChartEvaluation_T,
      coefficient_normalForm R n _ e (prime_coefficientT_isUnit R n p e he)]
    ext i j
    simp [Matrix.submatrix]
  apply quotientAlgHom_ext
  intro ij
  exact congrFun (congrFun hm ij.1) ij.2

/-- The global sheaf section restricts to the same concrete form as the verified symplectic atlas. -/
theorem orbitGlobalTwoForm_atlas (p : maximalRankOpen R n) (e : Equiv.Perm (n ⊕ n))
    (he : p.val ∈ permutationOpen R n e) :
    (orbitGlobalTwoForm R n).val p =
      canonicalTrace (R := R) ((chartT R n).map (primeChartEvaluation R n p.val e he))
        ((chartA R n).map (primeChartEvaluation R n p.val e he)) := by
  rw [orbitGlobalTwoForm_chart R n p e he, primeChartEvaluation_T, primeChartEvaluation_A]
  rfl

theorem toChartBase_isLocalization :
    letI := (toChartBase R n).toAlgebra
    IsLocalization.Away (topRightDet R n) (ChartRing R n) := by
  letI := (toChartBase R n).toAlgebra
  let e : LocalCoordinateRing R n ≃ₐ[CoordinateRing R n] ChartRing R n :=
    { (chartAlgEquiv R n).toRingEquiv with
      commutes' := by
        intro x
        change toChart R n (algebraMap (CoordinateRing R n) (LocalCoordinateRing R n) x) =
          toChartBase R n x
        exact awayLift_algebraMap R _ _ _ x }
  exact IsLocalization.isLocalization_of_algEquiv (Submonoid.powers (topRightDet R n)) e

theorem permutationChart_isLocalization (e : Equiv.Perm (n ⊕ n)) :
    letI := (permutationChartEmbedding R n e).toAlgebra
    IsLocalization.Away (chartMinor R n e) (ChartRing R n) := by
  letI := (toChartBase R n).toAlgebra
  letI := toChartBase_isLocalization R n
  have h := IsLocalization.isLocalization_of_base_ringEquiv
    (Submonoid.powers (topRightDet R n)) (ChartRing R n) (permuteCoordinate R n e).toRingEquiv
  simpa only [Submonoid.map_powers, AlgEquiv.coe_ringEquiv, permuteCoordinate_det, chartMinor] using h

/-- The polynomial chart coordinates evaluated in a local ring of the orbit. -/
def primeChartPolynomialEvaluation (p : PrimeSpectrum (CoordinateRing R n))
    (e : Equiv.Perm (n ⊕ n)) (he : p ∈ permutationOpen R n e) :
    ChartPolynomialRing R n →ₐ[R] PrimeLocalRing (CoordinateRing R n) p :=
  (primeChartEvaluation R n p e he).comp
    (IsScalarTower.toAlgHom R (ChartPolynomialRing R n) (ChartRing R n))

/-- A local ring on a chart is a localization of its polynomial coordinate ring. -/
theorem primeChartPolynomial_isLocalization (p : PrimeSpectrum (CoordinateRing R n))
    (e : Equiv.Perm (n ⊕ n)) (he : p ∈ permutationOpen R n e) :
    letI := (primeChartPolynomialEvaluation R n p e he).toAlgebra
    IsLocalization (IsLocalization.localizationLocalizationSubmodule
      (Submonoid.powers (chartDet R n))
      (p.asIdeal.primeCompl.map (permutationChartEmbedding R n e).toRingHom))
      (PrimeLocalRing (CoordinateRing R n) p) := by
  letI := (permutationChartEmbedding R n e).toAlgebra
  letI := permutationChart_isLocalization R n e
  letI := (primeChartEvaluation R n p e he).toAlgebra
  letI : IsScalarTower (CoordinateRing R n) (ChartRing R n)
      (PrimeLocalRing (CoordinateRing R n) p) :=
    IsScalarTower.of_algebraMap_eq' (congrArg AlgHom.toRingHom (primeChartEvaluation_over R n p e he)).symm
  have hle : Submonoid.powers (chartMinor R n e) ≤ p.asIdeal.primeCompl := by
    rintro x ⟨m, rfl⟩
    exact p.asIdeal.primeCompl.pow_mem he m
  let N := p.asIdeal.primeCompl.map (permutationChartEmbedding R n e).toRingHom
  letI : IsLocalization N (PrimeLocalRing (CoordinateRing R n) p) :=
    IsLocalization.isLocalization_of_submonoid_le (ChartRing R n)
      (PrimeLocalRing (CoordinateRing R n) p) _ _ hle
  letI : Algebra (ChartPolynomialRing R n) (PrimeLocalRing (CoordinateRing R n) p) :=
    (primeChartPolynomialEvaluation R n p e he).toAlgebra
  letI : SMul (ChartPolynomialRing R n) (PrimeLocalRing (CoordinateRing R n) p) :=
    (primeChartPolynomialEvaluation R n p e he).toAlgebra.toSMul
  letI : IsScalarTower (ChartPolynomialRing R n) (ChartRing R n)
      (PrimeLocalRing (CoordinateRing R n) p) :=
    IsScalarTower.of_algebraMap_eq' (R := ChartPolynomialRing R n) (S := ChartRing R n)
      (A := PrimeLocalRing (CoordinateRing R n) p) rfl
  exact IsLocalization.localization_localization_isLocalization _ _ _

theorem primeChartForm_perfect (p : PrimeSpectrum (CoordinateRing R n))
    (e : Equiv.Perm (n ⊕ n)) (he : p ∈ permutationOpen R n e) :
    Function.Bijective (primeChartForm R n p e) := by
  letI := (primeChartPolynomialEvaluation R n p e he).toAlgebra
  letI := IsScalarTower.of_algHom (primeChartPolynomialEvaluation R n p e he)
  letI := primeChartPolynomial_isLocalization R n p e he
  have h := (canonicalTrace_localized_equiv (R := R)
    (S := PrimeLocalRing (CoordinateRing R n) p) (n := n)
    (IsLocalization.localizationLocalizationSubmodule (Submonoid.powers (chartDet R n))
      (p.asIdeal.primeCompl.map (permutationChartEmbedding R n e).toRingHom))).bijective
  rw [show primeChartForm R n p e = canonicalTrace (R := R)
      (coordinateT (R := R) (S := PrimeLocalRing (CoordinateRing R n) p) (n := n))
      (coordinateA (R := R) (S := PrimeLocalRing (CoordinateRing R n) p) (n := n)) from ?_]
  · exact h
  · unfold primeChartForm
    rw [← primeChartEvaluation_T R n p e he, ← primeChartEvaluation_A R n p e he]
    rfl

theorem orbitGlobalTwoForm_perfect (p : maximalRankOpen R n) :
    Function.Bijective ((orbitGlobalTwoForm R n).val p) := by
  obtain ⟨e, he⟩ := exists_prime_chart R n p
  rw [orbitGlobalTwoForm_chart R n p e he]
  exact primeChartForm_perfect R n p.val e he

end
end Universality.GlobalSymplectic

namespace Universality.AffineGeometry
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits SquareZeroGeometry AffineForms
universe u
variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]

/-- The coordinate algebra of the relative tangent scheme of `Spec A`. -/
abbrev TangentRing : Type u := SymmetricAlgebra A (KaehlerDifferential R A)

def tangentScheme : Scheme.{u} := Spec (.of (TangentRing R A))

def tangentProjection : tangentScheme R A ⟶ Spec (.of A) :=
  Spec.map (CommRingCat.ofHom (algebraMap A (TangentRing R A)))

def tangentAlgebraHomEquiv (S : Type u) [CommRing S] [Algebra A S]
    [Algebra R S] [IsScalarTower R A S] :
    (TangentRing R A →ₐ[A] S) ≃ Derivation R A S :=
  SymmetricAlgebra.lift.symm.trans (KaehlerDifferential.linearMapEquivDerivation R A).toEquiv

@[simp] theorem tangentAlgebraHomEquiv_symm_apply (S : Type u) [CommRing S] [Algebra A S]
    [Algebra R S] [IsScalarTower R A S] (D : Derivation R A S) (a : A) :
    (tangentAlgebraHomEquiv R A S).symm D
      (SymmetricAlgebra.ι A _ (KaehlerDifferential.D R A a)) = D a := by
  exact (SymmetricAlgebra.lift_ι_apply _ _).trans (Derivation.liftKaehlerDifferential_comp_D D a)

variable {A} (B : Type u) [CommRing B] [Algebra A B]

def affineOverHomEquiv (T : Scheme.{u}) (x : T ⟶ Spec (.of A)) :
    {f : T ⟶ Spec (.of B) // f ≫ Spec.map (CommRingCat.ofHom (algebraMap A B)) = x} ≃
      (letI := (affineCoordinates x).toAlgebra; B →ₐ[A] Γ(T, ⊤)) := by
  letI := (affineCoordinates x).toAlgebra
  refine
    { toFun := fun f =>
        { __ := affineCoordinates f.val
          commutes' := fun a => by
            have h := congrArg affineCoordinates f.property
            rw [affineCoordinates_specMap] at h
            exact DFunLike.congr_fun h a }
      invFun := fun φ => ⟨T.toSpecΓ ≫ Spec.map (CommRingCat.ofHom φ.toRingHom), by
        apply affineCoordinates_injective
        rw [affineCoordinates_specMap, affineCoordinates_toSpec]
        ext a
        exact φ.commutes a⟩
      left_inv := ?_
      right_inv := ?_ }
  · intro f
    apply Subtype.ext
    apply affineCoordinates_injective
    exact affineCoordinates_toSpec _ _
  · intro φ
    apply AlgHom.ext
    intro b
    exact DFunLike.congr_fun (affineCoordinates_toSpec _ _) b

variable (A)

def tangentHomEquiv (T : Scheme.{u}) (x : T ⟶ Spec (.of A)) :
    {f : T ⟶ tangentScheme R A // f ≫ tangentProjection R A = x} ≃
      (letI := (affineCoordinates x).toAlgebra
       letI : Algebra R Γ(T, ⊤) := ((affineCoordinates x).comp (algebraMap R A)).toAlgebra
       Derivation R A Γ(T, ⊤)) := by
  letI := (affineCoordinates x).toAlgebra
  letI : Algebra R Γ(T, ⊤) := ((affineCoordinates x).comp (algebraMap R A)).toAlgebra
  letI : IsScalarTower R A Γ(T, ⊤) :=
    IsScalarTower.of_algebraMap_eq' (R := R) (S := A) (A := Γ(T, ⊤)) rfl
  exact (affineOverHomEquiv (TangentRing R A) T x).trans (tangentAlgebraHomEquiv R A Γ(T, ⊤))

def openTangentScheme (U : (Spec (.of A)).Opens) : Scheme.{u} :=
  pullback (tangentProjection R A) U.ι

def openTangentProjection (U : (Spec (.of A)).Opens) : openTangentScheme R A U ⟶ U.toScheme :=
  pullback.snd _ _

def openTangentHomEquiv (U : (Spec (.of A)).Opens) (T : Scheme.{u}) (x : T ⟶ U.toScheme) :
    {f : T ⟶ openTangentScheme R A U // f ≫ openTangentProjection R A U = x} ≃
      {f : T ⟶ tangentScheme R A // f ≫ tangentProjection R A = x ≫ U.ι} where
  toFun f := ⟨f.val ≫ pullback.fst _ _, by
    calc
      _ = f.val ≫ (pullback.snd (tangentProjection R A) U.ι ≫ U.ι) :=
        (Category.assoc _ _ _).trans (congrArg (fun h => f.val ≫ h)
          (pullback.condition (f := tangentProjection R A) (g := U.ι)))
      _ = x ≫ U.ι := (Category.assoc _ _ _).symm.trans
        (congrArg (fun h => h ≫ U.ι) f.property)⟩
  invFun f := ⟨pullback.lift f.val x f.property, pullback.lift_snd _ _ _⟩
  left_inv f := by
    apply Subtype.ext
    apply pullback.hom_ext
    · exact pullback.lift_fst _ _ _
    · simpa only [pullback.lift_snd] using f.property.symm
  right_inv f := Subtype.ext (pullback.lift_fst _ _ _)

def tangentChartIso {I : Type u} (b : Module.Basis I A (KaehlerDifferential R A)) :
    tangentScheme R A ≅ Spec (.of (MvPolynomial I A)) :=
  Scheme.Spec.mapIso (SymmetricAlgebra.equivMvPolynomial b).symm.toRingEquiv.toCommRingCatIso.op

theorem tangentChartIso_over {I : Type u} (b : Module.Basis I A (KaehlerDifferential R A)) :
    (tangentChartIso R A b).hom ≫ Spec.map (CommRingCat.ofHom (algebraMap A (MvPolynomial I A))) =
      tangentProjection R A := by
  change Spec.map (CommRingCat.ofHom (SymmetricAlgebra.equivMvPolynomial b).symm.toRingHom) ≫ _ = _
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 1
  exact CommRingCat.hom_ext (RingHom.ext fun a => (SymmetricAlgebra.equivMvPolynomial b).symm.commutes a)

section BaseChange
variable [Algebra R B] [IsScalarTower R A B]

def tangentMap : TangentRing R A →+* TangentRing R B := by
  letI : Algebra A (TangentRing R B) := RingHom.toAlgebra
    ((algebraMap B (TangentRing R B)).comp (algebraMap A B))
  letI : IsScalarTower A B (TangentRing R B) :=
    IsScalarTower.of_algebraMap_eq' (R := A) (S := B) (A := TangentRing R B) rfl
  let f : KaehlerDifferential R A →ₗ[A] TangentRing R B :=
    { toFun := fun w => SymmetricAlgebra.ι B _ (KaehlerDifferential.map R R A B w)
      map_add' := by intros; simp
      map_smul' := by
        intro a w
        rw [map_smul, RingHom.id_apply, ← IsScalarTower.algebraMap_smul B a _, map_smul]
        rfl }
  exact (SymmetricAlgebra.lift f).toRingHom

@[simp] theorem tangentMap_algebraMap (a : A) :
    tangentMap R A B (algebraMap A (TangentRing R A) a) =
      algebraMap B (TangentRing R B) (algebraMap A B a) :=
  AlgHom.commutes _ a

@[simp] theorem tangentMap_D (a : A) :
    tangentMap R A B (SymmetricAlgebra.ι A _ (KaehlerDifferential.D R A a)) =
      SymmetricAlgebra.ι B _ (KaehlerDifferential.D R B (algebraMap A B a)) := by
  simp [tangentMap, KaehlerDifferential.map_D]

def tangentSchemeMap : tangentScheme R B ⟶ tangentScheme R A :=
  Spec.map (CommRingCat.ofHom (tangentMap R A B))

theorem tangentSchemeMap_over :
    tangentSchemeMap R A B ≫ tangentProjection R A =
      tangentProjection R B ≫ Spec.map (CommRingCat.ofHom (algebraMap A B)) := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  exact RingHom.ext (tangentMap_algebraMap R A B)

theorem tangentMap_represents_derivative (S : Type u) [CommRing S] [Algebra B S]
    [Algebra R S] [IsScalarTower R B S] (D : Derivation R B S) (a : A) :
    (tangentAlgebraHomEquiv R B S).symm D
      (tangentMap R A B (SymmetricAlgebra.ι A _ (KaehlerDifferential.D R A a))) =
        D (algebraMap A B a) := by
  rw [tangentMap_D, tangentAlgebraHomEquiv_symm_apply]

variable (S : Type u) [CommRing S] [Algebra B S] [Algebra A S] [Algebra R S]
  [IsScalarTower A B S] [IsScalarTower R B S] [IsScalarTower R A S]

def extendDerivation [Algebra.FormallyEtale A B] (D : Derivation R A S) : Derivation R B S :=
  ((D.liftKaehlerDifferential.liftBaseChange B).comp
    (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale R A B).symm.toLinearMap).compDer
      (KaehlerDifferential.D R B)

@[simp] theorem extendDerivation_algebraMap [Algebra.FormallyEtale A B]
    (D : Derivation R A S) (a : A) : extendDerivation R A B S D (algebraMap A B a) = D a := by
  simp [extendDerivation, KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_symm_D_algebraMap,
    LinearMap.liftBaseChange_tmul, Derivation.liftKaehlerDifferential_comp_D]

theorem derivation_ext_of_formallyEtale [Algebra.FormallyEtale A B]
    (D E : Derivation R B S) (h : ∀ a, D (algebraMap A B a) = E (algebraMap A B a)) : D = E := by
  have hh : D.liftKaehlerDifferential.comp
        (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale R A B).toLinearMap =
      E.liftKaehlerDifferential.comp
        (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale R A B).toLinearMap := by
    apply LinearMap.restrictScalars_injective A
    apply TensorProduct.ext
    ext b a
    simp [KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_apply,
      KaehlerDifferential.mapBaseChange_tmul, KaehlerDifferential.map_D, h]
  have hl : D.liftKaehlerDifferential = E.liftKaehlerDifferential :=
    (LinearMap.cancel_right (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale R A B).surjective).mp hh
  ext b
  simpa using LinearMap.congr_fun hl (KaehlerDifferential.D R B b)

end BaseChange

theorem tangentRingHom_ext {S : Type u} [CommRing S] (f g : TangentRing R A →+* S)
    (hb : ∀ a, f (algebraMap A (TangentRing R A) a) = g (algebraMap A (TangentRing R A) a))
    (hd : ∀ a, f (SymmetricAlgebra.ι A _ (KaehlerDifferential.D R A a)) =
      g (SymmetricAlgebra.ι A _ (KaehlerDifferential.D R A a))) : f = g := by
  letI : Algebra A S := (f.comp (algebraMap A (TangentRing R A))).toAlgebra
  letI : Algebra R S := ((algebraMap A S).comp (algebraMap R A)).toAlgebra
  letI : IsScalarTower R A S := IsScalarTower.of_algebraMap_eq' (R := R) (S := A) (A := S) rfl
  let F : TangentRing R A →ₐ[A] S := { __ := f, commutes' := fun _ => rfl }
  let G : TangentRing R A →ₐ[A] S := { __ := g, commutes' := fun a => (hb a).symm }
  have h : F = G := by
    apply SymmetricAlgebra.algHom_ext
    apply Derivation.liftKaehlerDifferential_unique
    ext a
    exact hd a
  exact congrArg AlgHom.toRingHom h

set_option synthInstance.maxHeartbeats 100000 in
set_option maxHeartbeats 800000 in
theorem tangentMap_isPushout [Algebra R B] [IsScalarTower R A B] [Algebra.FormallyEtale A B] :
    IsPushout (CommRingCat.ofHom (algebraMap A B))
      (CommRingCat.ofHom (algebraMap A (TangentRing R A)))
      (CommRingCat.ofHom (algebraMap B (TangentRing R B)))
      (CommRingCat.ofHom (tangentMap R A B)) where
  w := by ext a; exact (tangentMap_algebraMap R A B a).symm
  isColimit' := ⟨PushoutCocone.isColimitAux' _ fun s => by
    let S := s.pt
    letI : Algebra B S := s.inl.hom.toAlgebra
    letI : Algebra A S := (s.inl.hom.comp (algebraMap A B)).toAlgebra
    letI : Algebra R S := ((algebraMap A S).comp (algebraMap R A)).toAlgebra
    letI : IsScalarTower A B S := IsScalarTower.of_algebraMap_eq' (R := A) (S := B) (A := S) rfl
    letI : IsScalarTower R A S := IsScalarTower.of_algebraMap_eq' (R := R) (S := A) (A := S) rfl
    letI : IsScalarTower R B S := IsScalarTower.of_algebraMap_eq' (R := R) (S := B) (A := S)
      (by ext r; exact congrArg s.inl.hom (IsScalarTower.algebraMap_apply R A B r).symm)
    have hb (a : A) : s.inl.hom (algebraMap A B a) =
        s.inr.hom (algebraMap A (TangentRing R A) a) :=
      congrArg (fun f => f.hom a) s.condition
    let F : TangentRing R A →ₐ[A] S := { __ := s.inr.hom, commutes' := fun a => (hb a).symm }
    let D := tangentAlgebraHomEquiv R A S F
    have hD (a : A) : F (SymmetricAlgebra.ι A _ (KaehlerDifferential.D R A a)) = D a := by
      simpa only [D, Equiv.symm_apply_apply] using tangentAlgebraHomEquiv_symm_apply R A S D a
    let E := extendDerivation R A B S D
    let L := (tangentAlgebraHomEquiv R B S).symm E
    have h₁ : CommRingCat.ofHom (algebraMap B (TangentRing R B)) ≫
        CommRingCat.ofHom L.toRingHom = s.inl := by
      ext b
      exact L.commutes b
    have h₂ : CommRingCat.ofHom (tangentMap R A B) ≫
        CommRingCat.ofHom L.toRingHom = s.inr := by
      apply CommRingCat.hom_ext
      apply tangentRingHom_ext R A
      · intro a
        change L (tangentMap R A B (algebraMap A _ a)) = _
        rw [tangentMap_algebraMap, L.commutes]
        exact hb a
      · intro a
        change L (tangentMap R A B (SymmetricAlgebra.ι A _ (KaehlerDifferential.D R A a))) = _
        rw [tangentMap_D, tangentAlgebraHomEquiv_symm_apply, extendDerivation_algebraMap]
        exact (hD a).symm
    refine ⟨CommRingCat.ofHom L.toRingHom, h₁, h₂, ?_⟩
    intro m hm₁ hm₂
    let M : TangentRing R B →ₐ[B] S :=
      { __ := m.hom, commutes' := fun b => congrArg (fun f => f.hom b) hm₁ }
    have hM (b : B) : M (SymmetricAlgebra.ι B _ (KaehlerDifferential.D R B b)) =
        tangentAlgebraHomEquiv R B S M b := by
      simpa only [Equiv.symm_apply_apply] using
        tangentAlgebraHomEquiv_symm_apply R B S (tangentAlgebraHomEquiv R B S M) b
    have hE : tangentAlgebraHomEquiv R B S M = E := by
      apply derivation_ext_of_formallyEtale R A B S
      intro a
      rw [← hM, extendDerivation_algebraMap, ← hD, ← tangentMap_D]
      exact congrArg (fun f => f.hom (SymmetricAlgebra.ι A _ (KaehlerDifferential.D R A a))) hm₂
    apply CommRingCat.hom_ext
    exact congrArg AlgHom.toRingHom ((tangentAlgebraHomEquiv R B S).injective
      (hE.trans ((tangentAlgebraHomEquiv R B S).apply_symm_apply E).symm))⟩

def tangentBaseChangeIso [Algebra R B] [IsScalarTower R A B] [Algebra.FormallyEtale A B] :
    tangentScheme R B ≅ pullback (Spec.map (CommRingCat.ofHom (algebraMap A B)))
      (tangentProjection R A) :=
  (isPullback_SpecMap_of_isPushout _ _ _ _ (tangentMap_isPushout R A B)).isoPullback

section OpenChart
variable [Algebra R B] [IsScalarTower R A B] [Algebra.FormallyEtale A B]
variable (U : (Spec (.of A)).Opens) (c : Spec (.of B) ⟶ U.toScheme)
  (hc : c ≫ U.ι = Spec.map (CommRingCat.ofHom (algebraMap A B)))

def tangentLiftToOpen : tangentScheme R B ⟶ openTangentScheme R A U :=
  pullback.lift (Spec.map (CommRingCat.ofHom (tangentMap R A B)))
    (tangentProjection R B ≫ c) (by
      rw [Category.assoc, hc]
      exact (isPullback_SpecMap_of_isPushout _ _ _ _ (tangentMap_isPushout R A B)).w.symm)

theorem tangentLiftToOpen_isPullback :
    IsPullback (tangentLiftToOpen R A B U c hc) (tangentProjection R B)
      (openTangentProjection R A U) c := by
  have hp := (isPullback_SpecMap_of_isPushout _ _ _ _ (tangentMap_isPushout R A B)).flip
  have hp' : IsPullback
      (tangentLiftToOpen R A B U c hc ≫ pullback.fst (tangentProjection R A) U.ι)
      (tangentProjection R B) (tangentProjection R A) (c ≫ U.ι) := by
    have hfst : tangentLiftToOpen R A B U c hc ≫ pullback.fst (tangentProjection R A) U.ι =
        Spec.map (CommRingCat.ofHom (tangentMap R A B)) := pullback.lift_fst _ _ _
    rw [hfst, hc]
    exact hp
  exact hp'.of_right (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback _ _)

def openTangentChartIso {I : Type u} (b : Module.Basis I B (KaehlerDifferential R B)) :
    pullback (openTangentProjection R A U) c ≅ Spec (.of (MvPolynomial I B)) :=
  (tangentLiftToOpen_isPullback R A B U c hc).isoPullback.symm ≪≫ tangentChartIso R B b

theorem openTangentChartIso_over {I : Type u} (b : Module.Basis I B (KaehlerDifferential R B)) :
    (openTangentChartIso R A B U c hc b).hom ≫
      Spec.map (CommRingCat.ofHom (algebraMap B (MvPolynomial I B))) =
        pullback.snd (openTangentProjection R A U) c := by
  change ((tangentLiftToOpen_isPullback R A B U c hc).isoPullback.inv ≫
    (tangentChartIso R B b).hom) ≫ _ = _
  rw [Category.assoc, tangentChartIso_over]
  exact (tangentLiftToOpen_isPullback R A B U c hc).isoPullback_inv_snd

end OpenChart

end
end Universality.AffineGeometry

namespace Universality.GlobalSymplectic
noncomputable section
open AffineGeometry AffineForms SquareZeroGeometry AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
variable (R n : Type u) [CommRing R] [Fintype n] [DecidableEq n]

def orbitTangentScheme : Scheme.{u} :=
  openTangentScheme R (CoordinateRing R n) (maximalRankOpen R n)

def orbitTangentProjection : orbitTangentScheme R n ⟶ maximalRankScheme R n :=
  openTangentProjection R (CoordinateRing R n) (maximalRankOpen R n)

def orbitProjectionTangentMap :
    tangentScheme R (GeneralLinearRing R n) ⟶ orbitTangentScheme R n := by
  letI := (orbitCoordinateMap R n).toAlgebra
  letI := IsScalarTower.of_algHom (orbitCoordinateMap R n)
  exact pullback.lift (tangentSchemeMap R (CoordinateRing R n) (GeneralLinearRing R n))
    (tangentProjection R (GeneralLinearRing R n) ≫ orbitProjection R n) (by
      exact (tangentSchemeMap_over R (CoordinateRing R n) (GeneralLinearRing R n)).trans
        ((congrArg (fun h => tangentProjection R (GeneralLinearRing R n) ≫ h)
          (orbitProjection_ι R n).symm).trans (Category.assoc _ _ _).symm))

theorem orbitProjectionTangentMap_over :
    orbitProjectionTangentMap R n ≫ orbitTangentProjection R n =
      tangentProjection R (GeneralLinearRing R n) ≫ orbitProjection R n :=
  pullback.lift_snd _ _ _

theorem orbitProjectionTangentMap_affine :
    letI := (orbitCoordinateMap R n).toAlgebra
    letI := IsScalarTower.of_algHom (orbitCoordinateMap R n)
    orbitProjectionTangentMap R n ≫
      pullback.fst (tangentProjection R (CoordinateRing R n)) (maximalRankOpen R n).ι =
        tangentSchemeMap R (CoordinateRing R n) (GeneralLinearRing R n) := by
  letI := (orbitCoordinateMap R n).toAlgebra
  letI := IsScalarTower.of_algHom (orbitCoordinateMap R n)
  exact pullback.lift_fst _ _ _

theorem orbitProjectionTangentMap_commutator
    (D : Derivation R (GeneralLinearRing R n) (GeneralLinearRing R n)) :
    letI := (orbitCoordinateMap R n).toAlgebra
    letI := IsScalarTower.of_algHom (orbitCoordinateMap R n)
    (fun i j => (tangentAlgebraHomEquiv R (GeneralLinearRing R n) (GeneralLinearRing R n)).symm D
      (tangentMap R (CoordinateRing R n) (GeneralLinearRing R n)
        (SymmetricAlgebra.ι _ _ (KaehlerDifferential.D R _ (universalMatrix R n i j))))) =
      Symplectic.comm (rightMaurerCartan (generalLinearUnit R n) D)
        ((universalMatrix R n).map (orbitCoordinateMap R n)) := by
  letI := (orbitCoordinateMap R n).toAlgebra
  letI := IsScalarTower.of_algHom (orbitCoordinateMap R n)
  simp only [tangentMap_represents_derivative]
  exact orbitProjection_derivative R n D

def orbitChartMap (e : Equiv.Perm (n ⊕ n)) : Spec (.of (ChartRing R n)) ⟶ maximalRankScheme R n :=
  (SquareZeroGeometry.orbitChartIso R n e).inv ≫ (orbitChartOpen R n e).ι

theorem orbitChartMap_over (e : Equiv.Perm (n ⊕ n)) :
    orbitChartMap R n e ≫ (maximalRankOpen R n).ι =
      Spec.map (CommRingCat.ofHom (permutationChartEmbedding R n e).toRingHom) := by
  simpa only [orbitChartMap, Category.assoc] using
    (orbitSymplecticAtlas R n).orbitChart_embedding e

def orbitTangentChartIso (e : Equiv.Perm (n ⊕ n)) :
    pullback (orbitTangentProjection R n) (orbitChartMap R n e) ≅
      Spec (.of (MvPolynomial ((n × n) ⊕ (n × n)) (ChartRing R n))) := by
  letI := (permutationChartEmbedding R n e).toAlgebra
  letI : IsScalarTower R (CoordinateRing R n) (ChartRing R n) :=
    IsScalarTower.of_algebraMap_eq' (R := R) (S := CoordinateRing R n) (A := ChartRing R n)
      (RingHom.ext fun r => ((permutationChartEmbedding R n e).commutes r).symm)
  letI := permutationChart_isLocalization R n e
  letI : Algebra.FormallyEtale (CoordinateRing R n) (ChartRing R n) :=
    Algebra.FormallyEtale.of_isLocalization (Rₘ := ChartRing R n) (Submonoid.powers (chartMinor R n e))
  exact openTangentChartIso R (CoordinateRing R n) (ChartRing R n) (maximalRankOpen R n)
    (orbitChartMap R n e) (orbitChartMap_over R n e)
    (localizedDifferentialBasis (R := R) (S := ChartRing R n) (Submonoid.powers (chartDet R n)))

theorem orbitTangentChartIso_over (e : Equiv.Perm (n ⊕ n)) :
    (orbitTangentChartIso R n e).hom ≫
      Spec.map (CommRingCat.ofHom (algebraMap (ChartRing R n)
        (MvPolynomial ((n × n) ⊕ (n × n)) (ChartRing R n)))) =
      pullback.snd (orbitTangentProjection R n) (orbitChartMap R n e) := by
  letI := (permutationChartEmbedding R n e).toAlgebra
  letI : IsScalarTower R (CoordinateRing R n) (ChartRing R n) :=
    IsScalarTower.of_algebraMap_eq' (R := R) (S := CoordinateRing R n) (A := ChartRing R n)
      (RingHom.ext fun r => ((permutationChartEmbedding R n e).commutes r).symm)
  letI := permutationChart_isLocalization R n e
  letI : Algebra.FormallyEtale (CoordinateRing R n) (ChartRing R n) :=
    Algebra.FormallyEtale.of_isLocalization (Rₘ := ChartRing R n) (Submonoid.powers (chartMinor R n e))
  exact openTangentChartIso_over R (CoordinateRing R n) (ChartRing R n) (maximalRankOpen R n)
    (orbitChartMap R n e) (orbitChartMap_over R n e)
    (localizedDifferentialBasis (R := R) (S := ChartRing R n) (Submonoid.powers (chartDet R n)))

def orbitTangentHomEquiv (T : Scheme.{u}) (x : T ⟶ maximalRankScheme R n) :
    {f : T ⟶ orbitTangentScheme R n // f ≫ orbitTangentProjection R n = x} ≃
      (letI := (affineCoordinates (x ≫ (maximalRankOpen R n).ι)).toAlgebra
       letI : Algebra R Γ(T, ⊤) :=
         ((affineCoordinates (x ≫ (maximalRankOpen R n).ι)).comp
           (algebraMap R (CoordinateRing R n))).toAlgebra
       Derivation R (CoordinateRing R n) Γ(T, ⊤)) :=
  (openTangentHomEquiv R (CoordinateRing R n) (maximalRankOpen R n) T x).trans
    (tangentHomEquiv R (CoordinateRing R n) T (x ≫ (maximalRankOpen R n).ι))

end
end Universality.GlobalSymplectic

namespace Universality.ExteriorGeometry
noncomputable section
open scoped TensorProduct
open AffineForms AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
universe u
variable (A : Type u) [CommRing A]
variable {M N : Type u} [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]

def alternatingToBilinear (f : AlternatingMap A M N (Fin 2)) : LinearMap.BilinMap A M N :=
  LinearMap.mk₂ A (fun x y => f ![x, y])
    (fun x y z => f.map_vecCons_add ![z] x y)
    (fun a x y => f.map_vecCons_smul ![y] a x)
    (fun x y z => by simpa using (f.curryLeft x).map_vecCons_add ![] y z)
    (fun a x y => by simpa using (f.curryLeft x).map_vecCons_smul ![] a y)

@[simp] theorem alternatingToBilinear_apply (f : AlternatingMap A M N (Fin 2)) (x y : M) :
    alternatingToBilinear A f x y = f ![x, y] := rfl

def bilinearToAlternating (f : LinearMap.BilinMap A M N) (h : ∀ x, f x x = 0) :
    AlternatingMap A M N (Fin 2) where
  toFun v := f (v 0) (v 1)
  map_update_add' v i x y := by fin_cases i <;> simp
  map_update_smul' v i a x := by fin_cases i <;> simp
  map_eq_zero_of_eq' v i j hij hne := by
    fin_cases i <;> fin_cases j <;> simp_all

@[simp] theorem bilinearToAlternating_apply (f : LinearMap.BilinMap A M N)
    (h : ∀ x, f x x = 0) (v : Fin 2 → M) :
    bilinearToAlternating A f h v = f (v 0) (v 1) := rfl

def wedgeBilinear : LinearMap.BilinMap A M (⋀[A]^2 M) :=
  alternatingToBilinear A (exteriorPower.ιMulti A 2)

@[simp] theorem wedgeBilinear_apply (x y : M) :
    wedgeBilinear A x y = exteriorPower.ιMulti A 2 ![x, y] := rfl

theorem wedgeBilinear_self (x : M) : wedgeBilinear A x x = 0 := by
  exact (exteriorPower.ιMulti A 2).map_eq_zero_of_eq ![x, x] (i := 0) (j := 1) rfl (by decide)

theorem wedgeBilinear_swap (x y : M) : wedgeBilinear A x y = -wedgeBilinear A y x := by
  have h := wedgeBilinear_self A (x + y)
  simp only [map_add, LinearMap.add_apply, wedgeBilinear_self, zero_add, add_zero] at h
  exact eq_neg_of_add_eq_zero_right h

variable (S : Type u) [CommRing S] [Algebra A S]

local instance (priority := 100) exteriorScalarModule (P : Type u) [AddCommGroup P] [Module S P] :
    Module A (⋀[S]^2 P) := Module.compHom _ (algebraMap A S)

local instance (priority := 100) exteriorScalarTower (P : Type u) [AddCommGroup P] [Module S P] :
    IsScalarTower A S (⋀[S]^2 P) := IsScalarTower.of_algebraMap_smul fun _ _ => rfl

def wedgeBaseChangeBilinear :
    LinearMap.BilinMap S (S ⊗[A] M) (S ⊗[A] (⋀[A]^2 M)) :=
  (wedgeBilinear A).baseChange S

theorem wedgeBaseChangeBilinear_swap (x y : S ⊗[A] M) :
    wedgeBaseChangeBilinear A S x y = -wedgeBaseChangeBilinear A S y x := by
  induction x with
  | zero => simp [wedgeBaseChangeBilinear]
  | add x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy, neg_add]
  | tmul s x =>
    induction y with
    | zero => simp [wedgeBaseChangeBilinear]
    | add y z hy hz => simp only [map_add, LinearMap.add_apply, hy, hz, neg_add]
    | tmul t y =>
      change (s * t) ⊗ₜ wedgeBilinear A x y = -(t * s) ⊗ₜ wedgeBilinear A y x
      rw [wedgeBilinear_swap, TensorProduct.tmul_neg, mul_comm]

theorem wedgeBaseChangeBilinear_self (x : S ⊗[A] M) : wedgeBaseChangeBilinear A S x x = 0 := by
  induction x with
  | zero => simp [wedgeBaseChangeBilinear]
  | tmul s x =>
    change (s * s) ⊗ₜ wedgeBilinear A x x = 0
    rw [wedgeBilinear_self, TensorProduct.tmul_zero]
  | add x y hx hy =>
    simp only [map_add, LinearMap.add_apply, hx, hy, zero_add, add_zero]
    exact add_eq_zero_iff_eq_neg.mpr (wedgeBaseChangeBilinear_swap A S y x)

def exteriorTwoToBaseChange : ⋀[S]^2 (S ⊗[A] M) →ₗ[S] S ⊗[A] (⋀[A]^2 M) :=
  exteriorPower.alternatingMapLinearEquiv
    (bilinearToAlternating S (wedgeBaseChangeBilinear A S) (wedgeBaseChangeBilinear_self A S))

@[simp] theorem exteriorTwoToBaseChange_wedge (s t : S) (x y : M) :
    exteriorTwoToBaseChange A S (exteriorPower.ιMulti S 2 ![s ⊗ₜ x, t ⊗ₜ y]) =
      (s * t) ⊗ₜ exteriorPower.ιMulti A 2 ![x, y] := by
  simp [exteriorTwoToBaseChange, wedgeBaseChangeBilinear]

def baseChangeWedgeAlternating : AlternatingMap A M (⋀[S]^2 (S ⊗[A] M)) (Fin 2) :=
  AlternatingMap.compLinearMap
    { (exteriorPower.ιMulti S 2).toMultilinearMap.restrictScalars A with
      map_eq_zero_of_eq' := fun v _ _ h hne =>
        (exteriorPower.ιMulti S 2).map_eq_zero_of_eq v h hne }
    (TensorProduct.mk A S M 1)

def exteriorTwoFromBaseChange : S ⊗[A] (⋀[A]^2 M) →ₗ[S] ⋀[S]^2 (S ⊗[A] M) :=
  (exteriorPower.alternatingMapLinearEquiv (baseChangeWedgeAlternating A S)).liftBaseChange S

@[simp] theorem exteriorTwoFromBaseChange_wedge (s : S) (x y : M) :
    exteriorTwoFromBaseChange A S (s ⊗ₜ exteriorPower.ιMulti A 2 ![x, y]) =
      s • exteriorPower.ιMulti S 2 ![1 ⊗ₜ x, 1 ⊗ₜ y] := by
  simp [exteriorTwoFromBaseChange, baseChangeWedgeAlternating]
  congr 1

theorem exteriorTwoToFromBaseChange :
    (exteriorTwoToBaseChange A S (M := M)).comp (exteriorTwoFromBaseChange A S) = LinearMap.id := by
  apply LinearMap.restrictScalars_injective A
  apply TensorProduct.ext
  apply LinearMap.ext
  intro s
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro v
  change exteriorTwoToBaseChange A S (exteriorTwoFromBaseChange A S (s ⊗ₜ exteriorPower.ιMulti A 2 v)) =
    s ⊗ₜ exteriorPower.ιMulti A 2 v
  have hv : v = ![v 0, v 1] := by ext i; fin_cases i <;> rfl
  rw [hv]
  simp [TensorProduct.smul_tmul']

theorem exteriorTwoFromToBaseChange :
    (exteriorTwoFromBaseChange A S (M := M)).comp (exteriorTwoToBaseChange A S) = LinearMap.id := by
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro v
  change exteriorTwoFromBaseChange A S (exteriorTwoToBaseChange A S (exteriorPower.ιMulti S 2 v)) =
    exteriorPower.ιMulti S 2 v
  have hv : v = ![v 0, v 1] := by ext i; fin_cases i <;> rfl
  rw [hv]
  generalize v 0 = x, v 1 = y
  induction x with
  | zero =>
    have hzero : exteriorPower.ιMulti S 2 ![0, y] = 0 := by
      change wedgeBilinear S 0 y = 0
      simp only [map_zero, LinearMap.zero_apply]
    rw [hzero, map_zero, map_zero]
  | add x z hx hz =>
    simp only [AlternatingMap.map_vecCons_add, map_add, hx, hz]
  | tmul s x =>
    induction y with
    | zero =>
      have hzero : exteriorPower.ιMulti S 2 ![s ⊗ₜ[A] x, 0] = 0 := by
        change wedgeBilinear S (s ⊗ₜ[A] x) 0 = 0
        exact map_zero _
      rw [hzero, map_zero, map_zero]
    | add y z hy hz =>
      have hadd (f : AlternatingMap S (S ⊗[A] M) (⋀[S]^2 (S ⊗[A] M)) (Fin 2)) :
          f ![s ⊗ₜ x, y + z] = f ![s ⊗ₜ x, y] + f ![s ⊗ₜ x, z] := by
        simpa using (f.curryLeft (s ⊗ₜ x)).map_vecCons_add ![] y z
      rw [hadd (exteriorPower.ιMulti S 2)]
      simp only [map_add, hy, hz]
    | tmul t y =>
      simp only [exteriorTwoToBaseChange_wedge, exteriorTwoFromBaseChange_wedge]
      rw [show s ⊗ₜ[A] x = s • ((1 : S) ⊗ₜ[A] x) by simp [TensorProduct.smul_tmul'],
        show t ⊗ₜ[A] y = t • ((1 : S) ⊗ₜ[A] y) by simp [TensorProduct.smul_tmul']]
      rw [AlternatingMap.map_vecCons_smul]
      have hsmul := (exteriorPower.ιMulti S 2).curryLeft ((1 : S) ⊗ₜ[A] x) |>.map_vecCons_smul ![] t ((1 : S) ⊗ₜ[A] y)
      simpa only [AlternatingMap.curryLeft_apply_apply, smul_smul] using
        (congrArg (fun z => s • z) hsmul).symm

def exteriorTwoBaseChangeEquiv : S ⊗[A] (⋀[A]^2 M) ≃ₗ[S] ⋀[S]^2 (S ⊗[A] M) :=
  { exteriorTwoFromBaseChange A S with
    invFun := exteriorTwoToBaseChange A S
    left_inv := fun w => LinearMap.congr_fun (exteriorTwoToFromBaseChange A S) w
    right_inv := fun w => LinearMap.congr_fun (exteriorTwoFromToBaseChange A S) w }

def exteriorCongr (d : ℕ) (e : M ≃ₗ[A] N) : (⋀[A]^d M) ≃ₗ[A] (⋀[A]^d N) :=
  { exteriorPower.map d e.toLinearMap with
    invFun := exteriorPower.map d e.symm.toLinearMap
    left_inv := fun w => by
      change exteriorPower.map d e.symm.toLinearMap (exteriorPower.map d e.toLinearMap w) = w
      rw [← LinearMap.comp_apply, ← exteriorPower.map_comp, e.symm_comp, exteriorPower.map_id]
      rfl
    right_inv := fun w => by
      change exteriorPower.map d e.toLinearMap (exteriorPower.map d e.symm.toLinearMap w) = w
      rw [← LinearMap.comp_apply, ← exteriorPower.map_comp, e.comp_symm, exteriorPower.map_id]
      rfl }

def exteriorTwoCongr (e : M ≃ₗ[A] N) : (⋀[A]^2 M) ≃ₗ[A] (⋀[A]^2 N) :=
  exteriorCongr A 2 e

@[simp] theorem exteriorTwoCongr_wedge (e : M ≃ₗ[A] N) (x y : M) :
    exteriorTwoCongr A e (exteriorPower.ιMulti A 2 ![x, y]) =
      exteriorPower.ιMulti A 2 ![e x, e y] := by
  change exteriorPower.map 2 e.toLinearMap _ = _
  rw [exteriorPower.map_apply_ιMulti]
  congr 1
  funext i
  fin_cases i <;> rfl

section Kaehler
variable (R : Type u) [CommRing R] [Algebra R A] [Algebra R S] [IsScalarTower R A S]

abbrev KaehlerTwoForms : Type u := ⋀[A]^2 (KaehlerDifferential R A)

def kaehlerExteriorMap : KaehlerTwoForms A R →ₗ[A] KaehlerTwoForms S R :=
  exteriorPower.alternatingMapLinearEquiv <|
    AlternatingMap.compLinearMap
      { (exteriorPower.ιMulti S 2).toMultilinearMap.restrictScalars A with
        map_eq_zero_of_eq' := fun v _ _ h hne =>
          (exteriorPower.ιMulti S 2).map_eq_zero_of_eq v h hne }
      (KaehlerDifferential.map R R A S)

@[simp] theorem kaehlerExteriorMap_wedge (x y : KaehlerDifferential R A) :
    kaehlerExteriorMap A S R (exteriorPower.ιMulti A 2 ![x, y]) =
      exteriorPower.ιMulti S 2 ![KaehlerDifferential.map R R A S x, KaehlerDifferential.map R R A S y] := by
  simp [kaehlerExteriorMap]
  congr 1
  funext i
  fin_cases i <;> rfl

def kaehlerExteriorBaseChangeEquiv [Algebra.FormallyEtale A S] :
    S ⊗[A] KaehlerTwoForms A R ≃ₗ[S] KaehlerTwoForms S R :=
  (exteriorTwoBaseChangeEquiv A S).trans
    (exteriorTwoCongr S (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale R A S))

theorem kaehlerExterior_isBaseChange [Algebra.FormallyEtale A S] :
    IsBaseChange S (kaehlerExteriorMap A S R) := by
  apply IsBaseChange.of_equiv (kaehlerExteriorBaseChangeEquiv A S R)
  have h : ((kaehlerExteriorBaseChangeEquiv A S R).toLinearMap.restrictScalars A).comp
        (TensorProduct.mk A S (KaehlerTwoForms A R) 1) = kaehlerExteriorMap A S R := by
    apply exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro v
    have hv : v = ![v 0, v 1] := by ext i; fin_cases i <;> rfl
    rw [hv]
    change exteriorTwoCongr S (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale R A S)
      (exteriorTwoFromBaseChange A S (1 ⊗ₜ exteriorPower.ιMulti A 2 ![v 0, v 1])) = _
    simp only [exteriorTwoFromBaseChange_wedge, one_smul, exteriorTwoCongr_wedge,
      KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_apply,
      KaehlerDifferential.mapBaseChange_tmul]
    simp
  intro w
  exact LinearMap.congr_fun h w

theorem kaehlerExterior_isLocalizedModule (N : Submonoid A) [IsLocalization N S] :
    IsLocalizedModule N (kaehlerExteriorMap A S R) := by
  letI := Algebra.FormallyEtale.of_isLocalization (Rₘ := S) N
  exact (isLocalizedModule_iff_isBaseChange N S _).mpr (kaehlerExterior_isBaseChange A S R)

end Kaehler

def exteriorEvaluation : (⋀[A]^2 M) →ₗ[A] Module.Dual A (⋀[A]^2 (Module.Dual A M)) :=
  (exteriorPower.pairingDual A (Module.Dual A M) 2).comp
    (exteriorPower.map 2 (Module.Dual.eval A M))

theorem exteriorEvaluation_pairing (w : ⋀[A]^2 M) (v : Fin 2 → Module.Dual A M) :
    exteriorEvaluation A w (exteriorPower.ιMulti A 2 v) =
      exteriorPower.pairingDual A M 2 (exteriorPower.ιMulti A 2 v) w := by
  have h : (Module.Dual.eval A (⋀[A]^2 (Module.Dual A M)) (exteriorPower.ιMulti A 2 v)).comp
        (exteriorEvaluation A) = exteriorPower.pairingDual A M 2 (exteriorPower.ιMulti A 2 v) := by
    apply exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro x
    simp [exteriorEvaluation, exteriorPower.pairingDual_ιMulti_ιMulti,
      Matrix.det_fin_two, mul_comm]
  exact LinearMap.congr_fun h w

theorem exteriorEvaluation_injective {I : Type*} [LinearOrder I] (b : Module.Basis I A M) :
    Function.Injective (exteriorEvaluation A (M := M)) := by
  intro x y h
  apply (b.exteriorPower 2).repr.injective
  ext s
  rw [exteriorPower.basis_repr_apply, exteriorPower.basis_repr_apply]
  have hh := congrArg (fun f => f (exteriorPower.ιMulti_family A 2 b.coord s)) h
  simpa only [exteriorPower.ιMulti_family, exteriorEvaluation_pairing,
    exteriorPower.ιMultiDual] using hh

section KaehlerEvaluation
variable (R : Type u) [CommRing R] [Algebra R A]

def kaehlerTwoEvaluation : KaehlerTwoForms A R →ₗ[A]
    LinearMap.BilinForm A (Derivation R A A) where
  toFun w := alternatingToBilinear A
    ((exteriorPower.alternatingMapLinearEquiv.symm (exteriorEvaluation A w)).compLinearMap
      (KaehlerDifferential.linearMapEquivDerivation R A).symm.toLinearMap)
  map_add' x y := by
    ext D E
    simp [alternatingToBilinear_apply]
  map_smul' a w := by
    ext D E
    simp [alternatingToBilinear_apply]

theorem kaehlerTwoEvaluation_wedge (x y : KaehlerDifferential R A) (D E : Derivation R A A) :
    kaehlerTwoEvaluation A R (exteriorPower.ιMulti A 2 ![x, y]) D E =
      D.liftKaehlerDifferential x * E.liftKaehlerDifferential y -
        E.liftKaehlerDifferential x * D.liftKaehlerDifferential y := by
  simp [kaehlerTwoEvaluation, alternatingToBilinear_apply, exteriorEvaluation,
    exteriorPower.pairingDual_ιMulti_ιMulti, Matrix.det_fin_two, mul_comm]

@[simp] theorem kaehlerTwoEvaluation_D_wedge (a b : A) :
    kaehlerTwoEvaluation A R
      (exteriorPower.ιMulti A 2 ![KaehlerDifferential.D R A a, KaehlerDifferential.D R A b]) =
        coordinateForm (R := R) a b := by
  ext D E
  simp [kaehlerTwoEvaluation_wedge, coordinateForm_apply]

theorem kaehlerTwoEvaluation_injective {I : Type*} [LinearOrder I]
    (b : Module.Basis I A (KaehlerDifferential R A)) :
    Function.Injective (kaehlerTwoEvaluation A R) := by
  intro x y h
  apply exteriorEvaluation_injective A b
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro v
  have hh := LinearMap.congr_fun (LinearMap.congr_fun h
    (KaehlerDifferential.linearMapEquivDerivation R A (v 0)))
    (KaehlerDifferential.linearMapEquivDerivation R A (v 1))
  have hv : v = ![v 0, v 1] := by ext i; fin_cases i <;> rfl
  rw [hv]
  have he : (fun i : Fin 2 =>
      (![KaehlerDifferential.linearMapEquivDerivation R A (v 0),
        KaehlerDifferential.linearMapEquivDerivation R A (v 1)] i).liftKaehlerDifferential) =
        ![v 0, v 1] := by
    funext i
    fin_cases i <;>
      exact (KaehlerDifferential.linearMapEquivDerivation R A).symm_apply_apply _
  simpa [kaehlerTwoEvaluation, alternatingToBilinear_apply,
    exteriorPower.alternatingMapLinearEquiv_symm_apply, he] using hh

end KaehlerEvaluation

section Expressions
variable (R : Type u) [CommRing R] [Algebra R A]

theorem kaehlerTwo_span :
    Submodule.span A (Set.range (fun ab : A × A => exteriorPower.ιMulti A 2
      ![KaehlerDifferential.D R A ab.1, KaehlerDifferential.D R A ab.2])) = ⊤ := by
  have h := exteriorPower.ιMulti_span_of_span A 2 (KaehlerDifferential R A)
    (KaehlerDifferential.span_range_derivation R A)
  rw [← top_le_iff] at h ⊢
  apply h.trans
  apply Submodule.span_mono
  rintro _ ⟨v, hv, rfl⟩
  obtain ⟨a, ha⟩ := hv (Set.mem_range_self 0)
  obtain ⟨b, hb⟩ := hv (Set.mem_range_self 1)
  refine ⟨(a, b), congrArg (exteriorPower.ιMulti A 2) ?_⟩
  ext i
  fin_cases i <;> assumption

set_option maxHeartbeats 800000 in
theorem kaehlerTwo_expression (w : KaehlerTwoForms A R) :
    ∃ (I : Type u) (_ : Fintype I) (c a b : I → A),
      w = ∑ i, c i • exteriorPower.ιMulti A 2
        ![KaehlerDifferential.D R A (a i), KaehlerDifferential.D R A (b i)] := by
  classical
  have hw : w ∈ Submodule.span A (Set.range (fun ab : A × A => exteriorPower.ιMulti A 2
      ![KaehlerDifferential.D R A ab.1, KaehlerDifferential.D R A ab.2])) := by
    rw [kaehlerTwo_span A R]
    trivial
  obtain ⟨l, hl⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hw
  refine ⟨l.support, inferInstance, (fun i => l i), (fun i => i.val.1), (fun i => i.val.2), ?_⟩
  change w = ∑ i ∈ l.support.attach, l i.val • exteriorPower.ιMulti A 2
    ![KaehlerDifferential.D R A i.val.1, KaehlerDifferential.D R A i.val.2]
  exact hl.symm.trans (Finset.sum_attach l.support (fun i : A × A =>
    l i • exteriorPower.ιMulti A 2
      ![KaehlerDifferential.D R A i.1, KaehlerDifferential.D R A i.2])).symm

end Expressions

section Localization
variable (R : Type u) [CommRing R] [Algebra R A] [Algebra R S] [IsScalarTower R A S]

@[simp] theorem kaehlerExteriorMap_D_wedge (a b : A) :
    kaehlerExteriorMap A S R (exteriorPower.ιMulti A 2
      ![KaehlerDifferential.D R A a, KaehlerDifferential.D R A b]) =
    exteriorPower.ιMulti S 2 ![KaehlerDifferential.D R S (algebraMap A S a),
      KaehlerDifferential.D R S (algebraMap A S b)] := by
  simp [kaehlerExteriorMap_wedge, KaehlerDifferential.map_D]

theorem kaehlerExteriorMap_smul (a : A) (w : KaehlerTwoForms A R) :
    kaehlerExteriorMap A S R (a • w) = algebraMap A S a • kaehlerExteriorMap A S R w := by
  rw [map_smul, ← IsScalarTower.algebraMap_smul S a]

theorem kaehlerExteriorMap_comp (T : Type u) [CommRing T] [Algebra A T] [Algebra S T]
    [Algebra R T] [IsScalarTower R A T] [IsScalarTower R S T] [IsScalarTower A S T]
    (w : KaehlerTwoForms A R) :
    kaehlerExteriorMap S T R (kaehlerExteriorMap A S R w) = kaehlerExteriorMap A T R w := by
  obtain ⟨I, hI, c, a, b, rfl⟩ := kaehlerTwo_expression A R w
  simp only [map_sum, kaehlerExteriorMap_smul, kaehlerExteriorMap_D_wedge,
    ← IsScalarTower.algebraMap_apply A S T]

def primeExteriorEquiv (p : PrimeSpectrum A) :
    LocalizedModule p.asIdeal.primeCompl (KaehlerTwoForms A R) ≃ₗ[A]
      KaehlerTwoForms (PrimeLocalRing A p) R := by
  letI := kaehlerExterior_isLocalizedModule A (PrimeLocalRing A p) R p.asIdeal.primeCompl
  exact IsLocalizedModule.iso p.asIdeal.primeCompl (kaehlerExteriorMap A (PrimeLocalRing A p) R)

@[simp] theorem primeExteriorEquiv_mk_one (p : PrimeSpectrum A) (w : KaehlerTwoForms A R) :
    primeExteriorEquiv A R p (LocalizedModule.mk w 1) =
      kaehlerExteriorMap A (PrimeLocalRing A p) R w := by
  letI := kaehlerExterior_isLocalizedModule A (PrimeLocalRing A p) R p.asIdeal.primeCompl
  unfold primeExteriorEquiv
  exact IsLocalizedModule.iso_mk_one _ _ _

theorem primeExteriorEquiv_mk_cancel (p : PrimeSpectrum A) (w : KaehlerTwoForms A R)
    (s : p.asIdeal.primeCompl) :
    algebraMap A (PrimeLocalRing A p) s.val •
      primeExteriorEquiv A R p (LocalizedModule.mk w s) =
        kaehlerExteriorMap A (PrimeLocalRing A p) R w := by
  rw [IsScalarTower.algebraMap_smul]
  rw [← (primeExteriorEquiv A R p).map_smul]
  have h : (s : A) • LocalizedModule.mk w s = LocalizedModule.mk w 1 := by
    rw [LocalizedModule.smul'_mk]
    change LocalizedModule.mk (s • w) s = _
    exact LocalizedModule.mk_cancel s w
  rw [h, primeExteriorEquiv_mk_one]

end Localization

section Principal
variable (R : Type u) [CommRing R] [Algebra R A]
variable (f : A) (p : PrimeSpectrum A) (hf : p ∈ PrimeSpectrum.basicOpen f)

local instance principalExteriorAlgebra [h : Fact (p ∈ PrimeSpectrum.basicOpen f)] :
    Algebra (Localization.Away f) (PrimeLocalRing A p) :=
  (principalToPrimeAlg A f p h.out).toAlgebra

local instance principalExteriorTower [h : Fact (p ∈ PrimeSpectrum.basicOpen f)] :
    IsScalarTower A (Localization.Away f) (PrimeLocalRing A p) :=
  IsScalarTower.of_algHom (principalToPrimeAlg A f p h.out)

local instance principalExteriorTowerR [h : Fact (p ∈ PrimeSpectrum.basicOpen f)] :
    IsScalarTower R (Localization.Away f) (PrimeLocalRing A p) :=
  IsScalarTower.of_algHom ((principalToPrimeAlg A f p h.out).restrictScalars R)

def principalExteriorToPrime : KaehlerTwoForms (Localization.Away f) R →
    KaehlerTwoForms (PrimeLocalRing A p) R := by
  letI : Fact (p ∈ PrimeSpectrum.basicOpen f) := ⟨hf⟩
  exact fun w => kaehlerExteriorMap (Localization.Away f) (PrimeLocalRing A p) R w

@[simp] theorem principalExteriorToPrime_add (x y : KaehlerTwoForms (Localization.Away f) R) :
    principalExteriorToPrime A R f p hf (x + y) =
      principalExteriorToPrime A R f p hf x + principalExteriorToPrime A R f p hf y := by
  letI : Fact (p ∈ PrimeSpectrum.basicOpen f) := ⟨hf⟩
  exact map_add (kaehlerExteriorMap (Localization.Away f) (PrimeLocalRing A p) R) _ _

theorem principalExteriorToPrime_sum {I : Type*} (t : Finset I)
    (w : I → KaehlerTwoForms (Localization.Away f) R) :
    principalExteriorToPrime A R f p hf (∑ i ∈ t, w i) =
      ∑ i ∈ t, principalExteriorToPrime A R f p hf (w i) := by
  letI : Fact (p ∈ PrimeSpectrum.basicOpen f) := ⟨hf⟩
  exact map_sum (kaehlerExteriorMap (Localization.Away f) (PrimeLocalRing A p) R) _ _

theorem principalExteriorToPrime_smul (c : Localization.Away f)
    (w : KaehlerTwoForms (Localization.Away f) R) :
    principalExteriorToPrime A R f p hf (c • w) =
      principalToPrime A f p hf c • principalExteriorToPrime A R f p hf w := by
  letI : Fact (p ∈ PrimeSpectrum.basicOpen f) := ⟨hf⟩
  exact kaehlerExteriorMap_smul (Localization.Away f) (PrimeLocalRing A p) R c w

@[simp] theorem principalExteriorToPrime_D_wedge (a b : Localization.Away f) :
    principalExteriorToPrime A R f p hf (exteriorPower.ιMulti (Localization.Away f) 2
      ![KaehlerDifferential.D R _ a, KaehlerDifferential.D R _ b]) =
    exteriorPower.ιMulti (PrimeLocalRing A p) 2
      ![KaehlerDifferential.D R _ (principalToPrime A f p hf a),
        KaehlerDifferential.D R _ (principalToPrime A f p hf b)] := by
  letI : Fact (p ∈ PrimeSpectrum.basicOpen f) := ⟨hf⟩
  exact kaehlerExteriorMap_D_wedge (Localization.Away f) (PrimeLocalRing A p) R a b

theorem principalExteriorToPrime_base (w : KaehlerTwoForms A R) :
    principalExteriorToPrime A R f p hf (kaehlerExteriorMap A (Localization.Away f) R w) =
      kaehlerExteriorMap A (PrimeLocalRing A p) R w := by
  letI : Fact (p ∈ PrimeSpectrum.basicOpen f) := ⟨hf⟩
  exact kaehlerExteriorMap_comp A (Localization.Away f) R (PrimeLocalRing A p) w

theorem primeExteriorEquiv_mk_eq_principal (w : KaehlerTwoForms A R) (d : A)
    (hd : d ∉ p.asIdeal) (v : KaehlerTwoForms (Localization.Away f) R)
    (h : algebraMap A (Localization.Away f) d • v = kaehlerExteriorMap A (Localization.Away f) R w) :
    primeExteriorEquiv A R p (LocalizedModule.mk w ⟨d, hd⟩) =
      principalExteriorToPrime A R f p hf v := by
  apply (IsLocalization.map_units (PrimeLocalRing A p)
    (⟨d, hd⟩ : p.asIdeal.primeCompl)).smul_left_cancel.mp
  rw [primeExteriorEquiv_mk_cancel]
  have hh := congrArg (principalExteriorToPrime A R f p hf) h
  simpa only [principalExteriorToPrime_smul, principalToPrime_algebraMap,
    principalExteriorToPrime_base] using hh.symm

end Principal

section SheafComparison
variable (R : Type u) [CommRing R] [Algebra R A]

def kaehlerTwoFormSheaf : TopCat.Sheaf (Type u) (PrimeSpectrum.Top A) :=
  structureSheafInType (CommRingCat.of A) (KaehlerTwoForms A R)

theorem kaehlerTwoFormSheaf_from_tilde :
    (tilde (R := CommRingCat.of A) (ModuleCat.of A (KaehlerTwoForms A R))).val.presheaf ⋙ forget AddCommGrpCat =
      (kaehlerTwoFormSheaf A R).obj := rfl

def exteriorGermEvaluation (p : PrimeSpectrum A)
    (w : LocalizedModule p.asIdeal.primeCompl (KaehlerTwoForms A R)) : TwoFormGerm R A p :=
  kaehlerTwoEvaluation (PrimeLocalRing A p) R (primeExteriorEquiv A R p w)

theorem principalExterior_evaluation (f : A) (p : PrimeSpectrum A)
    (hf : p ∈ PrimeSpectrum.basicOpen f) {I : Type u} [Fintype I]
    (c a b : I → Localization.Away f) :
    kaehlerTwoEvaluation (PrimeLocalRing A p) R (principalExteriorToPrime A R f p hf
      (∑ i, c i • exteriorPower.ιMulti (Localization.Away f) 2
        ![KaehlerDifferential.D R _ (a i), KaehlerDifferential.D R _ (b i)])) =
    ∑ i, principalToPrime A f p hf (c i) •
      coordinateForm (R := R) (principalToPrime A f p hf (a i))
        (principalToPrime A f p hf (b i)) := by
  simp only [principalExteriorToPrime_sum, principalExteriorToPrime_smul,
    principalExteriorToPrime_D_wedge, map_sum, map_smul, kaehlerTwoEvaluation_D_wedge]

theorem exteriorFraction_regular {U : Opens (PrimeSpectrum.Top A)}
    (s : ∀ p : U, LocalizedModule p.val.asIdeal.primeCompl (KaehlerTwoForms A R))
    (hs : StructureSheaf.IsFraction s) :
    (regularTwoFormPrelocal R A).pred (fun p => exteriorGermEvaluation A R p.val (s p)) := by
  classical
  obtain ⟨w, d, hs⟩ := hs
  obtain ⟨v, hv⟩ := (IsUnit.smul_bijective
    (β := KaehlerTwoForms (Localization.Away d) R)
    (IsLocalization.Away.algebraMap_isUnit (S := Localization.Away d) d)).2
      (kaehlerExteriorMap A (Localization.Away d) R w)
  obtain ⟨I, hI, c, a, b, hv'⟩ := kaehlerTwo_expression (Localization.Away d) R v
  have hU : U ≤ PrimeSpectrum.basicOpen d := fun p hp => (hs ⟨p, hp⟩).choose
  refine ⟨d, hU, I, hI, c, a, b, ?_⟩
  intro p
  obtain ⟨hd, hp⟩ := hs p
  dsimp only
  rw [hp]
  unfold exteriorGermEvaluation
  rw [primeExteriorEquiv_mk_eq_principal A R d p.val (hU p.property) w d hd v hv, hv']
  exact principalExterior_evaluation A R d p.val (hU p.property) c a b

def exteriorSheafEvaluation : kaehlerTwoFormSheaf A R ⟶ regularTwoFormSheaf R A where
  hom :=
    { app := fun U => TypeCat.ofHom fun s => ⟨fun p => exteriorGermEvaluation A R p.val (s.val p), by
        intro p
        obtain ⟨V, hp, i, hs⟩ := s.property p
        exact ⟨V, hp, i, exteriorFraction_regular A R _ hs⟩⟩
      naturality := by intros; rfl }

theorem regularExpression_fraction {U : Opens (PrimeSpectrum.Top A)}
    (s : ∀ p : U, TwoFormGerm R A p.val) (hs : (regularTwoFormPrelocal R A).pred s) :
    ∃ (w : KaehlerTwoForms A R) (d : A) (hd : ∀ p : U, d ∉ p.val.asIdeal),
      ∀ p : U, exteriorGermEvaluation A R p.val (LocalizedModule.mk w ⟨d, hd p⟩) = s p := by
  classical
  obtain ⟨f, hU, I, hI, c, a, b, hs⟩ := hs
  let v : KaehlerTwoForms (Localization.Away f) R := ∑ i, c i •
    exteriorPower.ιMulti (Localization.Away f) 2
      ![KaehlerDifferential.D R _ (a i), KaehlerDifferential.D R _ (b i)]
  letI := kaehlerExterior_isLocalizedModule A (Localization.Away f) R (Submonoid.powers f)
  obtain ⟨⟨w, d⟩, hd⟩ := IsLocalizedModule.surj (Submonoid.powers f)
    (kaehlerExteriorMap A (Localization.Away f) R) v
  have hdp : ∀ p : U, d.val ∉ p.val.asIdeal := by
    intro p
    obtain ⟨m, hm⟩ := d.property
    rw [← hm]
    exact p.val.asIdeal.primeCompl.pow_mem (hU p.property) m
  refine ⟨w, d.val, hdp, ?_⟩
  intro p
  unfold exteriorGermEvaluation
  rw [primeExteriorEquiv_mk_eq_principal A R f p.val (hU p.property) w d.val (hdp p) v
    (by simpa only [Submonoid.smul_def, IsScalarTower.algebraMap_smul] using hd)]
  exact (principalExterior_evaluation A R f p.val (hU p.property) c a b).trans (hs p).symm

theorem exteriorSheafEvaluation_point_preimage {U : Opens (PrimeSpectrum.Top A)}
    (s : (regularTwoFormSheaf R A).obj.obj (op U)) (p : U) :
    ∃ w, exteriorGermEvaluation A R p.val w = s.val p := by
  obtain ⟨V, hp, i, hs⟩ := s.property p
  obtain ⟨w, d, hd, h⟩ := regularExpression_fraction A R _ hs
  exact ⟨LocalizedModule.mk w ⟨d, hd ⟨p.val, hp⟩⟩, h ⟨p.val, hp⟩⟩

theorem exteriorSheafEvaluation_bijective (U : Opens (PrimeSpectrum.Top A))
    (hU : ∀ p : U, Function.Injective (kaehlerTwoEvaluation (PrimeLocalRing A p.val) R)) :
    Function.Bijective ((exteriorSheafEvaluation A R).hom.app (op U)) := by
  have hinj (p : U) : Function.Injective (exteriorGermEvaluation A R p.val) :=
    (hU p).comp (primeExteriorEquiv A R p.val).injective
  refine ⟨?_, ?_⟩
  · intro s t h
    apply Subtype.ext
    funext p
    exact hinj p (congrArg (fun s => s.val p) h)
  · intro s
    let t := fun p : U => (exteriorSheafEvaluation_point_preimage A R s p).choose
    have ht (p : U) : exteriorGermEvaluation A R p.val (t p) = s.val p :=
      (exteriorSheafEvaluation_point_preimage A R s p).choose_spec
    refine ⟨⟨t, ?_⟩, ?_⟩
    · intro p
      obtain ⟨V, hp, i, hs⟩ := s.property p
      obtain ⟨w, d, hd, h⟩ := regularExpression_fraction A R _ hs
      refine ⟨V, hp, i, w, d, ?_⟩
      intro q
      refine ⟨hd q, ?_⟩
      exact hinj (i q) ((ht (i q)).trans (h q).symm)
    · apply Subtype.ext
      exact funext ht

def exteriorSheafComparison (U : Opens (PrimeSpectrum.Top A))
    (hU : ∀ p : U, Function.Injective (kaehlerTwoEvaluation (PrimeLocalRing A p.val) R)) :
    (U.isOpenEmbedding.sheafPullback (Type u)).obj (kaehlerTwoFormSheaf A R) ≅
      (U.isOpenEmbedding.sheafPullback (Type u)).obj (regularTwoFormSheaf R A) := by
  let f := (U.isOpenEmbedding.sheafPullback (Type u)).map (exteriorSheafEvaluation A R)
  haveI (V : (Opens U)ᵒᵖ) : IsIso (f.hom.app V) := by
    apply (CategoryTheory.isIso_iff_bijective _).mpr
    apply exteriorSheafEvaluation_bijective A R
    intro p
    obtain ⟨q, hq, hp⟩ := p.property
    exact hU ⟨p.val, hp ▸ q.property⟩
  letI := NatIso.isIso_of_isIso_app f.hom
  exact ObjectProperty.isoMk _ (asIso f.hom)

end SheafComparison

section CanonicalTrace
variable (R : Type u) [CommRing R] [Algebra R A]
variable {n : Type u} [Fintype n]

def kaehlerCanonicalTrace (T B : Matrix n n A) : KaehlerTwoForms A R :=
  ∑ i, ∑ j, exteriorPower.ιMulti A 2 ![KaehlerDifferential.D R A (T i j),
    KaehlerDifferential.D R A (B j i)]

theorem kaehlerCanonicalTrace_evaluation (T B : Matrix n n A) :
    kaehlerTwoEvaluation A R (kaehlerCanonicalTrace A R T B) = canonicalTrace (R := R) T B := by
  simp only [kaehlerCanonicalTrace, map_sum, kaehlerTwoEvaluation_D_wedge, canonicalTrace]

theorem kaehlerCanonicalTrace_map [Algebra R S] [IsScalarTower R A S]
    (T B : Matrix n n A) :
    kaehlerExteriorMap A S R (kaehlerCanonicalTrace A R T B) =
      kaehlerCanonicalTrace S R (T.map (algebraMap A S)) (B.map (algebraMap A S)) := by
  simp only [kaehlerCanonicalTrace, map_sum, kaehlerExteriorMap_D_wedge, Matrix.map_apply]

theorem kaehlerCanonicalTrace_one [DecidableEq n] (B : Matrix n n A) :
    kaehlerCanonicalTrace A R (1 : Matrix n n A) B = 0 := by
  classical
  have h (x : KaehlerDifferential R A) : exteriorPower.ιMulti A 2 ![0, x] = 0 :=
    (exteriorPower.ιMulti A 2).map_coord_zero 0 rfl
  simp [kaehlerCanonicalTrace, Matrix.one_apply, apply_ite, h]

end CanonicalTrace

section Contraction
variable (R : Type u) [CommRing R] [Algebra R A]
variable [Module.IsReflexive A (KaehlerDifferential R A)]

def kaehlerOneEvaluationEquiv : KaehlerDifferential R A ≃ₗ[A]
    Module.Dual A (Derivation R A A) :=
  (Module.evalEquiv A (KaehlerDifferential R A)).trans
    (KaehlerDifferential.linearMapEquivDerivation R A).symm.dualMap

@[simp] theorem kaehlerOneEvaluationEquiv_apply (x : KaehlerDifferential R A)
    (D : Derivation R A A) : kaehlerOneEvaluationEquiv A R x D = D.liftKaehlerDifferential x := rfl

def kaehlerContraction (w : KaehlerTwoForms A R) : Derivation R A A →ₗ[A] KaehlerDifferential R A :=
  (kaehlerOneEvaluationEquiv A R).symm.toLinearMap.comp (kaehlerTwoEvaluation A R w)

theorem kaehlerContraction_pairing (w : KaehlerTwoForms A R) (D E : Derivation R A A) :
    E.liftKaehlerDifferential (kaehlerContraction A R w D) = kaehlerTwoEvaluation A R w D E := by
  exact LinearMap.congr_fun ((kaehlerOneEvaluationEquiv A R).apply_symm_apply
    (kaehlerTwoEvaluation A R w D)) E

theorem kaehlerContraction_wedge (x y : KaehlerDifferential R A) (D : Derivation R A A) :
    kaehlerContraction A R (exteriorPower.ιMulti A 2 ![x, y]) D =
      D.liftKaehlerDifferential x • y - D.liftKaehlerDifferential y • x := by
  apply (kaehlerOneEvaluationEquiv A R).injective
  ext E
  rw [kaehlerOneEvaluationEquiv_apply, kaehlerContraction_pairing, kaehlerTwoEvaluation_wedge,
    kaehlerOneEvaluationEquiv_apply]
  simp [mul_comm]

theorem kaehlerContraction_bijective (w : KaehlerTwoForms A R)
    (h : Function.Bijective (kaehlerTwoEvaluation A R w)) :
    Function.Bijective (kaehlerContraction A R w) :=
  (kaehlerOneEvaluationEquiv A R).symm.bijective.comp h

end Contraction

end
end Universality.ExteriorGeometry

namespace Universality.GlobalSymplectic
noncomputable section
open AffineForms SquareZeroGeometry ExteriorGeometry
universe u
variable (R n : Type u) [CommRing R] [Fintype n] [DecidableEq n]

def primeChartDifferentialBasis (p : PrimeSpectrum (CoordinateRing R n))
    (e : Equiv.Perm (n ⊕ n)) (he : p ∈ permutationOpen R n e) :
    Module.Basis ((n × n) ⊕ (n × n)) (PrimeLocalRing (CoordinateRing R n) p)
      (KaehlerDifferential R (PrimeLocalRing (CoordinateRing R n) p)) := by
  letI := (primeChartPolynomialEvaluation R n p e he).toAlgebra
  letI := IsScalarTower.of_algHom (primeChartPolynomialEvaluation R n p e he)
  letI := primeChartPolynomial_isLocalization R n p e he
  exact localizedDifferentialBasis (R := R) (S := PrimeLocalRing (CoordinateRing R n) p)
    (IsLocalization.localizationLocalizationSubmodule (Submonoid.powers (chartDet R n))
      (p.asIdeal.primeCompl.map (permutationChartEmbedding R n e).toRingHom))

theorem primeTwoEvaluation_injective (p : maximalRankOpen R n) :
    Function.Injective (kaehlerTwoEvaluation (PrimeLocalRing (CoordinateRing R n) p.val) R) := by
  obtain ⟨e, he⟩ := exists_prime_chart R n p
  exact kaehlerTwoEvaluation_injective _ R
    ((primeChartDifferentialBasis R n p.val e he).reindex (Fintype.equivFin _))

def orbitExteriorSheafComparison :
    ((maximalRankOpen R n).isOpenEmbedding.sheafPullback (Type u)).obj
        (kaehlerTwoFormSheaf (CoordinateRing R n) R) ≅
      ((maximalRankOpen R n).isOpenEmbedding.sheafPullback (Type u)).obj
        (regularTwoFormSheaf R (CoordinateRing R n)) :=
  exteriorSheafComparison (CoordinateRing R n) R (maximalRankOpen R n)
    (primeTwoEvaluation_injective R n)

def orbitKaehlerTwoForm :
    (kaehlerTwoFormSheaf (CoordinateRing R n) R).obj.obj
      (Opposite.op (maximalRankOpen R n)) :=
  (Equiv.ofBijective ((exteriorSheafEvaluation (CoordinateRing R n) R).hom.app
      (Opposite.op (maximalRankOpen R n)))
    (exteriorSheafEvaluation_bijective (CoordinateRing R n) R (maximalRankOpen R n)
      (primeTwoEvaluation_injective R n))).symm (orbitGlobalTwoForm R n)

theorem orbitKaehlerTwoForm_evaluation :
    (exteriorSheafEvaluation (CoordinateRing R n) R).hom.app
      (Opposite.op (maximalRankOpen R n)) (orbitKaehlerTwoForm R n) = orbitGlobalTwoForm R n :=
  (Equiv.ofBijective _ (exteriorSheafEvaluation_bijective (CoordinateRing R n) R
    (maximalRankOpen R n) (primeTwoEvaluation_injective R n))).apply_symm_apply _

theorem orbitKaehlerTwoForm_evaluation_point (p : maximalRankOpen R n) :
    exteriorGermEvaluation (CoordinateRing R n) R p.val ((orbitKaehlerTwoForm R n).val p) =
      (orbitGlobalTwoForm R n).val p :=
  congrArg (fun s => s.val p) (orbitKaehlerTwoForm_evaluation R n)

theorem orbitKaehlerTwoForm_chart (p : maximalRankOpen R n)
    (e : Equiv.Perm (n ⊕ n)) (he : p.val ∈ permutationOpen R n e) :
    primeExteriorEquiv (CoordinateRing R n) R p.val ((orbitKaehlerTwoForm R n).val p) =
      kaehlerCanonicalTrace (PrimeLocalRing (CoordinateRing R n) p.val) R
        ((chartT R n).map (primeChartEvaluation R n p.val e he))
        ((chartA R n).map (primeChartEvaluation R n p.val e he)) := by
  apply primeTwoEvaluation_injective R n p
  rw [kaehlerCanonicalTrace_evaluation]
  exact (orbitKaehlerTwoForm_evaluation_point R n p).trans (orbitGlobalTwoForm_atlas R n p e he)

theorem orbitKaehlerTwoForm_closed (p : maximalRankOpen R n) :
    IsClosed (exteriorGermEvaluation (CoordinateRing R n) R p.val ((orbitKaehlerTwoForm R n).val p)) := by
  rw [orbitKaehlerTwoForm_evaluation_point]
  exact orbitGlobalTwoForm_closed R n p

theorem orbitKaehlerTwoForm_perfect (p : maximalRankOpen R n) :
    Function.Bijective
      (exteriorGermEvaluation (CoordinateRing R n) R p.val ((orbitKaehlerTwoForm R n).val p)) := by
  rw [orbitKaehlerTwoForm_evaluation_point]
  exact orbitGlobalTwoForm_perfect R n p

theorem cell_kaehler_form_pullback_zero :
    letI := cellChartAlgebra R n
    letI := IsScalarTower.of_algHom (cellChartEval R n)
    kaehlerExteriorMap (ChartRing R n) (CellRing R n) R
      (kaehlerCanonicalTrace (ChartRing R n) R (chartT R n) (chartA R n)) = 0 := by
  letI := cellChartAlgebra R n
  letI := IsScalarTower.of_algHom (cellChartEval R n)
  rw [kaehlerCanonicalTrace_map]
  change kaehlerCanonicalTrace (CellRing R n) R
    ((chartT R n).map (cellChartEval R n)) ((chartA R n).map (cellChartEval R n)) = 0
  rw [cellChartEval_T]
  exact kaehlerCanonicalTrace_one _ _ _

def orbitKaehlerContraction (p : maximalRankOpen R n) :
    Derivation R (PrimeLocalRing (CoordinateRing R n) p.val) (PrimeLocalRing (CoordinateRing R n) p.val)
      →ₗ[PrimeLocalRing (CoordinateRing R n) p.val]
        KaehlerDifferential R (PrimeLocalRing (CoordinateRing R n) p.val) := by
  let e := (exists_prime_chart R n p).choose
  let b := primeChartDifferentialBasis R n p.val e (exists_prime_chart R n p).choose_spec
  letI := Module.Free.of_basis b
  letI := Module.Finite.of_basis b
  exact kaehlerContraction _ R
    (primeExteriorEquiv (CoordinateRing R n) R p.val ((orbitKaehlerTwoForm R n).val p))

theorem orbitKaehlerContraction_pairing (p : maximalRankOpen R n)
    (D E : Derivation R (PrimeLocalRing (CoordinateRing R n) p.val)
      (PrimeLocalRing (CoordinateRing R n) p.val)) :
    E.liftKaehlerDifferential (orbitKaehlerContraction R n p D) =
      exteriorGermEvaluation (CoordinateRing R n) R p.val ((orbitKaehlerTwoForm R n).val p) D E := by
  let e := (exists_prime_chart R n p).choose
  let b := primeChartDifferentialBasis R n p.val e (exists_prime_chart R n p).choose_spec
  letI := Module.Free.of_basis b
  letI := Module.Finite.of_basis b
  exact kaehlerContraction_pairing _ R _ D E

theorem orbitKaehlerContraction_bijective (p : maximalRankOpen R n) :
    Function.Bijective (orbitKaehlerContraction R n p) := by
  let e := (exists_prime_chart R n p).choose
  let b := primeChartDifferentialBasis R n p.val e (exists_prime_chart R n p).choose_spec
  letI := Module.Free.of_basis b
  letI := Module.Finite.of_basis b
  exact kaehlerContraction_bijective _ R _ (orbitKaehlerTwoForm_perfect R n p)

end
end Universality.GlobalSymplectic

namespace Universality.GlobalSymplectic
noncomputable section
set_option backward.isDefEq.respectTransparency false
open AffineForms AffineGeometry SquareZeroGeometry AlgebraicGeometry CategoryTheory Limits
universe u
variable (R n : Type u) [CommRing R] [Fintype n] [DecidableEq n]

section Commutator
variable (S : Type u) [CommRing S] [Algebra R S]

def squareZeroEvaluation (Z : Matrix (n ⊕ n) (n ⊕ n) S) (hZ : Z * Z = 0) :
    CoordinateRing R n →ₐ[R] S :=
  Ideal.Quotient.liftₐ _ (MvPolynomial.aeval (fun ij => Z ij.1 ij.2)) (by
    change squareZeroIdeal R n ≤ RingHom.ker
      (MvPolynomial.aeval (fun ij => Z ij.1 ij.2) : AmbientRing R n →ₐ[R] S).toRingHom
    apply Ideal.span_le.mpr
    rintro _ ⟨⟨i, j⟩, rfl⟩
    change (MvPolynomial.aeval (fun ij => Z ij.1 ij.2) : AmbientRing R n →ₐ[R] S)
      ((genericMatrix R n * genericMatrix R n) i j) = 0
    simpa [Matrix.mul_apply, genericMatrix] using congrFun (congrFun hZ i) j)

omit [DecidableEq n] in
@[simp] theorem squareZeroEvaluation_matrix
    (Z : Matrix (n ⊕ n) (n ⊕ n) S) (hZ : Z * Z = 0) (i j) :
    squareZeroEvaluation R n S Z hZ (universalMatrix R n i j) = Z i j := by
  simp [squareZeroEvaluation, universalMatrix, genericMatrix]

omit [DecidableEq n] in
theorem coordinateAlgHom_ext {f g : CoordinateRing R n →ₐ[R] S}
    (h : ∀ i j, f (universalMatrix R n i j) = g (universalMatrix R n i j)) : f = g := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  rintro ⟨i, j⟩
  exact h i j

variable [Algebra (CoordinateRing R n) S] [IsScalarTower R (CoordinateRing R n) S]

omit [DecidableEq n] [Algebra R S] [IsScalarTower R (CoordinateRing R n) S] in
theorem coefficientMatrix_square : coefficientMatrix R n S * coefficientMatrix R n S = 0 := by
  rw [coefficientMatrix, ← Matrix.map_mul, universalMatrix_square]
  ext i j
  exact (algebraMap (CoordinateRing R n) S).map_zero

/-- The first-order conjugation of the universal square-zero matrix. -/
def commutatorFirstOrder (X : Matrix (n ⊕ n) (n ⊕ n) S) :
    Matrix (n ⊕ n) (n ⊕ n) (DualNumber S) :=
  fun i j => ⟨coefficientMatrix R n S i j, Symplectic.comm X (coefficientMatrix R n S) i j⟩

omit [DecidableEq n] [Algebra R S] [IsScalarTower R (CoordinateRing R n) S] in
theorem commutatorFirstOrder_square (X : Matrix (n ⊕ n) (n ⊕ n) S) :
    commutatorFirstOrder R n S X * commutatorFirstOrder R n S X = 0 := by
  have h : coefficientMatrix R n S * Symplectic.comm X (coefficientMatrix R n S) +
      Symplectic.comm X (coefficientMatrix R n S) * coefficientMatrix R n S = 0 := by
    dsimp [Symplectic.comm]
    calc
      _ = X * (coefficientMatrix R n S * coefficientMatrix R n S) -
          (coefficientMatrix R n S * coefficientMatrix R n S) * X := by noncomm_ring
      _ = 0 := by rw [coefficientMatrix_square]; simp
  ext i j
  · simpa only [Matrix.mul_apply, commutatorFirstOrder, TrivSqZeroExt.fst_sum,
      TrivSqZeroExt.fst_mul, TrivSqZeroExt.fst_mk, TrivSqZeroExt.fst_zero, Matrix.zero_apply] using
      congrFun (congrFun (coefficientMatrix_square R n S) i) j
  · simpa only [Matrix.mul_apply, commutatorFirstOrder, TrivSqZeroExt.snd_sum,
      DualNumber.snd_mul, TrivSqZeroExt.fst_mk, TrivSqZeroExt.snd_mk,
      TrivSqZeroExt.snd_zero, Matrix.zero_apply, Matrix.add_apply, Finset.sum_add_distrib] using
      congrFun (congrFun h i) j

def commutatorFirstOrderMap (X : Matrix (n ⊕ n) (n ⊕ n) S) :
    CoordinateRing R n →ₐ[R] DualNumber S :=
  squareZeroEvaluation R n (DualNumber S) (commutatorFirstOrder R n S X)
    (commutatorFirstOrder_square R n S X)

omit [DecidableEq n] in
theorem commutatorFirstOrderMap_fst (X : Matrix (n ⊕ n) (n ⊕ n) S) (a : CoordinateRing R n) :
    (commutatorFirstOrderMap R n S X a).fst = algebraMap (CoordinateRing R n) S a := by
  have h : (TrivSqZeroExt.fstHom R S S).comp (commutatorFirstOrderMap R n S X) =
      IsScalarTower.toAlgHom R (CoordinateRing R n) S := by
    apply coordinateAlgHom_ext
    intro i j
    exact congrArg TrivSqZeroExt.fst
      (squareZeroEvaluation_matrix R n (DualNumber S) _ (commutatorFirstOrder_square R n S X) i j)
  exact DFunLike.congr_fun h a

/-- The infinitesimal conjugation action on the actual square-zero coordinate algebra. -/
def commutatorDerivation (X : Matrix (n ⊕ n) (n ⊕ n) S) :
    Derivation R (CoordinateRing R n) S where
  toFun a := (commutatorFirstOrderMap R n S X a).snd
  map_add' a b := by simp
  map_smul' r a := by simp
  map_one_eq_zero' := by simp
  leibniz' a b := by
    simp [commutatorFirstOrderMap_fst, Algebra.smul_def, mul_comm]

omit [DecidableEq n] in
@[simp] theorem commutatorDerivation_matrix (X : Matrix (n ⊕ n) (n ⊕ n) S) (i j) :
    commutatorDerivation R n S X (universalMatrix R n i j) =
      Symplectic.comm X (coefficientMatrix R n S) i j :=
  congrArg TrivSqZeroExt.snd (squareZeroEvaluation_matrix R n (DualNumber S) _ _ i j)

omit [DecidableEq n] [IsScalarTower R (CoordinateRing R n) S] in
theorem coordinateDerivation_ext {D E : Derivation R (CoordinateRing R n) S}
    (h : ∀ i j, D (universalMatrix R n i j) = E (universalMatrix R n i j)) : D = E := by
  apply Derivation.ext
  intro a
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
  induction p using MvPolynomial.induction_on with
  | C r =>
      change D (algebraMap R (CoordinateRing R n) r) = E (algebraMap R (CoordinateRing R n) r)
      simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p ij hp =>
      simp only [map_mul, Derivation.leibniz, hp]
      exact congrArg (fun x => Ideal.Quotient.mk (squareZeroIdeal R n) p • x +
        Ideal.Quotient.mk (squareZeroIdeal R n) (MvPolynomial.X ij) •
          E (Ideal.Quotient.mk (squareZeroIdeal R n) p)) (h ij.1 ij.2)

def commutatorLinearMap : Matrix (n ⊕ n) (n ⊕ n) S →ₗ[S]
    Derivation R (CoordinateRing R n) S where
  toFun := commutatorDerivation R n S
  map_add' X Y := by
    apply coordinateDerivation_ext
    intro i j
    simp [Symplectic.comm, add_mul, mul_add]
    abel
  map_smul' a X := by
    apply coordinateDerivation_ext
    intro i j
    simp [Symplectic.comm, mul_sub]

end Commutator

omit [DecidableEq n] in
theorem coordinateTangentRingHom_ext {S : Type u} [CommRing S]
    (f g : TangentRing R (CoordinateRing R n) →+* S)
    (hb : ∀ a, f (algebraMap (CoordinateRing R n) _ a) = g (algebraMap (CoordinateRing R n) _ a))
    (hd : ∀ i j, f (SymmetricAlgebra.ι _ _ (KaehlerDifferential.D R _ (universalMatrix R n i j))) =
      g (SymmetricAlgebra.ι _ _ (KaehlerDifferential.D R _ (universalMatrix R n i j)))) : f = g := by
  letI : Algebra (CoordinateRing R n) S := (f.comp (algebraMap (CoordinateRing R n) _)).toAlgebra
  letI : Algebra R S := ((algebraMap (CoordinateRing R n) S).comp (algebraMap R _)).toAlgebra
  letI : IsScalarTower R (CoordinateRing R n) S :=
    IsScalarTower.of_algebraMap_eq' (R := R) (S := CoordinateRing R n) (A := S) rfl
  let F : TangentRing R (CoordinateRing R n) →ₐ[CoordinateRing R n] S :=
    { __ := f, commutes' := fun _ => rfl }
  let G : TangentRing R (CoordinateRing R n) →ₐ[CoordinateRing R n] S :=
    { __ := g, commutes' := fun a => (hb a).symm }
  have h : tangentAlgebraHomEquiv R (CoordinateRing R n) S F =
      tangentAlgebraHomEquiv R (CoordinateRing R n) S G := by
    apply coordinateDerivation_ext
    intro i j
    have hF := tangentAlgebraHomEquiv_symm_apply R (CoordinateRing R n) S
      (tangentAlgebraHomEquiv R (CoordinateRing R n) S F) (universalMatrix R n i j)
    have hG := tangentAlgebraHomEquiv_symm_apply R (CoordinateRing R n) S
      (tangentAlgebraHomEquiv R (CoordinateRing R n) S G) (universalMatrix R n i j)
    rw [Equiv.symm_apply_apply] at hF hG
    exact hF.symm.trans ((hd i j).trans hG)
  exact congrArg AlgHom.toRingHom ((tangentAlgebraHomEquiv R (CoordinateRing R n) S).injective h)

section ChartSection
variable (e : Equiv.Perm (n ⊕ n))
variable (S : Type u) [CommRing S] [Algebra (ChartRing R n) S] [Algebra R S]
  [IsScalarTower R (ChartRing R n) S]

def chartCommutatorGenerator (D : Derivation R (ChartRing R n) S) :
    Matrix (n ⊕ n) (n ⊕ n) S :=
  (chartGenerator ((chartA R n).map (algebraMap (ChartRing R n) S))
    (Units.map (algebraMap (ChartRing R n) S).mapMatrix.toMonoidHom (chartUnitT R n))
    (fun i j => D (chartA R n i j)) (fun i j => D (chartT R n i j))).submatrix e.symm e.symm

omit [IsScalarTower R (ChartRing R n) S] in
theorem chartCommutatorGenerator_comm (D : Derivation R (ChartRing R n) S) :
    Symplectic.comm (chartCommutatorGenerator R n e S D)
      (((universalMatrix R n).map (permutationChartEmbedding R n e)).map
        (algebraMap (ChartRing R n) S)) =
      fun i j => D (permutationChartEmbedding R n e (universalMatrix R n i j)) := by
  rw [permutationChartEmbedding_matrix]
  have hm : ((generalChart (chartA R n) (chartT R n)).submatrix e.symm e.symm).map
      (algebraMap (ChartRing R n) S) =
      (generalChart ((chartA R n).map (algebraMap (ChartRing R n) S))
        ((chartT R n).map (algebraMap (ChartRing R n) S))).submatrix e.symm e.symm := by
    change ((generalChart (chartA R n) (chartT R n)).map
      (algebraMap (ChartRing R n) S)).submatrix e.symm e.symm = _
    congr 1
    ext (i | i) (j | j) <;> simp [generalChart, Matrix.mul_apply, map_sum, map_mul]
  rw [hm]
  change Symplectic.comm ((chartGenerator _ _ _ _).submatrix e.symm e.symm) _ = _
  rw [Symplectic.comm, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv]
  change (Symplectic.comm (chartGenerator _ _ _ _) (generalChart _ _)).submatrix e.symm e.symm = _
  have hc := chartGenerator_comm ((chartA R n).map (algebraMap (ChartRing R n) S))
    (Units.map (algebraMap (ChartRing R n) S).mapMatrix.toMonoidHom (chartUnitT R n))
    (fun i j => D (chartA R n i j)) (fun i j => D (chartT R n i j))
  change Symplectic.comm (chartGenerator _ _ _ _)
    (generalChart _ ((chartT R n).map (algebraMap (ChartRing R n) S))) = _ at hc
  rw [hc]
  let dA : Matrix n n S := fun i j => D (chartA R n i j)
  let dT : Matrix n n S := fun i j => D (chartT R n i j)
  let A := (chartA R n).map (algebraMap (ChartRing R n) S)
  let T := (chartT R n).map (algebraMap (ChartRing R n) S)
  let dM : Matrix n n (ChartRing R n) → Matrix n n S := fun M i j => D (M i j)
  have dmul (M N : Matrix n n (ChartRing R n)) :
      dM (M * N) = dM M * N.map (algebraMap (ChartRing R n) S) +
        M.map (algebraMap (ChartRing R n) S) * dM N := by
    ext i j
    simp only [dM, Matrix.mul_apply, Matrix.add_apply, Matrix.map_apply, map_sum,
      Derivation.leibniz, Algebra.smul_def, Finset.sum_add_distrib]
    rw [add_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro x _
    exact mul_comm _ _
  have hd : (fun i j => D (generalChart (chartA R n) (chartT R n) i j)) =
      Matrix.fromBlocks (dT * A + T * dA) dT
        (-(dA * T * A + A * dT * A + A * T * dA)) (-(dA * T + A * dT)) := by
    have hblock : (fun i j => D (generalChart (chartA R n) (chartT R n) i j)) =
        Matrix.fromBlocks (dM (chartT R n * chartA R n)) dT
          (-dM (chartA R n * chartT R n * chartA R n)) (-dM (chartA R n * chartT R n)) := by
      ext (i | i) (j | j) <;> simp [generalChart, dM, dT]
    rw [hblock]
    simp only [dmul, Matrix.map_mul, add_mul]
    rfl
  change (Matrix.fromBlocks (dT * A + T * dA) dT
    (-(dA * T * A + A * dT * A + A * T * dA)) (-(dA * T + A * dT))).submatrix e.symm e.symm = _
  rw [← hd]
  have h := congrArg (fun M => fun i j => D (M i j)) (permutationChartEmbedding_matrix R n e)
  exact h.symm

end ChartSection

abbrev CommutatorRing : Type u := MvPolynomial ((n ⊕ n) × (n ⊕ n)) (CoordinateRing R n)

def commutatorCoordinateMap : TangentRing R (CoordinateRing R n) →ₐ[CoordinateRing R n]
    CommutatorRing R n :=
  (tangentAlgebraHomEquiv R (CoordinateRing R n) (CommutatorRing R n)).symm
    (commutatorDerivation R n (CommutatorRing R n) (fun i j => MvPolynomial.X (i, j)))

omit [DecidableEq n] in
@[simp] theorem commutatorCoordinateMap_D (i j) :
    commutatorCoordinateMap R n
      (SymmetricAlgebra.ι (CoordinateRing R n) _
        (KaehlerDifferential.D R (CoordinateRing R n) (universalMatrix R n i j))) =
      Symplectic.comm (fun i j => MvPolynomial.X (i, j))
        (coefficientMatrix R n (CommutatorRing R n)) i j := by
  rw [commutatorCoordinateMap, tangentAlgebraHomEquiv_symm_apply, commutatorDerivation_matrix]

def commutatorAffineMap : Spec (.of (CommutatorRing R n)) ⟶ tangentScheme R (CoordinateRing R n) :=
  Spec.map (CommRingCat.ofHom (commutatorCoordinateMap R n).toRingHom)

def commutatorBaseProjection : Spec (.of (CommutatorRing R n)) ⟶ squareZeroScheme R n :=
  Spec.map (CommRingCat.ofHom (algebraMap (CoordinateRing R n) (CommutatorRing R n)))

omit [DecidableEq n] in
theorem commutatorAffineMap_over : commutatorAffineMap R n ≫
    tangentProjection R (CoordinateRing R n) = commutatorBaseProjection R n := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  exact RingHom.ext (commutatorCoordinateMap R n).commutes

/-- The trivial matrix bundle on the orbit, obtained by restricting the polynomial bundle. -/
def orbitMatrixBundle : Scheme.{u} :=
  pullback (commutatorBaseProjection R n) (maximalRankOpen R n).ι

def orbitMatrixBundleProjection : orbitMatrixBundle R n ⟶ maximalRankScheme R n :=
  pullback.snd _ _

/-- The global infinitesimal conjugation morphism into the canonical tangent scheme. -/
def orbitCommutatorMap : orbitMatrixBundle R n ⟶ orbitTangentScheme R n :=
  pullback.lift (pullback.fst _ _ ≫ commutatorAffineMap R n)
    (orbitMatrixBundleProjection R n) (by
      rw [Category.assoc, commutatorAffineMap_over]
      exact pullback.condition)

@[simp] theorem orbitCommutatorMap_over : orbitCommutatorMap R n ≫ orbitTangentProjection R n =
    orbitMatrixBundleProjection R n := pullback.lift_snd _ _ _

theorem orbitCommutatorMap_affine : orbitCommutatorMap R n ≫
    pullback.fst (tangentProjection R (CoordinateRing R n)) (maximalRankOpen R n).ι =
      pullback.fst (commutatorBaseProjection R n) (maximalRankOpen R n).ι ≫
        commutatorAffineMap R n := pullback.lift_fst _ _ _

def universalChartDerivation : Derivation R (ChartRing R n) (TangentRing R (ChartRing R n)) :=
  (SymmetricAlgebra.ι (ChartRing R n) _).compDer (KaehlerDifferential.D R (ChartRing R n))

def chartCommutatorSectionCoordinates (e : Equiv.Perm (n ⊕ n)) :
    CommutatorRing R n →+* TangentRing R (ChartRing R n) :=
  MvPolynomial.eval₂Hom
    ((algebraMap (ChartRing R n) (TangentRing R (ChartRing R n))).comp
      (permutationChartEmbedding R n e).toRingHom)
    (fun ij => chartCommutatorGenerator R n e (TangentRing R (ChartRing R n))
      (universalChartDerivation R n) ij.1 ij.2)

theorem chartCommutatorSectionCoordinates_comp (e : Equiv.Perm (n ⊕ n)) :
    letI := (permutationChartEmbedding R n e).toAlgebra
    letI := IsScalarTower.of_algHom (permutationChartEmbedding R n e)
    (chartCommutatorSectionCoordinates R n e).comp (commutatorCoordinateMap R n).toRingHom =
      tangentMap R (CoordinateRing R n) (ChartRing R n) := by
  letI := (permutationChartEmbedding R n e).toAlgebra
  letI := IsScalarTower.of_algHom (permutationChartEmbedding R n e)
  apply coordinateTangentRingHom_ext R n
  · intro a
    change chartCommutatorSectionCoordinates R n e
      (commutatorCoordinateMap R n (algebraMap (CoordinateRing R n) _ a)) = _
    rw [AlgHom.commutes, tangentMap_algebraMap]
    change MvPolynomial.eval₂Hom _ _ (MvPolynomial.C a) = _
    exact MvPolynomial.eval₂Hom_C _ _ a
  · intro i j
    change chartCommutatorSectionCoordinates R n e
      (commutatorCoordinateMap R n (SymmetricAlgebra.ι _ _ (KaehlerDifferential.D R _ _))) = _
    rw [commutatorCoordinateMap_D, tangentMap_D]
    have hm := congrFun (congrFun (chartCommutatorGenerator_comm R n e
      (TangentRing R (ChartRing R n)) (universalChartDerivation R n)) i) j
    simpa [chartCommutatorSectionCoordinates, Symplectic.comm, Matrix.mul_apply,
      coefficientMatrix, Matrix.map_apply, map_sum, map_sub, map_mul,
      universalChartDerivation] using hm

def orbitChartTangentMap (e : Equiv.Perm (n ⊕ n)) :
    tangentScheme R (ChartRing R n) ⟶ orbitTangentScheme R n := by
  letI := (permutationChartEmbedding R n e).toAlgebra
  letI := IsScalarTower.of_algHom (permutationChartEmbedding R n e)
  letI := permutationChart_isLocalization R n e
  letI : Algebra.FormallyEtale (CoordinateRing R n) (ChartRing R n) :=
    Algebra.FormallyEtale.of_isLocalization (Rₘ := ChartRing R n) (Submonoid.powers (chartMinor R n e))
  exact tangentLiftToOpen R (CoordinateRing R n) (ChartRing R n) (maximalRankOpen R n)
    (orbitChartMap R n e) (orbitChartMap_over R n e)

def chartCommutatorSectionMap (e : Equiv.Perm (n ⊕ n)) :
    tangentScheme R (ChartRing R n) ⟶ orbitMatrixBundle R n :=
  pullback.lift (Spec.map (CommRingCat.ofHom (chartCommutatorSectionCoordinates R n e)))
    (tangentProjection R (ChartRing R n) ≫ orbitChartMap R n e) (by
      rw [Category.assoc, orbitChartMap_over]
      change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
      rw [← Spec.map_comp, ← Spec.map_comp]
      apply congrArg Spec.map
      apply CommRingCat.hom_ext
      exact RingHom.ext (fun a => MvPolynomial.eval₂Hom_C _ _ a))

theorem chartCommutatorSectionMap_comp (e : Equiv.Perm (n ⊕ n)) :
    chartCommutatorSectionMap R n e ≫ orbitCommutatorMap R n = orbitChartTangentMap R n e := by
  letI := (permutationChartEmbedding R n e).toAlgebra
  letI := IsScalarTower.of_algHom (permutationChartEmbedding R n e)
  apply pullback.hom_ext
  · rw [Category.assoc, orbitCommutatorMap_affine, ← Category.assoc, chartCommutatorSectionMap,
      pullback.lift_fst]
    simp only [orbitChartTangentMap, tangentLiftToOpen, pullback.lift_fst]
    change Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp]
    apply congrArg Spec.map
    apply CommRingCat.hom_ext
    exact chartCommutatorSectionCoordinates_comp R n e
  · change (chartCommutatorSectionMap R n e ≫ orbitCommutatorMap R n) ≫
      orbitTangentProjection R n = _
    rw [Category.assoc, orbitCommutatorMap_over]
    exact (pullback.lift_snd _ _ _).trans (pullback.lift_snd _ _ _).symm

theorem orbitChartTangent_isPullback (e : Equiv.Perm (n ⊕ n)) :
    IsPullback (orbitChartTangentMap R n e) (tangentProjection R (ChartRing R n))
      (orbitTangentProjection R n) (orbitChartMap R n e) := by
  letI := (permutationChartEmbedding R n e).toAlgebra
  letI := IsScalarTower.of_algHom (permutationChartEmbedding R n e)
  letI := permutationChart_isLocalization R n e
  letI : Algebra.FormallyEtale (CoordinateRing R n) (ChartRing R n) :=
    Algebra.FormallyEtale.of_isLocalization (Rₘ := ChartRing R n) (Submonoid.powers (chartMinor R n e))
  exact tangentLiftToOpen_isPullback R (CoordinateRing R n) (ChartRing R n) (maximalRankOpen R n)
    (orbitChartMap R n e) (orbitChartMap_over R n e)

/-- A section of the global commutator map on the pullback to each orbit chart. -/
def orbitCommutatorLocalSection (e : Equiv.Perm (n ⊕ n)) :
    pullback (orbitTangentProjection R n) (orbitChartMap R n e) ⟶ orbitMatrixBundle R n :=
  (orbitChartTangent_isPullback R n e).isoPullback.inv ≫ chartCommutatorSectionMap R n e

theorem orbitCommutatorLocalSection_comp (e : Equiv.Perm (n ⊕ n)) :
    orbitCommutatorLocalSection R n e ≫ orbitCommutatorMap R n =
      pullback.fst (orbitTangentProjection R n) (orbitChartMap R n e) := by
  rw [orbitCommutatorLocalSection, Category.assoc, chartCommutatorSectionMap_comp]
  exact (orbitChartTangent_isPullback R n e).isoPullback_inv_fst

theorem orbitCommutatorMap_surjective : Surjective (orbitCommutatorMap R n) := by
  constructor
  intro y
  let x := orbitTangentProjection R n y
  have hx : x ∈ (⨆ e, orbitChartOpen R n e) := by rw [orbitChart_cover]; trivial
  obtain ⟨e, he⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
  have hc : x ∈ Set.range (orbitChartMap R n e) := by
    refine ⟨(SquareZeroGeometry.orbitChartIso R n e).hom ⟨x, he⟩, ?_⟩
    change ((SquareZeroGeometry.orbitChartIso R n e).hom ≫ orbitChartMap R n e) ⟨x, he⟩ = x
    simp only [orbitChartMap, Iso.hom_inv_id_assoc]
    rfl
  have hy : y ∈ Set.range (pullback.fst (orbitTangentProjection R n) (orbitChartMap R n e)) := by
    rw [Scheme.Pullback.range_fst]
    exact hc
  obtain ⟨z, hz⟩ := hy
  refine ⟨orbitCommutatorLocalSection R n e z, ?_⟩
  exact (congrArg (fun f => f z) (orbitCommutatorLocalSection_comp R n e)).trans hz

end
end Universality.GlobalSymplectic

namespace Universality.ExteriorGeometry
noncomputable section
open AffineForms AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open AlgebraicGeometry.StructureSheaf
set_option backward.isDefEq.respectTransparency false
universe u
variable (R A B : Type u) [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]

section Pullback

local instance (d : ℕ) [Algebra A B] : Module A (⋀[B]^d (KaehlerDifferential R B)) :=
  Module.compHom _ (algebraMap A B)
local instance (d : ℕ) [Algebra A B] : IsScalarTower A B (⋀[B]^d (KaehlerDifferential R B)) :=
  IsScalarTower.of_algebraMap_smul fun _ _ => rfl

def kaehlerDegreeMap (f : A →ₐ[R] B) (d : ℕ) :
    (⋀[A]^d (KaehlerDifferential R A)) →ₛₗ[f.toRingHom] (⋀[B]^d (KaehlerDifferential R B)) := by
  letI := f.toAlgebra
  letI := IsScalarTower.of_algHom f
  let L : (⋀[A]^d (KaehlerDifferential R A)) →ₗ[A] (⋀[B]^d (KaehlerDifferential R B)) :=
    exteriorPower.alternatingMapLinearEquiv <|
      AlternatingMap.compLinearMap
        { (exteriorPower.ιMulti B d).toMultilinearMap.restrictScalars A with
          map_eq_zero_of_eq' := fun v _ _ h hne => (exteriorPower.ιMulti B d).map_eq_zero_of_eq v h hne }
        (KaehlerDifferential.map R R A B)
  exact { toFun := L, map_add' := L.map_add, map_smul' := L.map_smul }

theorem kaehlerDegreeMap_D_wedge (f : A →ₐ[R] B) (d : ℕ) (a : Fin d → A) :
    kaehlerDegreeMap R A B f d (exteriorPower.ιMulti A d (fun i => KaehlerDifferential.D R A (a i))) =
      exteriorPower.ιMulti B d (fun i => KaehlerDifferential.D R B (f (a i))) := by
  letI := f.toAlgebra
  letI := IsScalarTower.of_algHom f
  change exteriorPower.alternatingMapLinearEquiv _ (exteriorPower.ιMulti A d _) = _
  rw [exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
  change exteriorPower.ιMulti B d (fun i =>
    KaehlerDifferential.map R R A B (KaehlerDifferential.D R A (a i))) = _
  simp only [KaehlerDifferential.map_D]
  rfl

end Pullback

/-- Pullback of the actual exterior square along an algebra homomorphism. -/
def kaehlerTwoMap (f : A →ₐ[R] B) : KaehlerTwoForms A R →ₛₗ[f.toRingHom] KaehlerTwoForms B R :=
  kaehlerDegreeMap R A B f 2

@[simp] theorem kaehlerTwoMap_D_wedge (f : A →ₐ[R] B) (a b : A) :
    kaehlerTwoMap R A B f (exteriorPower.ιMulti A 2 ![KaehlerDifferential.D R A a, KaehlerDifferential.D R A b]) =
      exteriorPower.ιMulti B 2 ![KaehlerDifferential.D R B (f a), KaehlerDifferential.D R B (f b)] := by
  exact kaehlerDegreeMap_D_wedge R A B f 2 ![a, b]

theorem kaehlerTwoMap_comp (C : Type u) [CommRing C] [Algebra R C]
    (f : A →ₐ[R] B) (g : B →ₐ[R] C) (w : KaehlerTwoForms A R) :
    kaehlerTwoMap R B C g (kaehlerTwoMap R A B f w) = kaehlerTwoMap R A C (g.comp f) w := by
  obtain ⟨I, hI, c, a, b, rfl⟩ := kaehlerTwo_expression A R w
  simp only [map_sum, map_smulₛₗ]
  apply Finset.sum_congr rfl
  intro i _
  rw [kaehlerTwoMap_D_wedge R A B f (a i) (b i),
    kaehlerTwoMap_D_wedge R B C g (f (a i)) (f (b i)),
    kaehlerTwoMap_D_wedge R A C (g.comp f) (a i) (b i)]
  rfl

theorem kaehlerTwoMap_canonicalTrace {n : Type u} [Fintype n]
    (f : A →ₐ[R] B) (T X : Matrix n n A) :
    kaehlerTwoMap R A B f (kaehlerCanonicalTrace A R T X) =
      kaehlerCanonicalTrace B R (T.map f) (X.map f) := by
  simp only [kaehlerCanonicalTrace, map_sum, kaehlerTwoMap_D_wedge, Matrix.map_apply]

theorem kaehlerTwoMap_algebraMap [Algebra A B] [IsScalarTower R A B] (w : KaehlerTwoForms A R) :
    kaehlerTwoMap R A B (IsScalarTower.toAlgHom R A B) w = kaehlerExteriorMap A B R w := by
  obtain ⟨I, hI, c, a, b, rfl⟩ := kaehlerTwo_expression A R w
  simp only [map_sum, map_smulₛₗ]
  apply Finset.sum_congr rfl
  intro i _
  rw [kaehlerTwoMap_D_wedge R A B (IsScalarTower.toAlgHom R A B) (a i) (b i),
    kaehlerExteriorMap_D_wedge A B R (a i) (b i)]
  rfl

/-- Pullback on sections uses mathlib's map of the associated module sheaves. -/
def kaehlerSectionPullback (f : A →ₐ[R] B)
    (U : Opens (PrimeSpectrum.Top A)) (V : Opens (PrimeSpectrum.Top B))
    (h : V.1 ⊆ PrimeSpectrum.comap f.toRingHom ⁻¹' U.1) :
    (structureSheafInType A (KaehlerTwoForms A R)).obj.obj (op U) →ₛₗ[f.toRingHom]
      (structureSheafInType B (KaehlerTwoForms B R)).obj.obj (op V) :=
  StructureSheaf.comapₗ (kaehlerTwoMap R A B f) U V h

theorem primeExterior_comap (f : A →ₐ[R] B) (q : PrimeSpectrum B)
    (w : LocalizedModule (PrimeSpectrum.comap f.toRingHom q).asIdeal.primeCompl (KaehlerTwoForms A R)) :
    primeExteriorEquiv B R q (Localizations.comapFun (kaehlerTwoMap R A B f) q w) =
      kaehlerTwoMap R (PrimeLocalRing A (PrimeSpectrum.comap f.toRingHom q)) (PrimeLocalRing B q)
        (Localization.localAlgHom (PrimeSpectrum.comap f.toRingHom q).asIdeal q.asIdeal f rfl)
        (primeExteriorEquiv A R (PrimeSpectrum.comap f.toRingHom q) w) := by
  let p := PrimeSpectrum.comap f.toRingHom q
  let g : PrimeLocalRing A p →ₐ[R] PrimeLocalRing B q :=
    Localization.localAlgHom p.asIdeal q.asIdeal f rfl
  induction w using LocalizedModule.induction_on with
  | h w s =>
    apply (IsUnit.smul_bijective (β := KaehlerTwoForms (PrimeLocalRing B q) R)
      (IsLocalization.map_units (PrimeLocalRing B q) (⟨f s.val, s.property⟩ : q.asIdeal.primeCompl))).1
    dsimp only
    rw [Localizations.comapFun_mk]
    refine (primeExteriorEquiv_mk_cancel B R q (kaehlerTwoMap R A B f w) ⟨f s.val, s.property⟩).trans ?_
    have hg : g (algebraMap A (PrimeLocalRing A p) s.val) =
        algebraMap B (PrimeLocalRing B q) (f s.val) := Localization.localRingHom_to_map _ _ _ rfl _
    rw [← hg]
    refine Eq.trans ?_ ((congrArg (kaehlerTwoMap R _ _ g)
      (primeExteriorEquiv_mk_cancel A R p w s)).symm.trans
        ((kaehlerTwoMap R _ _ g).map_smulₛₗ (algebraMap A (PrimeLocalRing A p) s.val) _))
    rw [← kaehlerTwoMap_algebraMap R B (PrimeLocalRing B q),
      ← kaehlerTwoMap_algebraMap R A (PrimeLocalRing A p)]
    rw [kaehlerTwoMap_comp, kaehlerTwoMap_comp]
    have hf : (IsScalarTower.toAlgHom R B (PrimeLocalRing B q)).comp f =
        g.comp (IsScalarTower.toAlgHom R A (PrimeLocalRing A p)) := by
      apply AlgHom.ext
      intro a
      exact (Localization.localRingHom_to_map _ _ _ rfl a).symm
    rw [hf]

end
end Universality.ExteriorGeometry

namespace Universality.AffineForms
noncomputable section
variable {R S n : Type*} [CommRing R] [CommRing S] [Algebra R S] [Fintype n] [DecidableEq n]

theorem canonicalTrace_eq_commutator_pairing (D E : Derivation R S S)
    (A : Matrix n n S) (T : (Matrix n n S)ˣ) (Z X Y : Matrix (n ⊕ n) (n ⊕ n) S)
    (e : Equiv.Perm (n ⊕ n)) (h : generalChart A T.val = Z.submatrix e e)
    (hX : Symplectic.comm X Z = derivMatrix D Z) (hY : Symplectic.comm Y Z = derivMatrix E Z) :
    canonicalTrace T.val A D E = Symplectic.traceForm Z X Y := by
  have hc (F : Derivation R S S) (W : Matrix (n ⊕ n) (n ⊕ n) S)
      (hW : Symplectic.comm W Z = derivMatrix F Z) :
      Symplectic.comm (chartGenerator A T (derivMatrix F A) (derivMatrix F T.val)) (generalChart A T.val) =
        Symplectic.comm (W.submatrix e e) (generalChart A T.val) := by
    rw [chartGenerator_derivative, h, comm_submatrix, hW]
    rfl
  rw [← canonicalTrace_eq_KKS,
    Symplectic.traceForm_wellDefined_left _ _ _ _ (hc D X hX),
    Symplectic.traceForm_wellDefined_right _ _ _ _ (hc E Y hY), h, traceForm_submatrix]

omit [DecidableEq n] in
theorem canonicalTrace_potential (T A : Matrix n n S) (D E : Derivation R S S) :
    canonicalTrace T A D E = D (Matrix.trace (T * derivMatrix E A)) -
      E (Matrix.trace (T * derivMatrix D A)) - Matrix.trace (T * derivMatrix ⁅D, E⁆ A) := by
  rw [canonicalTrace_apply, derivation_trace, derivation_trace, derivMatrix_mul, derivMatrix_mul]
  have hc : derivMatrix ⁅D, E⁆ A = derivMatrix D (derivMatrix E A) - derivMatrix E (derivMatrix D A) := rfl
  rw [hc, mul_sub, Matrix.trace_add, Matrix.trace_add, Matrix.trace_sub, Matrix.trace_sub]
  ring

end
end Universality.AffineForms

namespace Universality.GlobalSymplectic
noncomputable section
open AffineForms ExteriorGeometry SquareZeroGeometry AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
set_option backward.isDefEq.respectTransparency false
universe u
variable (R n : Type u) [CommRing R] [Fintype n] [DecidableEq n]

theorem kaehlerMaurerCartan_map_evaluation
    (A B : Type u) [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    [Algebra A B] [IsScalarTower R A B]
    (g : (Matrix n n A)ˣ) (J : Matrix n n A) (D E : Derivation R B B) :
    kaehlerTwoEvaluation B R
      (kaehlerExteriorMap A B R (-kaehlerCanonicalTrace A R (J * g.inv) g.val)) D E =
      -(D (maurerCartanTrace (Units.map (algebraMap A B).mapMatrix.toMonoidHom g)
          (J.map (algebraMap A B)) E) -
        E (maurerCartanTrace (Units.map (algebraMap A B).mapMatrix.toMonoidHom g)
          (J.map (algebraMap A B)) D) -
        maurerCartanTrace (Units.map (algebraMap A B).mapMatrix.toMonoidHom g)
          (J.map (algebraMap A B)) ⁅D, E⁆) := by
  rw [(kaehlerExteriorMap A B R).map_neg, kaehlerCanonicalTrace_map]
  rw [map_neg, LinearMap.neg_apply, LinearMap.neg_apply,
    kaehlerCanonicalTrace_evaluation, canonicalTrace_potential]
  simp only [maurerCartanTrace, maurerCartan, Matrix.map_mul, mul_assoc]
  rfl

def orbitKaehlerPullback :
    (structureSheafInType (GeneralLinearRing R n) (KaehlerTwoForms (GeneralLinearRing R n) R)).obj.obj (op ⊤) :=
  kaehlerSectionPullback R (CoordinateRing R n) (GeneralLinearRing R n) (orbitCoordinateMap R n)
    (maximalRankOpen R n) ⊤ (fun q _ => conjugationToSquareZero_mem_maximalRank R n q)
    (orbitKaehlerTwoForm R n)

def orbitImagePrime (q : PrimeSpectrum (GeneralLinearRing R n)) : maximalRankOpen R n :=
  ⟨PrimeSpectrum.comap (orbitCoordinateMap R n).toRingHom q,
    conjugationToSquareZero_mem_maximalRank R n q⟩

def orbitPrimeMap (q : PrimeSpectrum (GeneralLinearRing R n)) :
    PrimeLocalRing (CoordinateRing R n) (orbitImagePrime R n q).val →ₐ[R]
      PrimeLocalRing (GeneralLinearRing R n) q :=
  Localization.localAlgHom (orbitImagePrime R n q).val.asIdeal q.asIdeal (orbitCoordinateMap R n) rfl

theorem orbitKaehlerPullback_germ (q : PrimeSpectrum (GeneralLinearRing R n)) :
    primeExteriorEquiv (GeneralLinearRing R n) R q ((orbitKaehlerPullback R n).val ⟨q, trivial⟩) =
      kaehlerTwoMap R _ _ (orbitPrimeMap R n q)
        (primeExteriorEquiv (CoordinateRing R n) R (orbitImagePrime R n q).val
          ((orbitKaehlerTwoForm R n).val (orbitImagePrime R n q))) :=
  primeExterior_comap R (CoordinateRing R n) (GeneralLinearRing R n) (orbitCoordinateMap R n) q _

def orbitPullbackChartEvaluation (q : PrimeSpectrum (GeneralLinearRing R n))
    (e : Equiv.Perm (n ⊕ n)) (he : (orbitImagePrime R n q).val ∈ permutationOpen R n e) :
    ChartRing R n →ₐ[R] PrimeLocalRing (GeneralLinearRing R n) q :=
  (orbitPrimeMap R n q).comp (primeChartEvaluation R n (orbitImagePrime R n q).val e he)

theorem orbitKaehlerPullback_chart (q : PrimeSpectrum (GeneralLinearRing R n))
    (e : Equiv.Perm (n ⊕ n)) (he : (orbitImagePrime R n q).val ∈ permutationOpen R n e) :
    primeExteriorEquiv (GeneralLinearRing R n) R q ((orbitKaehlerPullback R n).val ⟨q, trivial⟩) =
      kaehlerCanonicalTrace (PrimeLocalRing (GeneralLinearRing R n) q) R
        ((chartT R n).map (orbitPullbackChartEvaluation R n q e he))
        ((chartA R n).map (orbitPullbackChartEvaluation R n q e he)) := by
  rw [orbitKaehlerPullback_germ, orbitKaehlerTwoForm_chart R n (orbitImagePrime R n q) e he,
    kaehlerTwoMap_canonicalTrace]
  rfl

def generalLinearPrimeUnit (q : PrimeSpectrum (GeneralLinearRing R n)) :
    (Matrix (n ⊕ n) (n ⊕ n) (PrimeLocalRing (GeneralLinearRing R n) q))ˣ :=
  Units.map (algebraMap (GeneralLinearRing R n) (PrimeLocalRing (GeneralLinearRing R n) q)).mapMatrix.toMonoidHom
    (generalLinearUnit R n)

theorem orbitPullbackChartEvaluation_over (q : PrimeSpectrum (GeneralLinearRing R n))
    (e : Equiv.Perm (n ⊕ n)) (he : (orbitImagePrime R n q).val ∈ permutationOpen R n e) :
    (orbitPullbackChartEvaluation R n q e he).comp (permutationChartEmbedding R n e) =
      (IsScalarTower.toAlgHom R (GeneralLinearRing R n) (PrimeLocalRing (GeneralLinearRing R n) q)).comp
        (orbitCoordinateMap R n) := by
  rw [orbitPullbackChartEvaluation, AlgHom.comp_assoc, primeChartEvaluation_over]
  apply AlgHom.ext
  intro a
  exact Localization.localRingHom_to_map _ _ _ rfl a

theorem orbitPullbackChart_normalForm (q : PrimeSpectrum (GeneralLinearRing R n))
    (e : Equiv.Perm (n ⊕ n)) (he : (orbitImagePrime R n q).val ∈ permutationOpen R n e) :
    generalChart ((chartA R n).map (orbitPullbackChartEvaluation R n q e he))
      ((chartT R n).map (orbitPullbackChartEvaluation R n q e he)) =
        (conjugateJordan n (generalLinearPrimeUnit R n q)).submatrix e e := by
  let f := orbitPullbackChartEvaluation R n q e he
  have h : (((universalMatrix R n).map (permutationChartEmbedding R n e)).map f) =
      conjugateJordan n (generalLinearPrimeUnit R n q) := by
    change (universalMatrix R n).map (f.comp (permutationChartEmbedding R n e)) = _
    rw [orbitPullbackChartEvaluation_over]
    change ((universalMatrix R n).map (orbitCoordinateMap R n)).map
      (algebraMap (GeneralLinearRing R n) (PrimeLocalRing (GeneralLinearRing R n) q)) = _
    rw [orbitCoordinateMap_matrix, map_conjugateJordan]
    rfl
  rw [permutationChartEmbedding_matrix] at h
  change ((generalChart (chartA R n) (chartT R n)).map f).submatrix e.symm e.symm = _ at h
  rw [map_generalChart] at h
  have hh := congrArg (fun M => M.submatrix e e) h
  simpa only [Matrix.submatrix_submatrix, Equiv.symm_comp_self, Matrix.submatrix_id_id] using hh

local instance (q : PrimeSpectrum (GeneralLinearRing R n)) :
    Module (PrimeLocalRing (GeneralLinearRing R n) q) (PrimeLocalRing (GeneralLinearRing R n) q) :=
  Semiring.toModule

theorem orbitKaehlerPullback_KKS (q : PrimeSpectrum (GeneralLinearRing R n))
    (D E : Derivation R (PrimeLocalRing (GeneralLinearRing R n) q) (PrimeLocalRing (GeneralLinearRing R n) q)) :
    exteriorGermEvaluation (GeneralLinearRing R n) R q ((orbitKaehlerPullback R n).val ⟨q, trivial⟩) D E =
      Symplectic.traceForm (conjugateJordan n (generalLinearPrimeUnit R n q))
        (rightMaurerCartan (generalLinearPrimeUnit R n q) D)
        (rightMaurerCartan (generalLinearPrimeUnit R n q) E) := by
  obtain ⟨e, he⟩ := exists_prime_chart R n (orbitImagePrime R n q)
  unfold exteriorGermEvaluation
  rw [orbitKaehlerPullback_chart R n q e he, kaehlerCanonicalTrace_evaluation]
  let T := Units.map (orbitPullbackChartEvaluation R n q e he).toRingHom.mapMatrix.toMonoidHom (chartUnitT R n)
  change canonicalTrace T.val ((chartA R n).map (orbitPullbackChartEvaluation R n q e he)) D E = _
  apply canonicalTrace_eq_commutator_pairing D E _ T _ _ _ e (orbitPullbackChart_normalForm R n q e he)
  · exact (conjugation_derivative (generalLinearPrimeUnit R n q) jordanCell D (derivMatrix_jordanCell R n D)).symm
  · exact (conjugation_derivative (generalLinearPrimeUnit R n q) jordanCell E (derivMatrix_jordanCell R n E)).symm

/-- The left side is the sheaf pullback of the constructed global Kähler section. -/
theorem orbitKaehlerPullback_exact (q : PrimeSpectrum (GeneralLinearRing R n))
    (D E : Derivation R (PrimeLocalRing (GeneralLinearRing R n) q) (PrimeLocalRing (GeneralLinearRing R n) q)) :
    exteriorGermEvaluation (GeneralLinearRing R n) R q ((orbitKaehlerPullback R n).val ⟨q, trivial⟩) D E =
      -(D (maurerCartanTrace (generalLinearPrimeUnit R n q) jordanCell E) -
        E (maurerCartanTrace (generalLinearPrimeUnit R n q) jordanCell D) -
        maurerCartanTrace (generalLinearPrimeUnit R n q) jordanCell ⁅D, E⁆) := by
  rw [orbitKaehlerPullback_KKS]
  exact conjugation_KKS_exact (generalLinearPrimeUnit R n q) jordanCell D E
    (derivMatrix_jordanCell R n D) (derivMatrix_jordanCell R n E)

def generalLinearPrimeDifferentialBasis (q : PrimeSpectrum (GeneralLinearRing R n)) :
    Module.Basis ((n ⊕ n) × (n ⊕ n)) (PrimeLocalRing (GeneralLinearRing R n) q)
      (KaehlerDifferential R (PrimeLocalRing (GeneralLinearRing R n) q)) := by
  let M := IsLocalization.localizationLocalizationSubmodule
    (Submonoid.powers (genericMatrix R n).det) q.asIdeal.primeCompl
  letI : IsLocalization M (PrimeLocalRing (GeneralLinearRing R n) q) :=
    IsLocalization.localization_localization_isLocalization _ _ _
  exact localizedDifferentialBasis (R := R) (S := PrimeLocalRing (GeneralLinearRing R n) q) M

theorem generalLinearPrimeTwoEvaluation_injective (q : PrimeSpectrum (GeneralLinearRing R n)) :
    Function.Injective (kaehlerTwoEvaluation (PrimeLocalRing (GeneralLinearRing R n) q) R) := by
  let b := (generalLinearPrimeDifferentialBasis R n q).reindex (Fintype.equivFin _)
  exact kaehlerTwoEvaluation_injective _ R b

/-- The explicit exterior derivative of the Maurer–Cartan potential. -/
def maurerCartanExactForm : KaehlerTwoForms (GeneralLinearRing R n) R :=
  -kaehlerCanonicalTrace (GeneralLinearRing R n) R
    (jordanCell * (generalLinearUnit R n).inv) (generalLinearUnit R n).val

theorem orbitKaehlerPullback_eq_exactForm : orbitKaehlerPullback R n =
    StructureSheaf.toOpenₗ (GeneralLinearRing R n) (KaehlerTwoForms (GeneralLinearRing R n) R) ⊤
      (maurerCartanExactForm R n) := by
  apply Subtype.ext
  funext q
  apply (primeExteriorEquiv (GeneralLinearRing R n) R q.val).injective
  apply generalLinearPrimeTwoEvaluation_injective R n q.val
  apply LinearMap.ext₂
  intro D E
  change exteriorGermEvaluation (GeneralLinearRing R n) R q.val ((orbitKaehlerPullback R n).val q) D E = _
  refine (orbitKaehlerPullback_exact R n q.val D E).trans ?_
  change _ = kaehlerTwoEvaluation (PrimeLocalRing (GeneralLinearRing R n) q.val) R
    (primeExteriorEquiv (GeneralLinearRing R n) R q.val (LocalizedModule.mk (maurerCartanExactForm R n) 1)) D E
  refine Eq.trans ?_ (congrArg
    (fun w => kaehlerTwoEvaluation (PrimeLocalRing (GeneralLinearRing R n) q.val) R w D E)
    (primeExteriorEquiv_mk_one (GeneralLinearRing R n) R q.val (maurerCartanExactForm R n))).symm
  have hh := kaehlerMaurerCartan_map_evaluation R (n ⊕ n) (GeneralLinearRing R n)
    (PrimeLocalRing (GeneralLinearRing R n) q.val) (generalLinearUnit R n) jordanCell D E
  simpa only [map_jordanCell] using hh.symm

end
end Universality.GlobalSymplectic

namespace Universality.ExteriorGeometry
noncomputable section
open AffineForms
set_option backward.isDefEq.respectTransparency false
universe u
variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]

theorem derivation_smul_commutator (a : A) (D E : Derivation R A A) :
    ⁅a • D, E⁆ = a • ⁅D, E⁆ - E a • D := by
  ext x
  simp only [Derivation.commutator_apply, Derivation.smul_apply, Derivation.sub_apply,
    smul_eq_mul, Derivation.leibniz]
  ring

theorem derivation_commutator_smul (a : A) (D E : Derivation R A A) :
    ⁅D, a • E⁆ = D a • E + a • ⁅D, E⁆ := by
  ext x
  simp only [Derivation.commutator_apply, Derivation.smul_apply, Derivation.add_apply,
    smul_eq_mul, Derivation.leibniz]
  ring

def cartanThreeForm (ω : LinearMap.BilinForm A (Derivation R A A)) (hω : ω.IsAlt) :
    (Derivation R A A) [⋀^Fin 3]→ₗ[A] A where
  toMultilinearMap := MultilinearMap.mk' (fun v => exteriorDerivative2 ω (v 0) (v 1) (v 2))
    (by
      intro v i X Y
      fin_cases i <;>
        simp [exteriorDerivative2, Function.update, add_lie, lie_add, Derivation.add_apply] <;> ring)
    (by
      intro v i a X
      have hx0 := hω.neg_eq X (v 0)
      have hx1 := hω.neg_eq X (v 1)
      fin_cases i <;>
        simp [exteriorDerivative2, Function.update, derivation_smul_commutator,
          derivation_commutator_smul, Derivation.smul_apply, Derivation.leibniz, smul_eq_mul,
          ← hx0, ← hx1] <;> ring)
  map_eq_zero_of_eq' v i j h hij := by
    have hc01 (D E : Derivation R A A) : exteriorDerivative2 ω D D E = 0 := by
      simp [exteriorDerivative2, hω.self_eq_zero]
    have hc02 (D E : Derivation R A A) : exteriorDerivative2 ω D E D = 0 := by
      have he : ω ⁅E, D⁆ D = -ω ⁅D, E⁆ D := by
        calc
          _ = ω (-⁅D, E⁆) D := congrArg (fun F => ω F D) (lie_skew E D).symm
          _ = _ := by simp only [map_neg, LinearMap.neg_apply]
      simp only [exteriorDerivative2, ← hω.neg_eq D E, map_neg, hω.self_eq_zero, map_zero,
        lie_self, LinearMap.zero_apply, he]
      ring
    have hc12 (D E : Derivation R A A) : exteriorDerivative2 ω D E E = 0 := by
      simp [exteriorDerivative2, hω.self_eq_zero]
    change exteriorDerivative2 ω (v 0) (v 1) (v 2) = 0
    fin_cases i <;> fin_cases j <;> simp only [Fin.reduceFinMk] at h hij
    all_goals first | exact False.elim (hij rfl) | skip
    all_goals rw [h]
    all_goals first | exact hc01 _ _ | exact hc02 _ _ | exact hc12 _ _

section ExteriorDuality
variable {M N : Type u} [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]

variable {I : Type*} [Fintype I] [LinearOrder I]

def exteriorPairingEquiv (b : Module.Basis I A M) (d : ℕ) :
    (⋀[A]^d (Module.Dual A M)) ≃ₗ[A] Module.Dual A (⋀[A]^d M) :=
  (b.dualBasis.exteriorPower d).equiv (b.exteriorPower d).dualBasis (Equiv.refl _)

theorem exteriorPairingEquiv_toLinearMap (b : Module.Basis I A M) (d : ℕ) :
    (exteriorPairingEquiv A b d).toLinearMap = exteriorPower.pairingDual A M d := by
  apply (b.dualBasis.exteriorPower d).ext
  intro s
  change (b.dualBasis.exteriorPower d).equiv (b.exteriorPower d).dualBasis (Equiv.refl _)
    ((b.dualBasis.exteriorPower d) s) = _
  rw [Module.Basis.equiv_apply]
  rw [Module.Basis.coe_dualBasis]
  change (b.exteriorPower d).coord s = _
  rw [exteriorPower.basis_coord, exteriorPower.basis_apply]
  rw [Module.Basis.coe_dualBasis]
  rfl

end ExteriorDuality

variable {I : Type*} [Fintype I] [LinearOrder I]

def kaehlerFormEquiv (b : Module.Basis I A (KaehlerDifferential R A)) (d : ℕ) :
    (⋀[A]^d (KaehlerDifferential R A)) ≃ₗ[A] (Derivation R A A) [⋀^Fin d]→ₗ[A] A := by
  letI := Module.Free.of_basis b
  letI := Module.Finite.of_basis b
  let bD := b.dualBasis.map (KaehlerDifferential.linearMapEquivDerivation R A)
  exact (exteriorCongr A d (kaehlerOneEvaluationEquiv A R)).trans
    ((exteriorPairingEquiv A bD d).trans exteriorPower.alternatingMapLinearEquiv.symm)

theorem kaehlerFormEquiv_wedge (b : Module.Basis I A (KaehlerDifferential R A)) (d : ℕ)
    (x : Fin d → KaehlerDifferential R A) (D : Fin d → Derivation R A A) :
    kaehlerFormEquiv R A b d (exteriorPower.ιMulti A d x) D =
      (Matrix.of (fun i j => (D j).liftKaehlerDifferential (x i))).det := by
  letI := Module.Free.of_basis b
  letI := Module.Finite.of_basis b
  change exteriorPower.alternatingMapLinearEquiv.symm
    (exteriorPairingEquiv A _ d (exteriorCongr A d (kaehlerOneEvaluationEquiv A R)
      (exteriorPower.ιMulti A d x))) D = _
  rw [← LinearEquiv.coe_coe (exteriorPairingEquiv A _ d), exteriorPairingEquiv_toLinearMap]
  change exteriorPower.pairingDual A (Derivation R A A) d
    (exteriorPower.map d (kaehlerOneEvaluationEquiv A R).toLinearMap (exteriorPower.ιMulti A d x))
      (exteriorPower.ιMulti A d D) = _
  rw [exteriorPower.map_apply_ιMulti, exteriorPower.pairingDual_ιMulti_ιMulti]
  change (Matrix.of (fun i j => (D i).liftKaehlerDifferential (x j))).det = _
  exact Matrix.det_transpose _

theorem kaehlerTwoEvaluation_alternating (w : KaehlerTwoForms A R) :
    (kaehlerTwoEvaluation A R w).IsAlt := by
  intro D
  exact ((exteriorPower.alternatingMapLinearEquiv.symm (exteriorEvaluation A w)).compLinearMap
    (KaehlerDifferential.linearMapEquivDerivation R A).symm.toLinearMap).map_eq_zero_of_eq
      ![D, D] (i := 0) (j := 1) rfl (by decide)

def kaehlerOnePairing (α : KaehlerDifferential R A) : Module.Dual A (Derivation R A A) :=
  (Module.Dual.eval A (KaehlerDifferential R A) α).comp
    (KaehlerDifferential.linearMapEquivDerivation R A).symm.toLinearMap

@[simp] theorem kaehlerOnePairing_apply (α : KaehlerDifferential R A) (D : Derivation R A A) :
    kaehlerOnePairing R A α D = D.liftKaehlerDifferential α := rfl

def cartanTwoForm (η : Module.Dual A (Derivation R A A)) :
    (Derivation R A A) [⋀^Fin 2]→ₗ[A] A where
  toMultilinearMap := MultilinearMap.mk'
    (fun v => v 0 (η (v 1)) - v 1 (η (v 0)) - η ⁅v 0, v 1⁆)
    (by intro v i X Y; fin_cases i <;>
        simp [Function.update, add_lie, lie_add, Derivation.add_apply] <;> ring)
    (by intro v i a X; fin_cases i <;>
        simp [Function.update, derivation_smul_commutator, derivation_commutator_smul,
          Derivation.smul_apply, Derivation.leibniz, smul_eq_mul] <;> ring)
  map_eq_zero_of_eq' v i j h hij := by
    change v 0 (η (v 1)) - v 1 (η (v 0)) - η ⁅v 0, v 1⁆ = 0
    fin_cases i <;> fin_cases j <;> simp_all

def deRhamOne (b : Module.Basis I A (KaehlerDifferential R A)) (α : KaehlerDifferential R A) :
    KaehlerTwoForms A R :=
  (kaehlerFormEquiv R A b 2).symm (cartanTwoForm R A (kaehlerOnePairing R A α))

theorem deRhamOne_evaluation (b : Module.Basis I A (KaehlerDifferential R A))
    (α : KaehlerDifferential R A) (D : Fin 2 → Derivation R A A) :
    kaehlerFormEquiv R A b 2 (deRhamOne R A b α) D =
      D 0 ((D 1).liftKaehlerDifferential α) - D 1 ((D 0).liftKaehlerDifferential α) -
        ⁅D 0, D 1⁆.liftKaehlerDifferential α :=
  congrArg (fun f => f D) ((kaehlerFormEquiv R A b 2).apply_symm_apply _)

theorem deRhamOne_add (b : Module.Basis I A (KaehlerDifferential R A))
    (α β : KaehlerDifferential R A) :
    deRhamOne R A b (α + β) = deRhamOne R A b α + deRhamOne R A b β := by
  apply (kaehlerFormEquiv R A b 2).injective
  ext D
  simp only [map_add, AlternatingMap.add_apply, deRhamOne_evaluation]
  ring

theorem deRhamOne_sum (b : Module.Basis I A (KaehlerDifferential R A))
    {J : Type*} (s : Finset J) (α : J → KaehlerDifferential R A) :
    deRhamOne R A b (∑ i ∈ s, α i) = ∑ i ∈ s, deRhamOne R A b (α i) :=
  map_sum (AddMonoidHom.mk' (deRhamOne R A b) (deRhamOne_add R A b)) α s

theorem deRhamOne_coordinate (b : Module.Basis I A (KaehlerDifferential R A)) (c a : A) :
    deRhamOne R A b (c • KaehlerDifferential.D R A a) =
      exteriorPower.ιMulti A 2 ![KaehlerDifferential.D R A c, KaehlerDifferential.D R A a] := by
  apply (kaehlerFormEquiv R A b 2).injective
  ext D
  rw [deRhamOne_evaluation, kaehlerFormEquiv_wedge]
  simp only [map_smul, Derivation.liftKaehlerDifferential_comp_D, smul_eq_mul,
    Derivation.leibniz, Derivation.commutator_apply, Matrix.det_fin_two, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

def kaehlerTracePotential {n : Type u} [Fintype n] (T X : Matrix n n A) : KaehlerDifferential R A :=
  ∑ i, ∑ j, T i j • KaehlerDifferential.D R A (X j i)

theorem deRhamOne_tracePotential {n : Type u} [Fintype n]
    (b : Module.Basis I A (KaehlerDifferential R A)) (T X : Matrix n n A) :
    deRhamOne R A b (kaehlerTracePotential R A T X) = kaehlerCanonicalTrace A R T X := by
  simp only [kaehlerTracePotential, deRhamOne_sum, deRhamOne_coordinate, kaehlerCanonicalTrace]

/-- The de Rham differential into the actual exterior cube.
`deRhamTwo_coordinate` and `deRhamTwo_unique` characterize it by its standard generator rule. -/
def deRhamTwo (b : Module.Basis I A (KaehlerDifferential R A)) (w : KaehlerTwoForms A R) :
    ⋀[A]^3 (KaehlerDifferential R A) :=
  (kaehlerFormEquiv R A b 3).symm
    (cartanThreeForm R A (kaehlerTwoEvaluation A R w) (kaehlerTwoEvaluation_alternating R A w))

theorem deRhamTwo_evaluation (b : Module.Basis I A (KaehlerDifferential R A))
    (w : KaehlerTwoForms A R) (D : Fin 3 → Derivation R A A) :
    kaehlerFormEquiv R A b 3 (deRhamTwo R A b w) D =
      exteriorDerivative2 (kaehlerTwoEvaluation A R w) (D 0) (D 1) (D 2) :=
  congrArg (fun f => f D) ((kaehlerFormEquiv R A b 3).apply_symm_apply _)

theorem deRhamTwo_eq_zero_iff (b : Module.Basis I A (KaehlerDifferential R A))
    (w : KaehlerTwoForms A R) : deRhamTwo R A b w = 0 ↔ IsClosed (kaehlerTwoEvaluation A R w) := by
  constructor
  · intro h D E F
    have hh := deRhamTwo_evaluation R A b w ![D, E, F]
    rw [h, map_zero] at hh
    exact hh.symm
  · intro h
    apply (kaehlerFormEquiv R A b 3).injective
    apply AlternatingMap.ext
    intro D
    rw [deRhamTwo_evaluation, map_zero]
    exact h _ _ _

theorem deRhamTwo_add (b : Module.Basis I A (KaehlerDifferential R A))
    (w z : KaehlerTwoForms A R) :
    deRhamTwo R A b (w + z) = deRhamTwo R A b w + deRhamTwo R A b z := by
  apply (kaehlerFormEquiv R A b 3).injective
  ext D
  simp only [map_add, AlternatingMap.add_apply, deRhamTwo_evaluation,
    exteriorDerivative2, LinearMap.add_apply]
  ring

theorem deRhamTwo_sum (b : Module.Basis I A (KaehlerDifferential R A))
    {J : Type*} (s : Finset J) (w : J → KaehlerTwoForms A R) :
    deRhamTwo R A b (∑ i ∈ s, w i) = ∑ i ∈ s, deRhamTwo R A b (w i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact (deRhamTwo_eq_zero_iff R A b 0).mpr (by simpa using (closed_zero (R := R) (S := A)))
  | @insert i s hi ih => simp only [Finset.sum_insert hi, deRhamTwo_add, ih]

/-- The defining coordinate rule for the algebraic de Rham differential. -/
theorem deRhamTwo_coordinate (b : Module.Basis I A (KaehlerDifferential R A)) (c a z : A) :
    deRhamTwo R A b (c • exteriorPower.ιMulti A 2
      ![KaehlerDifferential.D R A a, KaehlerDifferential.D R A z]) =
      exteriorPower.ιMulti A 3
        ![KaehlerDifferential.D R A c, KaehlerDifferential.D R A a, KaehlerDifferential.D R A z] := by
  apply (kaehlerFormEquiv R A b 3).injective
  apply AlternatingMap.ext
  intro D
  rw [deRhamTwo_evaluation, kaehlerFormEquiv_wedge, map_smul, kaehlerTwoEvaluation_D_wedge]
  simp only [exteriorDerivative2, LinearMap.smul_apply, smul_eq_mul, coordinateForm_apply,
    Derivation.leibniz, map_sub, Derivation.commutator_apply,
    Matrix.det_fin_three, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
    Derivation.liftKaehlerDifferential_comp_D]
  ring


theorem kaehlerDegree_expression (d : ℕ) (w : ⋀[A]^d (KaehlerDifferential R A)) :
    ∃ (J : Type u) (_ : Fintype J) (c : J → A) (a : J → Fin d → A),
      w = ∑ i, c i • exteriorPower.ιMulti A d (fun j => KaehlerDifferential.D R A (a i j)) := by
  classical
  have hs : Submodule.span A (Set.range (fun a : Fin d → A =>
      exteriorPower.ιMulti A d (fun j => KaehlerDifferential.D R A (a j)))) = ⊤ := by
    have h := exteriorPower.ιMulti_span_of_span A d (KaehlerDifferential R A)
      (KaehlerDifferential.span_range_derivation R A)
    rw [← top_le_iff] at h ⊢
    apply h.trans
    apply Submodule.span_mono
    rintro _ ⟨v, hv, rfl⟩
    have h : ∀ i, ∃ a, KaehlerDifferential.D R A a = v i := fun i => hv (Set.mem_range_self i)
    choose a ha using h
    exact ⟨a, congrArg (exteriorPower.ιMulti A d) (funext ha)⟩
  have hw : w ∈ Submodule.span A (Set.range (fun a : Fin d → A =>
      exteriorPower.ιMulti A d (fun j => KaehlerDifferential.D R A (a j)))) := by rw [hs]; trivial
  obtain ⟨l, hl⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hw
  refine ⟨l.support, inferInstance, (fun i => l i), (fun i => i.val), ?_⟩
  change w = ∑ i ∈ l.support.attach, l i.val • exteriorPower.ιMulti A d
    (fun j => KaehlerDifferential.D R A (i.val j))
  exact hl.symm.trans (Finset.sum_attach l.support (fun a : Fin d → A =>
    l a • exteriorPower.ιMulti A d (fun j => KaehlerDifferential.D R A (a j)))).symm

theorem kaehlerDegreeMap_comp (B C : Type u) [CommRing B] [CommRing C] [Algebra R B] [Algebra R C]
    (f : A →ₐ[R] B) (g : B →ₐ[R] C) (d : ℕ) (w : ⋀[A]^d (KaehlerDifferential R A)) :
    kaehlerDegreeMap R B C g d (kaehlerDegreeMap R A B f d w) =
      kaehlerDegreeMap R A C (g.comp f) d w := by
  obtain ⟨J, hJ, c, a, rfl⟩ := kaehlerDegree_expression R A d w
  simp only [map_sum, map_smulₛₗ, kaehlerDegreeMap_D_wedge]
  rfl

theorem kaehlerDegreeMap_id (d : ℕ) (w : ⋀[A]^d (KaehlerDifferential R A)) :
    kaehlerDegreeMap R A A (AlgHom.id R A) d w = w := by
  obtain ⟨J, hJ, c, a, rfl⟩ := kaehlerDegree_expression R A d w
  simp only [map_sum, map_smulₛₗ]
  apply Finset.sum_congr rfl
  intro i _
  rw [kaehlerDegreeMap_D_wedge R A A (AlgHom.id R A) d (a i)]
  rfl

theorem kaehlerDegreeMap_injective_of_retraction (B : Type u) [CommRing B] [Algebra R B]
    (f : A →ₐ[R] B) (g : B →ₐ[R] A) (h : g.comp f = AlgHom.id R A) (d : ℕ) :
    Function.Injective (kaehlerDegreeMap R A B f d) := by
  intro w z he
  have hh := congrArg (kaehlerDegreeMap R B A g d) he
  rw [kaehlerDegreeMap_comp, kaehlerDegreeMap_comp, h] at hh
  exact (kaehlerDegreeMap_id R A d w).symm.trans (hh.trans (kaehlerDegreeMap_id R A d z))

theorem deRhamTwo_natural (B : Type u) [CommRing B] [Algebra R B]
    {J : Type*} [Fintype J] [LinearOrder J]
    (b : Module.Basis I A (KaehlerDifferential R A)) (bB : Module.Basis J B (KaehlerDifferential R B))
    (f : A →ₐ[R] B) (w : KaehlerTwoForms A R) :
    deRhamTwo R B bB (kaehlerDegreeMap R A B f 2 w) =
      kaehlerDegreeMap R A B f 3 (deRhamTwo R A b w) := by
  obtain ⟨J, hJ, c, a, z, rfl⟩ := kaehlerTwo_expression A R w
  simp only [map_sum, map_smulₛₗ, deRhamTwo_sum]
  apply Finset.sum_congr rfl
  intro i _
  have h2 (a z : A) : kaehlerDegreeMap R A B f 2 (exteriorPower.ιMulti A 2
      ![KaehlerDifferential.D R A a, KaehlerDifferential.D R A z]) =
      exteriorPower.ιMulti B 2 ![KaehlerDifferential.D R B (f a), KaehlerDifferential.D R B (f z)] :=
    kaehlerDegreeMap_D_wedge R A B f 2 ![a, z]
  have h3 (c a z : A) : kaehlerDegreeMap R A B f 3 (exteriorPower.ιMulti A 3
      ![KaehlerDifferential.D R A c, KaehlerDifferential.D R A a, KaehlerDifferential.D R A z]) =
      exteriorPower.ιMulti B 3 ![KaehlerDifferential.D R B (f c), KaehlerDifferential.D R B (f a),
        KaehlerDifferential.D R B (f z)] := kaehlerDegreeMap_D_wedge R A B f 3 ![c, a, z]
  rw [h2, deRhamTwo_coordinate, deRhamTwo_coordinate, h3]
  rfl

theorem deRhamTwo_basis_independent {J : Type*} [Fintype J] [LinearOrder J]
    (b : Module.Basis I A (KaehlerDifferential R A)) (c : Module.Basis J A (KaehlerDifferential R A))
    (w : KaehlerTwoForms A R) : deRhamTwo R A b w = deRhamTwo R A c w := by
  have h := deRhamTwo_natural R A A b c (AlgHom.id R A) w
  rw [kaehlerDegreeMap_id, kaehlerDegreeMap_id] at h
  exact h.symm

theorem deRhamTwo_neg (b : Module.Basis I A (KaehlerDifferential R A)) (w : KaehlerTwoForms A R) :
    deRhamTwo R A b (-w) = -deRhamTwo R A b w := by
  have h := deRhamTwo_add R A b w (-w)
  have hz : deRhamTwo R A b 0 = 0 := (deRhamTwo_eq_zero_iff R A b 0).mpr (by
    simpa using (closed_zero (R := R) (S := A)))
  rw [add_neg_cancel, hz] at h
  exact eq_neg_of_add_eq_zero_right h.symm

theorem deRhamTwo_canonicalTrace {n : Type u} [Fintype n]
    (b : Module.Basis I A (KaehlerDifferential R A)) (T X : Matrix n n A) :
    deRhamTwo R A b (kaehlerCanonicalTrace A R T X) = 0 := by
  apply (deRhamTwo_eq_zero_iff R A b _).mpr
  rw [kaehlerCanonicalTrace_evaluation]
  exact canonicalTrace_closed T X

theorem deRhamTwo_deRhamOne (b : Module.Basis I A (KaehlerDifferential R A))
    (α : KaehlerDifferential R A) : deRhamTwo R A b (deRhamOne R A b α) = 0 := by
  classical
  have hα : α ∈ Submodule.span A (Set.range (KaehlerDifferential.D R A)) := by
    rw [KaehlerDifferential.span_range_derivation]
    trivial
  obtain ⟨l, hl⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hα
  have hh : α = ∑ a ∈ l.support, l a • KaehlerDifferential.D R A a := hl.symm
  rw [hh, deRhamOne_sum, deRhamTwo_sum]
  apply Finset.sum_eq_zero
  intro a _
  rw [deRhamOne_coordinate]
  apply (deRhamTwo_eq_zero_iff R A b _).mpr
  rw [kaehlerTwoEvaluation_D_wedge]
  exact coordinateForm_closed _ _

theorem primeExactTrace_deRham_closed (p : PrimeSpectrum A) {n : Type u} [Fintype n]
    (b : Module.Basis I (PrimeLocalRing A p) (KaehlerDifferential R (PrimeLocalRing A p)))
    (T X : Matrix n n A) :
    deRhamTwo R (PrimeLocalRing A p) b
      (primeExteriorEquiv A R p (LocalizedModule.mk (-kaehlerCanonicalTrace A R T X) 1)) = 0 := by
  have h := (primeExteriorEquiv_mk_one A R p (-kaehlerCanonicalTrace A R T X)).trans
    (((kaehlerExteriorMap A (PrimeLocalRing A p) R).map_neg (kaehlerCanonicalTrace A R T X)).trans
      (congrArg Neg.neg (kaehlerCanonicalTrace_map A (PrimeLocalRing A p) R T X)))
  rw [h, ← deRhamOne_tracePotential R (PrimeLocalRing A p) b, deRhamTwo_neg,
    deRhamTwo_deRhamOne, neg_zero]

/-- The coordinate rule determines the differential uniquely on all two-forms. -/
theorem deRhamTwo_unique (b : Module.Basis I A (KaehlerDifferential R A))
    (δ : KaehlerTwoForms A R →+ ⋀[A]^3 (KaehlerDifferential R A))
    (hδ : ∀ c a z : A, δ (c • exteriorPower.ιMulti A 2
      ![KaehlerDifferential.D R A a, KaehlerDifferential.D R A z]) =
        exteriorPower.ιMulti A 3
          ![KaehlerDifferential.D R A c, KaehlerDifferential.D R A a, KaehlerDifferential.D R A z])
    (w : KaehlerTwoForms A R) : δ w = deRhamTwo R A b w := by
  obtain ⟨J, hJ, c, a, z, rfl⟩ := kaehlerTwo_expression A R w
  simp only [map_sum, deRhamTwo_sum, hδ, deRhamTwo_coordinate]

/-- A local section of an affine morphism gives a retraction on the corresponding local rings. -/
theorem localSection_prime_retraction (B : Type u) [CommRing B] [Algebra R B]
    (f : A →ₐ[R] B) (p : PrimeSpectrum A) (g : B →ₐ[R] PrimeLocalRing A p)
    (h : g.comp f = IsScalarTower.toAlgHom R A (PrimeLocalRing A p)) :
    ∃ (q : PrimeSpectrum B) (hpq : p.asIdeal = q.asIdeal.comap f),
      ∃ r : PrimeLocalRing B q →ₐ[R] PrimeLocalRing A p,
        r.comp (Localization.localAlgHom p.asIdeal q.asIdeal f hpq) =
          AlgHom.id R (PrimeLocalRing A p) := by
  let q : PrimeSpectrum B := PrimeSpectrum.comap g.toRingHom
    ⟨IsLocalRing.maximalIdeal (PrimeLocalRing A p), inferInstance⟩
  have hpq : p.asIdeal = q.asIdeal.comap f := by
    change p.asIdeal = ((IsLocalRing.maximalIdeal (PrimeLocalRing A p)).comap g.toRingHom).comap f.toRingHom
    rw [Ideal.comap_comap]
    change p.asIdeal = (IsLocalRing.maximalIdeal (PrimeLocalRing A p)).comap (g.comp f).toRingHom
    rw [h]
    exact (Localization.AtPrime.comap_maximalIdeal (I := p.asIdeal)).symm
  have hu (s : q.asIdeal.primeCompl) : IsUnit (g s) := by
    have hs : g s ∉ IsLocalRing.maximalIdeal (PrimeLocalRing A p) := s.property
    simpa only [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not] using hs
  let r : PrimeLocalRing B q →ₐ[R] PrimeLocalRing A p := IsLocalization.liftAlgHom hu
  refine ⟨q, hpq, r, ?_⟩
  apply IsLocalization.algHom_ext p.asIdeal.primeCompl
  apply AlgHom.ext
  intro a
  change r (Localization.localRingHom p.asIdeal q.asIdeal f.toRingHom hpq
    (algebraMap A (PrimeLocalRing A p) a)) = algebraMap A (PrimeLocalRing A p) a
  rw [Localization.localRingHom_to_map]
  change IsLocalization.lift hu (algebraMap B (PrimeLocalRing B q) (f a)) = _
  rw [IsLocalization.lift_eq]
  exact DFunLike.congr_fun h a

end
end Universality.ExteriorGeometry

namespace Universality.GlobalSymplectic
noncomputable section
open AffineForms ExteriorGeometry SquareZeroGeometry AlgebraicGeometry
set_option backward.isDefEq.respectTransparency false
universe u
variable (R n : Type u) [CommRing R] [Fintype n] [DecidableEq n]

omit [Fintype n] [DecidableEq n] in
theorem kaehlerDegreeMap_two (A B : Type u) [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    (f : A →ₐ[R] B) (w : KaehlerTwoForms A R) :
    kaehlerDegreeMap R A B f 2 w = kaehlerTwoMap R A B f w := rfl

def orbitPrimeDifferentialBasis (p : maximalRankOpen R n) :
    Module.Basis (Fin (Fintype.card ((n × n) ⊕ (n × n))))
      (PrimeLocalRing (CoordinateRing R n) p.val)
      (KaehlerDifferential R (PrimeLocalRing (CoordinateRing R n) p.val)) :=
  (primeChartDifferentialBasis R n p.val (exists_prime_chart R n p).choose
    (exists_prime_chart R n p).choose_spec).reindex (Fintype.equivFin _)

theorem orbitPrimeMap_has_retraction (p : maximalRankOpen R n) :
    ∃ (q : PrimeSpectrum (GeneralLinearRing R n)) (_hp : orbitImagePrime R n q = p),
      ∃ r : PrimeLocalRing (GeneralLinearRing R n) q →ₐ[R]
        PrimeLocalRing (CoordinateRing R n) (orbitImagePrime R n q).val,
        r.comp (orbitPrimeMap R n q) = AlgHom.id R _ := by
  obtain ⟨e, he⟩ := exists_prime_chart R n p
  let g := (primeChartEvaluation R n p.val e he).comp (generalLinearEval R n (chartConjugator R n e))
  have hg : g.comp (orbitCoordinateMap R n) =
      IsScalarTower.toAlgHom R (CoordinateRing R n) (PrimeLocalRing (CoordinateRing R n) p.val) := by
    change (primeChartEvaluation R n p.val e he).comp
      ((generalLinearEval R n (chartConjugator R n e)).comp (orbitCoordinateMap R n)) = _
    rw [generalLinearEval_comp_orbitCoordinateMap, primeChartEvaluation_over]
  obtain ⟨q, hpq, r, hr⟩ := localSection_prime_retraction R (CoordinateRing R n) (GeneralLinearRing R n)
    (orbitCoordinateMap R n) p.val g hg
  have hp : orbitImagePrime R n q = p := by
    apply Subtype.ext
    apply PrimeSpectrum.ext
    exact hpq.symm
  subst p
  exact ⟨q, rfl, r, hr⟩

/-- Pullback is injective on families of canonical Kähler germs, hence in particular on regular forms. -/
theorem orbitFormsPullback_injective (d : ℕ) :
    Function.Injective (fun w : ∀ p : maximalRankOpen R n,
      ⋀[PrimeLocalRing (CoordinateRing R n) p.val]^d
        (KaehlerDifferential R (PrimeLocalRing (CoordinateRing R n) p.val)) =>
      fun q : PrimeSpectrum (GeneralLinearRing R n) =>
        kaehlerDegreeMap R _ _ (orbitPrimeMap R n q) d (w (orbitImagePrime R n q))) := by
  intro w z h
  funext p
  obtain ⟨q, hp, r, hr⟩ := orbitPrimeMap_has_retraction R n p
  subst p
  exact kaehlerDegreeMap_injective_of_retraction R _ _ (orbitPrimeMap R n q) r hr d (congrFun h q)

def generalLinearPrimeDeRhamBasis (q : PrimeSpectrum (GeneralLinearRing R n)) :
    Module.Basis (Fin (Fintype.card ((n ⊕ n) × (n ⊕ n)))) (PrimeLocalRing (GeneralLinearRing R n) q)
      (KaehlerDifferential R (PrimeLocalRing (GeneralLinearRing R n) q)) :=
  (generalLinearPrimeDifferentialBasis R n q).reindex (Fintype.equivFin _)

def generalLinearDeRhamBasis :
    Module.Basis (Fin (Fintype.card ((n ⊕ n) × (n ⊕ n)))) (GeneralLinearRing R n)
      (KaehlerDifferential R (GeneralLinearRing R n)) :=
  (localizedDifferentialBasis (R := R) (S := GeneralLinearRing R n)
    (Submonoid.powers (genericMatrix R n).det)).reindex (Fintype.equivFin _)

/-- The actual Kähler one-form tr(J g⁻¹ dg) on GL. -/
def maurerCartanPotential : KaehlerDifferential R (GeneralLinearRing R n) :=
  kaehlerTracePotential R (GeneralLinearRing R n)
    (jordanCell * (generalLinearUnit R n).inv) (generalLinearUnit R n).val

theorem maurerCartanPotential_evaluation (D : Derivation R (GeneralLinearRing R n) (GeneralLinearRing R n)) :
    D.liftKaehlerDifferential (maurerCartanPotential R n) =
      maurerCartanTrace (generalLinearUnit R n) jordanCell D := by
  calc
    _ = Matrix.trace ((jordanCell * (generalLinearUnit R n).inv) *
        derivMatrix D (generalLinearUnit R n).val) := by
      simp only [maurerCartanPotential, kaehlerTracePotential, map_sum, map_smul,
        Derivation.liftKaehlerDifferential_comp_D, smul_eq_mul, Matrix.trace,
        Matrix.diag, Matrix.mul_apply, derivMatrix]
    _ = _ := congrArg Matrix.trace (mul_assoc _ _ _)

theorem maurerCartanPotential_derivative :
    deRhamOne R (GeneralLinearRing R n) (generalLinearDeRhamBasis R n) (maurerCartanPotential R n) =
      kaehlerCanonicalTrace (GeneralLinearRing R n) R
        (jordanCell * (generalLinearUnit R n).inv) (generalLinearUnit R n).val := by
  exact deRhamOne_tracePotential R _ (generalLinearDeRhamBasis R n) _ _

theorem orbitKaehlerPullback_eq_deRham : orbitKaehlerPullback R n =
    StructureSheaf.toOpenₗ (GeneralLinearRing R n) (KaehlerTwoForms (GeneralLinearRing R n) R) ⊤
      (-deRhamOne R (GeneralLinearRing R n) (generalLinearDeRhamBasis R n) (maurerCartanPotential R n)) := by
  rw [maurerCartanPotential_derivative]
  exact orbitKaehlerPullback_eq_exactForm R n

set_option maxHeartbeats 400000 in
theorem orbitKaehlerTwoForm_deRham_pullback (q : PrimeSpectrum (GeneralLinearRing R n)) :
    deRhamTwo R (PrimeLocalRing (GeneralLinearRing R n) q) (generalLinearPrimeDeRhamBasis R n q)
      (primeExteriorEquiv (GeneralLinearRing R n) R q ((orbitKaehlerPullback R n).val ⟨q, trivial⟩)) =
      kaehlerDegreeMap R _ _ (orbitPrimeMap R n q) 3
        (deRhamTwo R _ (orbitPrimeDifferentialBasis R n (orbitImagePrime R n q))
          (primeExteriorEquiv (CoordinateRing R n) R (orbitImagePrime R n q).val
            ((orbitKaehlerTwoForm R n).val (orbitImagePrime R n q)))) := by
  rw [orbitKaehlerPullback_germ, ← kaehlerDegreeMap_two]
  exact deRhamTwo_natural R
    (PrimeLocalRing (CoordinateRing R n) (orbitImagePrime R n q).val)
    (PrimeLocalRing (GeneralLinearRing R n) q)
    (orbitPrimeDifferentialBasis R n (orbitImagePrime R n q))
    (generalLinearPrimeDeRhamBasis R n q) (orbitPrimeMap R n q)
    (primeExteriorEquiv (CoordinateRing R n) R (orbitImagePrime R n q).val
      ((orbitKaehlerTwoForm R n).val (orbitImagePrime R n q)))

theorem orbitKaehlerPullback_deRham_closed (q : PrimeSpectrum (GeneralLinearRing R n)) :
    deRhamTwo R (PrimeLocalRing (GeneralLinearRing R n) q) (generalLinearPrimeDeRhamBasis R n q)
      (primeExteriorEquiv (GeneralLinearRing R n) R q ((orbitKaehlerPullback R n).val ⟨q, trivial⟩)) = 0 := by
  have h := congrArg (fun s => primeExteriorEquiv (GeneralLinearRing R n) R q (s.val ⟨q, trivial⟩))
    (orbitKaehlerPullback_eq_exactForm R n)
  refine (congrArg (deRhamTwo R (PrimeLocalRing (GeneralLinearRing R n) q)
    (generalLinearPrimeDeRhamBasis R n q)) h).trans ?_
  exact primeExactTrace_deRham_closed R (GeneralLinearRing R n) q
    (generalLinearPrimeDeRhamBasis R n q) _ _

/-- Closedness descends along conjugation by injectivity of pullback in exterior degree three. -/
theorem orbitKaehlerTwoForm_closed_by_descent (p : maximalRankOpen R n) :
    deRhamTwo R (PrimeLocalRing (CoordinateRing R n) p.val) (orbitPrimeDifferentialBasis R n p)
      (primeExteriorEquiv (CoordinateRing R n) R p.val ((orbitKaehlerTwoForm R n).val p)) = 0 := by
  let w := fun p : maximalRankOpen R n =>
    deRhamTwo R _ (orbitPrimeDifferentialBasis R n p)
      (primeExteriorEquiv (CoordinateRing R n) R p.val ((orbitKaehlerTwoForm R n).val p))
  have h : w = (fun _ => 0) := orbitFormsPullback_injective R n 3 (by
      funext q
      dsimp only [w]
      rw [map_zero, ← orbitKaehlerTwoForm_deRham_pullback, orbitKaehlerPullback_deRham_closed])
  exact congrFun h p

open CategoryTheory AlgebraicGeometry.StructureSheaf

/-- Coordinates of the actual cell inclusion into the square-zero scheme. -/
def cellOrbitCoordinates : CoordinateRing R n →ₐ[R] CellRing R n :=
  (cellChartEval R n).comp (toChartBase R n)

theorem cellMorphism_squareZero : cellMorphism R n ≫ (maximalRankOpen R n).ι =
    Spec.map (CommRingCat.ofHom (cellOrbitCoordinates R n).toRingHom) := by
  apply (CategoryTheory.cancel_mono (squareZeroClosedImmersion R n)).mp
  rw [CategoryTheory.Category.assoc, cellMorphism_ambient]
  change Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply MvPolynomial.ringHom_ext
  · intro r
    simp [cellCoordinateMap, iotaCoordinateMap, graphEval, cellOrbitCoordinates]
    exact ((cellOrbitCoordinates R n).commutes r).symm
  · intro ij
    change cellCoordinateMap (R := R) n (MvPolynomial.X ij) =
      cellOrbitCoordinates R n (universalMatrix R n ij.1 ij.2)
    rw [cellCoordinateMap_X]
    exact (congrFun (congrFun (cellChartEval_toChartBase_universal R n) ij.1) ij.2).symm

theorem cellOrbitCoordinates_topRight :
    ((universalMatrix R n).map (cellOrbitCoordinates R n)).toBlocks₁₂ = 1 := by
  rw [cellOrbitCoordinates, cellChartEval_toChartBase_universal]
  simp [iota]

theorem cellOrbitCoordinates_mem_chart (q : PrimeSpectrum (CellRing R n)) :
    PrimeSpectrum.comap (cellOrbitCoordinates R n).toRingHom q ∈
      permutationOpen R n (Equiv.refl _) := by
  change cellOrbitCoordinates R n (((universalMatrix R n).submatrix (Equiv.refl _)
    (Equiv.refl _)).toBlocks₁₂.det) ∉ q.asIdeal
  have h : cellOrbitCoordinates R n ((universalMatrix R n).toBlocks₁₂.det) = 1 := by
    rw [AlgHom.map_det]
    change (((universalMatrix R n).map (cellOrbitCoordinates R n)).toBlocks₁₂).det = 1
    rw [cellOrbitCoordinates_topRight, Matrix.det_one]
  change cellOrbitCoordinates R n ((universalMatrix R n).toBlocks₁₂.det) ∉ q.asIdeal
  rw [h]
  exact q.asIdeal.one_notMem

theorem cellOrbitCoordinates_mem_orbit (q : PrimeSpectrum (CellRing R n)) :
    PrimeSpectrum.comap (cellOrbitCoordinates R n).toRingHom q ∈ maximalRankOpen R n :=
  permutationOpen_le_maximalRank R n _ (cellOrbitCoordinates_mem_chart R n q)

set_option synthInstance.maxHeartbeats 100000 in
set_option maxHeartbeats 800000 in
/-- The constructed global two-form pulls back to zero along the actual cell inclusion. -/
theorem cell_global_form_pullback_zero :
    kaehlerSectionPullback R (CoordinateRing R n) (CellRing R n) (cellOrbitCoordinates R n)
      (maximalRankOpen R n) ⊤ (fun q _ => cellOrbitCoordinates_mem_orbit R n q)
      (orbitKaehlerTwoForm R n) = 0 := by
  apply Subtype.ext
  funext q
  apply (primeExteriorEquiv (CellRing R n) R q.val).injective
  change _ = primeExteriorEquiv (CellRing R n) R q.val 0
  rw [map_zero]
  change primeExteriorEquiv (CellRing R n) R q.val
    (Localizations.comapFun (kaehlerTwoMap R _ _ (cellOrbitCoordinates R n)) q.val _) = 0
  rw [primeExterior_comap]
  let p : maximalRankOpen R n := ⟨PrimeSpectrum.comap (cellOrbitCoordinates R n).toRingHom q.val,
    cellOrbitCoordinates_mem_orbit R n q.val⟩
  let g := Localization.localAlgHom p.val.asIdeal q.val.asIdeal (cellOrbitCoordinates R n) rfl
  change kaehlerTwoMap R _ _ g (primeExteriorEquiv (CoordinateRing R n) R p.val
    ((orbitKaehlerTwoForm R n).val p)) = 0
  rw [orbitKaehlerTwoForm_chart R n p (Equiv.refl _) (cellOrbitCoordinates_mem_chart R n q.val),
    kaehlerTwoMap_canonicalTrace]
  have hT : ((chartT R n).map (primeChartEvaluation R n p.val (Equiv.refl _)
      (cellOrbitCoordinates_mem_chart R n q.val))).map g = 1 := by
    rw [primeChartEvaluation_T]
    have hm := congrArg (fun M => M.map (algebraMap (CellRing R n) (PrimeLocalRing (CellRing R n) q.val)))
      (cellOrbitCoordinates_topRight R n)
    ext i j
    change g (algebraMap (CoordinateRing R n) (PrimeLocalRing (CoordinateRing R n) p.val)
      (universalMatrix R n (Sum.inl i) (Sum.inr j))) = _
    change Localization.localRingHom p.val.asIdeal q.val.asIdeal
      (cellOrbitCoordinates R n).toRingHom rfl
        (algebraMap (CoordinateRing R n) (PrimeLocalRing (CoordinateRing R n) p.val)
          (universalMatrix R n (Sum.inl i) (Sum.inr j))) = _
    rw [Localization.localRingHom_to_map]
    simpa [Matrix.toBlocks₁₂, Matrix.map_apply, Matrix.one_apply] using congrFun (congrFun hm i) j
  rw [hT]
  exact kaehlerCanonicalTrace_one _ _ _

end
end Universality.GlobalSymplectic
