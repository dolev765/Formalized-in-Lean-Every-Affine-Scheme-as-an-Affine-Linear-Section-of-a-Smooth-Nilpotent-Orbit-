import Mathlib.Data.Matrix.Block
import Mathlib.Algebra.Group.Conj
import Mathlib.Data.Matrix.DualNumber
import Mathlib.Algebra.CharP.Two
import Mathlib.Tactic.NoncommRing
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.LinearAlgebra.Trace
import Mathlib.Logic.Equiv.Fintype
import Mathlib.RingTheory.Smooth.StandardSmooth

namespace Universality

variable {R n : Type*} [CommRing R] [Fintype n] [DecidableEq n]

/-- The affine matrix chart used to encode the squaring map. -/
def iota (A B : Matrix n n R) : Matrix (n ⊕ n) (n ⊕ n) R :=
  Matrix.fromBlocks A 1 (-B) (-A)

/-- The standard square-zero matrix with an identity upper-right block. -/
def jordanCell : Matrix (n ⊕ n) (n ⊕ n) R :=
  Matrix.fromBlocks 0 1 0 0

def chartUnit (A : Matrix n n R) : Matrix (n ⊕ n) (n ⊕ n) R :=
  Matrix.fromBlocks 1 0 (-A) 1

def chartUnitInv (A : Matrix n n R) : Matrix (n ⊕ n) (n ⊕ n) R :=
  Matrix.fromBlocks 1 0 A 1

theorem chartUnit_mul_inv (A : Matrix n n R) : chartUnit A * chartUnitInv A = 1 := by
  simp [chartUnit, chartUnitInv, Matrix.fromBlocks_multiply]

theorem chartUnit_inv_mul (A : Matrix n n R) : chartUnitInv A * chartUnit A = 1 := by
  simp [chartUnit, chartUnitInv, Matrix.fromBlocks_multiply]

theorem jordanCell_square : (jordanCell : Matrix (n ⊕ n) (n ⊕ n) R) * jordanCell = 0 := by
  simp [jordanCell, Matrix.fromBlocks_multiply]

theorem iota_square_iff (A B : Matrix n n R) : iota A B * iota A B = 0 ↔ B = A * A := by
  constructor
  · intro h
    have h' := congrArg Matrix.toBlocks₁₁ h
    have h'' : A * A - B = 0 := by
      simpa [iota, Matrix.fromBlocks_multiply, sub_eq_add_neg, Matrix.toBlocks₁₁] using h'
    exact (sub_eq_zero.mp h'').symm
  · rintro rfl
    simp [iota, Matrix.fromBlocks_multiply, mul_assoc]

theorem chart_conjugation (A : Matrix n n R) :
    chartUnit A * jordanCell * chartUnitInv A = iota A (A * A) := by
  simp [chartUnit, jordanCell, chartUnitInv, iota, Matrix.fromBlocks_multiply]

/-- Conjugacy expressed using a matrix and its two-sided inverse.
`inJordanOrbit_iff_isConj` identifies this explicit-witness interface with Mathlib's
standard conjugacy relation. -/
def InJordanOrbit (X : Matrix (n ⊕ n) (n ⊕ n) R) : Prop :=
  ∃ P Q : Matrix (n ⊕ n) (n ⊕ n) R, P * Q = 1 ∧ Q * P = 1 ∧
    X = P * jordanCell * Q

/-- The explicit matrix witnesses are precisely the units in Mathlib's `IsConj`. -/
theorem inJordanOrbit_iff_isConj (X : Matrix (n ⊕ n) (n ⊕ n) R) :
    InJordanOrbit X ↔ IsConj jordanCell X := by
  constructor
  · rintro ⟨P, Q, hPQ, hQP, rfl⟩
    refine ⟨⟨P, Q, hPQ, hQP⟩, ?_⟩
    change P * jordanCell = (P * jordanCell * Q) * P
    simp [mul_assoc, hQP]
  · rintro ⟨u, hu⟩
    refine ⟨u.val, u.inv, u.val_inv, u.inv_val, ?_⟩
    have h := congrArg (fun M => M * u.inv) hu.eq
    simpa [mul_assoc] using h.symm

theorem orbit_square_zero {X : Matrix (n ⊕ n) (n ⊕ n) R}
    (h : InJordanOrbit X) : X * X = 0 := by
  obtain ⟨u, hu⟩ := IsConj.pow 2 ((inJordanOrbit_iff_isConj X).mp h)
  have hz : X * X * u.val = 0 := by
    simpa [pow_two, jordanCell_square] using hu.eq.symm
  have hc := congrArg (fun M => M * u.inv) hz
  simpa [mul_assoc] using hc

/-- Over every commutative coefficient ring, the chart-orbit intersection is
    exactly the graph of matrix squaring. -/
theorem chart_orbit_iff (A B : Matrix n n R) : InJordanOrbit (iota A B) ↔ B = A * A := by
  constructor
  · intro h
    exact (iota_square_iff A B).mp (orbit_square_zero h)
  · rintro rfl
    exact ⟨chartUnit A, chartUnitInv A, chartUnit_mul_inv A,
      chartUnit_inv_mul A, (chart_conjugation A).symm⟩

/-- The kernel in the squaring chart is explicitly the graph of minus `A`. -/
theorem iota_kernel_iff (A : Matrix n n R) (x y : n → R) :
    (iota A (A * A)).mulVec (Sum.elim x y) = 0 ↔ y = -(A.mulVec x) := by
  constructor
  · intro h
    have h' := congrArg (fun v => v ∘ Sum.inl) h
    have h'' : A.mulVec x + y = 0 := by
      simpa [iota, Matrix.fromBlocks_mulVec, Function.comp_def] using h'
    exact eq_neg_of_add_eq_zero_right h''
  · rintro rfl
    rw [iota, Matrix.fromBlocks_mulVec]
    change Sum.elim (A.mulVec x + (1 : Matrix n n R).mulVec (-A.mulVec x))
      ((-(A * A)).mulVec x + (-A).mulVec (-A.mulVec x)) = 0
    simp [Matrix.neg_mulVec, Matrix.mulVec_neg, Matrix.mulVec_mulVec]

/-- Every kernel vector is already an image vector, with an explicit preimage. -/
theorem iota_image_eq_kernel (A : Matrix n n R) (v : n ⊕ n → R) :
    (∃ w, (iota A (A * A)).mulVec w = v) ↔
      (iota A (A * A)).mulVec v = 0 := by
  constructor
  · rintro ⟨w, rfl⟩
    rw [Matrix.mulVec_mulVec, (iota_square_iff A (A * A)).mpr rfl]
    simp
  · intro h
    have hv : Sum.elim (v ∘ Sum.inl) (v ∘ Sum.inr) = v := by
      ext (i | i) <;> rfl
    have hy := (iota_kernel_iff A (v ∘ Sum.inl) (v ∘ Sum.inr)).mp (by simpa [hv] using h)
    refine ⟨Sum.elim 0 (v ∘ Sum.inl), ?_⟩
    rw [← hv, hy]
    ext (i | i) <;> simp [iota, Function.comp_def,
      Matrix.mulVec, dotProduct, Matrix.one_apply]

/-- The full centralizer consists of equal diagonal blocks and zero lower-left block. -/
theorem jordanCell_commute_iff (P Q S T : Matrix n n R) :
    Matrix.fromBlocks P Q S T * jordanCell =
      jordanCell * Matrix.fromBlocks P Q S T ↔ S = 0 ∧ T = P := by
  simp only [jordanCell, Matrix.fromBlocks_multiply, mul_zero, zero_mul, mul_one,
    one_mul, add_zero, zero_add, Matrix.fromBlocks_inj]
  constructor
  · rintro ⟨hS, hPT, _, _⟩
    exact ⟨hS.symm, hPT.symm⟩
  · rintro ⟨rfl, rfl⟩
    simp

/-- A linear parametrization of the commutator image at the standard cell. -/
def cellTangentParam : (Matrix n n R × Matrix n n R) →ₗ[R]
    Matrix (n ⊕ n) (n ⊕ n) R where
  toFun p := Matrix.fromBlocks (-p.1) p.2 0 p.1
  map_add' p q := by simp [Matrix.fromBlocks_add, add_comm]
  map_smul' a p := by simp [Matrix.fromBlocks_smul]

omit [Fintype n] [DecidableEq n] in
theorem cellTangentParam_injective : Function.Injective
    (cellTangentParam : (Matrix n n R × Matrix n n R) →ₗ[R] _) := by
  intro p q h
  have h' : -p.1 = -q.1 ∧ p.2 = q.2 ∧ (0 : Matrix n n R) = 0 ∧ p.1 = q.1 :=
    Matrix.fromBlocks_inj.mp h
  exact Prod.ext h'.2.2.2 h'.2.1

theorem cell_commutator (P Q S T : Matrix n n R) :
    Matrix.fromBlocks P Q S T * jordanCell -
      jordanCell * Matrix.fromBlocks P Q S T = cellTangentParam (S, P - T) := by
  ext (i | i) (j | j) <;>
    simp [jordanCell, Matrix.fromBlocks_multiply, cellTangentParam]

theorem cell_commutator_range (X : Matrix (n ⊕ n) (n ⊕ n) R) :
    (∃ Y, Y * jordanCell - jordanCell * Y = X) ↔
      X ∈ LinearMap.range (cellTangentParam : (Matrix n n R × Matrix n n R) →ₗ[R] _) := by
  constructor
  · rintro ⟨Y, rfl⟩
    refine ⟨(Y.toBlocks₂₁, Y.toBlocks₁₁ - Y.toBlocks₂₂), ?_⟩
    conv_rhs => rw [← Matrix.fromBlocks_toBlocks Y]
    exact (cell_commutator _ _ _ _).symm
  · rintro ⟨⟨S, D⟩, rfl⟩
    exact ⟨Matrix.fromBlocks D 0 S 0, by simpa using cell_commutator D 0 S 0⟩

omit [DecidableEq n] in
theorem cellTangent_finrank {k : Type*} [Field k] :
    Module.finrank k (LinearMap.range
      (cellTangentParam : (Matrix n n k × Matrix n n k) →ₗ[k] _)) =
      2 * Fintype.card n ^ 2 := by
  rw [LinearMap.finrank_range_of_inj cellTangentParam_injective]
  simp [Module.finrank_prod, Module.finrank_matrix, pow_two, two_mul]

/-- Lower-unipotent directions in the orbit chart. -/
def cellLowerParam : Matrix n n R →ₗ[R] Matrix (n ⊕ n) (n ⊕ n) R where
  toFun A := Matrix.fromBlocks A 0 0 (-A)
  map_add' A B := by simp [Matrix.fromBlocks_add, add_comm]
  map_smul' a A := by simp [Matrix.fromBlocks_smul]

omit [Fintype n] [DecidableEq n] in
theorem cellLowerParam_injective : Function.Injective
    (cellLowerParam : Matrix n n R →ₗ[R] _) := by
  intro A B h
  exact (Matrix.fromBlocks_inj.mp h).1

omit [DecidableEq n] in
theorem cellLower_finrank {k : Type*} [Field k] :
    Module.finrank k (LinearMap.range (cellLowerParam : Matrix n n k →ₗ[k] _)) =
      Fintype.card n ^ 2 := by
  rw [LinearMap.finrank_range_of_inj cellLowerParam_injective]
  simp [Module.finrank_matrix, pow_two]

/-- An exact square-zero endomorphism is a direct sum of two-step Jordan cells.
    The construction chooses a linear section onto its image. -/
theorem squareZero_decomposition {k V : Type*} [Field k]
    [AddCommGroup V] [Module k V] (f : V →ₗ[k] V)
    (h : LinearMap.ker f = LinearMap.range f) :
    ∃ e : (LinearMap.range f × LinearMap.range f) ≃ₗ[k] V,
      ∀ x y, f (e (x, y)) = e (y, 0) := by
  classical
  obtain ⟨g, hg⟩ := f.rangeRestrict.exists_rightInverse_of_surjective f.range_rangeRestrict
  have hfg (x : LinearMap.range f) : f (g x) = x :=
    congrArg Subtype.val (LinearMap.congr_fun hg x)
  have hfzero (x : LinearMap.range f) : f x = 0 := by
    exact show x.val ∈ LinearMap.ker f from h.ge x.property
  let L : (LinearMap.range f × LinearMap.range f) →ₗ[k] V :=
    (LinearMap.range f).subtype.coprod g
  have hL (x y : LinearMap.range f) : L (x, y) = x + g y := rfl
  have hLf (x y : LinearMap.range f) : f (L (x, y)) = y := by
    rw [hL, map_add, hfzero, hfg, zero_add]
  have hLi : Function.Injective L := by
    rintro ⟨x, y⟩ ⟨x', y'⟩ heq
    have hy : y = y' := Subtype.ext (by simpa only [hLf] using congrArg f heq)
    subst y'
    have hx : x = x' := Subtype.ext (add_right_cancel (by simpa only [hL] using heq))
    exact Prod.ext hx rfl
  have hLs : Function.Surjective L := by
    intro v
    let y := f.rangeRestrict v
    have hx : v - g y ∈ LinearMap.range f := by
      apply h.le
      change f (v - g y) = 0
      rw [map_sub, hfg]
      exact sub_self _
    exact ⟨(⟨v - g y, hx⟩, y), by simp only [hL, sub_add_cancel]⟩
  refine ⟨LinearEquiv.ofBijective L ⟨hLi, hLs⟩, ?_⟩
  intro x y
  change f (L (x, y)) = L (y, 0)
  rw [hLf, hL, map_zero, add_zero]

theorem squareZero_maximal_rank_exact {k V : Type*} [Field k]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V] (f : V →ₗ[k] V)
    (hsq : f.comp f = 0)
    (hdim : Module.finrank k V = 2 * Module.finrank k (LinearMap.range f)) :
    LinearMap.ker f = LinearMap.range f := by
  have hle : LinearMap.range f ≤ LinearMap.ker f := by
    rintro _ ⟨v, rfl⟩
    exact LinearMap.congr_fun hsq v
  have hdim' := f.finrank_range_add_finrank_ker
  have heq : Module.finrank k (LinearMap.range f) = Module.finrank k (LinearMap.ker f) := by
    omega
  exact (Submodule.eq_of_le_of_finrank_eq hle heq).symm

theorem jordanCell_mulVec (v : n ⊕ n → R) :
    (jordanCell : Matrix (n ⊕ n) (n ⊕ n) R).mulVec v =
      Sum.elim (v ∘ Sum.inr) 0 := by
  rw [jordanCell, Matrix.fromBlocks_mulVec]
  simp

/-- Every square-zero matrix of maximal possible image dimension lies in the
    standard Jordan orbit; the proof constructs a basis from a linear section. -/
theorem squareZero_inJordanOrbit {k : Type*} [Field k]
    (X : Matrix (n ⊕ n) (n ⊕ n) k) (hsq : X * X = 0)
    (hr : Module.finrank k (LinearMap.range (Matrix.toLin' X)) = Fintype.card n) :
    InJordanOrbit X := by
  classical
  let f := Matrix.toLin' X
  have hf : f.comp f = 0 := by
    dsimp [f]
    rw [← Matrix.toLin'_mul, hsq, map_zero]
  have hdim : Module.finrank k (n ⊕ n → k) =
      2 * Module.finrank k (LinearMap.range f) := by
    simp [f, hr, Fintype.card_sum, two_mul]
  obtain ⟨e, he⟩ := squareZero_decomposition f (squareZero_maximal_rank_exact f hf hdim)
  let c : (n → k) ≃ₗ[k] LinearMap.range f :=
    LinearEquiv.ofFinrankEq (n → k) (LinearMap.range f)
      (by simp [f, hr])
  let E : (n ⊕ n → k) ≃ₗ[k] (n ⊕ n → k) :=
    ((LinearEquiv.sumArrowLequivProdArrow n n k k).trans
      (c.prodCongr c)).trans e
  have hE (v : n ⊕ n → k) : f (E v) = E (jordanCell.mulVec v) := by
    rw [jordanCell_mulVec]
    change f (e (c (v ∘ Sum.inl), c (v ∘ Sum.inr))) =
      e (c (v ∘ Sum.inr), c 0)
    rw [he, map_zero]
  let P := LinearMap.toMatrix' E.toLinearMap
  let Q := LinearMap.toMatrix' E.symm.toLinearMap
  refine ⟨P, Q, ?_, ?_, ?_⟩
  · apply Matrix.toLin'.injective
    apply LinearMap.ext
    intro v
    simp [P, Q, Matrix.toLin'_mul]
  · apply Matrix.toLin'.injective
    apply LinearMap.ext
    intro v
    simp [P, Q, Matrix.toLin'_mul]
  · apply Matrix.toLin'.injective
    apply LinearMap.ext
    intro v
    simpa [P, Q, Matrix.toLin'_mul, f] using hE (E.symm v)

theorem jordanCell_rank {k : Type*} [Field k] :
    (jordanCell : Matrix (n ⊕ n) (n ⊕ n) k).rank = Fintype.card n := by
  let f := Matrix.toLin' (jordanCell : Matrix (n ⊕ n) (n ⊕ n) k)
  have hkr : LinearMap.ker f = LinearMap.range f := by
    ext v
    simpa [f, Matrix.toLin'_apply, iota, jordanCell] using
      (iota_image_eq_kernel (0 : Matrix n n k) v).symm
  have hd := f.finrank_range_add_finrank_ker
  rw [hkr] at hd
  have hdim : Module.finrank k (n ⊕ n → k) = Fintype.card n + Fintype.card n := by
    simp [Fintype.card_sum]
  rw [hdim] at hd
  change (jordanCell : Matrix (n ⊕ n) (n ⊕ n) k).rank + jordanCell.rank =
    Fintype.card n + Fintype.card n at hd
  omega

/-- The standard orbit over a field is exactly the maximal-rank square-zero locus. -/
theorem inJordanOrbit_iff_square_zero_rank {k : Type*} [Field k]
    (X : Matrix (n ⊕ n) (n ⊕ n) k) :
    InJordanOrbit X ↔ X * X = 0 ∧ X.rank = Fintype.card n := by
  constructor
  · intro h
    refine ⟨orbit_square_zero h, ?_⟩
    obtain ⟨P, Q, hPQ, hQP, hX⟩ := h
    have hJ : jordanCell = Q * X * P := by
      rw [hX]
      simp only [← mul_assoc, hQP, one_mul]
      rw [mul_assoc, hQP, mul_one]
    have hle : X.rank ≤ (jordanCell : Matrix (n ⊕ n) (n ⊕ n) k).rank := by
      rw [hX]
      exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)
    have hge : (jordanCell : Matrix (n ⊕ n) (n ⊕ n) k).rank ≤ X.rank := by
      rw [hJ]
      exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)
    exact (le_antisymm hle hge).trans jordanCell_rank
  · rintro ⟨hsq, hr⟩
    exact squareZero_inJordanOrbit X hsq hr

theorem iota_rank {k : Type*} [Field k] (A : Matrix n n k) :
    (iota A (A * A)).rank = Fintype.card n :=
  ((inJordanOrbit_iff_square_zero_rank _).mp ((chart_orbit_iff A _).mpr rfl)).2

theorem centralizer_block_isUnit_iff (P Q : Matrix n n R) :
    IsUnit (Matrix.fromBlocks P Q 0 P) ↔ IsUnit P := by
  simp [Matrix.isUnit_iff_isUnit_det, Matrix.det_fromBlocks_zero₂₁]

/-- The stabilizer inside the general linear group has arbitrary upper-right
    block and an invertible repeated diagonal block. -/
theorem jordanCell_unit_centralizer_iff (G : Matrix (n ⊕ n) (n ⊕ n) R) :
    IsUnit G ∧ G * jordanCell = jordanCell * G ↔
      ∃ P Q : Matrix n n R, IsUnit P ∧ G = Matrix.fromBlocks P Q 0 P := by
  constructor
  · rintro ⟨hG, hc⟩
    have hb : G.toBlocks₂₁ = 0 ∧ G.toBlocks₂₂ = G.toBlocks₁₁ := by
      apply (jordanCell_commute_iff G.toBlocks₁₁ G.toBlocks₁₂ G.toBlocks₂₁ G.toBlocks₂₂).mp
      simpa only [Matrix.fromBlocks_toBlocks] using hc
    have heq : G = Matrix.fromBlocks G.toBlocks₁₁ G.toBlocks₁₂ 0 G.toBlocks₁₁ := by
      conv_lhs => rw [← Matrix.fromBlocks_toBlocks G]
      rw [hb.1, hb.2]
    refine ⟨G.toBlocks₁₁, G.toBlocks₁₂, ?_, heq⟩
    apply (centralizer_block_isUnit_iff _ _).mp
    rwa [← heq]
  · rintro ⟨P, Q, hP, rfl⟩
    exact ⟨(centralizer_block_isUnit_iff P Q).mpr hP,
      (jordanCell_commute_iff P Q 0 P).mpr ⟨rfl, rfl⟩⟩

/-- Coordinates on the open locus with invertible upper-right block. -/
def generalChart (A T : Matrix n n R) : Matrix (n ⊕ n) (n ⊕ n) R :=
  Matrix.fromBlocks (T * A) T (-(A * T * A)) (-(A * T))

omit [DecidableEq n] in
theorem generalChart_square (A T : Matrix n n R) :
    generalChart A T * generalChart A T = 0 := by
  simp [generalChart, Matrix.fromBlocks_multiply, mul_assoc]

def generalChartBasis (A : Matrix n n R) (T : (Matrix n n R)ˣ) :
    Matrix (n ⊕ n) (n ⊕ n) R :=
  Matrix.fromBlocks (T.val) 0 (-(A * T.val)) 1

def generalChartBasisInv (A : Matrix n n R) (T : (Matrix n n R)ˣ) :
    Matrix (n ⊕ n) (n ⊕ n) R :=
  Matrix.fromBlocks (T.inv) 0 A 1

theorem generalChartBasis_mul_inv (A : Matrix n n R) (T : (Matrix n n R)ˣ) :
    generalChartBasis A T * generalChartBasisInv A T = 1 := by
  simp [generalChartBasis, generalChartBasisInv, Matrix.fromBlocks_multiply, mul_assoc]

theorem generalChartBasis_inv_mul (A : Matrix n n R) (T : (Matrix n n R)ˣ) :
    generalChartBasisInv A T * generalChartBasis A T = 1 := by
  simp [generalChartBasis, generalChartBasisInv, Matrix.fromBlocks_multiply]

theorem generalChart_conjugation (A : Matrix n n R) (T : (Matrix n n R)ˣ) :
    generalChartBasis A T * jordanCell * generalChartBasisInv A T = generalChart A T.val := by
  simp [generalChartBasis, generalChartBasisInv, jordanCell, generalChart,
    Matrix.fromBlocks_multiply]

theorem generalChart_inOrbit (A : Matrix n n R) (T : (Matrix n n R)ˣ) :
    InJordanOrbit (generalChart A T.val) :=
  ⟨generalChartBasis A T, generalChartBasisInv A T, generalChartBasis_mul_inv A T,
    generalChartBasis_inv_mul A T, (generalChart_conjugation A T).symm⟩

/-- Squaring equations determine the remaining blocks uniquely when the
    upper-right block is invertible. -/
theorem square_zero_unit_block_iff (P Q S : Matrix n n R) (T : (Matrix n n R)ˣ) :
    Matrix.fromBlocks P (T.val) Q S * Matrix.fromBlocks P (T.val) Q S = 0 ↔
      Matrix.fromBlocks P (T.val) Q S = generalChart ((T.inv) * P) (T.val) := by
  constructor
  · intro h
    have h₁ := congrArg Matrix.toBlocks₁₁ h
    have h₂ := congrArg Matrix.toBlocks₁₂ h
    have h₁' : P * P + (T.val) * Q = 0 := by
      simpa [Matrix.fromBlocks_multiply, Matrix.toBlocks₁₁] using h₁
    have h₂' : P * (T.val) + (T.val) * S = 0 := by
      simpa [Matrix.fromBlocks_multiply, Matrix.toBlocks₁₂] using h₂
    have hQ : Q = -((T.inv) * P * P) := by
      apply eq_neg_of_add_eq_zero_right
      have hh := congrArg (fun M : Matrix n n R => (T.inv) * M) h₁'
      simpa [mul_add, ← mul_assoc] using hh
    have hS : S = -((T.inv) * P * (T.val)) := by
      apply eq_neg_of_add_eq_zero_right
      have hh := congrArg (fun M : Matrix n n R => (T.inv) * M) h₂'
      simpa [mul_add, ← mul_assoc] using hh
    have hP : P = (T.val) * ((T.inv) * P) := by simp
    rw [generalChart, Matrix.fromBlocks_inj]
    refine ⟨hP, rfl, ?_, hS⟩
    rw [hQ]
    congr 1
    rw [mul_assoc ((T.inv) * P) (T.val), ← hP]
  · intro h
    rw [h]
    exact generalChart_square _ _

theorem generalChart_coordinate_unique (A B : Matrix n n R) (T : (Matrix n n R)ˣ)
    (h : generalChart A (T.val) = generalChart B (T.val)) : A = B := by
  have hh := congrArg Matrix.toBlocks₁₁ h
  have hh' : (T.val) * A = (T.val) * B := by simpa [generalChart] using hh
  have hhh := congrArg (fun M : Matrix n n R => (T.inv) * M) hh'
  simpa [← mul_assoc] using hhh

theorem square_zero_invertible_block_normalForm (P Q S T : Matrix n n R)
    (hdet : IsUnit T.det)
    (hsq : Matrix.fromBlocks P T Q S * Matrix.fromBlocks P T Q S = 0) :
    generalChart (T⁻¹ * P) T = Matrix.fromBlocks P T Q S :=
  ((square_zero_unit_block_iff P Q S (Matrix.nonsingInvUnit T hdet)).mp hsq).symm

theorem generalChart_inOrbit_of_isUnit_det (A T : Matrix n n R) (hdet : IsUnit T.det) :
    InJordanOrbit (generalChart A T) :=
  generalChart_inOrbit A (Matrix.nonsingInvUnit T hdet)

theorem square_zero_of_unit_block_inOrbit (P Q S T : Matrix n n R)
    (hdet : IsUnit T.det)
    (hsq : Matrix.fromBlocks P T Q S * Matrix.fromBlocks P T Q S = 0) :
    InJordanOrbit (Matrix.fromBlocks P T Q S) := by
  rw [← square_zero_invertible_block_normalForm P Q S T hdet hsq]
  exact generalChart_inOrbit_of_isUnit_det _ T hdet

/-- Independent columns of a square-zero matrix force the complementary
    upper-right minor to be invertible. -/
theorem square_zero_independent_right_block_isUnit {k : Type*} [Field k]
    (P T Q S : Matrix n n k)
    (hsq : Matrix.fromBlocks P T Q S * Matrix.fromBlocks P T Q S = 0)
    (hi : Function.Injective (fun v : n → k =>
      (Matrix.fromBlocks P T Q S).mulVec (Sum.elim 0 v))) : IsUnit T := by
  have hkill (v : n → k) (hv : T.mulVec v = 0) : v = 0 := by
    have hz : (Matrix.fromBlocks P T Q S).mulVec (Sum.elim 0 v) =
        Sum.elim (0 : n → k) (S.mulVec v) := by
      rw [Matrix.fromBlocks_mulVec]
      change Sum.elim (P.mulVec 0 + T.mulVec v) (Q.mulVec 0 + S.mulVec v) = _
      simp [Matrix.mulVec_zero, hv]
    have hS : S.mulVec v = 0 := by
      apply hi
      dsimp only
      rw [← hz, Matrix.mulVec_mulVec, hsq]
      simp [Matrix.mulVec_zero]
    apply hi
    dsimp only
    rw [hz, hS]
    simp [Matrix.mulVec_zero]
  apply Matrix.mulVec_injective_iff_isUnit.mp
  intro v w h
  apply sub_eq_zero.mp
  apply hkill
  rw [Matrix.mulVec_sub, h, sub_self]

/-- A rank-`n` matrix admits a coordinate permutation whose last `n` columns
    are linearly independent. -/
theorem exists_independent_right_columns {k : Type*} [Field k]
    (X : Matrix (n ⊕ n) (n ⊕ n) k) (hr : X.rank = Fintype.card n) :
    ∃ e : Equiv.Perm (n ⊕ n),
      LinearIndependent k (fun j : n => X.col (e (Sum.inr j))) := by
  classical
  obtain ⟨y, hy, _, hli⟩ := Submodule.exists_fun_fin_finrank_span_eq k (Set.range X.col)
  have hd : Module.finrank k (Submodule.span k (Set.range X.col)) = Fintype.card n :=
    (X.rank_eq_finrank_span_cols).symm.trans hr
  let en : n ≃ Fin (Module.finrank k (Submodule.span k (Set.range X.col))) :=
    (Fintype.equivFin n).trans (finCongr hd.symm)
  choose c hc using fun j : n => hy (en j)
  have hci : LinearIndependent k (fun j => X.col (c j)) := by
    have heq : (fun j => X.col (c j)) = y ∘ en := funext hc
    rw [heq]
    exact hli.comp en en.injective
  have hc_inj : Function.Injective c := by
    intro i j h
    exact hci.injective (congrArg X.col h)
  let a : n ↪ n ⊕ n := ⟨Sum.inr, Sum.inr_injective⟩
  let b : n ↪ n ⊕ n := ⟨c, hc_inj⟩
  let er : Set.range a ≃ Set.range b := a.toEquivRange.symm.trans b.toEquivRange
  let e := er.extendSubtype
  have he (j : n) : e (Sum.inr j) = c j := by
    rw [show e (Sum.inr j) = er ⟨Sum.inr j, ⟨j, rfl⟩⟩ from
      Equiv.extendSubtype_apply_of_mem er _ ⟨j, rfl⟩]
    change ↑(b.toEquivRange (a.toEquivRange.symm (a.toEquivRange j))) = c j
    simp only [Equiv.symm_apply_apply]
    rfl
  refine ⟨e, ?_⟩
  simpa only [he] using hci

/-- Coordinate permutations of the invertible-upper-right chart cover the
    maximal-rank square-zero locus over every field. -/
theorem square_zero_exists_invertible_coordinate_chart {k : Type*} [Field k]
    (X : Matrix (n ⊕ n) (n ⊕ n) k) (hsq : X * X = 0)
    (hr : X.rank = Fintype.card n) :
    ∃ e : Equiv.Perm (n ⊕ n), IsUnit (X.submatrix e e).toBlocks₁₂.det := by
  classical
  obtain ⟨e, he⟩ := exists_independent_right_columns X hr
  let Y := X.submatrix e e
  have hy : Y * Y = 0 := by
    dsimp [Y]
    rw [Matrix.submatrix_mul_equiv, hsq]
    rfl
  let L := LinearEquiv.funCongrLeft k k e
  have hl : LinearIndependent k (Y.submatrix id Sum.inr).col := by
    have hli := he.map' L.toLinearMap (LinearMap.ker_eq_bot.mpr L.injective)
    exact hli
  have hir : Function.Injective (fun v : n → k => Y.mulVec (Sum.elim 0 v)) := by
    have heq (v : n → k) : Y.mulVec (Sum.elim 0 v) =
        (Y.submatrix id Sum.inr).mulVec v := by
      ext i
      simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type]
    intro v w h
    exact Matrix.mulVec_injective_iff.mpr hl (by simpa only [heq] using h)
  refine ⟨e, (Matrix.isUnit_iff_isUnit_det _).mp ?_⟩
  apply square_zero_independent_right_block_isUnit Y.toBlocks₁₁ Y.toBlocks₁₂ Y.toBlocks₂₁ Y.toBlocks₂₂
  · simpa only [Matrix.fromBlocks_toBlocks] using hy
  · simpa only [Matrix.fromBlocks_toBlocks] using hir

omit [DecidableEq n] in
theorem square_zero_rank_le {k : Type*} [Field k]
    (X : Matrix (n ⊕ n) (n ⊕ n) k) (hsq : X * X = 0) :
    X.rank ≤ Fintype.card n := by
  let f := X.mulVecLin
  have hle : LinearMap.range f ≤ LinearMap.ker f := by
    rintro _ ⟨v, rfl⟩
    change X.mulVec (X.mulVec v) = 0
    rw [Matrix.mulVec_mulVec, hsq]
    simp
  have hdim := f.finrank_range_add_finrank_ker
  have hdimV : Module.finrank k (n ⊕ n → k) = Fintype.card n + Fintype.card n := by
    simp [Fintype.card_sum]
  rw [hdimV] at hdim
  have hrk := Submodule.finrank_mono hle
  change X.rank + Module.finrank k (LinearMap.ker f) = _ at hdim
  change X.rank ≤ Module.finrank k (LinearMap.ker f) at hrk
  omega

theorem square_zero_rank_eq_of_invertible_minor {k : Type*} [Field k]
    (X : Matrix (n ⊕ n) (n ⊕ n) k) (hsq : X * X = 0)
    (r c : n → n ⊕ n) (hdet : IsUnit (X.submatrix r c).det) :
    X.rank = Fintype.card n := by
  apply le_antisymm (square_zero_rank_le X hsq)
  have hm := Matrix.rank_of_isUnit (X.submatrix r c)
    ((Matrix.isUnit_iff_isUnit_det _).mpr hdet)
  rw [← hm]
  exact Matrix.rank_submatrix_le X r c

theorem square_zero_invertible_minor_has_coordinate_chart {k : Type*} [Field k]
    (X : Matrix (n ⊕ n) (n ⊕ n) k) (hsq : X * X = 0)
    (r c : n → n ⊕ n) (hdet : IsUnit (X.submatrix r c).det) :
    ∃ e : Equiv.Perm (n ⊕ n), IsUnit (X.submatrix e e).toBlocks₁₂.det :=
  square_zero_exists_invertible_coordinate_chart X hsq
    (square_zero_rank_eq_of_invertible_minor X hsq r c hdet)

/-- The derivative of the squaring equations at the standard cell is precisely
    the commutator image, over every commutative coefficient ring. -/
theorem jordanCell_linearized_iff (D : Matrix (n ⊕ n) (n ⊕ n) R) :
    jordanCell * D + D * jordanCell = 0 ↔
      ∃ X, X * jordanCell - jordanCell * X = D := by
  constructor
  · intro h
    rw [← Matrix.fromBlocks_toBlocks D] at h
    have h₁ := congrArg Matrix.toBlocks₁₁ h
    have h₂ := congrArg Matrix.toBlocks₁₂ h
    have hS : D.toBlocks₂₁ = 0 := by
      simpa [jordanCell, Matrix.fromBlocks_multiply,
        ← Matrix.fromBlocks_add, Matrix.toBlocks₁₁] using h₁
    have hT : D.toBlocks₂₂ = -D.toBlocks₁₁ := by
      have hh : D.toBlocks₂₂ + D.toBlocks₁₁ = 0 := by
        simpa [jordanCell, Matrix.fromBlocks_multiply,
          ← Matrix.fromBlocks_add, Matrix.toBlocks₁₂] using h₂
      exact eq_neg_of_add_eq_zero_left hh
    refine ⟨Matrix.fromBlocks D.toBlocks₁₂ 0 (-D.toBlocks₁₁) 0, ?_⟩
    rw [cell_commutator]
    simp only [cellTangentParam, LinearMap.coe_mk, AddHom.coe_mk, sub_zero, neg_neg]
    conv_rhs => rw [← Matrix.fromBlocks_toBlocks D]
    rw [hS, hT]
  · rintro ⟨X, rfl⟩
    calc
      jordanCell * (X * jordanCell - jordanCell * X) +
          (X * jordanCell - jordanCell * X) * jordanCell =
        X * (jordanCell * jordanCell) - (jordanCell * jordanCell) * X := by noncomm_ring
      _ = 0 := by simp [jordanCell_square]

/-- The kernel of the derivative of `Z ↦ Z²` equals the conjugacy-orbit tangent
    image at every point of the standard orbit, without a characteristic restriction. -/
theorem orbit_linearized_iff {Z : Matrix (n ⊕ n) (n ⊕ n) R}
    (hZ : InJordanOrbit Z) (D : Matrix (n ⊕ n) (n ⊕ n) R) :
    Z * D + D * Z = 0 ↔ ∃ X, X * Z - Z * X = D := by
  constructor
  · intro hD
    obtain ⟨P, Q, hPQ, hQP, hZ⟩ := hZ
    have hJ : jordanCell = Q * Z * P := by
      rw [hZ]
      simp only [← mul_assoc, hQP, one_mul]
      rw [mul_assoc, hQP, mul_one]
    have hD' : jordanCell * (Q * D * P) + (Q * D * P) * jordanCell = 0 := by
      rw [hJ]
      calc
        Q * Z * P * (Q * D * P) + Q * D * P * (Q * Z * P) =
          Q * (Z * (P * Q) * D + D * (P * Q) * Z) * P := by noncomm_ring
        _ = 0 := by simp [hPQ, hD]
    obtain ⟨X, hX⟩ := (jordanCell_linearized_iff (Q * D * P)).mp hD'
    refine ⟨P * X * Q, ?_⟩
    rw [hZ]
    calc
      P * X * Q * (P * jordanCell * Q) - P * jordanCell * Q * (P * X * Q) =
          P * (X * (Q * P) * jordanCell - jordanCell * (Q * P) * X) * Q := by noncomm_ring
      _ = P * (Q * D * P) * Q := by simp only [hQP, mul_one, hX]
      _ = D := by
        calc
          P * (Q * D * P) * Q = (P * Q) * D * (P * Q) := by noncomm_ring
          _ = D := by simp [hPQ]
  · rintro ⟨X, rfl⟩
    calc
      Z * (X * Z - Z * X) + (X * Z - Z * X) * Z =
        X * (Z * Z) - (Z * Z) * X := by noncomm_ring
      _ = 0 := by simp [orbit_square_zero hZ]

/-- The matrix `Z + ε D` over the ring of dual numbers. -/
def firstOrderMatrix {K m : Type} [CommRing K] [Fintype m] [DecidableEq m]
    (Z D : Matrix m m K) : Matrix m m (DualNumber K) :=
  Matrix.dualNumberEquiv.symm ⟨Z, D⟩

theorem firstOrderMatrix_square_iff {K m : Type} [CommRing K]
    [Fintype m] [DecidableEq m] (Z D : Matrix m m K) :
    firstOrderMatrix Z D * firstOrderMatrix Z D = 0 ↔
      Z * Z = 0 ∧ Z * D + D * Z = 0 := by
  rw [← (Matrix.dualNumberEquiv : Matrix m m (DualNumber K) ≃ₐ[K]
    DualNumber (Matrix m m K)).injective.eq_iff]
  rw [map_mul, map_zero]
  simp only [firstOrderMatrix, AlgEquiv.apply_symm_apply]
  simp [TrivSqZeroExt.ext_iff]

theorem firstOrderMatrix_orbit_tangent_iff {K m : Type} [CommRing K]
    [Fintype m] [DecidableEq m] {Z : Matrix (m ⊕ m) (m ⊕ m) K}
    (hZ : InJordanOrbit Z) (D : Matrix (m ⊕ m) (m ⊕ m) K) :
    firstOrderMatrix Z D * firstOrderMatrix Z D = 0 ↔
      ∃ X, X * Z - Z * X = D := by
  rw [firstOrderMatrix_square_iff, orbit_linearized_iff hZ,
    and_iff_right (orbit_square_zero hZ)]

/-- Representations of the dual numbers are exactly square-zero matrices.
    The inverse sends `a + bε` to `aI + bZ`. -/
def dualNumberRepresentationEquiv {S : Type*} [CommRing S] [Algebra R S] :
    (DualNumber R →ₐ[R] Matrix n n S) ≃ {Z : Matrix n n S // Z * Z = 0} where
  toFun F := ⟨F DualNumber.eps, by rw [← map_mul, DualNumber.eps_mul_eps, map_zero]⟩
  invFun Z := DualNumber.lift ⟨(Algebra.ofId R (Matrix n n S), Z.val), Z.property,
    fun r => (Algebra.commutes r Z.val).symm⟩
  left_inv F := by
    apply DualNumber.algHom_ext
    simp
  right_inv Z := by
    apply Subtype.ext
    simp

theorem dualNumberRepresentationEquiv_apply {S : Type*} [CommRing S] [Algebra R S]
    (F : DualNumber R →ₐ[R] Matrix n n S) :
    (dualNumberRepresentationEquiv F).val = F DualNumber.eps := rfl

theorem dualNumberRepresentationEquiv_symm_apply {S : Type*} [CommRing S] [Algebra R S]
    (Z : {Z : Matrix n n S // Z * Z = 0}) (a : DualNumber R) :
    dualNumberRepresentationEquiv.symm Z a =
      algebraMap R (Matrix n n S) a.fst + algebraMap R (Matrix n n S) a.snd * Z.val := rfl

/-- Evaluation at `ε` commutes with algebra maps between matrix algebras. -/
theorem dualNumberRepresentationEquiv_natural {S T m : Type*}
    [CommRing S] [CommRing T] [Algebra R S] [Algebra R T] [Fintype m] [DecidableEq m]
    (F : DualNumber R →ₐ[R] Matrix n n S) (φ : Matrix n n S →ₐ[R] Matrix m m T) :
    (dualNumberRepresentationEquiv (φ.comp F)).val = φ (dualNumberRepresentationEquiv F).val := rfl

/-- Polynomial coordinates have their relative dimension, using the
    presentation with these generators and no relations. -/
theorem mvPolynomial_standardSmooth_dimension (R I : Type*) [CommRing R] [Fintype I] :
    Algebra.IsStandardSmoothOfRelativeDimension (Fintype.card I) R (MvPolynomial I R) := by
  classical
  let P : Algebra.PreSubmersivePresentation R (MvPolynomial I R) I Empty := {
    toGenerators := Algebra.Generators.ofSurjective MvPolynomial.X (by
      simpa [MvPolynomial.aeval_X_left] using
        (Function.surjective_id : Function.Surjective (id : MvPolynomial I R → _)))
    relation := Empty.elim
    span_range_relation_eq_ker := by
      rw [Set.range_eq_empty, Ideal.span_empty,
        Algebra.Generators.ker_eq_ker_aeval_val]
      simp [Algebra.Generators.ofSurjective, MvPolynomial.aeval_X_left]
      ext x
      rfl
    map := Empty.elim
    map_inj := fun a => Empty.elim a }
  let Q : Algebra.SubmersivePresentation R (MvPolynomial I R) I Empty := {
    toPreSubmersivePresentation := P
    jacobian_isUnit := by
      rw [Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det]
      simp }
  exact Q.isStandardSmoothOfRelativeDimension (by
    simp [Algebra.Presentation.dimension, Nat.card_eq_fintype_card])

/-- Inverting a polynomial preserves the relative dimension of polynomial coordinates. -/
theorem mvPolynomial_localization_standardSmooth_dimension
    (R I S : Type*) [CommRing R] [Fintype I] [CommRing S]
    [Algebra R S] [Algebra (MvPolynomial I R) S] [IsScalarTower R (MvPolynomial I R) S]
    (f : MvPolynomial I R) [IsLocalization.Away f S] :
    Algebra.IsStandardSmoothOfRelativeDimension (Fintype.card I) R S := by
  letI := mvPolynomial_standardSmooth_dimension R I
  letI := Algebra.IsStandardSmoothOfRelativeDimension.localization_away (S := S) f
  simpa using Algebra.IsStandardSmoothOfRelativeDimension.trans
    (n := Fintype.card I) (m := 0) R (MvPolynomial I R) S

theorem matrixPair_localization_standardSmooth_dimension
    (R n S : Type*) [CommRing R] [Fintype n] [CommRing S]
    [Algebra R S] [Algebra (MvPolynomial ((n × n) ⊕ (n × n)) R) S]
    [IsScalarTower R (MvPolynomial ((n × n) ⊕ (n × n)) R) S]
    (f : MvPolynomial ((n × n) ⊕ (n × n)) R) [IsLocalization.Away f S] :
    Algebra.IsStandardSmoothOfRelativeDimension (2 * Fintype.card n ^ 2) R S := by
  simpa [Fintype.card_sum, Fintype.card_prod, pow_two, two_mul] using
    mvPolynomial_localization_standardSmooth_dimension R ((n × n) ⊕ (n × n)) S f

/-- Orbit membership is given by square-zero equations and an explicit
    existential rectangular-matrix witness for maximal rank. -/
theorem inJordanOrbit_iff_rank_witness {k : Type*} [Field k]
    (Z : Matrix (n ⊕ n) (n ⊕ n) k) :
    InJordanOrbit Z ↔ Z * Z = 0 ∧
      ∃ P : Matrix (n ⊕ n) n k, ∃ Q : Matrix n (n ⊕ n) k, Q * Z * P = 1 := by
  constructor
  · intro h
    refine ⟨orbit_square_zero h, ?_⟩
    obtain ⟨A, B, hAB, hBA, hZ⟩ := h
    have hJ : B * Z * A = jordanCell := by
      rw [hZ]
      simp only [← mul_assoc, hBA, one_mul]
      rw [mul_assoc, hBA, mul_one]
    refine ⟨A.submatrix id Sum.inr, B.submatrix Sum.inl id, ?_⟩
    change B.submatrix Sum.inl (Equiv.refl _) *
      Z.submatrix (Equiv.refl _) (Equiv.refl _) *
      A.submatrix (Equiv.refl _) Sum.inr = 1
    rw [Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, hJ]
    rfl
  · rintro ⟨hsq, P, Q, hw⟩
    apply (inJordanOrbit_iff_square_zero_rank Z).mpr
    refine ⟨hsq, le_antisymm (square_zero_rank_le Z hsq) ?_⟩
    have hr := (Matrix.rank_mul_le_left (Q * Z) P).trans (Matrix.rank_mul_le_right Q Z)
    simpa [hw] using hr

/-- A one-dimensional unital algebra over a field is the base field itself. -/
theorem finrank_one_algebraMap_bijective {k A : Type*} [Field k] [Ring A] [Algebra k A]
    (h : Module.finrank k A = 1) : Function.Bijective (algebraMap k A) :=
  Module.Free.bijective_algebraMap_of_finrank_eq_one h

noncomputable def finrankOneAlgebraEquiv {k A : Type*} [Field k] [Ring A] [Algebra k A]
    (h : Module.finrank k A = 1) : A ≃ₐ[k] k :=
  (AlgEquiv.ofBijective (Algebra.ofId k A) (finrank_one_algebraMap_bijective h)).symm

/-- A one-dimensional algebra has at most one representation of a fixed size
    over any coefficient algebra. -/
theorem finrank_one_representations_subsingleton {k A S : Type*} [Field k] [Ring A]
    [Algebra k A] [CommRing S] [Algebra k S] (h : Module.finrank k A = 1) :
    Subsingleton (A →ₐ[k] Matrix n n S) := by
  refine ⟨fun F G => AlgHom.ext fun a => ?_⟩
  obtain ⟨r, rfl⟩ := (finrank_one_algebraMap_bijective h).surjective a
  simp

theorem dualNumber_eps_ne_zero {k : Type*} [Field k] :
    (DualNumber.eps : DualNumber k) ≠ 0 := by
  intro h
  have hh := congrArg TrivSqZeroExt.snd h
  exact one_ne_zero hh

/-- No quotient of a field can be the dual numbers: their nonzero `ε` has square zero. -/
theorem dualNumber_not_field_quotient {k : Type*} [Field k]
    (f : k →+* DualNumber k) : ¬Function.Surjective f := by
  intro hs
  obtain ⟨r, hr⟩ := hs DualNumber.eps
  have hr2 : r * r = 0 := f.injective (by
    rw [map_mul, hr, DualNumber.eps_mul_eps, map_zero])
  have hr0 : r = 0 := (mul_self_eq_zero.mp hr2)
  apply dualNumber_eps_ne_zero (k := k)
  rw [← hr, hr0, map_zero]

theorem dualNumber_finrank (k : Type*) [Field k] :
    Module.finrank k (DualNumber k) = 2 := by
  let e : DualNumber k ≃ₗ[k] (k × k) := {
    toFun x := (x.fst, x.snd)
    invFun x := (x.1, x.2)
    left_inv _ := rfl
    right_inv _ := rfl
    map_add' _ _ := rfl
    map_smul' _ _ := rfl }
  rw [e.finrank_eq]
  simp

theorem dualNumber_has_nonzero_square_zero (k : Type*) [Field k] :
    ∃ x : DualNumber k, x ≠ 0 ∧ x * x = 0 :=
  ⟨DualNumber.eps, dualNumber_eps_ne_zero, DualNumber.eps_mul_eps⟩

/-- Finite scalar circuits using affine operations and scalar squaring. -/
inductive ScalarSquareExpr (k : Type*) where
  | constant : k → ScalarSquareExpr k
  | left : ScalarSquareExpr k
  | right : ScalarSquareExpr k
  | add : ScalarSquareExpr k → ScalarSquareExpr k → ScalarSquareExpr k
  | smul : k → ScalarSquareExpr k → ScalarSquareExpr k
  | square : ScalarSquareExpr k → ScalarSquareExpr k

namespace ScalarSquareExpr

def eval {k : Type*} [CommRing k] (x y : k) : ScalarSquareExpr k → k
  | .constant c => c
  | .left => x
  | .right => y
  | .add f g => eval x y f + eval x y g
  | .smul c f => c * eval x y f
  | .square f => eval x y f ^ 2

/-- In characteristic two every scalar-square circuit is additively separable
    in its two inputs. -/
theorem separable {k : Type*} [CommRing k] [CharP k 2]
    (f : ScalarSquareExpr k) (x y : k) :
    f.eval x y + f.eval 0 0 = f.eval x 0 + f.eval 0 y := by
  induction f with
  | constant c => rfl
  | left => simp [eval]
  | right => simp [eval]
  | add f g hf hg =>
      simp only [eval]
      calc
        f.eval x y + g.eval x y + (f.eval 0 0 + g.eval 0 0) =
          (f.eval x y + f.eval 0 0) + (g.eval x y + g.eval 0 0) := by ring
        _ = (f.eval x 0 + f.eval 0 y) + (g.eval x 0 + g.eval 0 y) := by rw [hf, hg]
        _ = f.eval x 0 + g.eval x 0 + (f.eval 0 y + g.eval 0 y) := by ring
  | smul c f hf =>
      simp only [eval]
      rw [← mul_add, hf, mul_add]
  | square f hf =>
      simp only [eval]
      calc
        f.eval x y ^ 2 + f.eval 0 0 ^ 2 = (f.eval x y + f.eval 0 0) ^ 2 :=
          (CharTwo.add_sq _ _).symm
        _ = (f.eval x 0 + f.eval 0 y) ^ 2 := congrArg (fun z : k => z ^ 2) hf
        _ = f.eval x 0 ^ 2 + f.eval 0 y ^ 2 := CharTwo.add_sq _ _

/-- Scalar squaring together with arbitrary affine operations cannot compute
    multiplication in characteristic two. -/
theorem cannot_compute_mul {k : Type*} [CommRing k] [Nontrivial k] [CharP k 2]
    (f : ScalarSquareExpr k) : ¬∀ x y, f.eval x y = x * y := by
  intro h
  have hs := f.separable 1 1
  simp only [h, mul_one, mul_zero, add_zero] at hs
  exact one_ne_zero hs

end ScalarSquareExpr

theorem invertible_coordinate_chart_of_independent {k : Type*} [Field k]
    (X : Matrix (n ⊕ n) (n ⊕ n) k) (hsq : X * X = 0) (e : Equiv.Perm (n ⊕ n))
    (he : LinearIndependent k (fun j : n => X.col (e (Sum.inr j)))) :
    IsUnit (X.submatrix e e).toBlocks₁₂.det := by
  classical
  let Y := X.submatrix e e
  have hy : Y * Y = 0 := by
    dsimp [Y]
    rw [Matrix.submatrix_mul_equiv, hsq]
    rfl
  let L := LinearEquiv.funCongrLeft k k e
  have hl : LinearIndependent k (Y.submatrix id Sum.inr).col :=
    he.map' L.toLinearMap (LinearMap.ker_eq_bot.mpr L.injective)
  have hir : Function.Injective (fun v : n → k => Y.mulVec (Sum.elim 0 v)) := by
    have heq (v : n → k) : Y.mulVec (Sum.elim 0 v) =
        (Y.submatrix id Sum.inr).mulVec v := by
      ext i
      simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type]
    intro v w h
    exact Matrix.mulVec_injective_iff.mpr hl (by simpa only [heq] using h)
  apply (Matrix.isUnit_iff_isUnit_det _).mp
  apply square_zero_independent_right_block_isUnit Y.toBlocks₁₁ Y.toBlocks₁₂ Y.toBlocks₂₁ Y.toBlocks₂₂
  · simpa only [Matrix.fromBlocks_toBlocks] using hy
  · simpa only [Matrix.fromBlocks_toBlocks] using hir

/-- Every permutation chart intersects the fixed squaring cell, over every field,
    including finite fields. A partial permutation matrix supplies the intersection point. -/
theorem cell_meets_every_coordinate_chart {k : Type*} [Field k]
    (e : Equiv.Perm (n ⊕ n)) :
    ∃ A : Matrix n n k, IsUnit ((iota A (A * A)).submatrix e e).toBlocks₁₂.det := by
  classical
  let B : Set n := {j | ∃ v : n, e (Sum.inr j) = Sum.inr v}
  let b : B → n := fun j => j.property.choose
  have hb (j : B) : e (Sum.inr j.val) = Sum.inr (b j) := j.property.choose_spec
  have hbi : Function.Injective b := by
    intro j l h
    apply Subtype.ext
    apply Sum.inr_injective
    apply e.injective
    rw [hb, hb, h]
  let be : B ↪ n := ⟨b, hbi⟩
  let eb : B ≃ Set.range be := be.toEquivRange
  let q : Equiv.Perm n := eb.extendSubtype
  have hq (j v : n) (h : e (Sum.inr j) = Sum.inr v) : q j = v := by
    have hj : j ∈ B := ⟨v, h⟩
    change eb.extendSubtype j = v
    rw [Equiv.extendSubtype_apply_of_mem eb j hj]
    change b ⟨j, hj⟩ = v
    apply Sum.inr_injective
    rw [← hb ⟨j, hj⟩, h]
  let A : Matrix n n k := fun i u => match e.symm (Sum.inl u) with
    | Sum.inl _ => 0
    | Sum.inr j => (1 : Matrix n n k) i (q j)
  have htop (j i : n) : (iota A (A * A)) (Sum.inl i) (e (Sum.inr j)) =
      (1 : Matrix n n k) i (q j) := by
    cases h : e (Sum.inr j) with
    | inl u =>
        have hh : e.symm (Sum.inl u) = Sum.inr j := by rw [← h]; simp
        change A i u = _
        simp [A, hh]
    | inr v =>
        rw [hq j v h]
        rfl
  let top : (n ⊕ n → k) →ₗ[k] (n → k) := {
    toFun v i := v (Sum.inl i)
    map_add' _ _ := rfl
    map_smul' _ _ := rfl }
  have hl : LinearIndependent k (fun j : n => (iota A (A * A)).col (e (Sum.inr j))) := by
    apply LinearIndependent.of_comp top
    have ht : (top ∘ fun j : n => (iota A (A * A)).col (e (Sum.inr j))) =
        (fun j => (1 : Matrix n n k).col (q j)) := by
      funext j i
      exact htop j i
    rw [ht]
    exact (Matrix.linearIndependent_cols_of_isUnit (A := (1 : Matrix n n k)) isUnit_one).comp q q.injective
  exact ⟨A, invertible_coordinate_chart_of_independent _
    ((iota_square_iff A (A * A)).mpr rfl) e hl⟩

section BlockLift

variable {S a b c : Type*} [CommRing S]

/-- Apply a linear map to all four outer matrix blocks. -/
def matrixBlockLift (L : Matrix a a S →ₗ[S] Matrix b b S) :
    Matrix (a ⊕ a) (a ⊕ a) S →ₗ[S] Matrix (b ⊕ b) (b ⊕ b) S where
  toFun Z := Matrix.fromBlocks (L Z.toBlocks₁₁) (L Z.toBlocks₁₂)
    (L Z.toBlocks₂₁) (L Z.toBlocks₂₂)
  map_add' X Y := by
    ext i j
    cases i <;> cases j <;> exact congrFun (congrFun (L.map_add _ _) _) _
  map_smul' r X := by
    ext i j
    cases i <;> cases j <;> exact congrFun (congrFun (L.map_smul r _) _) _

@[simp] theorem matrixBlockLift_fromBlocks (L : Matrix a a S →ₗ[S] Matrix b b S)
    (A B C D : Matrix a a S) :
    matrixBlockLift L (Matrix.fromBlocks A B C D) =
      Matrix.fromBlocks (L A) (L B) (L C) (L D) := by
  simp [matrixBlockLift]

@[simp] theorem matrixBlockLift_id :
    matrixBlockLift (LinearMap.id : Matrix a a S →ₗ[S] Matrix a a S) = LinearMap.id := by
  ext Z i j
  cases i <;> cases j <;> rfl

@[simp] theorem matrixBlockLift_comp (L : Matrix a a S →ₗ[S] Matrix b b S)
    (M : Matrix b b S →ₗ[S] Matrix c c S) :
    (matrixBlockLift M).comp (matrixBlockLift L) = matrixBlockLift (M.comp L) := by
  ext Z i j
  cases i <;> cases j <;> rfl

theorem matrixBlockLift_iota [DecidableEq a] [DecidableEq b]
    (L : Matrix a a S →ₗ[S] Matrix b b S) (hL : L 1 = 1)
    (A B : Matrix a a S) :
    matrixBlockLift L (iota A B) = iota (L A) (L B) := by
  simp [iota, hL]

/-- Block lifting commutes with scalar change whenever the underlying matrix maps do. -/
theorem matrixBlockLift_map {T : Type*} [CommRing T] (φ : S →+* T)
    (L : Matrix a a S →ₗ[S] Matrix b b S)
    (M : Matrix a a T →ₗ[T] Matrix b b T)
    (h : ∀ A, (L A).map φ = M (A.map φ))
    (Z : Matrix (a ⊕ a) (a ⊕ a) S) :
    (matrixBlockLift L Z).map φ = matrixBlockLift M (Z.map φ) := by
  ext i j
  cases i <;> cases j <;> exact congrFun (congrFun (h _) _) _

end BlockLift

section KernelFlag

variable (k V : Type*) [Field k] [AddCommGroup V] [Module k V]

/-- The field points of the quotient-to-subspace isomorphism locus over a Grassmannian. -/
abbrev KernelFlag (d : ℕ) :=
  Σ K : {K : Submodule k V // Module.finrank k K = d}, (V ⧸ K.val) ≃ₗ[k] K.val

/-- Square-zero endomorphisms of prescribed rank. -/
abbrev SquareZeroRankMap (d : ℕ) :=
  {f : V →ₗ[k] V // f.comp f = 0 ∧ Module.finrank k (LinearMap.range f) = d}

variable {k V}

def kernelFlagEndomorphism {d : ℕ} (p : KernelFlag k V d) : V →ₗ[k] V :=
  p.1.val.subtype.comp (p.2.toLinearMap.comp p.1.val.mkQ)

theorem kernelFlagEndomorphism_range {d : ℕ} (p : KernelFlag k V d) :
    LinearMap.range (kernelFlagEndomorphism p) = p.1.val := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact (p.2 (p.1.val.mkQ y)).property
  · intro hx
    obtain ⟨y, hy⟩ := p.1.val.mkQ_surjective (p.2.symm ⟨x, hx⟩)
    refine ⟨y, ?_⟩
    change (p.2 (p.1.val.mkQ y) : V) = x
    rw [hy]
    simp

theorem kernelFlagEndomorphism_square {d : ℕ} (p : KernelFlag k V d) :
    (kernelFlagEndomorphism p).comp (kernelFlagEndomorphism p) = 0 := by
  ext x
  change (p.2 (p.1.val.mkQ (p.2 (p.1.val.mkQ x) : V)) : V) = 0
  simp

def kernelFlagToSquareZero {d : ℕ} (p : KernelFlag k V d) : SquareZeroRankMap k V d :=
  ⟨kernelFlagEndomorphism p, kernelFlagEndomorphism_square p, by
    rw [kernelFlagEndomorphism_range]; exact p.1.property⟩

theorem kernelFlagToSquareZero_injective {d : ℕ} :
    Function.Injective (kernelFlagToSquareZero (k := k) (V := V) (d := d)) := by
  rintro ⟨⟨K, hK⟩, e⟩ ⟨⟨L, hL⟩, f⟩ h
  have he : kernelFlagEndomorphism ⟨⟨K, hK⟩, e⟩ =
      kernelFlagEndomorphism ⟨⟨L, hL⟩, f⟩ := congrArg Subtype.val h
  have hKL : K = L := by
    calc
      K = LinearMap.range (kernelFlagEndomorphism ⟨⟨K, hK⟩, e⟩) :=
        (kernelFlagEndomorphism_range ⟨⟨K, hK⟩, e⟩).symm
      _ = LinearMap.range (kernelFlagEndomorphism ⟨⟨L, hL⟩, f⟩) := congrArg _ he
      _ = L := kernelFlagEndomorphism_range ⟨⟨L, hL⟩, f⟩
  subst L
  have hef : e = f := by
    apply LinearEquiv.ext
    intro q
    obtain ⟨v, rfl⟩ := K.mkQ_surjective q
    apply Subtype.ext
    exact congrArg (fun F : V →ₗ[k] V => F v) he
  subst f
  rfl

variable [FiniteDimensional k V]

theorem kernelFlagToSquareZero_surjective {d : ℕ}
    (hdim : Module.finrank k V = 2 * d) :
    Function.Surjective (kernelFlagToSquareZero (k := k) (V := V) (d := d)) := by
  rintro ⟨f, hsq, hr⟩
  have hkr : LinearMap.ker f = LinearMap.range f :=
    squareZero_maximal_rank_exact f hsq (by rw [hr]; exact hdim)
  have hk : Module.finrank k (LinearMap.ker f) = d := by rw [hkr]; exact hr
  let e : (V ⧸ LinearMap.ker f) ≃ₗ[k] LinearMap.ker f :=
    f.quotKerEquivRange.trans (LinearEquiv.ofEq _ _ hkr.symm)
  refine ⟨⟨⟨LinearMap.ker f, hk⟩, e⟩, ?_⟩
  apply Subtype.ext
  apply LinearMap.ext
  intro x
  exact f.quotKerEquivRange_apply_mk x

/-- The exact field-point classification by a half-dimensional subspace and
    an isomorphism from the quotient onto that subspace. -/
noncomputable def kernelFlagEquivSquareZeroRank {d : ℕ} (hdim : Module.finrank k V = 2 * d) :
    KernelFlag k V d ≃ SquareZeroRankMap k V d :=
  Equiv.ofBijective kernelFlagToSquareZero
    ⟨kernelFlagToSquareZero_injective, kernelFlagToSquareZero_surjective hdim⟩

@[simp] theorem kernelFlagEquivSquareZeroRank_apply {d : ℕ}
    (hdim : Module.finrank k V = 2 * d) (p : KernelFlag k V d) :
    (kernelFlagEquivSquareZeroRank hdim p).val =
      p.1.val.subtype.comp (p.2.toLinearMap.comp p.1.val.mkQ) := rfl

/-- The subspace recovered from an endomorphism is its kernel (and its image). -/
theorem kernelFlagEquivSquareZeroRank_symm_subspace {d : ℕ}
    (hdim : Module.finrank k V = 2 * d) (f : SquareZeroRankMap k V d) :
    ((kernelFlagEquivSquareZeroRank hdim).symm f).1.val = LinearMap.ker f.val := by
  let p := (kernelFlagEquivSquareZeroRank hdim).symm f
  have hp : kernelFlagEndomorphism p = f.val :=
    congrArg Subtype.val ((kernelFlagEquivSquareZeroRank hdim).apply_symm_apply f)
  have hkr : LinearMap.ker f.val = LinearMap.range f.val :=
    squareZero_maximal_rank_exact f.val f.property.1 (by rw [f.property.2]; exact hdim)
  calc
    p.1.val = LinearMap.range (kernelFlagEndomorphism p) :=
      (kernelFlagEndomorphism_range p).symm
    _ = LinearMap.range f.val := congrArg _ hp
    _ = LinearMap.ker f.val := hkr.symm

/-- The recovered quotient isomorphism sends the class of `x` to `f x`. -/
theorem kernelFlagEquivSquareZeroRank_symm_apply_mk {d : ℕ}
    (hdim : Module.finrank k V = 2 * d) (f : SquareZeroRankMap k V d) (x : V) :
    let p := (kernelFlagEquivSquareZeroRank hdim).symm f
    (p.2 (p.1.val.mkQ x) : V) = f.val x := by
  exact congrArg (fun g : SquareZeroRankMap k V d => g.val x)
    ((kernelFlagEquivSquareZeroRank hdim).apply_symm_apply f)

/-- In the paper's standard ambient vector space, the subspaces have dimension `N`. -/
noncomputable def standardKernelFlagEquiv (k n : Type*) [Field k] [Fintype n] :
    KernelFlag k ((n ⊕ n) → k) (Fintype.card n) ≃
      SquareZeroRankMap k ((n ⊕ n) → k) (Fintype.card n) :=
  kernelFlagEquivSquareZeroRank (by simp [Fintype.card_sum, two_mul])

end KernelFlag

end Universality
