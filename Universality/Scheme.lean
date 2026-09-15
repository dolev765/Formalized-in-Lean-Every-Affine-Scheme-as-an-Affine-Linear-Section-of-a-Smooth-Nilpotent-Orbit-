import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Universality.MatrixOrbit
import Universality.Circuit
import Mathlib.AlgebraicGeometry.Restrict
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Mathlib.RingTheory.Smooth.Basic
import Mathlib.Algebra.Category.CommAlgCat.Basic
import Mathlib.RingTheory.FinitePresentation
import Mathlib.Algebra.Category.Ring.Constructions
import Mathlib.AlgebraicGeometry.Sites.BigZariski
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.CategoryTheory.Sites.Subsheaf
import Mathlib.GroupTheory.Coset.Basic
import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp_
import Mathlib.CategoryTheory.Monoidal.Cartesian.Over

namespace Universality
noncomputable section
universe u
open CategoryTheory Limits AlgebraicGeometry

/-- Quotienting by `I + J` gives the pushout of the quotient maps. -/
theorem quotient_sup_isPushout (R : Type*) [CommRing R] (I J : Ideal R) :
    IsPushout (CommRingCat.ofHom (Ideal.Quotient.mk I))
      (CommRingCat.ofHom (Ideal.Quotient.mk J))
      (CommRingCat.ofHom (Ideal.Quotient.factor (show I ≤ I ⊔ J from le_sup_left)))
      (CommRingCat.ofHom (Ideal.Quotient.factor (show J ≤ I ⊔ J from le_sup_right))) where
  w := by ext x; rfl
  isColimit' := ⟨PushoutCocone.isColimitAux' _ fun s => by
    let F : R →+* s.pt := s.inl.hom.comp (Ideal.Quotient.mk I)
    have hfg (x : R) : s.inl.hom (Ideal.Quotient.mk I x) =
        s.inr.hom (Ideal.Quotient.mk J x) :=
      congrArg (fun f => f.hom x) s.condition
    have hI : I ≤ RingHom.ker F := by
      intro x hx
      change s.inl.hom (Ideal.Quotient.mk I x) = 0
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr hx, map_zero]
    have hJ : J ≤ RingHom.ker F := by
      intro x hx
      change s.inl.hom (Ideal.Quotient.mk I x) = 0
      rw [hfg, Ideal.Quotient.eq_zero_iff_mem.mpr hx, map_zero]
    let L : R ⧸ (I ⊔ J) →+* s.pt := Ideal.Quotient.lift (I ⊔ J) F
      (fun x hx => (show I ⊔ J ≤ RingHom.ker F from sup_le hI hJ) hx)
    refine ⟨CommRingCat.ofHom L, ?_, ?_, ?_⟩
    · ext q
      rfl
    · ext q
      exact hfg q
    · intro h h₁ _
      ext q
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective q
      exact congrArg (fun f => f.hom (Ideal.Quotient.mk I x)) h₁⟩

/-- Thus the exact quotient by the ideal sum is the scheme-theoretic intersection. -/
theorem quotient_sup_isPullback (R : Type u) [CommRing R] (I J : Ideal R) :
    IsPullback
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor (show I ≤ I ⊔ J from le_sup_left))))
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor (show J ≤ I ⊔ J from le_sup_right))))
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) :=
  isPullback_SpecMap_of_isPushout _ _ _ _ (quotient_sup_isPushout R I J)

theorem isPullback_restrict_mono {C : Type*} [Category* C]
    {P L O Z Y : C} (f : P ⟶ L) (g : P ⟶ O) (i : O ⟶ Z)
    (a : L ⟶ Y) (b : Z ⟶ Y) [Mono i]
    (h : IsPullback f (g ≫ i) a b) : IsPullback f g a (i ≫ b) where
  w := by simpa only [Category.assoc] using h.w
  isLimit' := ⟨PullbackCone.isLimitAux' _ fun s => by
    have hw : s.fst ≫ a = (s.snd ≫ i) ≫ b := by
      simpa only [Category.assoc] using s.condition
    refine ⟨h.lift s.fst (s.snd ≫ i) hw, h.lift_fst _ _ _, ?_, ?_⟩
    · apply (cancel_mono i).mp
      simpa only [Category.assoc] using h.lift_snd s.fst (s.snd ≫ i) hw
    · intro m h₁ h₂
      change m ≫ g = s.snd at h₂
      apply h.hom_ext
      · simpa only [h.lift_fst] using h₁
      · rw [h.lift_snd, ← Category.assoc]
        exact congrArg (fun z => z ≫ i) h₂⟩

open MvPolynomial
variable {R : Type u} [CommRing R] {α β : Type u}

/-- Equations cutting out the graph of a polynomial map. -/
def graphIdeal (f : β → MvPolynomial α R) : Ideal (MvPolynomial (α ⊕ β) R) :=
  Ideal.span (Set.range fun b => X (Sum.inr b) - rename Sum.inl (f b))

/-- Substitution of the graph equations. -/
def graphEval (f : β → MvPolynomial α R) :
    MvPolynomial (α ⊕ β) R →+* MvPolynomial α R :=
  eval₂Hom C (Sum.elim X f)

@[simp] theorem graphEval_rename (f : β → MvPolynomial α R) (p : MvPolynomial α R) :
    graphEval f (rename Sum.inl p) = p := by
  change eval₂Hom C (Sum.elim X f) (rename Sum.inl p) = p
  rw [eval₂Hom_rename]
  simp [Function.comp_def]

theorem graphEval_surjective (f : β → MvPolynomial α R) :
    Function.Surjective (graphEval f) :=
  fun p => ⟨rename Sum.inl p, graphEval_rename f p⟩

theorem graphIdeal_eq_ker (f : β → MvPolynomial α R) :
    graphIdeal f = RingHom.ker (graphEval f) := by
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro _ ⟨b, rfl⟩
    change graphEval f (X (Sum.inr b) - rename Sum.inl (f b)) = 0
    rw [map_sub, graphEval_rename]
    simp [graphEval]
  · let q := Ideal.Quotient.mk (graphIdeal f)
    have heq : q = (q.comp (rename Sum.inl).toRingHom).comp (graphEval f) := by
      apply MvPolynomial.ringHom_ext
      · intro r
        simp [q, graphEval]
      · intro i
        cases i with
        | inl a => simp [q, graphEval]
        | inr b =>
          simp only [RingHom.comp_apply, graphEval, coe_eval₂Hom, eval₂_X, Sum.elim_inr]
          change q (X (Sum.inr b)) = q (rename Sum.inl (f b))
          apply sub_eq_zero.mp
          rw [← map_sub]
          exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨b, rfl⟩)
    intro p hp
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    change q p = 0
    rw [heq]
    simpa using congrArg (q.comp (rename Sum.inl).toRingHom) hp

/-- Substitution preserves the coefficient algebra. -/
def graphEvalAlg (f : β → MvPolynomial α R) :
    MvPolynomial (α ⊕ β) R →ₐ[R] MvPolynomial α R :=
  { graphEval f with commutes' := by intro r; simp [graphEval] }

/-- The coordinate algebra of a polynomial graph is the polynomial algebra of its source. -/
noncomputable def graphCoordinateAlgEquiv (f : β → MvPolynomial α R) :
    (MvPolynomial (α ⊕ β) R ⧸ graphIdeal f) ≃ₐ[R] MvPolynomial α R :=
  (Ideal.quotientEquivAlgOfEq R (graphIdeal_eq_ker f)).trans
    (Ideal.quotientKerAlgEquivOfSurjective (f := graphEvalAlg f) (graphEval_surjective f))

/-- The underlying ring equivalence of graph elimination. -/
noncomputable def graphCoordinateRingEquiv (f : β → MvPolynomial α R) :
    (MvPolynomial (α ⊕ β) R ⧸ graphIdeal f) ≃+* MvPolynomial α R :=
  (graphCoordinateAlgEquiv f).toRingEquiv

/-- Restrict graph elimination by any further ideal of equations. -/
def graphSectionEval (f : β → MvPolynomial α R)
    (J : Ideal (MvPolynomial (α ⊕ β) R)) :
    MvPolynomial (α ⊕ β) R →ₐ[R] (MvPolynomial α R ⧸ J.map (graphEval f)) :=
  (Ideal.Quotient.mkₐ R (J.map (graphEval f))).comp (graphEvalAlg f)

theorem graphSection_ker (f : β → MvPolynomial α R)
    (J : Ideal (MvPolynomial (α ⊕ β) R)) :
    RingHom.ker (graphSectionEval f J).toRingHom = graphIdeal f ⊔ J := by
  change RingHom.ker ((Ideal.Quotient.mk (J.map (graphEval f))).comp (graphEval f)) = _
  rw [← RingHom.comap_ker, Ideal.mk_ker,
    Ideal.comap_map_of_surjective _ (graphEval_surjective f),
    ← RingHom.ker_eq_comap_bot, ← graphIdeal_eq_ker, sup_comm]

/-- Scheme-theoretic graph intersections preserve the entire quotient algebra. -/
noncomputable def graphSectionAlgEquiv (f : β → MvPolynomial α R)
    (J : Ideal (MvPolynomial (α ⊕ β) R)) :
    (MvPolynomial (α ⊕ β) R ⧸ (graphIdeal f ⊔ J)) ≃ₐ[R]
      (MvPolynomial α R ⧸ J.map (graphEval f)) :=
  (Ideal.quotientEquivAlgOfEq R (graphSection_ker f J).symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective (f := graphSectionEval f J)
      (Ideal.Quotient.mk_surjective.comp (graphEval_surjective f)))

open AlgebraicGeometry CategoryTheory

/-- A genuine scheme isomorphism between the polynomial graph and affine space. -/
noncomputable def graphSchemeIso (f : β → MvPolynomial α R) :
    Spec (.of (MvPolynomial (α ⊕ β) R ⧸ graphIdeal f)) ≅
      Spec (.of (MvPolynomial α R)) :=
  Scheme.Spec.mapIso (graphCoordinateRingEquiv f).symm.toCommRingCatIso.op

/-- The graph morphism into the product affine space is a closed immersion. -/
theorem graph_isClosedImmersion (f : β → MvPolynomial α R) :
    IsClosedImmersion (Spec.map (CommRingCat.ofHom (graphEval f))) :=
  IsClosedImmersion.spec_of_surjective _ (graphEval_surjective f)

/-- The universal entries of the matrix-square polynomial map. -/
def matrixSquarePolynomials (n : Type u) [Fintype n] :
    n × n → MvPolynomial (n × n) R :=
  fun ij => ∑ k, X (ij.1, k) * X (k, ij.2)

/-- The graph `B=A²`, as an affine scheme, is affine matrix space. -/
noncomputable def matrixSquareGraphSchemeIso (n : Type u) [Fintype n] :
    Spec (.of (MvPolynomial ((n × n) ⊕ (n × n)) R ⧸
      graphIdeal (matrixSquarePolynomials (R := R) n))) ≅
      Spec (.of (MvPolynomial (n × n) R)) :=
  graphSchemeIso _

/-- The ideal of all entries of a matrix of equations. -/
def matrixEntryIdeal {m n : Type*} (M : Matrix m n R) : Ideal R :=
  Ideal.span (Set.range fun ij : m × n => M ij.1 ij.2)

theorem matrixEntryIdeal_map {m n S : Type*} [CommRing S]
    (M : Matrix m n R) (φ : R →+* S) :
    (matrixEntryIdeal M).map φ = matrixEntryIdeal (M.map φ) := by
  rw [matrixEntryIdeal, Ideal.map_span]
  unfold matrixEntryIdeal
  congr 1
  apply Set.ext
  intro x
  constructor
  · rintro ⟨y, ⟨ij, rfl⟩, rfl⟩
    exact ⟨ij, rfl⟩
  · rintro ⟨ij, rfl⟩
    exact ⟨M ij.1 ij.2, ⟨ij, rfl⟩, rfl⟩

theorem matrixEntryIdeal_submatrix_equiv {m n : Type*} (M : Matrix m n R)
    (e : m ≃ m) (f : n ≃ n) :
    matrixEntryIdeal (M.submatrix e f) = matrixEntryIdeal M := by
  unfold matrixEntryIdeal
  congr 1
  apply Set.ext
  intro x
  constructor
  · rintro ⟨⟨i, j⟩, rfl⟩
    exact ⟨(e i, f j), rfl⟩
  · rintro ⟨⟨i, j⟩, rfl⟩
    exact ⟨(e.symm i, f.symm j), by simp⟩

theorem matrixEntryIdeal_le_iff {m n : Type*} (M : Matrix m n R) (I : Ideal R) :
    matrixEntryIdeal M ≤ I ↔ M.map (Ideal.Quotient.mk I) = 0 := by
  rw [matrixEntryIdeal, Ideal.span_le]
  constructor
  · intro h
    ext i j
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (h ⟨(i, j), rfl⟩)
  · intro h x hx
    obtain ⟨⟨i, j⟩, rfl⟩ := hx
    exact Ideal.Quotient.eq_zero_iff_mem.mp (congrFun (congrFun h i) j)

theorem map_iota {S : Type*} [CommRing S] {n : Type*} [Fintype n] [DecidableEq n]
    (f : R →+* S) (A B : Matrix n n R) :
    (iota A B).map f = iota (A.map f) (B.map f) := by
  ext (i | i) (j | j) <;> simp [iota, Matrix.map_apply, Matrix.one_apply]

/-- Scheme-theoretic equality: all entries of the block square generate exactly
the matrix graph equations; equality is of ideals, with no radical operation. -/
theorem iota_square_entryIdeal {n : Type*} [Fintype n] [DecidableEq n]
    (A B : Matrix n n R) :
    matrixEntryIdeal (iota A B * iota A B) = matrixEntryIdeal (B - A * A) := by
  have h (I : Ideal R) : matrixEntryIdeal (iota A B * iota A B) ≤ I ↔
      matrixEntryIdeal (B - A * A) ≤ I := by
    rw [matrixEntryIdeal_le_iff, matrixEntryIdeal_le_iff, Matrix.map_mul, map_iota,
      iota_square_iff]
    rw [Matrix.map_sub _ (map_sub _) _ _, Matrix.map_mul, sub_eq_zero]
  exact le_antisymm ((h _).mpr le_rfl) ((h _).mp le_rfl)

/-- Universal source matrix coordinates. -/
def universalMatrixA (n : Type u) : Matrix n n (MvPolynomial ((n × n) ⊕ (n × n)) R) :=
  fun i j => X (Sum.inl (i, j))

/-- Universal target matrix coordinates. -/
def universalMatrixB (n : Type u) : Matrix n n (MvPolynomial ((n × n) ⊕ (n × n)) R) :=
  fun i j => X (Sum.inr (i, j))

theorem universalMatrix_graphIdeal (n : Type u) [Fintype n] :
    matrixEntryIdeal (universalMatrixB (R := R) n -
      universalMatrixA n * universalMatrixA n) =
      graphIdeal (matrixSquarePolynomials (R := R) n) := by
  simp only [matrixEntryIdeal, graphIdeal, universalMatrixA, universalMatrixB,
    matrixSquarePolynomials, Matrix.sub_apply, Matrix.mul_apply, map_sum, map_mul, rename_X]

theorem universal_iota_square_ideal (n : Type u) [Fintype n] [DecidableEq n] :
    matrixEntryIdeal (iota (universalMatrixA (R := R) n) (universalMatrixB n) *
      iota (universalMatrixA n) (universalMatrixB n)) =
      graphIdeal (matrixSquarePolynomials (R := R) n) := by
  rw [iota_square_entryIdeal, universalMatrix_graphIdeal]

/-- The pullback homomorphism of the affine-linear block embedding. -/
def iotaCoordinateMap (n : Type u) [DecidableEq n] :
    MvPolynomial ((n ⊕ n) × (n ⊕ n)) R →+*
      MvPolynomial ((n × n) ⊕ (n × n)) R :=
  eval₂Hom C (fun ij => iota (universalMatrixA n) (universalMatrixB n) ij.1 ij.2)

def iotaCoordinateSection (n : Type u) :
    MvPolynomial ((n × n) ⊕ (n × n)) R →+*
      MvPolynomial ((n ⊕ n) × (n ⊕ n)) R :=
  eval₂Hom C (Sum.elim (fun ij => X (Sum.inl ij.1, Sum.inl ij.2))
    (fun ij => -X (Sum.inr ij.1, Sum.inl ij.2)))

theorem iotaCoordinate_retraction (n : Type u) [DecidableEq n] :
    (iotaCoordinateMap (R := R) n).comp (iotaCoordinateSection n) = RingHom.id _ := by
  apply MvPolynomial.ringHom_ext
  · intro r
    simp [iotaCoordinateMap, iotaCoordinateSection]
  · intro i
    cases i <;> simp [iotaCoordinateMap, iotaCoordinateSection, iota,
      universalMatrixA, universalMatrixB]

theorem iotaCoordinate_surjective (n : Type u) [DecidableEq n] :
    Function.Surjective (iotaCoordinateMap (R := R) n) := by
  intro p
  exact ⟨iotaCoordinateSection n p, DFunLike.congr_fun (iotaCoordinate_retraction n) p⟩

/-- The block chart is genuinely a closed immersion of affine schemes. -/
theorem iota_isClosedImmersion (n : Type u) [DecidableEq n] :
    IsClosedImmersion (Spec.map (CommRingCat.ofHom (iotaCoordinateMap (R := R) n))) :=
  IsClosedImmersion.spec_of_surjective _ (iotaCoordinate_surjective n)

/-- Coordinate map for the closed affine cell in the endomorphism scheme. -/
def cellCoordinateMap (n : Type u) [Fintype n] [DecidableEq n] :
    MvPolynomial ((n ⊕ n) × (n ⊕ n)) R →+* MvPolynomial (n × n) R :=
  (graphEval (matrixSquarePolynomials n)).comp (iotaCoordinateMap n)

theorem cell_isClosedImmersion (n : Type u) [Fintype n] [DecidableEq n] :
    IsClosedImmersion (Spec.map (CommRingCat.ofHom (cellCoordinateMap (R := R) n))) :=
  IsClosedImmersion.spec_of_surjective _
    ((graphEval_surjective _).comp (iotaCoordinate_surjective n))

/-- The closed subscheme defined by every entry of the block square is affine
matrix space, including its scheme structure and nilpotents. -/
noncomputable def squareZeroChartSchemeIso (n : Type u) [Fintype n] [DecidableEq n] :
    Spec (.of (MvPolynomial ((n × n) ⊕ (n × n)) R ⧸
      matrixEntryIdeal (iota (universalMatrixA (R := R) n) (universalMatrixB n) *
        iota (universalMatrixA n) (universalMatrixB n)))) ≅
      Spec (.of (MvPolynomial (n × n) R)) := by
  let e := (Ideal.quotientEquivAlgOfEq R (universal_iota_square_ideal (R := R) n)).toRingEquiv
  exact (Scheme.Spec.mapIso e.symm.toCommRingCatIso.op) ≪≫ matrixSquareGraphSchemeIso n

/-- The scheme-defining ideal of a family of polynomial equations. -/
def equationIdeal {V Q : Type*} (f : Q → MvPolynomial V R) : Ideal (MvPolynomial V R) :=
  Ideal.span (Set.range f)

/-- The universal solution in the quotient coordinate algebra. -/
def universalSolution {V Q : Type*} (f : Q → MvPolynomial V R) :
    V → MvPolynomial V R ⧸ equationIdeal f :=
  fun v => Ideal.Quotient.mk _ (X v)

theorem eval₂_algHom {V S : Type*} [CommRing S] [Algebra R S]
    (φ : MvPolynomial V R →ₐ[R] S) (p : MvPolynomial V R) :
    eval₂ (algebraMap R S) (fun v => φ (X v)) p = φ p := by
  induction p using MvPolynomial.induction_on with
  | C r => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p v hp => simp [hp]

theorem universalSolution_satisfies {V Q : Type*} (f : Q → MvPolynomial V R) (q : Q) :
    eval₂ (algebraMap R _) (universalSolution f) (f q) = 0 := by
  rw [show universalSolution f = fun v => (Ideal.Quotient.mkₐ R (equationIdeal f)) (X v)
    from rfl, eval₂_algHom]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨q, rfl⟩)

/-- A solution determines its algebra homomorphism from the full quotient ring. -/
def solutionLift {V Q S : Type*} [CommRing S] [Algebra R S]
    (f : Q → MvPolynomial V R) (x : V → S)
    (hx : ∀ q, eval₂ (algebraMap R S) x (f q) = 0) :
    (MvPolynomial V R ⧸ equationIdeal f) →ₐ[R] S :=
  Ideal.Quotient.liftₐ _ (aeval x) (by
    change equationIdeal f ≤ RingHom.ker (aeval x).toRingHom
    apply Ideal.span_le.mpr
    rintro _ ⟨q, rfl⟩
    exact hx q)

@[simp] theorem solutionLift_universalSolution {V Q S : Type*} [CommRing S] [Algebra R S]
    (f : Q → MvPolynomial V R) (x : V → S)
    (hx : ∀ q, eval₂ (algebraMap R S) x (f q) = 0) (v : V) :
    solutionLift f x hx (universalSolution f v) = x v := by
  simp [solutionLift, universalSolution]

theorem quotientAlgHom_ext {V Q S : Type*} [CommRing S] [Algebra R S]
    (f : Q → MvPolynomial V R)
    {φ ψ : (MvPolynomial V R ⧸ equationIdeal f) →ₐ[R] S}
    (h : ∀ v, φ (universalSolution f v) = ψ (universalSolution f v)) : φ = ψ := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  exact h

namespace GateSystem
variable {W G E : Type*} [Fintype W]

/-- Polynomial equations of the affine rows and multiplication gates. -/
def polynomials (C : GateSystem R W G E) : E ⊕ G → MvPolynomial W R :=
  Sum.elim (fun e => (C.equations e).eval X)
    (fun g => X (C.output g) - X (C.left g) * X (C.right g))

theorem polynomials_satisfied_iff {S : Type*} [CommRing S] [Algebra R S]
    (C : GateSystem R W G E) (w : W → S) :
    (∀ e, eval₂ (algebraMap R S) w (C.polynomials e) = 0) ↔ C.Satisfies w := by
  simp only [polynomials, Sum.forall, Sum.elim_inl, Sum.elim_inr,
    AffineEquation.eval, algebraMap_eq, eval₂_C, eval₂_X,
    eval₂_add, eval₂_sum, eval₂_mul, eval₂_sub, sub_eq_zero, Satisfies]

theorem universal_satisfies (C : GateSystem R W G E) :
    C.Satisfies (universalSolution C.polynomials) :=
  C.polynomials_satisfied_iff _ |>.mp (universalSolution_satisfies _)
end GateSystem

namespace ArithmeticExpr
theorem map_eval {V S T : Type*} [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
    (φ : S →ₐ[R] T) (t : ArithmeticExpr R V) (x : V → S) :
    φ (t.eval x) = t.eval (fun v => φ (x v)) := by
  induction t <;> simp_all [eval]
end ArithmeticExpr

namespace ExpressionPresentation
variable {V Q : Type u} [DecidableEq R] [DecidableEq V]

def rootPolynomials (P : ExpressionPresentation R V Q) : Q → MvPolynomial V R :=
  fun q => (P.roots q).polynomial

theorem rootUniversal_satisfies (P : ExpressionPresentation R V Q) (q : Q) :
    (P.roots q).eval (universalSolution P.rootPolynomials) = 0 := by
  rw [← ArithmeticExpr.eval_polynomial]
  exact universalSolution_satisfies _ q

def fromCircuit (P : ExpressionPresentation R V Q) :
    (MvPolynomial P.Wire R ⧸ equationIdeal P.gates.polynomials) →ₐ[R]
      (MvPolynomial V R ⧸ equationIdeal P.rootPolynomials) :=
  solutionLift P.gates.polynomials (P.extend (universalSolution P.rootPolynomials))
    ((P.gates.polynomials_satisfied_iff _).mpr
      (P.extend_satisfies _ P.rootUniversal_satisfies))

def toCircuit (P : ExpressionPresentation R V Q) :
    (MvPolynomial V R ⧸ equationIdeal P.rootPolynomials) →ₐ[R]
      (MvPolynomial P.Wire R ⧸ equationIdeal P.gates.polynomials) :=
  solutionLift P.rootPolynomials (P.input (universalSolution P.gates.polynomials))
    (fun q => by
      rw [rootPolynomials, ArithmeticExpr.eval_polynomial]
      exact P.input_satisfies _ P.gates.universal_satisfies q)

@[simp] theorem fromCircuit_generator (P : ExpressionPresentation R V Q) (t : P.Wire) :
    P.fromCircuit (universalSolution P.gates.polynomials t) =
      t.val.eval (universalSolution P.rootPolynomials) := by
  simp [fromCircuit, extend]

@[simp] theorem toCircuit_generator (P : ExpressionPresentation R V Q) (v : V) :
    P.toCircuit (universalSolution P.rootPolynomials v) =
      P.input (universalSolution P.gates.polynomials) v := by
  simp [toCircuit]

theorem fromCircuit_toCircuit (P : ExpressionPresentation R V Q) :
    P.fromCircuit.comp P.toCircuit = AlgHom.id R _ := by
  apply quotientAlgHom_ext P.rootPolynomials
  intro v
  simp [input, ArithmeticExpr.eval]

theorem toCircuit_fromCircuit (P : ExpressionPresentation R V Q) :
    P.toCircuit.comp P.fromCircuit = AlgHom.id R _ := by
  apply quotientAlgHom_ext P.gates.polynomials
  intro t
  simp only [AlgHom.comp_apply, fromCircuit_generator, ArithmeticExpr.map_eval,
    toCircuit_generator, AlgHom.id_apply]
  exact (P.wire_forced _ P.gates.universal_satisfies t.val t.property).symm

/-- Full coordinate-algebra reconstruction: circuit auxiliaries are uniquely
eliminated over the universal, possibly nonreduced quotient algebra. -/
def coordinateAlgEquiv (P : ExpressionPresentation R V Q) :
    (MvPolynomial V R ⧸ equationIdeal P.rootPolynomials) ≃ₐ[R]
      (MvPolynomial P.Wire R ⧸ equationIdeal P.gates.polynomials) :=
  AlgEquiv.ofAlgHom P.toCircuit P.fromCircuit P.toCircuit_fromCircuit P.fromCircuit_toCircuit

/-- Every finite polynomial presentation has exactly the circuit coordinate algebra. -/
def polynomialCoordinateAlgEquiv [Fintype V] [Fintype Q] (f : Q → MvPolynomial V R) :
    (MvPolynomial V R ⧸ equationIdeal f) ≃ₐ[R]
      (MvPolynomial (ofPolynomials f).Wire R ⧸ equationIdeal (ofPolynomials f).gates.polynomials) := by
  have h : f = (ofPolynomials f).rootPolynomials := by
    funext q
    exact (ofPolynomials_roots f q).symm
  exact (Ideal.quotientEquivAlgOfEq R (congrArg equationIdeal h)).trans
    (ofPolynomials f).coordinateAlgEquiv

/-- Scheme-level reconstruction for arbitrary finite polynomial presentations. -/
def polynomialCircuitSchemeIso [Fintype V] [Fintype Q] (f : Q → MvPolynomial V R) :
    Spec (.of (MvPolynomial V R ⧸ equationIdeal f)) ≅
      Spec (.of (MvPolynomial (ofPolynomials f).Wire R ⧸
        equationIdeal (ofPolynomials f).gates.polynomials)) :=
  Scheme.Spec.mapIso (polynomialCoordinateAlgEquiv f).symm.toRingEquiv.toCommRingCatIso.op
end ExpressionPresentation

namespace SquareZeroGeometry
variable (R) (n : Type u) [Fintype n] [DecidableEq n]

abbrev AmbientRing : Type u := MvPolynomial ((n ⊕ n) × (n ⊕ n)) R

def genericMatrix : Matrix (n ⊕ n) (n ⊕ n) (AmbientRing R n) :=
  fun i j => X (i, j)

def squareZeroIdeal : Ideal (AmbientRing R n) :=
  matrixEntryIdeal (genericMatrix R n * genericMatrix R n)

abbrev CoordinateRing : Type u := AmbientRing R n ⧸ squareZeroIdeal R n

/-- The genuine affine scheme defined by every entry of `Z²`. -/
def squareZeroScheme : Scheme := Spec (.of (CoordinateRing R n))

def universalMatrix : Matrix (n ⊕ n) (n ⊕ n) (CoordinateRing R n) :=
  (genericMatrix R n).map (Ideal.Quotient.mk (squareZeroIdeal R n))

omit [DecidableEq n] in
theorem universalMatrix_square : universalMatrix R n * universalMatrix R n = 0 := by
  rw [universalMatrix, ← Matrix.map_mul]
  exact (matrixEntryIdeal_le_iff _ _).mp le_rfl

/-- The open subscheme where at least one size-`N` minor is invertible locally. -/
def maximalRankOpen : (squareZeroScheme R n).Opens :=
  ⨆ (r : n → n ⊕ n) (c : n → n ⊕ n),
    PrimeSpectrum.basicOpen ((universalMatrix R n).submatrix r c).det

/-- The maximal-rank square-zero scheme, defined as an open subscheme. -/
def maximalRankScheme : Scheme := (maximalRankOpen R n).toScheme

/-- The identity-block chart is contained in this principal open. -/
def topRightDet : CoordinateRing R n := (universalMatrix R n).toBlocks₁₂.det

def topRightOpen : (squareZeroScheme R n).Opens := PrimeSpectrum.basicOpen (topRightDet R n)

theorem topRightOpen_le_maximalRank : topRightOpen R n ≤ maximalRankOpen R n :=
  le_iSup_of_le Sum.inl (le_iSup_of_le Sum.inr le_rfl)

/-- The principal chart has precisely its localized square-zero coordinate ring. -/
def topRightChartLocalizationIso : (topRightOpen R n).toScheme ≅
    Spec (.of (Localization.Away (topRightDet R n))) := basicOpenIsoSpecAway _

/-- Polynomial coordinates `(A,T)` for the proposed invertible-block chart. -/
abbrev ChartPolynomialRing : Type u := MvPolynomial ((n × n) ⊕ (n × n)) R

def chartDet : ChartPolynomialRing R n := (universalMatrixB (R := R) n).det

abbrev ChartRing : Type u := Localization.Away (chartDet R n)

instance chartRing_smooth : Algebra.Smooth R (ChartRing R n) := by
  letI : Algebra.Smooth R (ChartPolynomialRing R n) := ⟨inferInstance, inferInstance⟩
  letI : Algebra.Smooth (ChartPolynomialRing R n) (ChartRing R n) :=
    Algebra.Smooth.of_isLocalization_Away (chartDet R n)
  exact Algebra.Smooth.comp R (ChartPolynomialRing R n) (ChartRing R n)

/-- Algebra-valued universal property of a principal localization. -/
def awayLift {A S : Type*} [CommRing A] [CommRing S] [Algebra R A] [Algebra R S]
    (r : A) (φ : A →ₐ[R] S) (h : IsUnit (φ r)) : Localization.Away r →ₐ[R] S :=
  IsLocalization.liftAlgHom (M := Submonoid.powers r) (f := φ) (by
    rintro ⟨y, k, rfl⟩
    simpa using h.pow k)

@[simp] theorem awayLift_algebraMap {A S : Type*} [CommRing A] [CommRing S]
    [Algebra R A] [Algebra R S] (r : A) (φ : A →ₐ[R] S) (h : IsUnit (φ r)) (a : A) :
    awayLift R r φ h (algebraMap A (Localization.Away r) a) = φ a := by
  simp [awayLift]

abbrev LocalCoordinateRing : Type u := Localization.Away (topRightDet R n)

def localMatrix : Matrix (n ⊕ n) (n ⊕ n) (LocalCoordinateRing R n) :=
  (universalMatrix R n).map (algebraMap (CoordinateRing R n) (LocalCoordinateRing R n))

theorem localMatrix_square : localMatrix R n * localMatrix R n = 0 := by
  rw [localMatrix, ← Matrix.map_mul, universalMatrix_square]
  ext i j
  simp

theorem localMatrix_topRight_isUnit : IsUnit (localMatrix R n).toBlocks₁₂.det := by
  have h : (localMatrix R n).toBlocks₁₂ = (universalMatrix R n).toBlocks₁₂.map
      (algebraMap (CoordinateRing R n) (LocalCoordinateRing R n)) := rfl
  rw [h]
  have he : ((universalMatrix R n).toBlocks₁₂.map
      (algebraMap (CoordinateRing R n) (LocalCoordinateRing R n))).det =
      algebraMap (CoordinateRing R n) (LocalCoordinateRing R n) (topRightDet R n) :=
    ((algebraMap (CoordinateRing R n) (LocalCoordinateRing R n)).map_det _).symm
  rw [he]
  exact IsLocalization.Away.algebraMap_isUnit (topRightDet R n)

def chartA : Matrix n n (ChartRing R n) :=
  (universalMatrixA n).map (algebraMap (ChartPolynomialRing R n) (ChartRing R n))

def chartT : Matrix n n (ChartRing R n) :=
  (universalMatrixB n).map (algebraMap (ChartPolynomialRing R n) (ChartRing R n))

theorem chartT_isUnit : IsUnit (chartT R n).det := by
  have he : (chartT R n).det =
      algebraMap (ChartPolynomialRing R n) (ChartRing R n) (chartDet R n) :=
    ((algebraMap (ChartPolynomialRing R n) (ChartRing R n)).map_det _).symm
  rw [he]
  exact IsLocalization.Away.algebraMap_isUnit (chartDet R n)

def chartAmbientEval : AmbientRing R n →ₐ[R] ChartRing R n :=
  aeval (fun ij => generalChart (chartA R n) (chartT R n) ij.1 ij.2)

theorem chartAmbientEval_generic : (genericMatrix R n).map (chartAmbientEval R n) =
    generalChart (chartA R n) (chartT R n) := by
  ext i j
  simp [genericMatrix, chartAmbientEval]

def toChartBase : CoordinateRing R n →ₐ[R] ChartRing R n :=
  Ideal.Quotient.liftₐ _ (chartAmbientEval R n) (by
    change squareZeroIdeal R n ≤ RingHom.ker (chartAmbientEval R n).toRingHom
    apply Ideal.span_le.mpr
    rintro _ ⟨⟨i, j⟩, rfl⟩
    have h : (genericMatrix R n * genericMatrix R n).map (chartAmbientEval R n) = 0 := by
      rw [Matrix.map_mul, chartAmbientEval_generic]
      exact generalChart_square _ _
    exact congrFun (congrFun h i) j)

theorem toChartBase_universal : (universalMatrix R n).map (toChartBase R n) =
    generalChart (chartA R n) (chartT R n) := by
  ext i j
  simp [universalMatrix, genericMatrix, toChartBase, chartAmbientEval]

theorem toChartBase_det : toChartBase R n (topRightDet R n) = (chartT R n).det := by
  rw [topRightDet, AlgHom.map_det]
  congr 1
  have h := congrArg Matrix.toBlocks₁₂ (toChartBase_universal R n)
  simpa [generalChart] using h

/-- Evaluation of the localized square-zero chart at the free coordinates `(A,T)`. -/
def toChart : LocalCoordinateRing R n →ₐ[R] ChartRing R n :=
  awayLift R (topRightDet R n) (toChartBase R n) (by
    rw [toChartBase_det]
    exact chartT_isUnit R n)

def fromChartPolynomial : ChartPolynomialRing R n →ₐ[R] LocalCoordinateRing R n :=
  aeval (Sum.elim (fun ij => ((localMatrix R n).toBlocks₁₂⁻¹ *
    (localMatrix R n).toBlocks₁₁) ij.1 ij.2)
    (fun ij => (localMatrix R n).toBlocks₁₂ ij.1 ij.2))

theorem fromChartPolynomial_T : (universalMatrixB n).map (fromChartPolynomial R n) =
    (localMatrix R n).toBlocks₁₂ := by
  ext i j
  simp [universalMatrixB, fromChartPolynomial]

theorem fromChartPolynomial_A : (universalMatrixA n).map (fromChartPolynomial R n) =
    (localMatrix R n).toBlocks₁₂⁻¹ * (localMatrix R n).toBlocks₁₁ := by
  ext i j
  simp [universalMatrixA, fromChartPolynomial]

theorem fromChartPolynomial_det : fromChartPolynomial R n (chartDet R n) =
    (localMatrix R n).toBlocks₁₂.det := by
  rw [chartDet, AlgHom.map_det]
  exact congrArg Matrix.det (fromChartPolynomial_T R n)

/-- Recovering chart coordinates from the universal square-zero endomorphism. -/
def fromChart : ChartRing R n →ₐ[R] LocalCoordinateRing R n :=
  awayLift R (chartDet R n) (fromChartPolynomial R n) (by
    rw [fromChartPolynomial_det]
    exact localMatrix_topRight_isUnit R n)

theorem toChart_localMatrix : (localMatrix R n).map (toChart R n) =
    generalChart (chartA R n) (chartT R n) := by
  rw [← toChartBase_universal R n]
  ext i j
  simp [localMatrix, toChart]

theorem fromChart_chartA : (chartA R n).map (fromChart R n) =
    (localMatrix R n).toBlocks₁₂⁻¹ * (localMatrix R n).toBlocks₁₁ := by
  rw [← fromChartPolynomial_A R n]
  ext i j
  simp [chartA, fromChart]

theorem fromChart_chartT : (chartT R n).map (fromChart R n) =
    (localMatrix R n).toBlocks₁₂ := by
  rw [← fromChartPolynomial_T R n]
  ext i j
  simp [chartT, fromChart]

omit [DecidableEq n] in
theorem map_generalChart {S T F : Type*} [CommRing S] [CommRing T]
    [FunLike F S T] [RingHomClass F S T] (φ : F) (A B : Matrix n n S) :
    (generalChart A B).map φ = generalChart (A.map φ) (B.map φ) := by
  simp only [generalChart, Matrix.fromBlocks_map, Matrix.map_mul,
    Matrix.map_neg φ (map_neg φ)]

theorem localMatrix_normalForm :
    generalChart ((localMatrix R n).toBlocks₁₂⁻¹ * (localMatrix R n).toBlocks₁₁)
      (localMatrix R n).toBlocks₁₂ = localMatrix R n := by
  have h := square_zero_invertible_block_normalForm
    (localMatrix R n).toBlocks₁₁ (localMatrix R n).toBlocks₂₁
    (localMatrix R n).toBlocks₂₂ (localMatrix R n).toBlocks₁₂
    (localMatrix_topRight_isUnit R n)
    (by simpa only [Matrix.fromBlocks_toBlocks] using localMatrix_square R n)
  simpa only [Matrix.fromBlocks_toBlocks] using h

theorem fromChart_toChart : (fromChart R n).comp (toChart R n) = AlgHom.id R _ := by
  have hm : (localMatrix R n).map ((fromChart R n).comp (toChart R n)) = localMatrix R n := by
    rw [show (localMatrix R n).map ((fromChart R n).comp (toChart R n)) =
      ((localMatrix R n).map (toChart R n)).map (fromChart R n) from rfl,
      toChart_localMatrix, map_generalChart n (fromChart R n),
      fromChart_chartA, fromChart_chartT, localMatrix_normalForm]
  apply IsLocalization.algHom_ext (Submonoid.powers (topRightDet R n))
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro ij
  exact congrFun (congrFun hm ij.1) ij.2

theorem toChart_local_topRight : (localMatrix R n).toBlocks₁₂.map (toChart R n) =
    chartT R n := by
  have h := congrArg Matrix.toBlocks₁₂ (toChart_localMatrix R n)
  simpa [generalChart] using h

theorem toChart_local_topLeft : (localMatrix R n).toBlocks₁₁.map (toChart R n) =
    chartT R n * chartA R n := by
  have h := congrArg Matrix.toBlocks₁₁ (toChart_localMatrix R n)
  simpa [generalChart] using h

theorem toChart_inverseProduct :
    ((localMatrix R n).toBlocks₁₂⁻¹ * (localMatrix R n).toBlocks₁₁).map (toChart R n) =
      chartA R n := by
  have hm : (localMatrix R n).toBlocks₁₂ *
      ((localMatrix R n).toBlocks₁₂⁻¹ * (localMatrix R n).toBlocks₁₁) =
      (localMatrix R n).toBlocks₁₁ := by
    rw [← mul_assoc, Matrix.mul_nonsing_inv _ (localMatrix_topRight_isUnit R n), one_mul]
  have he := congrArg (fun M => M.map (toChart R n)) hm
  dsimp only at he
  rw [Matrix.map_mul, toChart_local_topRight, toChart_local_topLeft] at he
  have hh := congrArg (fun M => (chartT R n)⁻¹ * M) he
  simpa only [← mul_assoc, Matrix.nonsing_inv_mul _ (chartT_isUnit R n), one_mul] using hh

theorem toChart_fromChart : (toChart R n).comp (fromChart R n) = AlgHom.id R _ := by
  have hA : (chartA R n).map ((toChart R n).comp (fromChart R n)) = chartA R n := by
    change ((chartA R n).map (fromChart R n)).map (toChart R n) = _
    rw [fromChart_chartA, toChart_inverseProduct]
  have hT : (chartT R n).map ((toChart R n).comp (fromChart R n)) = chartT R n := by
    change ((chartT R n).map (fromChart R n)).map (toChart R n) = _
    rw [fromChart_chartT, toChart_local_topRight]
  apply IsLocalization.algHom_ext (Submonoid.powers (chartDet R n))
  apply MvPolynomial.algHom_ext
  intro ij
  cases ij with
  | inl ij => exact congrFun (congrFun hA ij.1) ij.2
  | inr ij => exact congrFun (congrFun hT ij.1) ij.2

/-- The principal square-zero chart has the free localized coordinate
algebra `R[A,T,1/det(T)]`, with explicit two-sided inverse maps. -/
def chartAlgEquiv : LocalCoordinateRing R n ≃ₐ[R] ChartRing R n :=
  AlgEquiv.ofAlgHom (toChart R n) (fromChart R n)
    (toChart_fromChart R n) (fromChart_toChart R n)

instance localCoordinate_smooth : Algebra.Smooth R (LocalCoordinateRing R n) :=
  Algebra.Smooth.of_equiv (chartAlgEquiv R n).symm

def topRightChartIso : (topRightOpen R n).toScheme ≅ Spec (.of (ChartRing R n)) :=
  topRightChartLocalizationIso R n ≪≫
    Scheme.Spec.mapIso (chartAlgEquiv R n).symm.toRingEquiv.toCommRingCatIso.op

theorem localizedSquareScheme_smooth :
    Smooth (Spec.map (CommRingCat.ofHom (algebraMap R (LocalCoordinateRing R n)))) := by
  apply (HasRingHomProperty.Spec_iff (P := @Smooth) (Q := RingHom.Smooth)).mpr
  exact RingHom.smooth_algebraMap.mpr inferInstance

theorem chartScheme_smooth :
    Smooth (Spec.map (CommRingCat.ofHom (algebraMap R (ChartRing R n)))) := by
  apply (HasRingHomProperty.Spec_iff (P := @Smooth) (Q := RingHom.Smooth)).mpr
  exact RingHom.smooth_algebraMap.mpr inferInstance

def structureMap : squareZeroScheme R n ⟶ Spec (.of R) :=
  Spec.map (CommRingCat.ofHom (algebraMap R (CoordinateRing R n)))

theorem topRight_structure_factor :
    (topRightChartLocalizationIso R n).hom ≫
      Spec.map (CommRingCat.ofHom (algebraMap R (LocalCoordinateRing R n))) =
        (topRightOpen R n).ι ≫ structureMap R n := by
  have hfac : (topRightChartLocalizationIso R n).hom ≫
      Spec.map (CommRingCat.ofHom
        (algebraMap (CoordinateRing R n) (LocalCoordinateRing R n))) =
      (topRightOpen R n).ι := IsOpenImmersion.isoOfRangeEq_hom_fac
        (Scheme.Opens.ι (X := Spec (.of (CoordinateRing R n)))
          (PrimeSpectrum.basicOpen (topRightDet R n))) _ (by
            simp only [Scheme.Opens.range_ι]
            exact (PrimeSpectrum.localization_away_comap_range _ _).symm)
  rw [IsScalarTower.algebraMap_eq R (CoordinateRing R n) (LocalCoordinateRing R n),
    CommRingCat.ofHom_comp, Spec.map_comp, ← Category.assoc, hfac]
  rfl

/-- Smoothness holds for the canonical projection of the principal open. -/
theorem topRightOpen_smooth : Smooth ((topRightOpen R n).ι ≫ structureMap R n) := by
  rw [← topRight_structure_factor]
  letI := localizedSquareScheme_smooth R n
  infer_instance

set_option backward.isDefEq.respectTransparency false in
theorem topRightChartIso_inv_ι :
    (topRightChartIso R n).inv ≫ (topRightOpen R n).ι =
      Spec.map (CommRingCat.ofHom (toChartBase R n).toRingHom) := by
  change (Spec.map (CommRingCat.ofHom (toChart R n).toRingHom) ≫
    (topRightChartLocalizationIso R n).inv) ≫ (topRightOpen R n).ι = _
  have hfac : (topRightChartLocalizationIso R n).inv ≫ (topRightOpen R n).ι =
      Spec.map (CommRingCat.ofHom
        (algebraMap (CoordinateRing R n) (LocalCoordinateRing R n))) :=
    IsOpenImmersion.isoOfRangeEq_inv_fac
      (Scheme.Opens.ι (X := Spec (.of (CoordinateRing R n)))
        (PrimeSpectrum.basicOpen (topRightDet R n))) _ (by
          simp only [Scheme.Opens.range_ι]
          exact (PrimeSpectrum.localization_away_comap_range _ _).symm)
  have hr : (toChart R n).toRingHom.comp
      (algebraMap (CoordinateRing R n) (LocalCoordinateRing R n)) =
      (toChartBase R n).toRingHom := by
    apply RingHom.ext
    intro q
    change toChart R n (algebraMap (CoordinateRing R n) (LocalCoordinateRing R n) q) = toChartBase R n q
    simp only [toChart, awayLift_algebraMap]
  rw [Category.assoc, hfac, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rw [hr]

/-- Simultaneous row/column permutations are automorphisms of the ambient coordinate algebra. -/
def permuteAmbient (e : (n ⊕ n) ≃ (n ⊕ n)) : AmbientRing R n ≃ₐ[R] AmbientRing R n :=
  MvPolynomial.renameEquiv R (e.prodCongr e)

omit [Fintype n] [DecidableEq n] in
theorem permuteAmbient_generic (e : (n ⊕ n) ≃ (n ⊕ n)) :
    (genericMatrix R n).map (permuteAmbient R n e) = (genericMatrix R n).submatrix e e := by
  ext i j
  simp [genericMatrix, permuteAmbient]

omit [DecidableEq n] in
theorem permuteAmbient_squareZeroIdeal (e : (n ⊕ n) ≃ (n ⊕ n)) :
    (squareZeroIdeal R n).map (permuteAmbient R n e).toRingEquiv.toRingHom =
      squareZeroIdeal R n := by
  rw [squareZeroIdeal, matrixEntryIdeal_map, Matrix.map_mul]
  change matrixEntryIdeal ((genericMatrix R n).map (permuteAmbient R n e) *
    (genericMatrix R n).map (permuteAmbient R n e)) = _
  rw [permuteAmbient_generic, Matrix.submatrix_mul_equiv,
    matrixEntryIdeal_submatrix_equiv]

/-- Coordinate permutation descends to the full square-zero scheme, including nilpotents. -/
def permuteCoordinate (e : (n ⊕ n) ≃ (n ⊕ n)) :
    CoordinateRing R n ≃ₐ[R] CoordinateRing R n :=
  Ideal.quotientEquivAlg _ _ (permuteAmbient R n e) (permuteAmbient_squareZeroIdeal R n e).symm

def permuteScheme (e : (n ⊕ n) ≃ (n ⊕ n)) : squareZeroScheme R n ≅ squareZeroScheme R n :=
  Scheme.Spec.mapIso (permuteCoordinate R n e).toRingEquiv.toCommRingCatIso.op

omit [DecidableEq n] in
theorem permuteScheme_over (e : (n ⊕ n) ≃ (n ⊕ n)) :
    (permuteScheme R n e).hom ≫ structureMap R n = structureMap R n := by
  change Spec.map (CommRingCat.ofHom (permuteCoordinate R n e).toRingEquiv.toRingHom) ≫
    Spec.map (CommRingCat.ofHom (algebraMap R (CoordinateRing R n))) = _
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 1
  ext r
  exact (permuteCoordinate R n e).commutes r

omit [DecidableEq n] in
theorem permuteCoordinate_universal (e : (n ⊕ n) ≃ (n ⊕ n)) :
    (universalMatrix R n).map (permuteCoordinate R n e) =
      (universalMatrix R n).submatrix e e := by
  ext i j
  simp [universalMatrix, genericMatrix, permuteCoordinate, permuteAmbient]

def permutationOpen (e : (n ⊕ n) ≃ (n ⊕ n)) : (squareZeroScheme R n).Opens :=
  PrimeSpectrum.basicOpen ((universalMatrix R n).submatrix e e).toBlocks₁₂.det

theorem permuteCoordinate_det (e : (n ⊕ n) ≃ (n ⊕ n)) :
    permuteCoordinate R n e (topRightDet R n) =
      ((universalMatrix R n).submatrix e e).toBlocks₁₂.det := by
  rw [topRightDet, AlgEquiv.map_det]
  exact congrArg Matrix.det (congrArg Matrix.toBlocks₁₂ (permuteCoordinate_universal R n e))

theorem permuteScheme_preimage_topRight (e : (n ⊕ n) ≃ (n ⊕ n)) :
    (permuteScheme R n e).hom ⁻¹ᵁ topRightOpen R n = permutationOpen R n e := by
  change PrimeSpectrum.basicOpen ((permuteCoordinate R n e) (topRightDet R n)) = _
  rw [permuteCoordinate_det]
  rfl

theorem permutationOpen_smooth (e : (n ⊕ n) ≃ (n ⊕ n)) :
    Smooth ((permutationOpen R n e).ι ≫ structureMap R n) := by
  rw [← permuteScheme_preimage_topRight]
  have hfac : ((permuteScheme R n e).hom.preimageIso (topRightOpen R n)).hom ≫
      ((topRightOpen R n).ι ≫ structureMap R n) =
      ((permuteScheme R n e).hom ⁻¹ᵁ topRightOpen R n).ι ≫ structureMap R n := by
    rw [← Category.assoc, Scheme.Hom.preimageIso_hom_ι, Category.assoc, permuteScheme_over]
  rw [← hfac]
  letI := topRightOpen_smooth R n
  infer_instance

theorem permutationOpen_le_maximalRank (e : (n ⊕ n) ≃ (n ⊕ n)) :
    permutationOpen R n e ≤ maximalRankOpen R n :=
  le_iSup_of_le (fun i => e (Sum.inl i))
    (le_iSup_of_le (fun i => e (Sum.inr i)) le_rfl)

/-- Every point of the maximal-rank scheme belongs to an invertible-block chart.
The proof passes to its residue field, so it covers all scheme points. -/
theorem permutationOpen_cover : (⨆ e, permutationOpen R n e) = maximalRankOpen R n := by
  apply le_antisymm
  · exact iSup_le (permutationOpen_le_maximalRank R n)
  · intro p hp
    obtain ⟨r, hr⟩ := TopologicalSpace.Opens.mem_iSup.mp hp
    obtain ⟨c, hc⟩ := TopologicalSpace.Opens.mem_iSup.mp hr
    let p' : PrimeSpectrum (CoordinateRing R n) := p
    let φ := algebraMap (CoordinateRing R n) p'.asIdeal.ResidueField
    let Z := (universalMatrix R n).map φ
    have hsq : Z * Z = 0 := by
      change (universalMatrix R n).map φ * (universalMatrix R n).map φ = 0
      rw [← Matrix.map_mul, universalMatrix_square]
      ext i j
      simp
    have hm : (Z.submatrix r c).det = φ ((universalMatrix R n).submatrix r c).det :=
      (φ.map_det _).symm
    have hdet : IsUnit (Z.submatrix r c).det := by
      rw [hm]
      apply isUnit_iff_ne_zero.mpr
      intro hz
      exact hc (Ideal.algebraMap_residueField_eq_zero.mp hz)
    obtain ⟨e, he⟩ := square_zero_invertible_minor_has_coordinate_chart Z hsq r c hdet
    apply TopologicalSpace.Opens.mem_iSup.mpr
    refine ⟨e, ?_⟩
    have hm' : ((Z.submatrix e e).toBlocks₁₂).det =
        φ ((universalMatrix R n).submatrix e e).toBlocks₁₂.det := (φ.map_det _).symm
    change ((universalMatrix R n).submatrix e e).toBlocks₁₂.det ∉ p'.asIdeal
    intro hmem
    have hz := Ideal.algebraMap_residueField_eq_zero.mpr hmem
    rw [hm', hz] at he
    exact not_isUnit_zero he

def permutationChartIso (e : (n ⊕ n) ≃ (n ⊕ n)) :
    (permutationOpen R n e).toScheme ≅ Spec (.of (ChartRing R n)) :=
  (squareZeroScheme R n).isoOfEq (permuteScheme_preimage_topRight R n e).symm ≪≫
    (permuteScheme R n e).hom.preimageIso (topRightOpen R n) ≪≫ topRightChartIso R n

@[reassoc (attr := simp)] private theorem opens_eqToIso_inv_ι {X : Scheme.{u}}
    {U V : X.Opens} (h : U = V) :
    (eqToIso (congrArg (fun W : X.Opens => W.toScheme) h)).inv ≫ U.ι = V.ι := by
  subst V
  simp

def permutationChartEmbedding (e : (n ⊕ n) ≃ (n ⊕ n)) :
    CoordinateRing R n →ₐ[R] ChartRing R n :=
  (toChartBase R n).comp (permuteCoordinate R n e).symm.toAlgHom

theorem permutationChartIso_inv_ι (e : (n ⊕ n) ≃ (n ⊕ n)) :
    (permutationChartIso R n e).inv ≫ (permutationOpen R n e).ι =
      Spec.map (CommRingCat.ofHom (permutationChartEmbedding R n e).toRingHom) := by
  apply (cancel_mono (permuteScheme R n e).hom).mp
  calc
    _ = (topRightChartIso R n).inv ≫ (topRightOpen R n).ι := by
      simp only [permutationChartIso, Iso.trans_inv, Category.assoc,
        Scheme.isoOfEq_inv_ι_assoc, Scheme.Hom.preimageIso_inv_ι]
    _ = Spec.map (CommRingCat.ofHom (toChartBase R n).toRingHom) := topRightChartIso_inv_ι R n
    _ = _ := by
      change Spec.map (CommRingCat.ofHom (toChartBase R n).toRingHom) =
        Spec.map (CommRingCat.ofHom (permutationChartEmbedding R n e).toRingHom) ≫
          Spec.map (CommRingCat.ofHom (permuteCoordinate R n e).toRingEquiv.toRingHom)
      have hr : (permutationChartEmbedding R n e).toRingHom.comp
          (permuteCoordinate R n e).toRingEquiv.toRingHom = (toChartBase R n).toRingHom := by
        apply RingHom.ext
        intro q
        exact congrArg (toChartBase R n) ((permuteCoordinate R n e).symm_apply_apply q)
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hr]

def orbitChartOpen (e : (n ⊕ n) ≃ (n ⊕ n)) : (maximalRankScheme R n).Opens :=
  (maximalRankOpen R n).ι ⁻¹ᵁ permutationOpen R n e

theorem orbitChart_cover : (⨆ e, orbitChartOpen R n e) = ⊤ := by
  exact ((maximalRankOpen R n).ι.preimage_iSup (permutationOpen R n)).symm.trans
    ((congrArg (fun U => (maximalRankOpen R n).ι ⁻¹ᵁ U)
      (permutationOpen_cover R n)).trans (maximalRankOpen R n).ι_preimage_self)

def orbitChartToPermutationIso (e : (n ⊕ n) ≃ (n ⊕ n)) :
    (orbitChartOpen R n e).toScheme ≅ (permutationOpen R n e).toScheme :=
  Scheme.Opens.isoOfLE (permutationOpen_le_maximalRank R n e)

def orbitChartIso (e : (n ⊕ n) ≃ (n ⊕ n)) :
    (orbitChartOpen R n e).toScheme ≅ Spec (.of (ChartRing R n)) :=
  orbitChartToPermutationIso R n e ≪≫ permutationChartIso R n e

/-- An open cover of the maximal-rank square-zero scheme. -/
def orbitOpenCover : (maximalRankScheme R n).OpenCover :=
  (maximalRankScheme R n).openCoverOfIsOpenCover (orbitChartOpen R n) (orbitChart_cover R n)

def maximalRankStructureMap : maximalRankScheme R n ⟶ Spec (.of R) :=
  (maximalRankOpen R n).ι ≫ structureMap R n

/-- The maximal-rank square-zero scheme is smooth over every commutative base. -/
theorem maximalRankScheme_smooth : Smooth (maximalRankStructureMap R n) := by
  apply IsZariskiLocalAtSource.of_iSup_eq_top (P := @Smooth)
    (orbitChartOpen R n) (orbitChart_cover R n)
  intro e
  change Smooth (((maximalRankOpen R n).ι ⁻¹ᵁ permutationOpen R n e).ι ≫
    ((maximalRankOpen R n).ι ≫ structureMap R n))
  rw [← Category.assoc, ← Scheme.Opens.isoOfLE_hom_ι (permutationOpen_le_maximalRank R n e),
    Category.assoc]
  letI := permutationOpen_smooth R n e
  infer_instance

instance chartRing_standard_dimension :
    Algebra.IsStandardSmoothOfRelativeDimension (2 * Fintype.card n ^ 2) R (ChartRing R n) :=
  matrixPair_localization_standardSmooth_dimension R n (ChartRing R n) (chartDet R n)

instance localCoordinate_standard_dimension :
    Algebra.IsStandardSmoothOfRelativeDimension (2 * Fintype.card n ^ 2) R
      (LocalCoordinateRing R n) :=
  Algebra.IsStandardSmoothOfRelativeDimension.of_algEquiv (2 * Fintype.card n ^ 2)
    (chartAlgEquiv R n).symm

theorem localizedSquareScheme_dimension :
    SmoothOfRelativeDimension (2 * Fintype.card n ^ 2)
      (Spec.map (CommRingCat.ofHom (algebraMap R (LocalCoordinateRing R n)))) := by
  apply (HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension (2 * Fintype.card n ^ 2))).mpr
  exact RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso _
    ((RingHom.isStandardSmoothOfRelativeDimension_algebraMap (2 * Fintype.card n ^ 2)).mpr inferInstance)

theorem topRightOpen_dimension : SmoothOfRelativeDimension (2 * Fintype.card n ^ 2)
    ((topRightOpen R n).ι ≫ structureMap R n) := by
  rw [← topRight_structure_factor]
  exact IsZariskiLocalAtSource.comp (localizedSquareScheme_dimension R n) _

theorem permutationOpen_dimension (e : (n ⊕ n) ≃ (n ⊕ n)) :
    SmoothOfRelativeDimension (2 * Fintype.card n ^ 2)
      ((permutationOpen R n e).ι ≫ structureMap R n) := by
  rw [← permuteScheme_preimage_topRight]
  have hfac : ((permuteScheme R n e).hom.preimageIso (topRightOpen R n)).hom ≫
      ((topRightOpen R n).ι ≫ structureMap R n) =
      ((permuteScheme R n e).hom ⁻¹ᵁ topRightOpen R n).ι ≫ structureMap R n := by
    rw [← Category.assoc, Scheme.Hom.preimageIso_hom_ι, Category.assoc, permuteScheme_over]
  rw [← hfac]
  exact IsZariskiLocalAtSource.comp (topRightOpen_dimension R n) _

/-- Scheme-level relative dimension of the smooth maximal square-zero orbit. -/
theorem maximalRankScheme_dimension :
    SmoothOfRelativeDimension (2 * Fintype.card n ^ 2) (maximalRankStructureMap R n) := by
  apply IsZariskiLocalAtSource.of_iSup_eq_top
    (P := @SmoothOfRelativeDimension (2 * Fintype.card n ^ 2))
    (orbitChartOpen R n) (orbitChart_cover R n)
  intro e
  change SmoothOfRelativeDimension (2 * Fintype.card n ^ 2)
    (((maximalRankOpen R n).ι ⁻¹ᵁ permutationOpen R n e).ι ≫
      ((maximalRankOpen R n).ι ≫ structureMap R n))
  rw [← Category.assoc, ← Scheme.Opens.isoOfLE_hom_ι (permutationOpen_le_maximalRank R n e),
    Category.assoc]
  exact IsZariskiLocalAtSource.comp (permutationOpen_dimension R n e) _

def cellSourceMatrix : Matrix n n (MvPolynomial (n × n) R) := fun i j => X (i, j)

omit [DecidableEq n] in
theorem cellSource_dimension : SmoothOfRelativeDimension (Fintype.card n ^ 2)
    (Spec.map (CommRingCat.ofHom (algebraMap R (MvPolynomial (n × n) R)))) := by
  letI : Algebra.IsStandardSmoothOfRelativeDimension (Fintype.card n ^ 2) R
      (MvPolynomial (n × n) R) := by
    simpa [Fintype.card_prod, pow_two] using mvPolynomial_standardSmooth_dimension R (n × n)
  apply (HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension (Fintype.card n ^ 2))).mpr
  exact RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso _
    ((RingHom.isStandardSmoothOfRelativeDimension_algebraMap (Fintype.card n ^ 2)).mpr inferInstance)

def cellChartPolynomial : ChartPolynomialRing R n →ₐ[R] MvPolynomial (n × n) R :=
  graphEvalAlg (fun ij => (1 : Matrix n n (MvPolynomial (n × n) R)) ij.1 ij.2)

omit [Fintype n] in
theorem cellChartPolynomial_T : (universalMatrixB n).map (cellChartPolynomial R n) = 1 := by
  ext i j
  simp [universalMatrixB, cellChartPolynomial, graphEvalAlg, graphEval, Matrix.one_apply]

theorem cellChartPolynomial_det : cellChartPolynomial R n (chartDet R n) = 1 := by
  rw [chartDet, AlgHom.map_det]
  exact (congrArg Matrix.det (cellChartPolynomial_T R n)).trans Matrix.det_one

def cellChartEval : ChartRing R n →ₐ[R] MvPolynomial (n × n) R :=
  awayLift R (chartDet R n) (cellChartPolynomial R n) (by
    rw [cellChartPolynomial_det]
    exact isUnit_one)

theorem cellChartEval_surjective : Function.Surjective (cellChartEval R n) := by
  intro p
  refine ⟨algebraMap (ChartPolynomialRing R n) (ChartRing R n) (rename Sum.inl p), ?_⟩
  rw [cellChartEval, awayLift_algebraMap]
  exact graphEval_rename _ p

theorem cellChartEval_A : (chartA R n).map (cellChartEval R n) = cellSourceMatrix R n := by
  ext i j
  simp [chartA, cellChartEval, cellSourceMatrix, universalMatrixA,
    cellChartPolynomial, graphEvalAlg, graphEval]

theorem cellChartEval_T : (chartT R n).map (cellChartEval R n) = 1 := by
  rw [← cellChartPolynomial_T R n]
  ext i j
  simp [chartT, cellChartEval]

/-- The morphism of the closed affine cell into the maximal-rank scheme. -/
def cellMorphism : Spec (.of (MvPolynomial (n × n) R)) ⟶ maximalRankScheme R n :=
  Spec.map (CommRingCat.ofHom (cellChartEval R n).toRingHom) ≫
    (topRightChartIso R n).inv ≫
      (squareZeroScheme R n).homOfLE (topRightOpen_le_maximalRank R n)

def squareZeroClosedImmersion : squareZeroScheme R n ⟶ Spec (.of (AmbientRing R n)) :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (squareZeroIdeal R n)))

instance squareZeroClosedImmersion_isClosedImmersion :
    IsClosedImmersion (squareZeroClosedImmersion R n) :=
  IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective

theorem cellCoordinateMap_X (ij : (n ⊕ n) × (n ⊕ n)) :
    cellCoordinateMap (R := R) n (X ij) =
      iota (cellSourceMatrix R n) (cellSourceMatrix R n * cellSourceMatrix R n) ij.1 ij.2 := by
  rcases ij with ⟨i | i, j | j⟩ <;>
    simp [cellCoordinateMap, iotaCoordinateMap, iota, universalMatrixA, universalMatrixB,
      graphEval, matrixSquarePolynomials, cellSourceMatrix, Matrix.mul_apply, Matrix.one_apply]

theorem cellChartEval_toChartBase_universal :
    (universalMatrix R n).map ((cellChartEval R n).comp (toChartBase R n)) =
      iota (cellSourceMatrix R n) (cellSourceMatrix R n * cellSourceMatrix R n) := by
  change ((universalMatrix R n).map (toChartBase R n)).map (cellChartEval R n) = _
  rw [toChartBase_universal, map_generalChart n (cellChartEval R n),
    cellChartEval_A, cellChartEval_T]
  simp [generalChart, iota]

set_option backward.isDefEq.respectTransparency false in
theorem cellMorphism_ambient :
    cellMorphism R n ≫ (maximalRankOpen R n).ι ≫ squareZeroClosedImmersion R n =
      Spec.map (CommRingCat.ofHom (cellCoordinateMap (R := R) n)) := by
  unfold cellMorphism
  simp only [Category.assoc, Scheme.homOfLE_ι_assoc]
  rw [← Category.assoc (topRightChartIso R n).inv, topRightChartIso_inv_ι]
  change Spec.map (CommRingCat.ofHom (cellChartEval R n).toRingHom) ≫
    Spec.map (CommRingCat.ofHom (toChartBase R n).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (squareZeroIdeal R n))) = _
  rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
  congr 1
  apply congrArg CommRingCat.ofHom
  apply MvPolynomial.ringHom_ext
  · intro r
    simp [cellCoordinateMap, iotaCoordinateMap, graphEval]
    change cellChartEval R n (toChartBase R n (algebraMap R (CoordinateRing R n) r)) =
      algebraMap R (MvPolynomial (n × n) R) r
    simp only [AlgHom.commutes]
  · intro ij
    rw [cellCoordinateMap_X]
    exact congrFun (congrFun (cellChartEval_toChartBase_universal R n) ij.1) ij.2

theorem cellMorphism_isClosedImmersion : IsClosedImmersion (cellMorphism R n) := by
  letI : IsSeparated (squareZeroClosedImmersion R n) := inferInstance
  letI : IsSeparated (maximalRankOpen R n).ι := inferInstance
  have hsep : IsSeparated ((maximalRankOpen R n).ι ≫ squareZeroClosedImmersion R n) :=
    (IsSeparated.comp_iff (f := (maximalRankOpen R n).ι)
      (g := squareZeroClosedImmersion R n)).mpr inferInstance
  have hclosed : IsClosedImmersion
      (cellMorphism R n ≫ ((maximalRankOpen R n).ι ≫ squareZeroClosedImmersion R n)) := by
    rw [cellMorphism_ambient]
    exact cell_isClosedImmersion n
  exact @IsClosedImmersion.of_comp _ _ _ (cellMorphism R n)
    ((maximalRankOpen R n).ι ≫ squareZeroClosedImmersion R n) hclosed hsep

omit [DecidableEq n] in
theorem squareZeroClosedImmersion_over : squareZeroClosedImmersion R n ≫
    Spec.map (CommRingCat.ofHom (algebraMap R (AmbientRing R n))) = structureMap R n := by
  change Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (squareZeroIdeal R n))) ≫
    Spec.map (CommRingCat.ofHom (algebraMap R (AmbientRing R n))) = _
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rfl

/-- The cell embedding is a morphism over the stated coefficient ring. -/
theorem cellMorphism_over : cellMorphism R n ≫ maximalRankStructureMap R n =
    Spec.map (CommRingCat.ofHom (algebraMap R (MvPolynomial (n × n) R))) := by
  calc
    _ = (cellMorphism R n ≫ (maximalRankOpen R n).ι ≫ squareZeroClosedImmersion R n) ≫
        Spec.map (CommRingCat.ofHom (algebraMap R (AmbientRing R n))) := by
      simp only [maximalRankStructureMap, Category.assoc, squareZeroClosedImmersion_over]
    _ = Spec.map (CommRingCat.ofHom (cellCoordinateMap (R := R) n)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap R (AmbientRing R n))) := by
      rw [cellMorphism_ambient]
    _ = _ := by
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
      congr 1
      apply congrArg CommRingCat.ofHom
      apply RingHom.ext
      intro r
      simp [cellCoordinateMap, iotaCoordinateMap, graphEval]

/-- The orbit is a locally closed subscheme of the ambient matrix affine space. -/
instance maximalRankScheme_isImmersion :
    IsImmersion ((maximalRankOpen R n).ι ≫ squareZeroClosedImmersion R n) := by
  infer_instance

/-- The determinant inverted in the chart is a nonzero polynomial. -/
theorem chartDet_ne_zero [Nontrivial R] : chartDet R n ≠ 0 := by
  intro h
  have he := cellChartPolynomial_det R n
  rw [h, map_zero] at he
  exact zero_ne_one he

instance chartRing_isDomain [IsDomain R] : IsDomain (ChartRing R n) :=
  IsLocalization.isDomain_of_le_nonZeroDivisors (ChartRing R n)
    (powers_le_nonZeroDivisors_of_noZeroDivisors (chartDet_ne_zero R n))

instance permutationOpen_irreducible [IsDomain R] (e : Equiv.Perm (n ⊕ n)) :
    IrreducibleSpace (permutationOpen R n e).toScheme := by
  let h := TopCat.homeoOfIso (Scheme.forgetToTop.mapIso (permutationChartIso R n e))
  apply h.irreducibleSpace_iff.mpr
  change IrreducibleSpace (PrimeSpectrum (ChartRing R n))
  infer_instance

instance orbitChart_irreducible [IsDomain R] (e : Equiv.Perm (n ⊕ n)) :
    IrreducibleSpace (orbitChartOpen R n e).toScheme := by
  let h := TopCat.homeoOfIso (Scheme.forgetToTop.mapIso (orbitChartToPermutationIso R n e))
  exact h.irreducibleSpace_iff.mpr (permutationOpen_irreducible R n e)

/-- An irreducible open chart meeting every irreducible member of an open cover is dense. -/
private theorem dense_of_irreducible_open_cover {X : Type*} [TopologicalSpace X]
    {I : Type*} (U : I → TopologicalSpace.Opens X) (hc : (⨆ i, U i) = ⊤)
    (hi : ∀ i, IsIrreducible (U i : Set X)) (i₀ : I)
    (hm : ∀ i, ((U i : Set X) ∩ (U i₀ : Set X)).Nonempty) :
    Dense (U i₀ : Set X) := by
  apply dense_iff_inter_open.mpr
  intro V hV hne
  obtain ⟨x, hx⟩ := hne
  have hxU : x ∈ ⨆ i, U i := by rw [hc]; trivial
  obtain ⟨i, hxi⟩ := TopologicalSpace.Opens.mem_iSup.mp hxU
  obtain ⟨y, hyi, hyV, hy₀⟩ := (hi i).2 V (U i₀) hV (U i₀).isOpen
    ⟨x, hxi, hx⟩ (hm i)
  exact ⟨y, hyV, hy₀⟩

section FieldIrreducibility
variable {k : Type u} [Field k]

def cellPointEval (A : Matrix n n k) : CoordinateRing k n →ₐ[k] k :=
  (aeval (fun ij : n × n => A ij.1 ij.2)).comp
    ((cellChartEval k n).comp (toChartBase k n))

set_option backward.isDefEq.respectTransparency false in
theorem cellPointEval_universal (A : Matrix n n k) :
    (universalMatrix k n).map (cellPointEval n A) = iota A (A * A) := by
  change ((universalMatrix k n).map ((cellChartEval k n).comp (toChartBase k n))).map
    (aeval (fun ij : n × n => A ij.1 ij.2)) = _
  rw [cellChartEval_toChartBase_universal]
  ext (i | i) (j | j) <;>
    simp [iota, cellSourceMatrix, Matrix.map_apply, Matrix.mul_apply, Matrix.one_apply]

def cellPoint (A : Matrix n n k) : PrimeSpectrum (CoordinateRing k n) :=
  PrimeSpectrum.comap (cellPointEval n A).toRingHom ⟨⊥, inferInstance⟩

theorem cellPoint_mem_permutationOpen (A : Matrix n n k) (e : Equiv.Perm (n ⊕ n))
    (he : IsUnit ((iota A (A * A)).submatrix e e).toBlocks₁₂.det) :
    cellPoint n A ∈ permutationOpen k n e := by
  change ¬ (cellPointEval n A)
    (((universalMatrix k n).submatrix e e).toBlocks₁₂.det) ∈ (⊥ : Ideal k)
  rw [Ideal.mem_bot]
  have hm : (((universalMatrix k n).submatrix e e).toBlocks₁₂).map
      (cellPointEval n A) = ((iota A (A * A)).submatrix e e).toBlocks₁₂ := by
    have h := cellPointEval_universal n A
    exact congrArg (fun M : Matrix (n ⊕ n) (n ⊕ n) k =>
      (M.submatrix e e).toBlocks₁₂) h
  have hd : (cellPointEval n A) (((universalMatrix k n).submatrix e e).toBlocks₁₂.det) =
      ((((universalMatrix k n).submatrix e e).toBlocks₁₂).map (cellPointEval n A)).det :=
    (cellPointEval n A).map_det _
  rw [hm] at hd
  rw [hd]
  exact he.ne_zero

theorem orbitChart_inter_identity_nonempty (e : Equiv.Perm (n ⊕ n)) :
    ((orbitChartOpen k n e : Set (maximalRankScheme k n)) ∩
      (orbitChartOpen k n (Equiv.refl _) : Set (maximalRankScheme k n))).Nonempty := by
  obtain ⟨A, hA⟩ := cell_meets_every_coordinate_chart (k := k) (n := n) e
  have hp := cellPoint_mem_permutationOpen n A e hA
  have h₀ := cellPoint_mem_permutationOpen n A (Equiv.refl _) (by
    simp [iota])
  let x : maximalRankScheme k n :=
    ⟨cellPoint n A, permutationOpen_le_maximalRank k n e hp⟩
  exact ⟨x, hp, h₀⟩

/-- The maximal-rank square-zero scheme is irreducible over every field. -/
instance maximalRankScheme_irreducible : IrreducibleSpace (maximalRankScheme k n) := by
  have hi (e : Equiv.Perm (n ⊕ n)) :
      IsIrreducible (orbitChartOpen k n e : Set (maximalRankScheme k n)) := by
    apply isIrreducible_iff_irreducibleSpace.mpr
    exact orbitChart_irreducible k n e
  have hd := dense_of_irreducible_open_cover (orbitChartOpen k n) (orbitChart_cover k n)
    hi (Equiv.refl _) (orbitChart_inter_identity_nonempty n)
  apply (irreducibleSpace_def _).mpr
  simpa only [hd.closure_eq] using (hi (Equiv.refl _)).closure

end FieldIrreducibility

end SquareZeroGeometry

/-- A finite polynomial presentation with its surjective algebra map. -/
structure FinitePolynomialPresentation (R A : Type u) [CommRing R] [CommRing A] [Algebra R A] where
  Variable : Type u
  Relation : Type u
  [finiteVariable : Fintype Variable]
  [finiteRelation : Fintype Relation]
  equations : Relation → MvPolynomial Variable R
  quotientMap : MvPolynomial Variable R →ₐ[R] A
  surjective : Function.Surjective quotientMap
  kernel : equationIdeal equations = RingHom.ker quotientMap.toRingHom

attribute [instance] FinitePolynomialPresentation.finiteVariable
  FinitePolynomialPresentation.finiteRelation

namespace FinitePolynomialPresentation
variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]

theorem nonempty [Algebra.FinitePresentation R A] : Nonempty (FinitePolynomialPresentation R A) := by
  classical
  obtain ⟨(V : Type u), hV, φ, hsurj, hfg⟩ :=
    (Algebra.FinitePresentation.iff_quotient_mvPolynomial' (R := R) (A := A)).mp inferInstance
  letI := hV
  obtain ⟨s, hs⟩ := hfg
  refine ⟨⟨V, s, (fun q => q.val), φ, hsurj, ?_⟩⟩
  change Ideal.span (Set.range (fun q : s => q.val)) = _
  have hr : Set.range (fun q : s => q.val) = (s : Set (MvPolynomial V R)) := by
    ext q
    simp
  rw [hr]
  exact hs

def choose [Algebra.FinitePresentation R A] : FinitePolynomialPresentation R A :=
  (nonempty R A).some

variable {R A}

def coordinateAlgEquiv (P : FinitePolynomialPresentation R A) :
    (MvPolynomial P.Variable R ⧸ equationIdeal P.equations) ≃ₐ[R] A :=
  (Ideal.quotientEquivAlgOfEq R P.kernel).trans
    (Ideal.quotientKerAlgEquivOfSurjective P.surjective)

@[simp] theorem coordinateAlgEquiv_mk (P : FinitePolynomialPresentation R A)
    (p : MvPolynomial P.Variable R) :
    P.coordinateAlgEquiv (Ideal.Quotient.mk _ p) = P.quotientMap p := by
  change (Ideal.quotientKerAlgEquivOfSurjective P.surjective)
    (Ideal.quotientEquivAlgOfEq R P.kernel (Ideal.Quotient.mk _ p)) = _
  rw [Ideal.quotientEquivAlgOfEq_mk]
  rfl

@[simp] theorem coordinateAlgEquiv_symm_quotientMap (P : FinitePolynomialPresentation R A)
    (p : MvPolynomial P.Variable R) :
    P.coordinateAlgEquiv.symm (P.quotientMap p) = Ideal.Quotient.mk _ p := by
  apply P.coordinateAlgEquiv.injective
  simp

@[simp] theorem quotientMap_equations (P : FinitePolynomialPresentation R A) (q : P.Relation) :
    P.quotientMap (P.equations q) = 0 := by
  apply RingHom.mem_ker.mp
  change P.equations q ∈ RingHom.ker P.quotientMap.toRingHom
  rw [← P.kernel]
  exact Ideal.subset_span ⟨q, rfl⟩

end FinitePolynomialPresentation

namespace FiniteDiagram
open CategoryTheory Opposite

variable {J : Type u} [Category J] {R : Type u} [CommRing R]
variable (F : Jᵒᵖ ⥤ CommAlgCat.{u} R)
variable (P : ∀ j : J, FinitePolynomialPresentation R (F.obj (op j)))

/-- Lift the image of every generator along an arrow of the algebra diagram. -/
def polynomialArrow {i j : J} (α : i ⟶ j) (v : (P j).Variable) :
    MvPolynomial (P i).Variable R :=
  ((P i).surjective ((F.map α.op).hom ((P j).quotientMap (X v)))).choose

theorem polynomialArrow_spec {i j : J} (α : i ⟶ j) (v : (P j).Variable) :
    (P i).quotientMap (polynomialArrow F P α v) =
      (F.map α.op).hom ((P j).quotientMap (X v)) :=
  ((P i).surjective _).choose_spec

theorem polynomialArrow_comp_quotientMap {i j : J} (α : i ⟶ j) :
    (P i).quotientMap.comp (aeval (polynomialArrow F P α)) =
      (F.map α.op).hom.comp (P j).quotientMap := by
  ext v
  simpa using polynomialArrow_spec F P α v

theorem polynomialArrow_preserves {i j : J} (α : i ⟶ j) (q : (P j).Relation) :
    aeval (polynomialArrow F P α) ((P j).equations q) ∈ equationIdeal (P i).equations := by
  rw [(P i).kernel, RingHom.mem_ker]
  change ((P i).quotientMap.comp (aeval (polynomialArrow F P α))) _ = 0
  rw [polynomialArrow_comp_quotientMap]
  simp

theorem polynomialArrow_id (i : J) (v : (P i).Variable) :
    polynomialArrow F P (𝟙 i) v - X v ∈ equationIdeal (P i).equations := by
  rw [(P i).kernel, RingHom.mem_ker]
  change (P i).quotientMap (polynomialArrow F P (𝟙 i) v - X v) = 0
  rw [map_sub, polynomialArrow_spec]
  simp

theorem polynomialArrow_comp {i j l : J} (α : i ⟶ j) (β : j ⟶ l)
    (v : (P l).Variable) :
    aeval (polynomialArrow F P α) (polynomialArrow F P β v) -
      polynomialArrow F P (α ≫ β) v ∈ equationIdeal (P i).equations := by
  rw [(P i).kernel, RingHom.mem_ker]
  change (P i).quotientMap (aeval (polynomialArrow F P α) (polynomialArrow F P β v) -
    polynomialArrow F P (α ≫ β) v) = 0
  rw [map_sub]
  have h := DFunLike.congr_fun (polynomialArrow_comp_quotientMap F P α)
    (polynomialArrow F P β v)
  change (P i).quotientMap (aeval (polynomialArrow F P α) (polynomialArrow F P β v)) =
    (F.map α.op).hom ((P j).quotientMap (polynomialArrow F P β v)) at h
  rw [h, polynomialArrow_spec, polynomialArrow_spec]
  simp

theorem eval_eq_zero_of_mem_equationIdeal {V Q S : Type*} [CommRing S] [Algebra R S]
    (f : Q → MvPolynomial V R) (x : V → S)
    (hx : ∀ q, aeval x (f q) = 0) {p : MvPolynomial V R}
    (hp : p ∈ equationIdeal f) : aeval x p = 0 := by
  have h : equationIdeal f ≤ RingHom.ker (aeval x).toRingHom := by
    apply Ideal.span_le.mpr
    rintro _ ⟨q, rfl⟩
    exact hx q
  exact h hp

def polynomialInput {S : Type*} [CommRing S] [Algebra R S] {i j : J}
    (α : i ⟶ j) (x : (P i).Variable → S) : (P j).Variable → S :=
  fun v => aeval x (polynomialArrow F P α v)

theorem polynomialInput_preserves {S : Type*} [CommRing S] [Algebra R S] {i j : J}
    (α : i ⟶ j) (x : (P i).Variable → S)
    (hx : ∀ q, aeval x ((P i).equations q) = 0) (q : (P j).Relation) :
    aeval (polynomialInput F P α x) ((P j).equations q) = 0 := by
  have h := eval_eq_zero_of_mem_equationIdeal (P i).equations x hx
    (polynomialArrow_preserves F P α q)
  simpa only [comp_aeval_apply, polynomialInput] using h

theorem polynomialInput_id {S : Type*} [CommRing S] [Algebra R S]
    (i : J) (x : (P i).Variable → S) (hx : ∀ q, aeval x ((P i).equations q) = 0) :
    polynomialInput F P (𝟙 i) x = x := by
  funext v
  have h := eval_eq_zero_of_mem_equationIdeal (P i).equations x hx
    (polynomialArrow_id F P i v)
  simpa only [map_sub, aeval_X, sub_eq_zero, polynomialInput] using h

theorem polynomialInput_comp {S : Type*} [CommRing S] [Algebra R S] {i j l : J}
    (α : i ⟶ j) (β : j ⟶ l) (x : (P i).Variable → S)
    (hx : ∀ q, aeval x ((P i).equations q) = 0) :
    polynomialInput F P (α ≫ β) x = polynomialInput F P β (polynomialInput F P α x) := by
  funext v
  have h := eval_eq_zero_of_mem_equationIdeal (P i).equations x hx
    (polynomialArrow_comp F P α β v)
  have h' := sub_eq_zero.mp (show
    aeval (polynomialInput F P α x) (polynomialArrow F P β v) -
      aeval x (polynomialArrow F P (α ≫ β) v) = 0 by
    simpa only [map_sub, comp_aeval_apply, polynomialInput] using h)
  exact h'.symm

variable [Fintype J] [∀ i j : J, Fintype (i ⟶ j)] [DecidableEq R]
  [∀ j, DecidableEq (P j).Variable]

/-- The copied finite circuit presentation of an arbitrary finite affine algebra diagram. -/
def ofAlgebraDiagram : CircuitDiagram (J := J) (R := R)
    (V := fun j => (P j).Variable) (Q := fun j => (P j).Relation) := by
  classical
  exact CircuitDiagram.ofPolynomials (fun j => (P j).equations) (polynomialArrow F P)

theorem ofAlgebraDiagram_root_eval {S : Type u} [CommRing S] [Algebra R S]
    (i : J) (q : (P i).Relation) (x : (P i).Variable → S) :
    (((ofAlgebraDiagram F P).presentation i).roots q).eval x =
      aeval x ((P i).equations q) := by
  classical
  rw [← ArithmeticExpr.eval_polynomial]
  simp only [ofAlgebraDiagram, CircuitDiagram.ofPolynomials_roots]
  rfl

theorem ofAlgebraDiagram_inputMap {S : Type u} [CommRing S] [Algebra R S]
    {i j : J} (α : i ⟶ j) (x : (P i).Variable → S) :
    (ofAlgebraDiagram F P).inputMap α x = polynomialInput F P α x := by
  classical
  funext v
  simp only [CircuitDiagram.inputMap, ← ArithmeticExpr.eval_polynomial,
    ofAlgebraDiagram, CircuitDiagram.ofPolynomials_lift]
  rfl

theorem ofAlgebraDiagram_laws {S : Type u} [CommRing S] [Algebra R S] :
    (ofAlgebraDiagram F P).Laws (S := S) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro i j α x hx q
    simp only [ofAlgebraDiagram_root_eval] at hx ⊢
    rw [ofAlgebraDiagram_inputMap]
    exact polynomialInput_preserves F P α x hx q
  · intro i x hx
    simp only [ofAlgebraDiagram_root_eval] at hx
    rw [ofAlgebraDiagram_inputMap]
    exact polynomialInput_id F P i x hx
  · intro i j l α β x hx
    simp only [ofAlgebraDiagram_root_eval] at hx
    simp only [ofAlgebraDiagram_inputMap]
    exact polynomialInput_comp F P α β x hx

namespace CircuitDiagram
variable {V Q : J → Type u} [∀ j, DecidableEq (V j)]
variable (D : CircuitDiagram (J := J) (R := R) (V := V) (Q := Q))
variable (h : ∀ (S : Type u) [CommRing S] [Algebra R S], D.Laws (S := S))

def fromCopiedCircuit (i : J) :
    (MvPolynomial (D.Wire i) R ⧸ equationIdeal (D.gates i).polynomials) →ₐ[R]
      (MvPolynomial (V i) R ⧸ equationIdeal (D.presentation i).rootPolynomials) :=
  solutionLift (D.gates i).polynomials
    (D.extend i (universalSolution (D.presentation i).rootPolynomials))
    (((D.gates i).polynomials_satisfied_iff _).mpr
      (D.extend_satisfies (h _) i _ (D.presentation i).rootUniversal_satisfies))

def toCopiedCircuit (i : J) :
    (MvPolynomial (V i) R ⧸ equationIdeal (D.presentation i).rootPolynomials) →ₐ[R]
      (MvPolynomial (D.Wire i) R ⧸ equationIdeal (D.gates i).polynomials) :=
  solutionLift (D.presentation i).rootPolynomials
    (D.input i (universalSolution (D.gates i).polynomials)) (fun q => by
      rw [ExpressionPresentation.rootPolynomials, ArithmeticExpr.eval_polynomial]
      exact D.input_satisfies i _ (D.gates i).universal_satisfies q)

@[simp] theorem fromCopiedCircuit_generator (i : J) (t : D.Wire i) :
    D.fromCopiedCircuit h i (universalSolution (D.gates i).polynomials t) =
      D.extend i (universalSolution (D.presentation i).rootPolynomials) t := by
  simp [fromCopiedCircuit]

@[simp] theorem toCopiedCircuit_generator (i : J) (v : V i) :
    D.toCopiedCircuit i (universalSolution (D.presentation i).rootPolynomials v) =
      D.input i (universalSolution (D.gates i).polynomials) v := by
  simp [toCopiedCircuit]

@[simp] theorem toCopiedCircuit_mk (i : J) (p : MvPolynomial (V i) R) :
    D.toCopiedCircuit i (Ideal.Quotient.mk _ p) =
      aeval (D.input i (universalSolution (D.gates i).polynomials)) p := by
  simp [toCopiedCircuit, solutionLift]

theorem fromCopiedCircuit_toCopiedCircuit (i : J) :
    (D.fromCopiedCircuit h i).comp (D.toCopiedCircuit i) = AlgHom.id R _ := by
  apply quotientAlgHom_ext (D.presentation i).rootPolynomials
  intro v
  simp only [AlgHom.comp_apply, toCopiedCircuit_generator, input,
    fromCopiedCircuit_generator, AlgHom.id_apply]
  change D.inputMap (𝟙 i) (universalSolution (D.presentation i).rootPolynomials) v = _
  exact congrFun ((h _).identity i _ (D.presentation i).rootUniversal_satisfies) v

theorem toCopiedCircuit_fromCopiedCircuit (i : J) :
    (D.toCopiedCircuit i).comp (D.fromCopiedCircuit h i) = AlgHom.id R _ := by
  apply quotientAlgHom_ext (D.gates i).polynomials
  intro t
  simp only [AlgHom.comp_apply, fromCopiedCircuit_generator, extend, inputMap,
    ArithmeticExpr.map_eval, toCopiedCircuit_generator, AlgHom.id_apply]
  exact congrFun (D.wire_forced i _ (D.gates i).universal_satisfies) t

/-- Every copied auxiliary coordinate is uniquely reconstructed in the full coordinate algebra. -/
def copiedCoordinateAlgEquiv (i : J) :
    (MvPolynomial (V i) R ⧸ equationIdeal (D.presentation i).rootPolynomials) ≃ₐ[R]
      (MvPolynomial (D.Wire i) R ⧸ equationIdeal (D.gates i).polynomials) :=
  AlgEquiv.ofAlgHom (D.toCopiedCircuit i) (D.fromCopiedCircuit h i)
    (D.toCopiedCircuit_fromCopiedCircuit h i) (D.fromCopiedCircuit_toCopiedCircuit h i)

def copiedMap {i j : J} (α : i ⟶ j) :
    (MvPolynomial (D.Wire j) R ⧸ equationIdeal (D.gates j).polynomials) →ₐ[R]
      (MvPolynomial (D.Wire i) R ⧸ equationIdeal (D.gates i).polynomials) :=
  solutionLift (D.gates j).polynomials
    (projection _ (fun j => (D.presentation j).Wire) α
      (universalSolution (D.gates i).polynomials))
    (((D.gates j).polynomials_satisfied_iff _).mpr
      (D.projection_satisfies α _ (D.gates i).universal_satisfies))

@[simp] theorem copiedMap_generator {i j : J} (α : i ⟶ j) (t : D.Wire j) :
    D.copiedMap α (universalSolution (D.gates j).polynomials t) =
      universalSolution (D.gates i).polynomials ⟨t.1, α ≫ t.2.1, t.2.2⟩ := by
  simp [copiedMap, projection]

end CircuitDiagram

/-- Objectwise algebra reconstruction for an arbitrary finite diagram of algebras. -/
def ofAlgebraDiagramCoordinateAlgEquiv (i : J) :
    (F.obj (op i)) ≃ₐ[R]
      (MvPolynomial ((ofAlgebraDiagram F P).Wire i) R ⧸
        equationIdeal ((ofAlgebraDiagram F P).gates i).polynomials) := by
  classical
  have hr : ((ofAlgebraDiagram F P).presentation i).rootPolynomials = (P i).equations := by
    funext q
    exact CircuitDiagram.ofPolynomials_roots _ _ _ _
  let e := (ofAlgebraDiagram F P).copiedCoordinateAlgEquiv
    (fun S _ _ => ofAlgebraDiagram_laws F P (S := S)) i
  exact (P i).coordinateAlgEquiv.symm.trans
    ((Ideal.quotientEquivAlgOfEq R (congrArg equationIdeal hr.symm)).trans e)

theorem ofAlgebraDiagramCoordinateAlgEquiv_quotientMap (i : J)
    (p : MvPolynomial (P i).Variable R) :
    ofAlgebraDiagramCoordinateAlgEquiv F P i ((P i).quotientMap p) =
      (ofAlgebraDiagram F P).toCopiedCircuit i (Ideal.Quotient.mk _ p) := by
  classical
  simp only [ofAlgebraDiagramCoordinateAlgEquiv, AlgEquiv.trans_apply,
    FinitePolynomialPresentation.coordinateAlgEquiv_symm_quotientMap,
    Ideal.quotientEquivAlgOfEq_mk, CircuitDiagram.copiedCoordinateAlgEquiv]
  rfl

@[simp] theorem ofAlgebraDiagramCoordinateAlgEquiv_generator (i : J) (v : (P i).Variable) :
    ofAlgebraDiagramCoordinateAlgEquiv F P i ((P i).quotientMap (X v)) =
      (ofAlgebraDiagram F P).input i
        (universalSolution ((ofAlgebraDiagram F P).gates i).polynomials) v := by
  rw [ofAlgebraDiagramCoordinateAlgEquiv_quotientMap]
  exact CircuitDiagram.toCopiedCircuit_generator _ _ _

/-- The reconstruction commutes with every arrow of the original algebra diagram. -/
theorem ofAlgebraDiagramCoordinateAlgEquiv_natural {i j : J} (α : i ⟶ j) :
    (ofAlgebraDiagramCoordinateAlgEquiv F P i).toAlgHom.comp (F.map α.op).hom =
      ((ofAlgebraDiagram F P).copiedMap α).comp
        (ofAlgebraDiagramCoordinateAlgEquiv F P j).toAlgHom := by
  classical
  have h : ((ofAlgebraDiagramCoordinateAlgEquiv F P i).toAlgHom.comp
      (F.map α.op).hom).comp (P j).quotientMap =
      (((ofAlgebraDiagram F P).copiedMap α).comp
        (ofAlgebraDiagramCoordinateAlgEquiv F P j).toAlgHom).comp (P j).quotientMap := by
    apply MvPolynomial.algHom_ext
    intro v
    change ofAlgebraDiagramCoordinateAlgEquiv F P i
      ((F.map α.op).hom ((P j).quotientMap (X v))) =
      (ofAlgebraDiagram F P).copiedMap α
        (ofAlgebraDiagramCoordinateAlgEquiv F P j ((P j).quotientMap (X v)))
    rw [← polynomialArrow_spec F P α v, ofAlgebraDiagramCoordinateAlgEquiv_quotientMap,
      CircuitDiagram.toCopiedCircuit_mk, ofAlgebraDiagramCoordinateAlgEquiv_generator]
    let D := ofAlgebraDiagram F P
    have hp := congrFun (D.input_projection α
      (universalSolution (D.gates i).polynomials) (D.gates i).universal_satisfies) v
    rw [ofAlgebraDiagram_inputMap] at hp
    change polynomialInput F P α
      (D.input i (universalSolution (D.gates i).polynomials)) v = _
    rw [← hp]
    simp only [CircuitDiagram.input, projection, CircuitDiagram.copiedMap_generator,
      CircuitDiagram.copy]
    rfl
  apply AlgHom.ext
  intro a
  obtain ⟨p, rfl⟩ := (P j).surjective a
  exact DFunLike.congr_fun h p

end FiniteDiagram

end
end Universality

namespace Universality.SquareZeroGeometry
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite MvPolynomial
set_option backward.isDefEq.respectTransparency false
universe u
variable (R n : Type u) [CommRing R] [Fintype n] [DecidableEq n]

/-! ### Conjugation and its local sections -/

/-- Coordinate algebra of `GL(2n)` over the specified base. -/
abbrev GeneralLinearRing : Type u := Localization.Away (genericMatrix R n).det

def generalLinearScheme : Scheme := Spec (.of (GeneralLinearRing R n))

def generalLinearMatrix : Matrix (n ⊕ n) (n ⊕ n) (GeneralLinearRing R n) :=
  (genericMatrix R n).map (algebraMap (AmbientRing R n) (GeneralLinearRing R n))

theorem generalLinearMatrix_isUnit : IsUnit (generalLinearMatrix R n).det := by
  have hd : algebraMap (AmbientRing R n) (GeneralLinearRing R n) (genericMatrix R n).det =
      (generalLinearMatrix R n).det :=
    (algebraMap (AmbientRing R n) (GeneralLinearRing R n)).map_det _
  rw [← hd]
  exact IsLocalization.Away.algebraMap_isUnit _

def generalLinearUnit : (Matrix (n ⊕ n) (n ⊕ n) (GeneralLinearRing R n))ˣ :=
  Matrix.nonsingInvUnit _ (generalLinearMatrix_isUnit R n)

def conjugateJordan {S : Type*} [CommRing S]
    (g : (Matrix (n ⊕ n) (n ⊕ n) S)ˣ) : Matrix (n ⊕ n) (n ⊕ n) S :=
  g.val * jordanCell * g.inv

theorem conjugateJordan_square {S : Type*} [CommRing S]
    (g : (Matrix (n ⊕ n) (n ⊕ n) S)ˣ) :
    conjugateJordan n g * conjugateJordan n g = 0 :=
  orbit_square_zero ⟨g.val, g.inv, g.val_inv, g.inv_val, rfl⟩

omit [Fintype n] in
@[simp] theorem map_jordanCell {S T : Type*} [CommRing S] [CommRing T] (f : S →+* T) :
    (jordanCell : Matrix (n ⊕ n) (n ⊕ n) S).map f = jordanCell := by
  simp [jordanCell, Matrix.fromBlocks_map]

theorem map_conjugateJordan {S T : Type*} [CommRing S] [CommRing T]
    (f : S →+* T) (g : (Matrix (n ⊕ n) (n ⊕ n) S)ˣ) :
    (conjugateJordan n g).map f =
      conjugateJordan n (Units.map f.mapMatrix.toMonoidHom g) := by
  simp [conjugateJordan, Matrix.map_mul]

/-- The conjugation morphism is defined by the universal invertible matrix. -/
def orbitPolynomialMap : AmbientRing R n →ₐ[R] GeneralLinearRing R n :=
  aeval (fun ij => conjugateJordan n (generalLinearUnit R n) ij.1 ij.2)

theorem orbitPolynomialMap_matrix :
    (genericMatrix R n).map (orbitPolynomialMap R n) =
      conjugateJordan n (generalLinearUnit R n) := by
  ext i j
  simp [genericMatrix, orbitPolynomialMap]

def orbitCoordinateMap : CoordinateRing R n →ₐ[R] GeneralLinearRing R n :=
  Ideal.Quotient.liftₐ _ (orbitPolynomialMap R n) (by
    change squareZeroIdeal R n ≤ RingHom.ker (orbitPolynomialMap R n).toRingHom
    apply Ideal.span_le.mpr
    rintro _ ⟨⟨i, j⟩, rfl⟩
    have h : (genericMatrix R n * genericMatrix R n).map (orbitPolynomialMap R n) = 0 := by
      rw [Matrix.map_mul, orbitPolynomialMap_matrix]
      exact conjugateJordan_square n _
    exact congrFun (congrFun h i) j)

def conjugationToSquareZero : generalLinearScheme R n ⟶ squareZeroScheme R n :=
  Spec.map (CommRingCat.ofHom (orbitCoordinateMap R n).toRingHom)

theorem orbitCoordinateMap_matrix :
    (universalMatrix R n).map (orbitCoordinateMap R n) =
      conjugateJordan n (generalLinearUnit R n) := by
  ext i j
  simp [universalMatrix, genericMatrix, orbitCoordinateMap, orbitPolynomialMap]

def generalLinearEval {S : Type u} [CommRing S] [Algebra R S]
    (g : (Matrix (n ⊕ n) (n ⊕ n) S)ˣ) : GeneralLinearRing R n →ₐ[R] S :=
  awayLift R (genericMatrix R n).det (aeval (fun ij => g.val ij.1 ij.2)) (by
    have hm : (genericMatrix R n).map (aeval (fun ij => g.val ij.1 ij.2) :
        AmbientRing R n →ₐ[R] S) = g.val := by
      ext i j
      simp [genericMatrix]
    have hd : (aeval (fun ij => g.val ij.1 ij.2) : AmbientRing R n →ₐ[R] S)
        (genericMatrix R n).det = g.val.det :=
      (AlgHom.map_det _ _).trans (congrArg Matrix.det hm)
    rw [hd]
    exact (Matrix.isUnit_iff_isUnit_det _).mp g.isUnit)

theorem generalLinearEval_matrix {S : Type u} [CommRing S] [Algebra R S]
    (g : (Matrix (n ⊕ n) (n ⊕ n) S)ˣ) :
    (generalLinearMatrix R n).map (generalLinearEval R n g) = g.val := by
  ext i j
  simp [generalLinearMatrix, genericMatrix, generalLinearEval, awayLift_algebraMap]

theorem generalLinearEval_unit {S : Type u} [CommRing S] [Algebra R S]
    (g : (Matrix (n ⊕ n) (n ⊕ n) S)ˣ) :
    Units.map (generalLinearEval R n g).toRingHom.mapMatrix.toMonoidHom
      (generalLinearUnit R n) = g := by
  apply Units.ext
  exact generalLinearEval_matrix R n g

/-- A regular local section of conjugation on each explicit orbit chart. -/
def chartConjugator (e : Equiv.Perm (n ⊕ n)) :
    (Matrix (n ⊕ n) (n ⊕ n) (ChartRing R n))ˣ where
  val := (generalChartBasis (chartA R n)
    (Matrix.nonsingInvUnit _ (chartT_isUnit R n))).submatrix e.symm id
  inv := (generalChartBasisInv (chartA R n)
    (Matrix.nonsingInvUnit _ (chartT_isUnit R n))).submatrix id e.symm
  val_inv := by
    rw [← Matrix.submatrix_mul _ _ _ id _ Function.bijective_id,
      generalChartBasis_mul_inv]
    exact Matrix.submatrix_one_equiv _
  inv_val := by
    rw [Matrix.submatrix_mul_equiv, generalChartBasis_inv_mul]
    rfl

theorem chartConjugator_conjugation (e : Equiv.Perm (n ⊕ n)) :
    conjugateJordan n (chartConjugator R n e) =
      (generalChart (chartA R n) (chartT R n)).submatrix e.symm e.symm := by
  unfold conjugateJordan chartConjugator
  dsimp only
  have hJ : (jordanCell : Matrix (n ⊕ n) (n ⊕ n) (ChartRing R n)) =
      jordanCell.submatrix id id := rfl
  conv_lhs => arg 1; arg 2; rw [hJ]
  rw [← Matrix.submatrix_mul _ _ _ id _ Function.bijective_id,
    ← Matrix.submatrix_mul _ _ _ id _ Function.bijective_id,
    generalChart_conjugation]
  rfl

def chartSection (e : Equiv.Perm (n ⊕ n)) :
    Spec (.of (ChartRing R n)) ⟶ generalLinearScheme R n :=
  Spec.map (CommRingCat.ofHom (generalLinearEval R n (chartConjugator R n e)).toRingHom)

theorem permutationChartEmbedding_matrix (e : Equiv.Perm (n ⊕ n)) :
    (universalMatrix R n).map (permutationChartEmbedding R n e) =
      (generalChart (chartA R n) (chartT R n)).submatrix e.symm e.symm := by
  ext i j
  simp [universalMatrix, genericMatrix, permutationChartEmbedding, permuteCoordinate,
    permuteAmbient, toChartBase, chartAmbientEval]

/-- Evaluating conjugation at a chart conjugator recovers the chart coordinates. -/
theorem generalLinearEval_comp_orbitCoordinateMap (e : Equiv.Perm (n ⊕ n)) :
    (generalLinearEval R n (chartConjugator R n e)).comp (orbitCoordinateMap R n) =
      permutationChartEmbedding R n e := by
  have h : ((universalMatrix R n).map (orbitCoordinateMap R n)).map
      (generalLinearEval R n (chartConjugator R n e)) =
      (universalMatrix R n).map (permutationChartEmbedding R n e) := by
    rw [orbitCoordinateMap_matrix]
    change (conjugateJordan n (generalLinearUnit R n)).map
      (generalLinearEval R n (chartConjugator R n e)).toRingHom = _
    rw [map_conjugateJordan, generalLinearEval_unit,
      chartConjugator_conjugation, permutationChartEmbedding_matrix]
  apply quotientAlgHom_ext
  intro ij
  exact congrArg (fun M => M ij.1 ij.2) h

theorem chartSection_conjugation (e : Equiv.Perm (n ⊕ n)) :
    chartSection R n e ≫ conjugationToSquareZero R n =
      (permutationChartIso R n e).inv ≫ (permutationOpen R n e).ι := by
  rw [permutationChartIso_inv_ι]
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  exact congrArg AlgHom.toRingHom (generalLinearEval_comp_orbitCoordinateMap R n e)

theorem conjugationToSquareZero_mem_maximalRank (p : generalLinearScheme R n) :
    conjugationToSquareZero R n p ∈ maximalRankOpen R n := by
  let p' : PrimeSpectrum (GeneralLinearRing R n) := p
  let φ := algebraMap (GeneralLinearRing R n) p'.asIdeal.ResidueField
  let g := Units.map φ.mapMatrix.toMonoidHom (generalLinearUnit R n)
  have h := (inJordanOrbit_iff_square_zero_rank (conjugateJordan n g)).mp
    ⟨g.val, g.inv, g.val_inv, g.inv_val, rfl⟩
  obtain ⟨e, he⟩ := square_zero_exists_invertible_coordinate_chart _ h.1 h.2
  apply permutationOpen_le_maximalRank R n e
  change (orbitCoordinateMap R n) ((universalMatrix R n).submatrix e e).toBlocks₁₂.det ∉
    p'.asIdeal
  intro hmem
  have hz := Ideal.algebraMap_residueField_eq_zero.mpr hmem
  have hm : ((universalMatrix R n).map
      (φ.comp (orbitCoordinateMap R n).toRingHom)).submatrix e e =
      (conjugateJordan n g).submatrix e e := by
    change (((universalMatrix R n).map (orbitCoordinateMap R n)).map φ).submatrix e e = _
    rw [orbitCoordinateMap_matrix, map_conjugateJordan]
  have hd : φ ((orbitCoordinateMap R n)
      ((universalMatrix R n).submatrix e e).toBlocks₁₂.det) =
      ((conjugateJordan n g).submatrix e e).toBlocks₁₂.det := by
    exact ((φ.comp (orbitCoordinateMap R n).toRingHom).map_det _).trans
      (congrArg (fun M => M.toBlocks₁₂.det) hm)
  rw [hd] at hz
  rw [hz] at he
  exact not_isUnit_zero he

/-- The conjugation morphism `GL(2n) → O`. -/
def orbitProjection : generalLinearScheme R n ⟶ maximalRankScheme R n := by
  change generalLinearScheme R n ⟶ (maximalRankOpen R n).toScheme
  exact IsOpenImmersion.lift (maximalRankOpen R n).ι (conjugationToSquareZero R n) (by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨p, rfl⟩
    exact conjugationToSquareZero_mem_maximalRank R n p)

@[reassoc (attr := simp)] theorem orbitProjection_ι :
    orbitProjection R n ≫ (maximalRankOpen R n).ι = conjugationToSquareZero R n :=
  IsOpenImmersion.lift_fac _ _ _

theorem orbitChartSection (e : Equiv.Perm (n ⊕ n)) :
    (orbitChartIso R n e).hom ≫ chartSection R n e ≫ orbitProjection R n =
      (orbitChartOpen R n e).ι := by
  apply (cancel_mono (maximalRankOpen R n).ι).mp
  rw [Category.assoc, Category.assoc, orbitProjection_ι,
    chartSection_conjugation, ← Category.assoc]
  simp only [orbitChartIso, Iso.trans_hom, Category.assoc, Iso.hom_inv_id_assoc]
  exact Scheme.Opens.isoOfLE_hom_ι (permutationOpen_le_maximalRank R n e)

/-- The presheaf image of the conjugation morphism. Its fibres are identified below with
right cosets of the explicitly computed stabilizer. -/
def conjugationImage : Subfunctor (yoneda.obj (squareZeroScheme R n)) :=
  Subfunctor.range (yoneda.map (conjugationToSquareZero R n))

def orbitImage : Subfunctor (yoneda.obj (squareZeroScheme R n)) :=
  Subfunctor.range (yoneda.map (maximalRankOpen R n).ι)

theorem conjugationImage_le_orbitImage : conjugationImage R n ≤ orbitImage R n := by
  intro T f hf
  obtain ⟨g, rfl⟩ := hf
  exact ⟨g ≫ orbitProjection R n, by simp⟩

theorem orbitImage_isSheaf :
    Presieve.IsSheaf Scheme.zariskiTopology (orbitImage R n).toFunctor :=
  Presieve.isSheaf_iso _ (asIso (Subfunctor.toRange (yoneda.map (maximalRankOpen R n).ι)))
    (GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable _)

/-- Zariski sheafification of the conjugation image is represented by the orbit scheme. -/
theorem conjugationImage_sheafify :
    (conjugationImage R n).sheafify Scheme.zariskiTopology = orbitImage R n := by
  apply le_antisymm
  · exact (conjugationImage R n).sheafify_le (orbitImage R n) (conjugationImage_le_orbitImage R n)
      (GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable _)
      (orbitImage_isSheaf R n)
  · have hid : (maximalRankOpen R n).ι ∈
        ((conjugationImage R n).sheafify Scheme.zariskiTopology).obj
          (op (maximalRankScheme R n)) := by
      apply Scheme.mem_grothendieckTopology_iff.mpr
      refine ⟨orbitOpenCover R n, ?_⟩
      rintro T f ⟨e⟩
      refine ⟨(orbitChartIso R n e).hom ≫ chartSection R n e, ?_⟩
      change ((orbitChartIso R n e).hom ≫ chartSection R n e) ≫
          conjugationToSquareZero R n = (orbitChartOpen R n e).ι ≫ (maximalRankOpen R n).ι
      rw [← orbitProjection_ι, ← Category.assoc, Category.assoc _ (chartSection R n e),
        orbitChartSection]
    intro T f hf
    obtain ⟨g, rfl⟩ := hf
    exact ((conjugationImage R n).sheafify Scheme.zariskiTopology).map g.op hid

def conjugationSheafIso :
    ((conjugationImage R n).sheafify Scheme.zariskiTopology).toFunctor ≅
      yoneda.obj (maximalRankScheme R n) :=
  { hom := Subfunctor.homOfLe (conjugationImage_sheafify R n).le
    inv := Subfunctor.homOfLe (conjugationImage_sheafify R n).ge
    hom_inv_id := by ext; rfl
    inv_hom_id := by ext; rfl } ≪≫
    (asIso (Subfunctor.toRange (yoneda.map (maximalRankOpen R n).ι))).symm

/-! ### Invertible matrices on arbitrary test schemes -/

/-- Pullback of affine coordinates along a morphism from an arbitrary test scheme. -/
def affineCoordinates {S : Type u} [CommRing S] {T : Scheme.{u}}
    (f : T ⟶ Spec (.of S)) : S →+* Γ(T, ⊤) :=
  ((Scheme.ΓSpecIso (.of S)).inv ≫ f.appTop).hom

theorem affineCoordinates_comp {S : Type u} [CommRing S] {T U : Scheme.{u}}
    (f : T ⟶ U) (g : U ⟶ Spec (.of S)) :
    affineCoordinates (f ≫ g) = f.appTop.hom.comp (affineCoordinates g) := by
  ext s
  simp [affineCoordinates]

theorem affineCoordinates_specMap {S B : Type u} [CommRing S] [CommRing B]
    {T : Scheme.{u}} (f : T ⟶ Spec (.of B)) (φ : S →+* B) :
    affineCoordinates (f ≫ Spec.map (CommRingCat.ofHom φ)) =
      (affineCoordinates f).comp φ := by
  unfold affineCoordinates
  rw [Scheme.Hom.comp_appTop, ← Category.assoc, ← Scheme.ΓSpecIso_inv_naturality]
  rfl

theorem affineCoordinates_injective {S : Type u} [CommRing S] {T : Scheme.{u}} :
    Function.Injective (affineCoordinates (S := S) (T := T)) := by
  intro f g h
  apply ext_to_Spec
  exact CommRingCat.hom_ext h

def pointConjugator {T : Scheme.{u}} (f : T ⟶ generalLinearScheme R n) :
    (Matrix (n ⊕ n) (n ⊕ n) Γ(T, ⊤))ˣ :=
  Units.map (affineCoordinates f).mapMatrix.toMonoidHom (generalLinearUnit R n)

def generalLinearBase {T : Scheme.{u}} (f : T ⟶ generalLinearScheme R n) : R →+* Γ(T, ⊤) :=
  (affineCoordinates f).comp (algebraMap R (GeneralLinearRing R n))

theorem generalLinearHom_ext {T : Scheme.{u}} {f g : T ⟶ generalLinearScheme R n}
    (hb : generalLinearBase R n f = generalLinearBase R n g)
    (hm : pointConjugator R n f = pointConjugator R n g) : f = g := by
  apply affineCoordinates_injective
  apply IsLocalization.ringHom_ext (Submonoid.powers (genericMatrix R n).det)
  apply MvPolynomial.ringHom_ext
  · intro r
    exact DFunLike.congr_fun hb r
  · intro ij
    exact congrArg (fun h : (Matrix (n ⊕ n) (n ⊕ n) Γ(T, ⊤))ˣ => h.val ij.1 ij.2) hm

@[simp] theorem affineCoordinates_toSpec {S : Type u} [CommRing S] (T : Scheme.{u})
    (φ : S →+* Γ(T, ⊤)) :
    affineCoordinates (T.toSpecΓ ≫ Spec.map (CommRingCat.ofHom φ)) = φ := by
  rw [affineCoordinates_specMap]
  change (((Scheme.ΓSpecIso Γ(T, ⊤)).inv ≫ T.toSpecΓ.appTop).hom).comp φ = φ
  rw [Scheme.toSpecΓ_appTop, Iso.inv_hom_id]
  rfl

/-- This affine scheme represents invertible matrices over the global functions of every
test scheme, together with its morphism to the specified base. -/
def generalLinearHomEquiv (T : Scheme.{u}) :
    (T ⟶ generalLinearScheme R n) ≃
      (R →+* Γ(T, ⊤)) × (Matrix (n ⊕ n) (n ⊕ n) Γ(T, ⊤))ˣ where
  toFun f := ⟨generalLinearBase R n f, pointConjugator R n f⟩
  invFun p :=
    letI := p.1.toAlgebra
    T.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (generalLinearEval R n p.2).toRingHom)
  left_inv f := by
    letI := (generalLinearBase R n f).toAlgebra
    dsimp only
    apply generalLinearHom_ext R n
    · unfold generalLinearBase
      rw [affineCoordinates_toSpec]
      ext r
      exact (generalLinearEval R n (pointConjugator R n f)).commutes r
    · unfold pointConjugator
      rw [affineCoordinates_toSpec]
      exact generalLinearEval_unit R n _
  right_inv p := by
    letI := p.1.toAlgebra
    dsimp only
    apply Prod.ext
    · unfold generalLinearBase
      rw [affineCoordinates_toSpec]
      ext r
      exact (generalLinearEval R n p.2).commutes r
    · unfold pointConjugator
      rw [affineCoordinates_toSpec]
      exact generalLinearEval_unit R n _

/-- Coordinates of a morphism into `GL(2n)` obtained by evaluating the universal matrix. -/
theorem generalLinearHomEquiv_comp_eval {S : Type u} [CommRing S] [Algebra R S]
    {T : Scheme.{u}} (f : T ⟶ Spec (.of S)) (g : (Matrix (n ⊕ n) (n ⊕ n) S)ˣ) :
    generalLinearHomEquiv R n T
        (f ≫ Spec.map (CommRingCat.ofHom (generalLinearEval R n g).toRingHom)) =
      ((affineCoordinates f).comp (algebraMap R S),
        Units.map (affineCoordinates f).mapMatrix.toMonoidHom g) := by
  apply Prod.ext
  · change (affineCoordinates (f ≫ Spec.map _)).comp _ = _
    rw [affineCoordinates_specMap]
    ext r
    exact congrArg (affineCoordinates f) ((generalLinearEval R n g).commutes r)
  · change Units.map (affineCoordinates (f ≫ Spec.map _)).mapMatrix.toMonoidHom
      (generalLinearUnit R n) = _
    rw [affineCoordinates_specMap]
    change Units.map (affineCoordinates f).mapMatrix.toMonoidHom
      (Units.map (generalLinearEval R n g).toRingHom.mapMatrix.toMonoidHom
        (generalLinearUnit R n)) = _
    rw [generalLinearEval_unit]

theorem conjugation_coordinates {T : Scheme.{u}} (f : T ⟶ generalLinearScheme R n) :
    (universalMatrix R n).map (affineCoordinates (f ≫ conjugationToSquareZero R n)) =
      conjugateJordan n (pointConjugator R n f) := by
  rw [conjugationToSquareZero, affineCoordinates_specMap]
  change ((universalMatrix R n).map (orbitCoordinateMap R n)).map (affineCoordinates f) = _
  rw [orbitCoordinateMap_matrix, map_conjugateJordan]
  rfl

theorem conjugateJordan_eq_iff {S : Type*} [CommRing S]
    (g h : (Matrix (n ⊕ n) (n ⊕ n) S)ˣ) :
    conjugateJordan n g = conjugateJordan n h ↔
      (g⁻¹ * h).val * jordanCell = jordanCell * (g⁻¹ * h).val := by
  constructor
  · intro he
    have hh := congrArg (fun M => g.inv * M * h.val) he
    simpa [conjugateJordan, mul_assoc] using hh.symm
  · intro he
    have hh := congrArg (fun M => g.val * M * h.inv) he
    simpa [conjugateJordan, mul_assoc] using hh.symm

/-! ### The stabilizer and its cosets -/

/-- The stabilizer as a subgroup of the general linear group. -/
def jordanStabilizer (S : Type*) [CommRing S] :
    Subgroup (Matrix (n ⊕ n) (n ⊕ n) S)ˣ where
  carrier := {g | g.val * jordanCell = jordanCell * g.val}
  one_mem' := by simp
  mul_mem' := by
    intro g h hg hh
    change g.val * h.val * jordanCell = jordanCell * (g.val * h.val)
    rw [mul_assoc, hh, ← mul_assoc, hg, mul_assoc]
  inv_mem' := by
    intro g hg
    have h := congrArg (fun M => g.inv * M * g.inv) hg
    simpa [mul_assoc] using h.symm

theorem mem_jordanStabilizer_iff {S : Type*} [CommRing S]
    (g : (Matrix (n ⊕ n) (n ⊕ n) S)ˣ) :
    g ∈ jordanStabilizer n S ↔
      ∃ P Q : Matrix n n S, IsUnit P ∧ g.val = Matrix.fromBlocks P Q 0 P := by
  exact ⟨fun h => (jordanCell_unit_centralizer_iff g.val).mp ⟨g.isUnit, h⟩,
    fun h => ((jordanCell_unit_centralizer_iff g.val).mpr h).2⟩

/-- Equality in the geometric orbit is exactly equality of the base map and of cosets
for the right stabilizer action, on arbitrary test schemes. -/
theorem conjugation_fibres {T : Scheme.{u}} (f g : T ⟶ generalLinearScheme R n) :
    f ≫ conjugationToSquareZero R n = g ≫ conjugationToSquareZero R n ↔
      generalLinearBase R n f = generalLinearBase R n g ∧
      (pointConjugator R n f)⁻¹ * pointConjugator R n g ∈ jordanStabilizer n Γ(T, ⊤) := by
  have hb (h : T ⟶ generalLinearScheme R n) :
      (affineCoordinates (h ≫ conjugationToSquareZero R n)).comp
        (algebraMap R (CoordinateRing R n)) = generalLinearBase R n h := by
    rw [conjugationToSquareZero, affineCoordinates_specMap]
    ext r
    exact congrArg (affineCoordinates h) ((orbitCoordinateMap R n).commutes r)
  constructor
  · intro h
    constructor
    · rw [← hb f, ← hb g, h]
    · apply (conjugateJordan_eq_iff n _ _).mp
      rw [← conjugation_coordinates R n f, ← conjugation_coordinates R n g, h]
  · rintro ⟨hbase, hcoset⟩
    apply affineCoordinates_injective
    apply Ideal.Quotient.ringHom_ext
    apply MvPolynomial.ringHom_ext
    · intro r
      exact DFunLike.congr_fun ((hb f).trans (hbase.trans (hb g).symm)) r
    · intro ij
      have hm := (conjugation_coordinates R n f).trans
        (((conjugateJordan_eq_iff n _ _).mpr hcoset).trans
          (conjugation_coordinates R n g).symm)
      exact congrFun (congrFun hm ij.1) ij.2

/-- Cosets for the right stabilizer action, with the base morphism held fixed. -/
def stabilizerCosetSetoid (T : Scheme.{u}) : Setoid (T ⟶ generalLinearScheme R n) where
  r f g := generalLinearBase R n f = generalLinearBase R n g ∧
    (pointConjugator R n f)⁻¹ * pointConjugator R n g ∈ jordanStabilizer n Γ(T, ⊤)
  iseqv := ⟨fun f => (conjugation_fibres R n f f).mp rfl,
    fun h => (conjugation_fibres R n _ _).mp ((conjugation_fibres R n _ _).mpr h).symm,
    fun h₁ h₂ => (conjugation_fibres R n _ _).mp
      (((conjugation_fibres R n _ _).mpr h₁).trans ((conjugation_fibres R n _ _).mpr h₂))⟩

theorem stabilizerCosetSetoid_iff {T : Scheme.{u}} (f g : T ⟶ generalLinearScheme R n) :
    stabilizerCosetSetoid R n T f g ↔
      generalLinearBase R n f = generalLinearBase R n g ∧
      (QuotientGroup.mk (pointConjugator R n f) :
        (Matrix (n ⊕ n) (n ⊕ n) Γ(T, ⊤))ˣ ⧸ jordanStabilizer n Γ(T, ⊤)) =
        QuotientGroup.mk (pointConjugator R n g) := by
  rw [QuotientGroup.eq]
  rfl

/-- The naive presheaf `T ↦ GL(2n)(T)/H(T)`. -/
def homogeneousCosets : Scheme.{u}ᵒᵖ ⥤ Type u where
  obj T := Quotient (stabilizerCosetSetoid R n T.unop)
  map α := TypeCat.ofHom (Quotient.map (fun g => α.unop ≫ g) (by
    intro f g h
    apply (conjugation_fibres R n _ _).mp
    simpa only [Category.assoc] using congrArg (fun f => α.unop ≫ f)
      ((conjugation_fibres R n _ _).mpr h)))
  map_id T := by
    ext x
    refine Quotient.inductionOn x ?_
    intro f
    simp
  map_comp α β := by
    ext x
    refine Quotient.inductionOn x ?_
    intro f
    simp [Category.assoc]

def cosetsToConjugationImage : homogeneousCosets R n ⟶ (conjugationImage R n).toFunctor where
  app T := TypeCat.ofHom (Quotient.lift
    (fun f => ⟨f ≫ conjugationToSquareZero R n, ⟨f, rfl⟩⟩)
    (fun f g h => Subtype.ext ((conjugation_fibres R n f g).mpr h)))
  naturality T U α := by
    ext x
    refine Quotient.inductionOn x ?_
    intro f
    apply Subtype.ext
    exact Category.assoc _ _ _

/-- The quotient objects are the usual general-linear-group cosets, one for each base morphism. -/
def homogeneousCosetsEquiv (T : Scheme.{u}) :
    (homogeneousCosets R n).obj (op T) ≃
      (R →+* Γ(T, ⊤)) ×
        ((Matrix (n ⊕ n) (n ⊕ n) Γ(T, ⊤))ˣ ⧸ jordanStabilizer n Γ(T, ⊤)) := by
  let q : (homogeneousCosets R n).obj (op T) →
      (R →+* Γ(T, ⊤)) ×
        ((Matrix (n ⊕ n) (n ⊕ n) Γ(T, ⊤))ˣ ⧸ jordanStabilizer n Γ(T, ⊤)) :=
    Quotient.lift (fun f => ⟨generalLinearBase R n f,
      QuotientGroup.mk (pointConjugator R n f)⟩)
      (fun f g h => Prod.ext h.1 (QuotientGroup.eq.mpr h.2))
  apply Equiv.ofBijective q
  constructor
  · intro x y
    refine Quotient.inductionOn₂ x y ?_
    intro f g h
    apply Quotient.sound
    exact ⟨congrArg Prod.fst h, QuotientGroup.eq.mp (congrArg Prod.snd h)⟩
  · rintro ⟨b, c⟩
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective c
    refine ⟨Quotient.mk _ ((generalLinearHomEquiv R n T).symm ⟨b, g⟩), ?_⟩
    exact congrArg (fun p : (R →+* Γ(T, ⊤)) × (Matrix (n ⊕ n) (n ⊕ n) Γ(T, ⊤))ˣ =>
      (p.1, (QuotientGroup.mk p.2 : _ ⧸ jordanStabilizer n Γ(T, ⊤))))
      ((generalLinearHomEquiv R n T).apply_symm_apply ⟨b, g⟩)

theorem homogeneousCosetsEquiv_mk {T : Scheme.{u}} (g : T ⟶ generalLinearScheme R n) :
    homogeneousCosetsEquiv R n T (Quotient.mk _ g) =
      (generalLinearBase R n g,
        (QuotientGroup.mk (pointConjugator R n g) :
          (Matrix (n ⊕ n) (n ⊕ n) Γ(T, ⊤))ˣ ⧸ jordanStabilizer n Γ(T, ⊤))) := rfl

instance cosetsToConjugationImage_isIso : IsIso (cosetsToConjugationImage R n) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro T
  rw [isIso_iff_bijective]
  constructor
  · intro x y
    refine Quotient.inductionOn₂ x y ?_
    intro f g h
    apply Quotient.sound
    exact (conjugation_fibres R n f g).mp (congrArg Subtype.val h)
  · rintro ⟨f, g, rfl⟩
    exact ⟨Quotient.mk _ g, rfl⟩

def cosetImageIso : homogeneousCosets R n ≅ (conjugationImage R n).toFunctor :=
  asIso (cosetsToConjugationImage R n)

/-! ### The represented sheaf quotient -/

/-- The canonical quotient map into the functor represented by the geometric orbit. -/
def homogeneousQuotientMap : homogeneousCosets R n ⟶ yoneda.obj (maximalRankScheme R n) :=
  (cosetImageIso R n).hom ≫
    Subfunctor.homOfLe ((conjugationImage R n).le_sheafify Scheme.zariskiTopology) ≫
      (conjugationSheafIso R n).hom

theorem conjugationSheafIso_ι :
    (conjugationSheafIso R n).hom ≫ yoneda.map (maximalRankOpen R n).ι =
      ((conjugationImage R n).sheafify Scheme.zariskiTopology).ι := by
  have hι : (asIso (Subfunctor.toRange (yoneda.map (maximalRankOpen R n).ι))).inv ≫
      yoneda.map (maximalRankOpen R n).ι = (orbitImage R n).ι := by
    apply (cancel_epi (Subfunctor.toRange (yoneda.map (maximalRankOpen R n).ι))).mp
    simp only [← Category.assoc, asIso_inv, IsIso.hom_inv_id, Category.id_comp]
    exact (Subfunctor.toRange_ι _).symm
  unfold conjugationSheafIso
  simp only [Iso.trans_hom, Category.assoc, Iso.symm_hom, hι, Subfunctor.homOfLe_ι]

/-- On every representative the quotient map is the conjugation morphism. -/
theorem homogeneousQuotientMap_mk {T : Scheme.{u}} (f : T ⟶ generalLinearScheme R n) :
    (homogeneousQuotientMap R n).app (op T) (Quotient.mk _ f) = f ≫ orbitProjection R n := by
  apply (cancel_mono (maximalRankOpen R n).ι).mp
  have h := congrArg (fun η : homogeneousCosets R n ⟶ yoneda.obj (squareZeroScheme R n) =>
      η.app (op T) (Quotient.mk _ f))
    (show homogeneousQuotientMap R n ≫ yoneda.map (maximalRankOpen R n).ι =
        cosetsToConjugationImage R n ≫ (conjugationImage R n).ι by
      simp only [homogeneousQuotientMap, Category.assoc, conjugationSheafIso_ι,
        Subfunctor.homOfLe_ι]
      rfl)
  simpa only [NatTrans.comp_app, ConcreteCategory.comp_apply, yoneda_map_app,
    Category.assoc, orbitProjection_ι] using h

/-- The representing scheme satisfies the universal property of the Zariski sheaf
quotient by the explicit stabilizer, against every sheaf of sets. -/
theorem homogeneousQuotient_universal (F : Scheme.{u}ᵒᵖ ⥤ Type u)
    (hF : Presieve.IsSheaf Scheme.zariskiTopology F)
    (f : homogeneousCosets R n ⟶ F) :
    ∃! g : yoneda.obj (maximalRankScheme R n) ⟶ F,
      homogeneousQuotientMap R n ≫ g = f := by
  let lift := (conjugationImage R n).sheafifyLift ((cosetImageIso R n).inv ≫ f) hF
  have hfac : Subfunctor.homOfLe
      ((conjugationImage R n).le_sheafify Scheme.zariskiTopology) ≫ lift =
      (cosetImageIso R n).inv ≫ f :=
    (conjugationImage R n).to_sheafifyLift _ hF
  refine ⟨(conjugationSheafIso R n).inv ≫ lift, ?_, ?_⟩
  · simp only [homogeneousQuotientMap, Category.assoc, Iso.hom_inv_id_assoc]
    rw [hfac]
    simp
  · intro g hg
    have he : (conjugationSheafIso R n).hom ≫ g = lift := by
      apply (conjugationImage R n).to_sheafify_lift_unique hF
      rw [hfac]
      apply (cancel_epi (cosetImageIso R n).hom).mp
      simpa only [homogeneousQuotientMap, Category.assoc, Iso.hom_inv_id_assoc] using hg
    rw [← he]
    simp

/-- The same representing scheme is also the fppf sheaf quotient. -/
theorem homogeneousQuotient_fppf_universal (F : Scheme.{u}ᵒᵖ ⥤ Type u)
    (hF : Presieve.IsSheaf Scheme.fppfTopology F)
    (f : homogeneousCosets R n ⟶ F) :
    ∃! g : yoneda.obj (maximalRankScheme R n) ⟶ F,
      homogeneousQuotientMap R n ≫ g = f :=
  homogeneousQuotient_universal R n F
    (Presieve.isSheaf_of_le F
      (Precoverage.toGrothendieck_mono Scheme.zariskiPrecoverage_le_fppfPrecoverage) hF) f

theorem orbit_fppf_isSheaf :
    Presieve.IsSheaf Scheme.fppfTopology (yoneda.obj (maximalRankScheme R n)) :=
  GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable _

end
end Universality.SquareZeroGeometry

namespace Universality.SquareZeroGeometry
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite MvPolynomial
set_option backward.isDefEq.respectTransparency false
universe u
variable (R n : Type u) [CommRing R] [Fintype n] [DecidableEq n]

def chartUnitT : (Matrix n n (ChartRing R n))ˣ :=
  Matrix.nonsingInvUnit _ (chartT_isUnit R n)

def chartEval {S : Type u} [CommRing S] [Algebra R S]
    (A : Matrix n n S) (T : (Matrix n n S)ˣ) : ChartRing R n →ₐ[R] S :=
  awayLift R (chartDet R n)
    (aeval (Sum.elim (fun ij => A ij.1 ij.2) (fun ij => T.val ij.1 ij.2))) (by
      have hm : (universalMatrixB n).map
          (aeval (Sum.elim (fun ij => A ij.1 ij.2) (fun ij => T.val ij.1 ij.2)) :
            ChartPolynomialRing R n →ₐ[R] S) = T.val := by
        ext i j
        simp [universalMatrixB]
      have hd := (AlgHom.map_det
        (aeval (Sum.elim (fun ij => A ij.1 ij.2) (fun ij => T.val ij.1 ij.2)) :
          ChartPolynomialRing R n →ₐ[R] S) (universalMatrixB n)).trans (congrArg Matrix.det hm)
      change IsUnit ((aeval _ : ChartPolynomialRing R n →ₐ[R] S) (universalMatrixB n).det)
      rw [hd]
      exact (Matrix.isUnit_iff_isUnit_det _).mp T.isUnit)

@[simp] theorem chartEval_A {S : Type u} [CommRing S] [Algebra R S]
    (A : Matrix n n S) (T : (Matrix n n S)ˣ) :
    (chartA R n).map (chartEval R n A T) = A := by
  ext i j
  simp [chartA, chartEval, universalMatrixA]

@[simp] theorem chartEval_T {S : Type u} [CommRing S] [Algebra R S]
    (A : Matrix n n S) (T : (Matrix n n S)ˣ) :
    Units.map (chartEval R n A T).toRingHom.mapMatrix.toMonoidHom (chartUnitT R n) = T := by
  apply Units.ext
  change (chartT R n).map (chartEval R n A T) = T.val
  ext i j
  simp [chartT, chartEval, universalMatrixB]

theorem chartRingHom_ext {S : Type u} [CommRing S] {f g : ChartRing R n →+* S}
    (hb : f.comp (algebraMap R (ChartRing R n)) = g.comp (algebraMap R (ChartRing R n)))
    (hA : (chartA R n).map f = (chartA R n).map g)
    (hT : (chartT R n).map f = (chartT R n).map g) : f = g := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (chartDet R n))
  apply MvPolynomial.ringHom_ext
  · intro r
    exact DFunLike.congr_fun hb r
  · rintro (ij | ij)
    · exact congrFun (congrFun hA ij.1) ij.2
    · exact congrFun (congrFun hT ij.1) ij.2

def chartHomEquiv (T : Scheme.{u}) :
    (T ⟶ Spec (.of (ChartRing R n))) ≃
      (R →+* Γ(T, ⊤)) × Matrix n n Γ(T, ⊤) × (Matrix n n Γ(T, ⊤))ˣ where
  toFun f := ((affineCoordinates f).comp (algebraMap R (ChartRing R n)),
    (chartA R n).map (affineCoordinates f),
    Units.map (affineCoordinates f).mapMatrix.toMonoidHom (chartUnitT R n))
  invFun p :=
    letI := p.1.toAlgebra
    T.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (chartEval R n p.2.1 p.2.2).toRingHom)
  left_inv f := by
    letI := ((affineCoordinates f).comp (algebraMap R (ChartRing R n))).toAlgebra
    apply affineCoordinates_injective
    rw [affineCoordinates_toSpec]
    apply chartRingHom_ext R n
    · ext r
      exact (chartEval R n _ _).commutes r
    · exact chartEval_A R n _ _
    · exact congrArg Units.val (chartEval_T R n _ _)
  right_inv p := by
    letI := p.1.toAlgebra
    dsimp only
    rw [affineCoordinates_toSpec]
    apply Prod.ext
    · ext r
      exact (chartEval R n _ _).commutes r
    · exact Prod.ext (chartEval_A R n _ _) (chartEval_T R n _ _)

def stabilizerBlock {S : Type u} [CommRing S]
    (P : (Matrix n n S)ˣ) (Q : Matrix n n S) :
    (Matrix (n ⊕ n) (n ⊕ n) S)ˣ where
  val := Matrix.fromBlocks P.val Q 0 P.val
  inv := Matrix.fromBlocks P.inv (-(P.inv * Q * P.inv)) 0 P.inv
  val_inv := by
    simp [Matrix.fromBlocks_multiply, mul_assoc]
  inv_val := by
    simp [Matrix.fromBlocks_multiply, mul_assoc]

theorem stabilizerBlock_mem {S : Type u} [CommRing S]
    (P : (Matrix n n S)ˣ) (Q : Matrix n n S) :
    stabilizerBlock n P Q ∈ jordanStabilizer n S :=
  (mem_jordanStabilizer_iff n _).mpr ⟨P.val, Q, P.isUnit, rfl⟩

theorem stabilizerBlock_injective {S : Type u} [CommRing S]
    {P P' : (Matrix n n S)ˣ} {Q Q' : Matrix n n S}
    (h : stabilizerBlock n P Q = stabilizerBlock n P' Q') : P = P' ∧ Q = Q' := by
  have hm := congrArg Units.val h
  exact ⟨Units.ext (congrArg Matrix.toBlocks₁₁ hm), congrArg Matrix.toBlocks₁₂ hm⟩

theorem map_stabilizerBlock {S B : Type u} [CommRing S] [CommRing B]
    (f : S →+* B) (P : (Matrix n n S)ˣ) (Q : Matrix n n S) :
    Units.map f.mapMatrix.toMonoidHom (stabilizerBlock n P Q) =
      stabilizerBlock n (Units.map f.mapMatrix.toMonoidHom P) (Q.map f) := by
  apply Units.ext
  simp [stabilizerBlock, Matrix.fromBlocks_map]

/-- Coordinates `(Q,P)` with `det P` inverted represent the explicit stabilizer. -/
def stabilizerScheme : Scheme := Spec (.of (ChartRing R n))

def stabilizerInclusion : stabilizerScheme R n ⟶ generalLinearScheme R n :=
  Spec.map (CommRingCat.ofHom
    (generalLinearEval R n (stabilizerBlock n (chartUnitT R n) (chartA R n))).toRingHom)

theorem stabilizerScheme_dimension : SmoothOfRelativeDimension (2 * Fintype.card n ^ 2)
    (Spec.map (CommRingCat.ofHom (algebraMap R (ChartRing R n)))) := by
  apply (HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension (2 * Fintype.card n ^ 2))).mpr
  exact RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso _
    ((RingHom.isStandardSmoothOfRelativeDimension_algebraMap (2 * Fintype.card n ^ 2)).mpr inferInstance)

theorem stabilizerInclusion_coordinates {T : Scheme.{u}} (f : T ⟶ stabilizerScheme R n) :
    generalLinearHomEquiv R n T (f ≫ stabilizerInclusion R n) =
      ((chartHomEquiv R n T f).1,
        stabilizerBlock n (chartHomEquiv R n T f).2.2 (chartHomEquiv R n T f).2.1) := by
  rw [stabilizerInclusion, generalLinearHomEquiv_comp_eval, map_stabilizerBlock]
  rfl

theorem stabilizerInclusion_hom_injective (T : Scheme.{u}) :
    Function.Injective (fun f : T ⟶ stabilizerScheme R n => f ≫ stabilizerInclusion R n) := by
  intro f g h
  apply (chartHomEquiv R n T).injective
  have he := congrArg (generalLinearHomEquiv R n T) h
  rw [stabilizerInclusion_coordinates, stabilizerInclusion_coordinates] at he
  have hm := stabilizerBlock_injective n (congrArg Prod.snd he)
  have hb := congrArg Prod.fst he
  apply Prod.ext
  · exact hb
  · exact Prod.ext hm.2 hm.1

theorem stabilizerInclusion_range (T : Scheme.{u}) (g : T ⟶ generalLinearScheme R n) :
    (∃ f : T ⟶ stabilizerScheme R n, f ≫ stabilizerInclusion R n = g) ↔
      pointConjugator R n g ∈ jordanStabilizer n Γ(T, ⊤) := by
  constructor
  · rintro ⟨f, rfl⟩
    have he := congrArg Prod.snd (stabilizerInclusion_coordinates R n f)
    change pointConjugator R n (f ≫ stabilizerInclusion R n) = _ at he
    rw [he]
    exact stabilizerBlock_mem n _ _
  · intro hg
    obtain ⟨P, Q, hP, he⟩ := (mem_jordanStabilizer_iff n _).mp hg
    let f := (chartHomEquiv R n T).symm (generalLinearBase R n g, Q, hP.unit)
    refine ⟨f, (generalLinearHomEquiv R n T).injective ?_⟩
    rw [stabilizerInclusion_coordinates]
    dsimp only [f]
    rw [Equiv.apply_symm_apply]
    apply Prod.ext
    · rfl
    apply Units.ext
    simpa [stabilizerBlock] using he.symm

/-- The inverse image of an orbit chart has coordinates for the chart and its stabilizer. -/
abbrev OrbitTrivializationRing := ChartRing (ChartRing R n) n

def orbitTrivializationFst : Spec (.of (OrbitTrivializationRing R n)) ⟶
    Spec (.of (ChartRing R n)) :=
  Spec.map (CommRingCat.ofHom (algebraMap (ChartRing R n) (OrbitTrivializationRing R n)))

def orbitTrivializationUnit (e : Equiv.Perm (n ⊕ n)) :
    (Matrix (n ⊕ n) (n ⊕ n) (OrbitTrivializationRing R n))ˣ :=
  Units.map (algebraMap (ChartRing R n) (OrbitTrivializationRing R n)).mapMatrix.toMonoidHom
    (chartConjugator R n e) *
      stabilizerBlock n (chartUnitT (ChartRing R n) n) (chartA (ChartRing R n) n)

def orbitTrivializationToGL (e : Equiv.Perm (n ⊕ n)) :
    Spec (.of (OrbitTrivializationRing R n)) ⟶ generalLinearScheme R n :=
  Spec.map (CommRingCat.ofHom (generalLinearEval R n (orbitTrivializationUnit R n e)).toRingHom)

theorem orbitTrivialization_coordinates (e : Equiv.Perm (n ⊕ n)) {T : Scheme.{u}}
    (f : T ⟶ Spec (.of (OrbitTrivializationRing R n))) :
    generalLinearHomEquiv R n T (f ≫ orbitTrivializationToGL R n e) =
      ((chartHomEquiv (ChartRing R n) n T f).1.comp (algebraMap R (ChartRing R n)),
        Units.map (chartHomEquiv (ChartRing R n) n T f).1.mapMatrix.toMonoidHom
          (chartConjugator R n e) *
        stabilizerBlock n (chartHomEquiv (ChartRing R n) n T f).2.2
          (chartHomEquiv (ChartRing R n) n T f).2.1) := by
  rw [orbitTrivializationToGL, generalLinearHomEquiv_comp_eval,
    orbitTrivializationUnit, map_mul, map_stabilizerBlock]
  rfl

theorem chartSection_coordinates (e : Equiv.Perm (n ⊕ n)) {T : Scheme.{u}}
    (f : T ⟶ Spec (.of (ChartRing R n))) :
    generalLinearHomEquiv R n T (f ≫ chartSection R n e) =
      ((affineCoordinates f).comp (algebraMap R (ChartRing R n)),
        Units.map (affineCoordinates f).mapMatrix.toMonoidHom (chartConjugator R n e)) := by
  exact generalLinearHomEquiv_comp_eval R n f (chartConjugator R n e)

set_option maxHeartbeats 800000 in
theorem orbitTrivialization_condition (e : Equiv.Perm (n ⊕ n)) :
    orbitTrivializationFst R n ≫ chartSection R n e ≫ orbitProjection R n =
      orbitTrivializationToGL R n e ≫ orbitProjection R n := by
  apply (cancel_mono (maximalRankOpen R n).ι).mp
  simp only [Category.assoc, orbitProjection_ι]
  rw [← Category.assoc]
  apply (conjugation_fibres R n _ _).mpr
  have hf := chartSection_coordinates R n e (orbitTrivializationFst R n)
  have hg := orbitTrivialization_coordinates R n e (𝟙 _)
  simp only [Category.id_comp] at hg
  have hbase : affineCoordinates (orbitTrivializationFst R n) =
      (chartHomEquiv (ChartRing R n) n _ (𝟙 _)).1 := by
    change affineCoordinates (Spec.map _) = (affineCoordinates (𝟙 _)).comp _
    simpa using affineCoordinates_specMap (𝟙 (Spec (.of (OrbitTrivializationRing R n))))
      (algebraMap (ChartRing R n) (OrbitTrivializationRing R n))
  rw [hbase] at hf
  constructor
  · exact (congrArg Prod.fst hf).trans (congrArg Prod.fst hg).symm
  · have hfm := congrArg Prod.snd hf
    have hgm := congrArg Prod.snd hg
    simp only [generalLinearHomEquiv, Equiv.coe_fn_mk] at hfm hgm
    rw [hfm, hgm, inv_mul_cancel_left]
    exact stabilizerBlock_mem n _ _

theorem orbitTrivialization_hom_ext (e : Equiv.Perm (n ⊕ n)) {T : Scheme.{u}}
    {f g : T ⟶ Spec (.of (OrbitTrivializationRing R n))}
    (ha : f ≫ orbitTrivializationFst R n = g ≫ orbitTrivializationFst R n)
    (hg : f ≫ orbitTrivializationToGL R n e = g ≫ orbitTrivializationToGL R n e) : f = g := by
  have hb := congrArg affineCoordinates ha
  simp only [orbitTrivializationFst, affineCoordinates_specMap] at hb
  change (chartHomEquiv (ChartRing R n) n T f).1 =
    (chartHomEquiv (ChartRing R n) n T g).1 at hb
  have hcoords := congrArg (generalLinearHomEquiv R n T) hg
  rw [orbitTrivialization_coordinates, orbitTrivialization_coordinates] at hcoords
  have hm := congrArg Prod.snd hcoords
  dsimp only at hm
  rw [hb] at hm
  have he := stabilizerBlock_injective n (mul_left_cancel hm)
  apply (chartHomEquiv (ChartRing R n) n T).injective
  exact Prod.ext hb (Prod.ext he.2 he.1)

theorem orbitTrivialization_isPullback (e : Equiv.Perm (n ⊕ n)) :
    IsPullback (orbitTrivializationFst R n) (orbitTrivializationToGL R n e)
      (chartSection R n e ≫ orbitProjection R n) (orbitProjection R n) where
  w := orbitTrivialization_condition R n e
  isLimit' := ⟨PullbackCone.isLimitAux' _ fun s => by
    apply Classical.choice
    have hc : (s.fst ≫ chartSection R n e) ≫ conjugationToSquareZero R n =
        s.snd ≫ conjugationToSquareZero R n := by
      have h := congrArg (fun f => f ≫ (maximalRankOpen R n).ι) s.condition
      simpa only [Category.assoc, orbitProjection_ι] using h
    have hf := (conjugation_fibres R n _ _).mp hc
    obtain ⟨P, Q, hP, hPQ⟩ := (mem_jordanStabilizer_iff n _).mp hf.2
    let l := (chartHomEquiv (ChartRing R n) n s.pt).symm (affineCoordinates s.fst, Q, hP.unit)
    have hl₁ : l ≫ orbitTrivializationFst R n = s.fst := by
      apply affineCoordinates_injective
      rw [orbitTrivializationFst, affineCoordinates_specMap]
      change (chartHomEquiv (ChartRing R n) n s.pt l).1 = _
      dsimp only [l]
      rw [Equiv.apply_symm_apply]
    have hl₂ : l ≫ orbitTrivializationToGL R n e = s.snd := by
      apply (generalLinearHomEquiv R n s.pt).injective
      rw [orbitTrivialization_coordinates]
      dsimp only [l]
      rw [Equiv.apply_symm_apply]
      have hs := chartSection_coordinates R n e s.fst
      have hsb := congrArg Prod.fst hs
      have hsm := congrArg Prod.snd hs
      apply Prod.ext
      · exact hsb.symm.trans hf.1
      · have hp : stabilizerBlock n hP.unit Q =
            (pointConjugator R n (s.fst ≫ chartSection R n e))⁻¹ * pointConjugator R n s.snd := by
          apply Units.ext
          simpa [stabilizerBlock] using hPQ.symm
        dsimp only
        rw [hp]
        change pointConjugator R n (s.fst ≫ chartSection R n e) = _ at hsm
        simp only at hsm
        rw [← hsm]
        exact mul_inv_cancel_left _ _
    exact ⟨⟨l, hl₁, hl₂, fun hm₁ hm₂ =>
      orbitTrivialization_hom_ext R n e (hm₁.trans hl₁.symm) (hm₂.trans hl₂.symm)⟩⟩⟩

theorem orbitTrivializationOpen_isPullback (e : Equiv.Perm (n ⊕ n)) :
    IsPullback (orbitTrivializationFst R n ≫ (orbitChartIso R n e).inv)
      (orbitTrivializationToGL R n e) (orbitChartOpen R n e).ι (orbitProjection R n) := by
  apply (orbitTrivialization_isPullback R n e).of_iso
    (Iso.refl _) (orbitChartIso R n e).symm (Iso.refl _) (Iso.refl _)
  · simp
  · simp
  · simp only [Iso.symm_hom]
    apply (cancel_epi (orbitChartIso R n e).hom).mp
    simpa only [Category.assoc, Iso.hom_inv_id_assoc] using orbitChartSection R n e
  · simp

/-- Conjugation is smooth of relative dimension `2n²`, with the explicit stabilizer as fibre. -/
theorem orbitProjection_dimension : SmoothOfRelativeDimension (2 * Fintype.card n ^ 2)
    (orbitProjection R n) := by
  apply IsZariskiLocalAtTarget.of_openCover (P := @SmoothOfRelativeDimension (2 * Fintype.card n ^ 2))
    (orbitOpenCover R n)
  intro e
  change SmoothOfRelativeDimension (2 * Fintype.card n ^ 2)
    (pullback.snd (orbitProjection R n) (orbitChartOpen R n e).ι)
  rw [← (orbitTrivializationOpen_isPullback R n e).flip.isoPullback_inv_snd]
  apply IsZariskiLocalAtSource.comp
  have hd : SmoothOfRelativeDimension (2 * Fintype.card n ^ 2) (orbitTrivializationFst R n) :=
    stabilizerScheme_dimension (ChartRing R n) n
  exact (MorphismProperty.cancel_right_of_respectsIso
    (@SmoothOfRelativeDimension (2 * Fintype.card n ^ 2)) _ _).mpr hd

theorem orbitProjection_smooth : Smooth (orbitProjection R n) := by
  letI := orbitProjection_dimension R n
  exact SmoothOfRelativeDimension.smooth (2 * Fintype.card n ^ 2) _

theorem orbitProjection_surjective : Surjective (orbitProjection R n) := by
  constructor
  intro x
  have hx : x ∈ (⨆ e, orbitChartOpen R n e) := by rw [orbitChart_cover]; trivial
  obtain ⟨e, he⟩ := (TopologicalSpace.Opens.mem_iSup.mp hx)
  refine ⟨((orbitChartIso R n e).hom ≫ chartSection R n e) ⟨x, he⟩, ?_⟩
  exact congrArg (fun f => f ⟨x, he⟩) (orbitChartSection R n e)

/-- Faithful flatness of the quotient morphism, expressed as flat and surjective. -/
theorem orbitProjection_faithfullyFlat : Flat (orbitProjection R n) ∧ Surjective (orbitProjection R n) := by
  letI := orbitProjection_smooth R n
  exact ⟨inferInstance, orbitProjection_surjective R n⟩

def stabilizerOver : Over (Spec (.of R)) :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R (ChartRing R n))))

theorem stabilizerInclusion_base {T : Scheme.{u}} (f : T ⟶ stabilizerScheme R n) :
    generalLinearBase R n (f ≫ stabilizerInclusion R n) =
      affineCoordinates (f ≫ (stabilizerOver R n).hom) := by
  have h := congrArg Prod.fst (stabilizerInclusion_coordinates R n f)
  change _ = affineCoordinates (f ≫ Spec.map (CommRingCat.ofHom (algebraMap R (ChartRing R n))))
  rw [affineCoordinates_specMap]
  exact h

def stabilizerGroupFunctor : (Over (Spec (.of R)))ᵒᵖ ⥤ GrpCat.{u} where
  obj T := GrpCat.of (jordanStabilizer n Γ(T.unop.left, ⊤))
  map α := GrpCat.ofHom {
    toFun g := ⟨Units.map α.unop.left.appTop.hom.mapMatrix.toMonoidHom g.val, by
      have h := congrArg (fun M => M.map α.unop.left.appTop.hom) g.property
      simpa only [Matrix.map_mul, map_jordanCell] using h⟩
    map_one' := by apply Subtype.ext; exact map_one _
    map_mul' := by intro g h; apply Subtype.ext; exact map_mul _ _ _ }
  map_id T := by
    apply GrpCat.hom_ext
    apply MonoidHom.ext
    intro g
    apply Subtype.ext
    apply Units.ext
    ext i j
    simp
  map_comp α β := by
    apply GrpCat.hom_ext
    apply MonoidHom.ext
    intro g
    apply Subtype.ext
    apply Units.ext
    ext i j
    simp

def stabilizerOverPoint {T : Over (Spec (.of R))} (f : T ⟶ stabilizerOver R n) :
    jordanStabilizer n Γ(T.left, ⊤) :=
  ⟨pointConjugator R n (f.left ≫ stabilizerInclusion R n),
    (stabilizerInclusion_range R n T.left _).mp ⟨f.left, rfl⟩⟩

theorem stabilizerOverPoint_bijective (T : Over (Spec (.of R))) :
    Function.Bijective (stabilizerOverPoint R n (T := T)) := by
  constructor
  · intro f g h
    apply Over.OverMorphism.ext
    apply stabilizerInclusion_hom_injective R n T.left
    apply generalLinearHom_ext R n
    · rw [stabilizerInclusion_base, stabilizerInclusion_base, Over.w, Over.w]
    · exact congrArg Subtype.val h
  · intro h
    let g := (generalLinearHomEquiv R n T.left).symm (affineCoordinates T.hom, h.val)
    have hg := (generalLinearHomEquiv R n T.left).apply_symm_apply (affineCoordinates T.hom, h.val)
    have hgm : pointConjugator R n g = h.val := congrArg Prod.snd hg
    have hgb : generalLinearBase R n g = affineCoordinates T.hom := congrArg Prod.fst hg
    obtain ⟨f, hf⟩ := (stabilizerInclusion_range R n T.left g).mpr (hgm.symm ▸ h.property)
    have hb : f ≫ (stabilizerOver R n).hom = T.hom := by
      apply affineCoordinates_injective
      rw [← stabilizerInclusion_base, hf, hgb]
    refine ⟨Over.homMk f hb, ?_⟩
    apply Subtype.ext
    change pointConjugator R n (f ≫ stabilizerInclusion R n) = h.val
    rw [hf, hgm]

def stabilizerRepresentableBy :
    (stabilizerGroupFunctor R n ⋙ forget _).RepresentableBy (stabilizerOver R n) where
  homEquiv := Equiv.ofBijective (stabilizerOverPoint R n) (stabilizerOverPoint_bijective R n _)
  homEquiv_comp f g := by
    apply Subtype.ext
    apply Units.ext
    change (generalLinearUnit R n).val.map
      (affineCoordinates ((f ≫ g).left ≫ stabilizerInclusion R n)) =
        ((generalLinearUnit R n).val.map
          (affineCoordinates (g.left ≫ stabilizerInclusion R n))).map f.left.appTop.hom
    rw [show (f ≫ g).left ≫ stabilizerInclusion R n =
      f.left ≫ (g.left ≫ stabilizerInclusion R n) from Category.assoc _ _ _, affineCoordinates_comp]
    rfl

/-- The represented stabilizer is a group scheme over the specified commutative base. -/
@[implicit_reducible] def stabilizerGroupScheme : GrpObj (stabilizerOver R n) :=
  GrpObj.ofRepresentableBy _ (stabilizerGroupFunctor R n) (stabilizerRepresentableBy R n)

abbrev MatrixCoordinateRing := MvPolynomial (n × n) R

def smallGenericMatrix : Matrix n n (MatrixCoordinateRing R n) := fun i j => X (i, j)

abbrev SmallGeneralLinearRing := Localization.Away (smallGenericMatrix R n).det

def smallGeneralLinearUnit : (Matrix n n (SmallGeneralLinearRing R n))ˣ :=
  Matrix.nonsingInvUnit ((smallGenericMatrix R n).map (algebraMap _ _)) (by
    have hd : algebraMap (MatrixCoordinateRing R n) (SmallGeneralLinearRing R n)
        (smallGenericMatrix R n).det =
          ((smallGenericMatrix R n).map (algebraMap _ (SmallGeneralLinearRing R n))).det :=
      (algebraMap (MatrixCoordinateRing R n) (SmallGeneralLinearRing R n)).map_det _
    rw [← hd]
    exact IsLocalization.Away.algebraMap_isUnit _)

def stabilizerDiagonal : SmallGeneralLinearRing R n →ₐ[R] ChartRing R n :=
  awayLift R (smallGenericMatrix R n).det (aeval (fun ij => chartT R n ij.1 ij.2)) (by
    have hm : (smallGenericMatrix R n).map
        (aeval (fun ij => chartT R n ij.1 ij.2) : MatrixCoordinateRing R n →ₐ[R] ChartRing R n) =
          chartT R n := by ext i j; simp [smallGenericMatrix]
    have hd := (AlgHom.map_det
      (aeval (fun ij => chartT R n ij.1 ij.2) : MatrixCoordinateRing R n →ₐ[R] ChartRing R n)
        (smallGenericMatrix R n)).trans (congrArg Matrix.det hm)
    rw [hd]
    exact chartT_isUnit R n)

def stabilizerUpper : MatrixCoordinateRing R n →ₐ[R] ChartRing R n :=
  aeval (fun ij => chartA R n ij.1 ij.2)

theorem stabilizerProduct_isPushout :
    IsPushout (CommRingCat.ofHom (algebraMap R (SmallGeneralLinearRing R n)))
      (CommRingCat.ofHom (algebraMap R (MatrixCoordinateRing R n)))
      (CommRingCat.ofHom (stabilizerDiagonal R n).toRingHom)
      (CommRingCat.ofHom (stabilizerUpper R n).toRingHom) where
  w := by
    ext r
    exact ((stabilizerDiagonal R n).commutes r).trans ((stabilizerUpper R n).commutes r).symm
  isColimit' := ⟨PushoutCocone.isColimitAux' _ fun s => by
    let b := s.inl.hom.comp (algebraMap R (SmallGeneralLinearRing R n))
    letI := b.toAlgebra
    let P := Units.map s.inl.hom.mapMatrix.toMonoidHom (smallGeneralLinearUnit R n)
    let Q := (smallGenericMatrix R n).map s.inr.hom
    let L := chartEval R n Q P
    have hb (r : R) : s.inl.hom (algebraMap R (SmallGeneralLinearRing R n) r) =
        s.inr.hom (algebraMap R (MatrixCoordinateRing R n) r) :=
      congrArg (fun f => f.hom r) s.condition
    have hT : (chartT R n).map L = P.val := congrArg Units.val (chartEval_T R n Q P)
    have hA : (chartA R n).map L = Q := chartEval_A R n Q P
    have h₁ : CommRingCat.ofHom (stabilizerDiagonal R n).toRingHom ≫
        CommRingCat.ofHom L.toRingHom = s.inl := by
      apply CommRingCat.hom_ext
      apply IsLocalization.ringHom_ext (Submonoid.powers (smallGenericMatrix R n).det)
      apply MvPolynomial.ringHom_ext
      · intro r
        change L ((stabilizerDiagonal R n) (algebraMap R _ r)) = _
        rw [AlgHom.commutes, L.commutes]
        rfl
      · intro ij
        change L ((stabilizerDiagonal R n) (algebraMap _ _ (X ij))) = _
        rw [stabilizerDiagonal, awayLift_algebraMap, aeval_X]
        exact congrFun (congrFun hT ij.1) ij.2
    have h₂ : CommRingCat.ofHom (stabilizerUpper R n).toRingHom ≫
        CommRingCat.ofHom L.toRingHom = s.inr := by
      apply CommRingCat.hom_ext
      apply MvPolynomial.ringHom_ext
      · intro r
        change L ((stabilizerUpper R n) (C r)) = _
        rw [stabilizerUpper, aeval_C, L.commutes]
        exact hb r
      · intro ij
        change L ((stabilizerUpper R n) (X ij)) = _
        rw [stabilizerUpper, aeval_X]
        exact congrFun (congrFun hA ij.1) ij.2
    refine ⟨CommRingCat.ofHom L.toRingHom, h₁, h₂, ?_⟩
    intro m hm₁ hm₂
    apply CommRingCat.hom_ext
    apply chartRingHom_ext R n
    · ext r
      have hm := congrArg (fun f => f.hom (algebraMap R (SmallGeneralLinearRing R n) r)) hm₁
      change m.hom ((stabilizerDiagonal R n) (algebraMap R _ r)) = _ at hm
      rw [AlgHom.commutes] at hm
      exact hm.trans (L.commutes r).symm
    · ext i j
      have hm := congrArg (fun f => f.hom (X (i, j))) hm₂
      change m.hom ((stabilizerUpper R n) (X (i, j))) = _ at hm
      rw [stabilizerUpper, aeval_X] at hm
      exact hm.trans (congrFun (congrFun hA i) j).symm
    · ext i j
      have hm := congrArg (fun f => f.hom (algebraMap (MatrixCoordinateRing R n)
        (SmallGeneralLinearRing R n) (X (i, j)))) hm₁
      change m.hom ((stabilizerDiagonal R n) (algebraMap _ _ (X (i, j)))) = _ at hm
      rw [stabilizerDiagonal, awayLift_algebraMap, aeval_X] at hm
      exact hm.trans (congrFun (congrFun hT i) j).symm⟩

/-- As a scheme, the stabilizer is exactly `GL(n) ×_R M(n)`. -/
def stabilizerProductIso : stabilizerScheme R n ≅
    pullback
      (Spec.map (CommRingCat.ofHom (algebraMap R (SmallGeneralLinearRing R n))))
      (Spec.map (CommRingCat.ofHom (algebraMap R (MatrixCoordinateRing R n)))) :=
  (isPullback_SpecMap_of_isPushout _ _ _ _ (stabilizerProduct_isPushout R n)).isoPullback

end
end Universality.SquareZeroGeometry
