import Mathlib.Data.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.LinearAlgebra.AffineSpace.AffineMap
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.CategoryTheory.Types.Basic
namespace Universality
noncomputable section

/-- An affine equation with explicitly finitely many coefficients. -/
structure AffineEquation (R : Type*) (W : Type*) where
  constant : R
  coeff : W → R

namespace AffineEquation
variable {R W S : Type*} [CommRing R] [CommRing S] [Algebra R S] [Fintype W]
def eval (e : AffineEquation R W) (w : W → S) : S :=
  algebraMap R S e.constant + ∑ i, algebraMap R S (e.coeff i) * w i

def zero : AffineEquation R W := ⟨0, fun _ => 0⟩
def constantForm (c : R) : AffineEquation R W := ⟨c, fun _ => 0⟩
def coordinate [DecidableEq W] (i : W) : AffineEquation R W :=
  ⟨0, fun j => if j = i then 1 else 0⟩
def sub (a b : AffineEquation R W) : AffineEquation R W :=
  ⟨a.constant - b.constant, fun j => a.coeff j - b.coeff j⟩
def add (a b : AffineEquation R W) : AffineEquation R W :=
  ⟨a.constant + b.constant, fun j => a.coeff j + b.coeff j⟩

@[simp] theorem eval_zero (w : W → S) : (zero : AffineEquation R W).eval w = 0 := by
  simp [zero, eval]
@[simp] theorem eval_constantForm (c : R) (w : W → S) :
    (constantForm c : AffineEquation R W).eval w = algebraMap R S c := by
  simp [constantForm, eval]
@[simp] theorem eval_coordinate [DecidableEq W] (i : W) (w : W → S) :
    (coordinate i : AffineEquation R W).eval w = w i := by
  simp [coordinate, eval, apply_ite]
@[simp] theorem eval_sub (a b : AffineEquation R W) (w : W → S) :
    (a.sub b).eval w = a.eval w - b.eval w := by
  simp [sub, eval, sub_mul, Finset.sum_sub_distrib]
  abel
@[simp] theorem eval_add (a b : AffineEquation R W) (w : W → S) :
    (a.add b).eval w = a.eval w + b.eval w := by
  simp [add, eval, add_mul, Finset.sum_add_distrib]
  abel
end AffineEquation

/-- A finite arithmetic gate presentation. -/
structure GateSystem (R : Type*) (W G E : Type*) where
  left : G → W
  right : G → W
  output : G → W
  equations : E → AffineEquation R W

namespace GateSystem
variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
variable {W G E : Type*} [Fintype W] [DecidableEq W] [Fintype G] [DecidableEq G]
abbrev Index (W G : Type*) := W ⊕ (Fin 2 × G)

omit [DecidableEq W] [DecidableEq G] in
@[simp] theorem card_index : Fintype.card (Index W G) =
    Fintype.card W + 2 * Fintype.card G := by
  simp [Index]

def gateBlock (a b : S) : Matrix (Fin 2) (Fin 2) S := !![0, a; b, 0]

@[simp] theorem gateBlock_square (a b : S) :
    gateBlock a b * gateBlock a b = Matrix.diagonal ![a*b, a*b] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [gateBlock, Matrix.mul_apply, Fin.sum_univ_two, mul_comm]

def assemble (C : GateSystem R W G E) (w : W → S) :
    Matrix (Index W G) (Index W G) S :=
  Matrix.fromBlocks (Matrix.diagonal w) 0 0
    (Matrix.blockDiagonal fun g => gateBlock (w (C.left g)) (w (C.right g)))

def wires (A : Matrix (Index W G) (Index W G) S) : W → S :=
  fun i => A (Sum.inl i) (Sum.inl i)

omit [CommRing R] [Algebra R S] [Fintype W] [Fintype G] in
@[simp] theorem wires_assemble (C : GateSystem R W G E) (w : W → S) :
    wires (C.assemble w) = w := by
  funext i
  simp [wires, assemble]

omit [CommRing R] [Algebra R S] in
@[simp] theorem assemble_square_gate (C : GateSystem R W G E) (w : W → S) (g : G) :
    (C.assemble w * C.assemble w) (Sum.inr (0,g)) (Sum.inr (0,g)) =
      w (C.left g) * w (C.right g) := by
  simp [assemble, Matrix.fromBlocks_multiply, ← Matrix.blockDiagonal_mul,
    gateBlock_square]

/-- Original scalar gate equations, before matrix compilation. -/
def Satisfies (C : GateSystem R W G E) (w : W → S) : Prop :=
  (∀ q, (C.equations q).eval w = 0) ∧
  ∀ g, w (C.output g) = w (C.left g) * w (C.right g)

/-- Only affine equations: fixed block pattern, affine input equations, and copies of B entries. -/
def LinearSection (C : GateSystem R W G E)
    (A B : Matrix (Index W G) (Index W G) S) : Prop :=
  A = C.assemble (wires A) ∧
  (∀ q, (C.equations q).eval (wires A) = 0) ∧
  ∀ g, wires A (C.output g) = B (Sum.inr (0,g)) (Sum.inr (0,g))

/-- Exact reconstruction over every commutative R-algebra, including nonreduced ones. -/
theorem linearSection_square_iff (C : GateSystem R W G E)
    (A B : Matrix (Index W G) (Index W G) S) :
    C.LinearSection A B ∧ B = A * A ↔
      ∃ w, C.Satisfies w ∧ A = C.assemble w ∧ B = C.assemble w * C.assemble w := by
  constructor
  · rintro ⟨⟨hA, he, hg⟩, hB⟩
    refine ⟨wires A, ⟨he, ?_⟩, hA, ?_⟩
    · intro g
      rw [hg g, hB, hA, assemble_square_gate, wires_assemble]
    · rw [hB, hA, wires_assemble]
  · rintro ⟨w, ⟨he, hg⟩, rfl, rfl⟩
    simpa only [LinearSection, wires_assemble, assemble_square_gate, true_and,
      and_true, eq_self_iff_true] using And.intro he hg

/-- Wire extraction is inverse to assembly: there are no free auxiliary coordinates. -/
def solutionEquiv (C : GateSystem R W G E) :
    {w : W → S // C.Satisfies w} ≃
    {p : Matrix (Index W G) (Index W G) S × Matrix (Index W G) (Index W G) S //
      C.LinearSection p.1 p.2 ∧ p.2 = p.1 * p.1} where
  toFun w := ⟨(C.assemble w.val, C.assemble w.val * C.assemble w.val),
    (C.linearSection_square_iff _ _).mpr ⟨w.val, w.property, rfl, rfl⟩⟩
  invFun p := ⟨wires p.val.1, by
    rcases p.property with ⟨⟨hA, he, hg⟩, hB⟩
    refine ⟨he, fun g => ?_⟩
    rw [hg g, hB, hA, assemble_square_gate, wires_assemble]⟩
  left_inv w := by apply Subtype.ext; exact wires_assemble C w.val
  right_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · exact p.property.1.1.symm
    · change C.assemble (wires p.val.1) * C.assemble (wires p.val.1) = p.val.2
      rw [← p.property.1.1, p.property.2]

end GateSystem

/-- Arithmetic syntax is finite by construction. -/
inductive ArithmeticExpr (R V : Type*)
  | const : R → ArithmeticExpr R V
  | var : V → ArithmeticExpr R V
  | add : ArithmeticExpr R V → ArithmeticExpr R V → ArithmeticExpr R V
  | mul : ArithmeticExpr R V → ArithmeticExpr R V → ArithmeticExpr R V
  deriving DecidableEq

namespace ArithmeticExpr
variable {R V S : Type*} [CommRing R] [CommRing S] [Algebra R S]

def eval (x : V → S) : ArithmeticExpr R V → S
  | .const c => algebraMap R S c
  | .var i => x i
  | .add a b => a.eval x + b.eval x
  | .mul a b => a.eval x * b.eval x

def polynomial : ArithmeticExpr R V → MvPolynomial V R
  | .const c => MvPolynomial.C c
  | .var i => MvPolynomial.X i
  | .add a b => a.polynomial + b.polynomial
  | .mul a b => a.polynomial * b.polynomial

theorem eval_polynomial (t : ArithmeticExpr R V) (x : V → S) :
    MvPolynomial.eval₂ (algebraMap R S) x t.polynomial = t.eval x := by
  induction t <;> simp_all [polynomial, eval]

/-- The circuit evaluator commutes with every homomorphism of test algebras. -/
theorem eval_natural {T : Type*} [CommRing T] [Algebra R T]
    (φ : S →ₐ[R] T) (t : ArithmeticExpr R V) (x : V → S) :
    φ (t.eval x) = t.eval (fun i => φ (x i)) := by
  induction t <;> simp_all [eval]

theorem polynomial_surjective : Function.Surjective (polynomial : ArithmeticExpr R V → _) := by
  intro p
  induction p using MvPolynomial.induction_on with
  | C c => exact ⟨.const c, rfl⟩
  | add p q hp hq =>
    obtain ⟨a, rfl⟩ := hp
    obtain ⟨b, rfl⟩ := hq
    exact ⟨.add a b, rfl⟩
  | mul_X p i hp =>
    obtain ⟨a, rfl⟩ := hp
    exact ⟨.mul a (.var i), rfl⟩

variable [DecidableEq R] [DecidableEq V]
def subterms : ArithmeticExpr R V → Finset (ArithmeticExpr R V)
  | .const c => {.const c}
  | .var i => {.var i}
  | .add a b => insert (.add a b) (a.subterms ∪ b.subterms)
  | .mul a b => insert (.mul a b) (a.subterms ∪ b.subterms)

omit [CommRing R] in
@[simp] theorem mem_subterms (t : ArithmeticExpr R V) : t ∈ t.subterms := by
  cases t <;> simp [subterms]

omit [CommRing R] in
theorem subterms_trans {a b : ArithmeticExpr R V} (h : a ∈ b.subterms) :
    a.subterms ⊆ b.subterms := by
  induction b with
  | const c =>
    have : a = .const c := by simpa [subterms] using h
    subst a
    exact Finset.Subset.refl _
  | var i =>
    have : a = .var i := by simpa [subterms] using h
    subst a
    exact Finset.Subset.refl _
  | add b c hb hc =>
    simp only [subterms, Finset.mem_insert, Finset.mem_union] at h
    rcases h with rfl | h | h
    · exact Finset.Subset.refl _
    · intro t ht
      simp only [subterms, Finset.mem_insert, Finset.mem_union]
      exact Or.inr (Or.inl (hb h ht))
    · intro t ht
      simp only [subterms, Finset.mem_insert, Finset.mem_union]
      exact Or.inr (Or.inr (hc h ht))
  | mul b c hb hc =>
    simp only [subterms, Finset.mem_insert, Finset.mem_union] at h
    rcases h with rfl | h | h
    · exact Finset.Subset.refl _
    · intro t ht
      simp only [subterms, Finset.mem_insert, Finset.mem_union]
      exact Or.inr (Or.inl (hb h ht))
    · intro t ht
      simp only [subterms, Finset.mem_insert, Finset.mem_union]
      exact Or.inr (Or.inr (hc h ht))

end ArithmeticExpr

/-- A finite subterm-closed collection of expressions with designated zero outputs. -/
structure ExpressionPresentation (R V Q : Type*) [Zero R] [DecidableEq R] [DecidableEq V] where
  nodes : Finset (ArithmeticExpr R V)
  closed : ∀ t ∈ nodes, t.subterms ⊆ nodes
  zero_mem : ArithmeticExpr.const 0 ∈ nodes
  var_mem : ∀ i, ArithmeticExpr.var i ∈ nodes
  roots : Q → ArithmeticExpr R V
  root_mem : ∀ q, roots q ∈ nodes

namespace ExpressionPresentation
variable {R V Q S : Type*} [CommRing R] [DecidableEq R] [DecidableEq V]
variable [CommRing S] [Algebra R S]
abbrev Wire (P : ExpressionPresentation R V Q) := {t // t ∈ P.nodes}

/-- Multiplication nodes, with no gates for constants, variables, or additions. -/
abbrev Gate (P : ExpressionPresentation R V Q) :=
  {t : P.Wire // match t.val with | .mul _ _ => True | _ => False}

noncomputable instance gateFintype (P : ExpressionPresentation R V Q) : Fintype P.Gate := by
  classical
  exact Subtype.fintype _

def zeroWire (P : ExpressionPresentation R V Q) : P.Wire := ⟨.const 0, P.zero_mem⟩
def input (P : ExpressionPresentation R V Q) (w : P.Wire → S) : V → S :=
  fun i => w ⟨.var i, P.var_mem i⟩
def extend (P : ExpressionPresentation R V Q) (x : V → S) : P.Wire → S :=
  fun t => t.val.eval x

theorem extend_natural {T : Type*} [CommRing T] [Algebra R T]
    (P : ExpressionPresentation R V Q) (φ : S →ₐ[R] T) (x : V → S) (t : P.Wire) :
    φ (P.extend x t) = P.extend (fun i => φ (x i)) t :=
  ArithmeticExpr.eval_natural φ t.val x

theorem add_left_mem (P : ExpressionPresentation R V Q) {a b} (h : ArithmeticExpr.add a b ∈ P.nodes) :
    a ∈ P.nodes := P.closed _ h (by simp [ArithmeticExpr.subterms])
theorem add_right_mem (P : ExpressionPresentation R V Q) {a b} (h : ArithmeticExpr.add a b ∈ P.nodes) :
    b ∈ P.nodes := P.closed _ h (by simp [ArithmeticExpr.subterms])
theorem mul_left_mem (P : ExpressionPresentation R V Q) {a b} (h : ArithmeticExpr.mul a b ∈ P.nodes) :
    a ∈ P.nodes := P.closed _ h (by simp [ArithmeticExpr.subterms])
theorem mul_right_mem (P : ExpressionPresentation R V Q) {a b} (h : ArithmeticExpr.mul a b ∈ P.nodes) :
    b ∈ P.nodes := P.closed _ h (by simp [ArithmeticExpr.subterms])

def nodeEquation (P : ExpressionPresentation R V Q) : P.Wire → AffineEquation R P.Wire
  | ⟨.const c, ht⟩ => (AffineEquation.coordinate ⟨.const c, ht⟩).sub (AffineEquation.constantForm c)
  | ⟨.var _, _⟩ => AffineEquation.zero
  | ⟨.add a b, ht⟩ => (AffineEquation.coordinate ⟨.add a b, ht⟩).sub
      ((AffineEquation.coordinate ⟨a, P.add_left_mem ht⟩).add
        (AffineEquation.coordinate ⟨b, P.add_right_mem ht⟩))
  | ⟨.mul _ _, _⟩ => AffineEquation.zero

def left (P : ExpressionPresentation R V Q) : P.Gate → P.Wire
  | ⟨⟨.mul a _, ht⟩, _⟩ => ⟨a, P.mul_left_mem ht⟩
def right (P : ExpressionPresentation R V Q) : P.Gate → P.Wire
  | ⟨⟨.mul _ b, ht⟩, _⟩ => ⟨b, P.mul_right_mem ht⟩
def output (P : ExpressionPresentation R V Q) (g : P.Gate) : P.Wire := g.val

/-- Expression trees compiled to finite affine rows and multiplication triples. -/
def gates (P : ExpressionPresentation R V Q) : GateSystem R P.Wire P.Gate (P.Wire ⊕ Q) where
  left := P.left
  right := P.right
  output := P.output
  equations := Sum.elim P.nodeEquation (fun q => AffineEquation.coordinate ⟨P.roots q, P.root_mem q⟩)

theorem gates_output_injective (P : ExpressionPresentation R V Q) :
    Function.Injective P.gates.output := Subtype.val_injective

theorem gates_output_range (P : ExpressionPresentation R V Q) :
    Set.range P.gates.output = {t | ∃ a b, t.val = ArithmeticExpr.mul a b} := by
  ext ⟨t, ht⟩
  constructor
  · rintro ⟨⟨⟨s, hs⟩, hm⟩, h⟩
    cases s with
    | mul a b => exact ⟨a, b, (congrArg Subtype.val h).symm⟩
    | const c => exact False.elim hm
    | var i => exact False.elim hm
    | add a b => exact False.elim hm
  · rintro ⟨a, b, rfl⟩
    exact ⟨⟨⟨.mul a b, ht⟩, trivial⟩, rfl⟩

/-- The matrix size is the number of wires plus twice the number of multiplication nodes. -/
theorem card_index (P : ExpressionPresentation R V Q) :
    Fintype.card (GateSystem.Index P.Wire P.Gate) = P.nodes.card + 2 * Fintype.card P.Gate := by
  rw [GateSystem.card_index, Fintype.card_coe]

theorem extend_satisfies (P : ExpressionPresentation R V Q) (x : V → S)
    (hx : ∀ q, (P.roots q).eval x = 0) : P.gates.Satisfies (P.extend x) := by
  constructor
  · intro q
    cases q with
    | inl t =>
      rcases t with ⟨t, ht⟩
      cases t <;> simp [gates, nodeEquation, extend, ArithmeticExpr.eval]
    | inr q => simpa [gates, extend] using hx q
  · rintro ⟨⟨t, ht⟩, hm⟩
    cases t with
    | mul a b => rfl
    | const c => exact False.elim hm
    | var i => exact False.elim hm
    | add a b => exact False.elim hm

/-- Every internal wire is forced, even over arbitrary nonreduced algebras. -/
theorem wire_forced (P : ExpressionPresentation R V Q) (w : P.Wire → S)
    (hw : P.gates.Satisfies w) (t : ArithmeticExpr R V) (ht : t ∈ P.nodes) :
    w ⟨t, ht⟩ = t.eval (P.input w) := by
  induction t with
  | const c =>
    have h := hw.1 (Sum.inl ⟨.const c, ht⟩)
    simpa [gates, nodeEquation, ArithmeticExpr.eval, sub_eq_zero] using h
  | var i => rfl
  | add a b ha hb =>
    have h := hw.1 (Sum.inl ⟨.add a b, ht⟩)
    simp only [gates, Sum.elim_inl, nodeEquation, AffineEquation.eval_sub,
      AffineEquation.eval_coordinate, AffineEquation.eval_add, sub_eq_zero] at h
    rw [h, ha (P.add_left_mem ht), hb (P.add_right_mem ht)]
    rfl
  | mul a b ha hb =>
    have h := hw.2 ⟨⟨.mul a b, ht⟩, trivial⟩
    change w ⟨.mul a b, ht⟩ = w ⟨a, P.mul_left_mem ht⟩ * w ⟨b, P.mul_right_mem ht⟩ at h
    rw [h, ha (P.mul_left_mem ht), hb (P.mul_right_mem ht)]
    rfl

theorem input_satisfies (P : ExpressionPresentation R V Q) (w : P.Wire → S)
    (hw : P.gates.Satisfies w) : ∀ q, (P.roots q).eval (P.input w) = 0 := by
  intro q
  rw [← P.wire_forced w hw _ (P.root_mem q)]
  simpa [gates] using hw.1 (Sum.inr q)

/-- Input solutions and all circuit wires are canonically equivalent. -/
def solutionEquiv (P : ExpressionPresentation R V Q) :
    {x : V → S // ∀ q, (P.roots q).eval x = 0} ≃
    {w : P.Wire → S // P.gates.Satisfies w} where
  toFun x := ⟨P.extend x.val, P.extend_satisfies x.val x.property⟩
  invFun w := ⟨P.input w.val, P.input_satisfies w.val w.property⟩
  left_inv x := by apply Subtype.ext; rfl
  right_inv w := by
    apply Subtype.ext
    funext t
    exact (P.wire_forced w.val w.property t.val t.property).symm

end ExpressionPresentation

namespace ExpressionPresentation
variable {R V Q : Type*} [CommRing R] [DecidableEq R] [DecidableEq V]
variable [Fintype V] [Fintype Q]

/-- Every finite expression family has a finite closed wire set. -/
def ofExpressions (f : Q → ArithmeticExpr R V) : ExpressionPresentation R V Q where
  nodes := insert (.const 0) ((Finset.univ.image ArithmeticExpr.var) ∪
    Finset.univ.biUnion (fun q => (f q).subterms))
  closed := by
    intro t ht u hu
    simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_image,
      Finset.mem_univ, true_and, Finset.mem_biUnion] at ht ⊢
    rcases ht with rfl | ⟨i, rfl⟩ | ⟨q, hq⟩
    · left
      simpa [ArithmeticExpr.subterms] using hu
    · right; left
      have : u = .var i := by simpa [ArithmeticExpr.subterms] using hu
      exact ⟨i, this.symm⟩
    · right; right
      exact ⟨q, ArithmeticExpr.subterms_trans hq hu⟩
  zero_mem := by simp
  var_mem := by intro i; simp
  roots := f
  root_mem := by
    intro q
    simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_image,
      Finset.mem_biUnion, Finset.mem_univ, true_and]
    exact Or.inr (Or.inr ⟨q, ArithmeticExpr.mem_subterms _⟩)

/-- Arbitrary multivariate polynomials are compiled, not assumed to come with circuits. -/
def ofPolynomials (f : Q → MvPolynomial V R) : ExpressionPresentation R V Q :=
  ofExpressions fun q => Classical.choose (ArithmeticExpr.polynomial_surjective (f q))

theorem ofPolynomials_roots (f : Q → MvPolynomial V R) (q : Q) :
    ((ofPolynomials f).roots q).polynomial = f q :=
  Classical.choose_spec (ArithmeticExpr.polynomial_surjective (f q))

variable {S : Type*} [CommRing S] [Algebra R S]

/-- Full finite polynomial-system reconstruction in one matrix-square graph. -/
def polynomialSolutionEquiv (f : Q → MvPolynomial V R) :
    {x : V → S // ∀ q, MvPolynomial.eval₂ (algebraMap R S) x (f q) = 0} ≃
    {p : Matrix (GateSystem.Index (ofPolynomials f).Wire (ofPolynomials f).Gate)
        (GateSystem.Index (ofPolynomials f).Wire (ofPolynomials f).Gate) S ×
      Matrix (GateSystem.Index (ofPolynomials f).Wire (ofPolynomials f).Gate)
        (GateSystem.Index (ofPolynomials f).Wire (ofPolynomials f).Gate) S //
      (ofPolynomials f).gates.LinearSection p.1 p.2 ∧ p.2 = p.1 * p.1} :=
  (Equiv.subtypeEquivRight (fun x => by
    simp only [← ArithmeticExpr.eval_polynomial, ofPolynomials_roots])).trans
      ((ofPolynomials f).solutionEquiv.trans (ofPolynomials f).gates.solutionEquiv)

end ExpressionPresentation

namespace GateSystem
variable {R S W G E : Type*} [CommRing R] [CommRing S] [Algebra R S]
variable [Fintype W] [DecidableEq W] [Fintype G] [DecidableEq G]

theorem gateBlock_add (a b c d : S) :
    gateBlock (a+c) (b+d) = gateBlock a b + gateBlock c d := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [gateBlock]

theorem gateBlock_smul (c a b : S) : gateBlock (c*a) (c*b) = c • gateBlock a b := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [gateBlock]

/-- Assembly is a linear map, not an implicit polynomial constraint. -/
def assembleLinear (C : GateSystem R W G E) :
    (W → S) →ₗ[S] Matrix (Index W G) (Index W G) S where
  toFun := C.assemble
  map_add' w v := by
    simp only [assemble, Matrix.fromBlocks_add, Matrix.diagonal_add, Pi.add_apply,
      gateBlock_add, zero_add]
    rw [← Matrix.blockDiagonal_add]
    rfl
  map_smul' c w := by
    simp only [assemble, Matrix.fromBlocks_smul, Matrix.diagonal_smul, Pi.smul_apply,
      smul_eq_mul, gateBlock_smul, smul_zero]
    rw [← Matrix.blockDiagonal_smul]
    rfl

def wiresLinear : Matrix (Index W G) (Index W G) S →ₗ[S] (W → S) where
  toFun := wires
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

abbrev Ambient (W G S : Type*) := Matrix (Index W G) (Index W G) S ×
  Matrix (Index W G) (Index W G) S

/-- The linear part of all residual equations. -/
def residualLinear (C : GateSystem R W G E) :
    Ambient W G S →ₗ[S] (Matrix (Index W G) (Index W G) S × ((E → S) × (G → S))) where
  toFun p := (p.1 - C.assemble (wires p.1),
    ((fun q => ∑ i, algebraMap R S ((C.equations q).coeff i) * wires p.1 i),
     (fun g => wires p.1 (C.output g) - p.2 (Sum.inr (0,g)) (Sum.inr (0,g)))))
  map_add' p q := by
    apply Prod.ext
    · change p.1 + q.1 - C.assembleLinear (wiresLinear (p.1 + q.1)) = _
      rw [map_add, map_add]
      simp only [assembleLinear, wiresLinear, LinearMap.coe_mk, AddHom.coe_mk,
        Prod.fst_add]
      abel
    · apply Prod.ext
      · funext j
        simp [wires, mul_add, Finset.sum_add_distrib]
      · funext g
        simp [wires]
        abel
  map_smul' c p := by
    apply Prod.ext
    · change c • p.1 - C.assembleLinear (wiresLinear (c • p.1)) = _
      rw [map_smul, map_smul]
      simp [assembleLinear, wiresLinear, smul_sub]
    · apply Prod.ext
      · funext j
        simp [wires, Finset.mul_sum, mul_left_comm]
      · funext g
        simp [wires, mul_sub]

/-- A genuine affine map whose zero fiber is exactly the compiler's linear section. -/
def residualAffine (C : GateSystem R W G E) :
    Ambient W G S →ᵃ[S] (Matrix (Index W G) (Index W G) S × ((E → S) × (G → S))) :=
  C.residualLinear.toAffineMap + AffineMap.const S (Ambient W G S)
    (0, (fun q => algebraMap R S (C.equations q).constant), 0)

omit [Fintype G] in
theorem residualAffine_eq_zero_iff (C : GateSystem R W G E) (p : Ambient W G S) :
    C.residualAffine (S := S) p = 0 ↔ C.LinearSection p.1 p.2 := by
  change (p.1 - C.assemble (wires p.1),
    ((fun q => ∑ i, algebraMap R S ((C.equations q).coeff i) * wires p.1 i),
     (fun g => wires p.1 (C.output g) - p.2 (Sum.inr (0,g)) (Sum.inr (0,g))))) +
      (0, (fun q => algebraMap R S (C.equations q).constant), 0) = 0 ↔ _
  simp only [Prod.mk_add_mk, add_zero, Prod.mk_eq_zero, sub_eq_zero]
  simp only [LinearSection, AffineEquation.eval, funext_iff, Pi.add_apply,
    Pi.zero_apply, add_comm, sub_eq_zero]

end GateSystem
end

namespace GateSystem

noncomputable section

variable {S W₁ W₂ W₃ G₁ G₂ G₃ : Type*} [CommRing S]

/-- Relabel wire and gate indices, preserving the position inside each gate. -/
def indexMap (fw : W₂ → W₁) (fg : G₂ → G₁) : Index W₂ G₂ → Index W₁ G₁ :=
  Sum.map fw (fun p => (p.1, fg p.2))

/-- The block containing a matrix index: a wire singleton or a two-dimensional gate. -/
def blockLabel : Index W₁ G₁ → W₁ ⊕ G₁ :=
  Sum.elim Sum.inl (fun p => Sum.inr p.2)

/-- Pull back arbitrary matrices, suppressing an off-block entry precisely when
    its two distinct block labels collide. This retains the identity map. -/
def matrixPullback (fw : W₂ → W₁) (fg : G₂ → G₁) :
    Matrix (Index W₁ G₁) (Index W₁ G₁) S →ₗ[S]
      Matrix (Index W₂ G₂) (Index W₂ G₂) S := by
  classical
  exact {
    toFun := fun A i j => if blockLabel i = blockLabel j ∨
        blockLabel (indexMap fw fg i) ≠ blockLabel (indexMap fw fg j)
      then A (indexMap fw fg i) (indexMap fw fg j) else 0
    map_add' := by intros; ext i j; dsimp; split_ifs <;> simp
    map_smul' := by intros; ext i j; dsimp; split_ifs <;> simp }

@[simp] theorem matrixPullback_id :
    matrixPullback (S := S) (id : W₁ → W₁) (id : G₁ → G₁) = LinearMap.id := by
  classical
  ext A i j
  have h : indexMap (id : W₁ → W₁) (id : G₁ → G₁) = id := by
    funext i; cases i <;> rfl
  simp [matrixPullback, h]

theorem matrixPullback_map {T : Type*} [CommRing T] (φ : S →+* T)
    (fw : W₂ → W₁) (fg : G₂ → G₁) (A : Matrix (Index W₁ G₁) (Index W₁ G₁) S) :
    (matrixPullback fw fg A).map φ = matrixPullback fw fg (A.map φ) := by
  classical
  ext i j
  by_cases h : blockLabel i = blockLabel j ∨
      blockLabel (indexMap fw fg i) ≠ blockLabel (indexMap fw fg j)
  · simp [matrixPullback, h, Matrix.map_apply]
  · simp [matrixPullback, h, Matrix.map_apply]

theorem indexMap_block_eq (fw : W₂ → W₁) (fg : G₂ → G₁)
    {i j : Index W₂ G₂} (h : blockLabel i = blockLabel j) :
    blockLabel (indexMap fw fg i) = blockLabel (indexMap fw fg j) := by
  cases i with
  | inl i => cases j <;> simp_all [blockLabel, indexMap]
  | inr i => cases j <;> simp_all [blockLabel, indexMap]

@[simp] theorem matrixPullback_comp (fw : W₂ → W₁) (fg : G₂ → G₁)
    (hw : W₃ → W₂) (hg : G₃ → G₂) :
    (matrixPullback (S := S) hw hg).comp (matrixPullback fw fg) =
      matrixPullback (fw ∘ hw) (fg ∘ hg) := by
  classical
  ext A i j
  have hi : indexMap (fw ∘ hw) (fg ∘ hg) i =
      indexMap fw fg (indexMap hw hg i) := by cases i <;> rfl
  have hj : indexMap (fw ∘ hw) (fg ∘ hg) j =
      indexMap fw fg (indexMap hw hg j) := by cases j <;> rfl
  by_cases h₀ : blockLabel i = blockLabel j
  · have h₁ := indexMap_block_eq hw hg h₀
    simp [matrixPullback, hi, hj, h₀, h₁]
  · by_cases h₁ : blockLabel (indexMap hw hg i) = blockLabel (indexMap hw hg j)
    · have h₂ := indexMap_block_eq fw fg h₁
      simp [matrixPullback, hi, hj, h₀, h₁, h₂]
    · simp [matrixPullback, hi, hj, h₀, h₁]

@[simp] theorem matrixPullback_one [DecidableEq W₁] [DecidableEq W₂]
    [DecidableEq G₁] [DecidableEq G₂] (fw : W₂ → W₁) (fg : G₂ → G₁) :
    matrixPullback (S := S) fw fg 1 = 1 := by
  classical
  ext i j
  cases i with
  | inl i =>
    cases j with
    | inl j => by_cases h : i = j <;> by_cases hh : fw i = fw j <;>
        simp_all [matrixPullback, blockLabel, indexMap, Matrix.one_apply]
    | inr j => simp [matrixPullback, blockLabel, indexMap]
  | inr i =>
    cases j with
    | inl j => simp [matrixPullback, blockLabel, indexMap]
    | inr j => by_cases h : i.2 = j.2 <;> by_cases hh : fg i.2 = fg j.2 <;>
        simp_all [matrixPullback, blockLabel, indexMap, Matrix.one_apply, Prod.ext_iff]

theorem matrixPullback_blocks [DecidableEq W₁] [DecidableEq W₂]
    [DecidableEq G₁] [DecidableEq G₂] (fw : W₂ → W₁) (fg : G₂ → G₁)
    (w : W₁ → S) (H : G₁ → Matrix (Fin 2) (Fin 2) S) :
    matrixPullback fw fg (Matrix.fromBlocks (Matrix.diagonal w) 0 0
      (Matrix.blockDiagonal H)) =
    Matrix.fromBlocks (Matrix.diagonal (w ∘ fw)) 0 0
      (Matrix.blockDiagonal (H ∘ fg)) := by
  classical
  ext i j
  cases i with
  | inl i =>
    cases j with
    | inl j => by_cases h : i = j <;> by_cases hh : fw i = fw j <;>
        simp_all [matrixPullback, blockLabel, indexMap]
    | inr j => simp [matrixPullback, blockLabel, indexMap]
  | inr i =>
    cases j with
    | inl j => simp [matrixPullback, blockLabel, indexMap]
    | inr j => by_cases h : i.2 = j.2 <;> by_cases hh : fg i.2 = fg j.2 <;>
        simp_all [matrixPullback, blockLabel, indexMap, Matrix.blockDiagonal_apply]

variable {R E₁ E₂ : Type*}

theorem matrixPullback_assemble [DecidableEq W₁] [DecidableEq W₂]
    [DecidableEq G₁] [DecidableEq G₂]
    (C₁ : GateSystem R W₁ G₁ E₁) (C₂ : GateSystem R W₂ G₂ E₂)
    (fw : W₂ → W₁) (fg : G₂ → G₁)
    (hl : ∀ g, fw (C₂.left g) = C₁.left (fg g))
    (hr : ∀ g, fw (C₂.right g) = C₁.right (fg g)) (w : W₁ → S) :
    matrixPullback fw fg (C₁.assemble w) = C₂.assemble (w ∘ fw) := by
  rw [assemble, matrixPullback_blocks]
  simp only [assemble, Function.comp_def, hl, hr]

theorem matrixPullback_assemble_square [DecidableEq W₁] [DecidableEq W₂]
    [DecidableEq G₁] [DecidableEq G₂] [Fintype W₁] [Fintype W₂]
    [Fintype G₁] [Fintype G₂]
    (C₁ : GateSystem R W₁ G₁ E₁) (C₂ : GateSystem R W₂ G₂ E₂)
    (fw : W₂ → W₁) (fg : G₂ → G₁)
    (hl : ∀ g, fw (C₂.left g) = C₁.left (fg g))
    (hr : ∀ g, fw (C₂.right g) = C₁.right (fg g)) (w : W₁ → S) :
    matrixPullback fw fg (C₁.assemble w * C₁.assemble w) =
      C₂.assemble (w ∘ fw) * C₂.assemble (w ∘ fw) := by
  simp only [assemble, Matrix.fromBlocks_multiply, Matrix.mul_zero,
    Matrix.zero_mul, add_zero, zero_add, ← Matrix.blockDiagonal_mul,
    Matrix.diagonal_mul_diagonal]
  rw [matrixPullback_blocks]
  simp only [Function.comp_def, hl, hr]

end
end GateSystem

namespace FiniteDiagram

noncomputable section

open CategoryTheory

universe u v w s t

variable {J : Type u} [Category.{v} J]

/-- At `i`, keep a copy of every named target coordinate for every arrow out of `i`. -/
abbrev Coordinate (Name : J → Type w) (i : J) := Σ j : J, (i ⟶ j) × Name j

variable (S : Type s) [CommRing S] (Name : J → Type w)

/-- The arrow map is a linear coordinate projection by precomposition. -/
def projection {i j : J} (α : i ⟶ j) :
    (Coordinate Name i → S) →ₗ[S] (Coordinate Name j → S) where
  toFun x c := x ⟨c.1, (α ≫ c.2.1, c.2.2)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem projection_id (i : J) :
    projection S Name (𝟙 i) = LinearMap.id := by
  ext x ⟨j, β, c⟩
  simp [projection]

@[simp] theorem projection_comp {i j k : J} (α : i ⟶ j) (β : j ⟶ k) :
    (projection S Name β).comp (projection S Name α) = projection S Name (α ≫ β) := by
  ext x ⟨l, γ, c⟩
  simp [projection, Category.assoc]

/-- The ambient modules and their coordinate projections form a functor. -/
def ambientFunctor : J ⥤ ModuleCat S where
  obj i := ModuleCat.of S (Coordinate Name i → S)
  map α := ModuleCat.ofHom (projection S Name α)
  map_id i := by
    apply ModuleCat.hom_ext
    exact projection_id S Name i
  map_comp α β := by
    apply ModuleCat.hom_ext
    exact (projection_comp S Name α β).symm

variable {S Name}

/-- Evaluate each named coordinate after the corresponding diagram arrow. -/
def embedding (F : J ⥤ Type t) (value : ∀ j, F.obj j → Name j → S)
    (i : J) (x : F.obj i) : Coordinate Name i → S :=
  fun c => value c.1 (F.map c.2.1 x) c.2.2

theorem projection_embedding (F : J ⥤ Type t) (value : ∀ j, F.obj j → Name j → S)
    {i j : J} (α : i ⟶ j) (x : F.obj i) :
    projection S Name α (embedding F value i x) = embedding F value j (F.map α x) := by
  funext ⟨k, β, c⟩
  simp [projection, embedding, Functor.map_comp]

omit [CommRing S] in
/-- Identity-arrow coordinates recover the original embedding at every object. -/
theorem embedding_injective (F : J ⥤ Type t) (value : ∀ j, F.obj j → Name j → S)
    (hvalue : ∀ j, Function.Injective (value j)) (i : J) :
    Function.Injective (embedding F value i) := by
  intro x y h
  apply hvalue i
  funext c
  have hc := congrFun h ⟨i, (𝟙 i, c)⟩
  simpa [embedding] using hc

variable (Name)

instance coordinateFintype [Fintype J] [∀ i j : J, Fintype (i ⟶ j)]
    [∀ j, Fintype (Name j)] (i : J) : Fintype (Coordinate Name i) := inferInstance

theorem coordinate_card [Fintype J] [∀ i j : J, Fintype (i ⟶ j)]
    [∀ j, Fintype (Name j)] (i : J) :
    Fintype.card (Coordinate Name i) =
      ∑ j : J, Fintype.card (i ⟶ j) * Fintype.card (Name j) := by
  simp [Coordinate, Fintype.card_sigma, Fintype.card_prod]

/-- Named polynomial coordinates containing the original variables. Identity-arrow
    coordinates in the replicated construction provide precisely this recovery map. -/
structure PolynomialCoordinates (R V C : Type*) [CommRing R] where
  recover : V → C
  polynomial : C → MvPolynomial V R
  polynomial_recover : ∀ v, polynomial (recover v) = MvPolynomial.X v

namespace PolynomialCoordinates

variable {R V C Q S : Type*} [CommRing R] [CommRing S] [Algebra R S]

def evaluate (P : PolynomialCoordinates R V C) (x : V → S) : C → S :=
  fun c => MvPolynomial.eval₂ (algebraMap R S) x (P.polynomial c)

@[simp] theorem evaluate_recover (P : PolynomialCoordinates R V C) (x : V → S) :
    P.evaluate x ∘ P.recover = x := by
  funext v
  simp [evaluate, P.polynomial_recover]

theorem evaluate_injective (P : PolynomialCoordinates R V C) :
    Function.Injective (P.evaluate (S := S)) := by
  intro x y h
  have hh := congrArg (fun w : C → S => w ∘ P.recover) h
  simpa using hh

/-- Explicit polynomial equations for the image of the named-coordinate embedding. -/
def graphEquation (P : PolynomialCoordinates R V C) (c : C) : MvPolynomial C R :=
  MvPolynomial.X c - MvPolynomial.rename P.recover (P.polynomial c)

theorem graph_equations_iff (P : PolynomialCoordinates R V C) (w : C → S) :
    (∀ c, MvPolynomial.eval₂ (algebraMap R S) w (P.graphEquation c) = 0) ↔
      P.evaluate (w ∘ P.recover) = w := by
  simp only [graphEquation, evaluate, MvPolynomial.eval₂_sub, MvPolynomial.eval₂_X,
    MvPolynomial.eval₂_rename, sub_eq_zero, funext_iff]
  exact forall_congr' fun c => eq_comm

/-- The coordinate-ring map of the closed polynomial embedding. -/
def coordinateMap (P : PolynomialCoordinates R V C) :
    MvPolynomial C R →ₐ[R] MvPolynomial V R := MvPolynomial.aeval P.polynomial

theorem coordinateMap_rename (P : PolynomialCoordinates R V C) (p : MvPolynomial V R) :
    P.coordinateMap (MvPolynomial.rename P.recover p) = p := by
  rw [coordinateMap, MvPolynomial.aeval_rename]
  have h : P.polynomial ∘ P.recover = MvPolynomial.X := funext P.polynomial_recover
  rw [h, MvPolynomial.aeval_X_left_apply]

theorem coordinateMap_surjective (P : PolynomialCoordinates R V C) :
    Function.Surjective P.coordinateMap :=
  fun p => ⟨MvPolynomial.rename P.recover p, P.coordinateMap_rename p⟩

/-- Add the original equations to the graph equations without introducing free coordinates. -/
def equations (P : PolynomialCoordinates R V C) (f : Q → MvPolynomial V R) :
    Q ⊕ C → MvPolynomial C R :=
  Sum.elim (fun q => MvPolynomial.rename P.recover (f q)) P.graphEquation

theorem equations_iff (P : PolynomialCoordinates R V C) (f : Q → MvPolynomial V R)
    (w : C → S) :
    (∀ q, MvPolynomial.eval₂ (algebraMap R S) w (P.equations f q) = 0) ↔
      (∀ q, MvPolynomial.eval₂ (algebraMap R S) (w ∘ P.recover) (f q) = 0) ∧
        P.evaluate (w ∘ P.recover) = w := by
  simp only [Sum.forall, equations, Sum.elim_inl, Sum.elim_inr,
    MvPolynomial.eval₂_rename, P.graph_equations_iff]

/-- This proves the closed polynomial-image statement on every commutative test algebra. -/
def solutionEquiv (P : PolynomialCoordinates R V C) (f : Q → MvPolynomial V R) :
    {x : V → S // ∀ q, MvPolynomial.eval₂ (algebraMap R S) x (f q) = 0} ≃
    {w : C → S // ∀ q, MvPolynomial.eval₂ (algebraMap R S) w (P.equations f q) = 0} where
  toFun x := ⟨P.evaluate x.val, (P.equations_iff f _).mpr (by
    rw [P.evaluate_recover]
    exact ⟨x.property, rfl⟩)⟩
  invFun w := ⟨w.val ∘ P.recover, ((P.equations_iff f _).mp w.property).1⟩
  left_inv x := Subtype.ext (P.evaluate_recover x.val)
  right_inv w := Subtype.ext (((P.equations_iff f _).mp w.property).2)

/-- Apply the matrix-square compiler to the enlarged finite polynomial system. -/
noncomputable def compiledSolutionEquiv [Fintype C] [DecidableEq C] [Fintype Q] [DecidableEq R]
    (P : PolynomialCoordinates R V C) (f : Q → MvPolynomial V R) :=
  (P.solutionEquiv (S := S) f).trans
    (ExpressionPresentation.polynomialSolutionEquiv (S := S) (P.equations f))

end PolynomialCoordinates

end
end FiniteDiagram

namespace AffineEquation
variable {R S W V : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [Fintype W] [Fintype V] [DecidableEq V]

/-- Rename an affine row, allowing several old coordinates to coincide. -/
def push (e : AffineEquation R W) (f : W → V) : AffineEquation R V :=
  ⟨e.constant, fun v => ∑ w, if f w = v then e.coeff w else 0⟩

@[simp] theorem eval_push (e : AffineEquation R W) (f : W → V) (x : V → S) :
    (e.push f).eval x = e.eval (x ∘ f) := by
  classical
  simp only [push, eval, map_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  simp [apply_ite, ite_mul, eq_comm]
end AffineEquation

namespace FiniteDiagram
noncomputable section
open CategoryTheory
universe u
variable {J R S : Type u} [Category J] [Fintype J] [∀ i j : J, Fintype (i ⟶ j)]
  [CommRing R] [DecidableEq R] [CommRing S] [Algebra R S]
  {V Q : J → Type u} [∀ j, DecidableEq (V j)]
  [∀ j, Fintype (V j)] [∀ j, Fintype (Q j)]

/-- Finite expression presentations together with chosen polynomial coordinate lifts
for every arrow. The lifts are existing wires, so no unconstrained coordinates appear. -/
structure CircuitDiagram where
  presentation : ∀ j, ExpressionPresentation R (V j) (Q j)
  lift : ∀ {i j}, (i ⟶ j) → V j → (presentation i).Wire

namespace CircuitDiagram
variable (D : CircuitDiagram (J := J) (R := R) (V := V) (Q := Q))

/-- Enrich the finite wire set with every outgoing coordinate polynomial, while
designating only the original equations as zero outputs. -/
def ofPolynomials (f : ∀ j, Q j → MvPolynomial (V j) R)
    (p : ∀ {i j}, (i ⟶ j) → V j → MvPolynomial (V i) R) :
    CircuitDiagram (J := J) (R := R) (V := V) (Q := Q) := by
  classical
  let all (i : J) : Q i ⊕ Coordinate V i → MvPolynomial (V i) R :=
    Sum.elim (f i) (fun c => p c.2.1 c.2.2)
  let P (i : J) := ExpressionPresentation.ofPolynomials (all i)
  exact {
    presentation := fun i => { P i with
      roots := fun q => (P i).roots (Sum.inl q)
      root_mem := fun q => (P i).root_mem (Sum.inl q) }
    lift := fun {i j} α v =>
      ⟨(P i).roots (Sum.inr ⟨j,α,v⟩), (P i).root_mem (Sum.inr ⟨j,α,v⟩)⟩ }

@[simp] theorem ofPolynomials_roots (f : ∀ j, Q j → MvPolynomial (V j) R)
    (p : ∀ {i j}, (i ⟶ j) → V j → MvPolynomial (V i) R) (i : J) (q : Q i) :
    (((ofPolynomials f p).presentation i).roots q).polynomial = f i q := by
  classical
  exact ExpressionPresentation.ofPolynomials_roots _ _

@[simp] theorem ofPolynomials_lift (f : ∀ j, Q j → MvPolynomial (V j) R)
    (p : ∀ {i j}, (i ⟶ j) → V j → MvPolynomial (V i) R)
    {i j} (α : i ⟶ j) (v : V j) :
    ((ofPolynomials f p).lift α v).val.polynomial = p α v := by
  classical
  exact ExpressionPresentation.ofPolynomials_roots _ _

abbrev Wire (i : J) := Coordinate (fun j => (D.presentation j).Wire) i
abbrev Gate (i : J) := Coordinate (fun j => (D.presentation j).Gate) i
instance wireDecidableEq (i : J) : DecidableEq (D.Wire i) := Classical.decEq _
instance gateDecidableEq (i : J) : DecidableEq (D.Gate i) := Classical.decEq _

omit [(j : J) → Fintype (V j)] [(j : J) → Fintype (Q j)] in
theorem index_card_pos (i : J) : 0 < Fintype.card (GateSystem.Index (D.Wire i) (D.Gate i)) := by
  apply Fintype.card_pos_iff.mpr
  exact ⟨Sum.inl ⟨i, 𝟙 i, (D.presentation i).zeroWire⟩⟩
abbrev LocalRow (i : J) := Coordinate (fun j => (D.presentation j).Wire ⊕ Q j) i
abbrev Transition (i : J) := Σ j : J, (i ⟶ j) × (Σ k : J, (j ⟶ k) × V k)
abbrev Row (i : J) := D.LocalRow i ⊕ Transition (V := V) i

def copy {i j} (α : i ⟶ j) (t : (D.presentation j).Wire) : D.Wire i := ⟨j, α, t⟩
def slice {i j} (α : i ⟶ j) (w : D.Wire i → S) : (D.presentation j).Wire → S :=
  fun t => w (D.copy α t)
def variableWire (j : J) (v : V j) : (D.presentation j).Wire :=
  ⟨.var v, (D.presentation j).var_mem v⟩

/-- Every local circuit is copied along every outgoing arrow, together with all
composable-pair equations identifying arrow inputs with their polynomial lifts. -/
def gates (i : J) : GateSystem R (D.Wire i) (D.Gate i) (D.Row i) := by
  classical
  exact {
    left := fun c => D.copy c.2.1 ((D.presentation c.1).left c.2.2)
    right := fun c => D.copy c.2.1 ((D.presentation c.1).right c.2.2)
    output := fun c => D.copy c.2.1 ((D.presentation c.1).output c.2.2)
    equations := Sum.elim
      (fun c => ((D.presentation c.1).gates.equations c.2.2).push (D.copy c.2.1))
      (fun c => (AffineEquation.coordinate
          (D.copy (c.2.1 ≫ c.2.2.2.1) (D.variableWire c.2.2.1 c.2.2.2.2))).sub
        (AffineEquation.coordinate (D.copy c.2.1 (D.lift c.2.2.2.1 c.2.2.2.2)))) }

omit [(j : J) → Fintype (V j)] [(j : J) → Fintype (Q j)] in
theorem satisfies_iff (i : J) (w : D.Wire i → S) :
    (D.gates i).Satisfies w ↔
      (∀ j (α : i ⟶ j), (D.presentation j).gates.Satisfies (D.slice α w)) ∧
      (∀ j (β : i ⟶ j) k (α : j ⟶ k) v,
        w (D.copy (β ≫ α) (D.variableWire k v)) = w (D.copy β (D.lift α v))) := by
  classical
  simp only [GateSystem.Satisfies, gates, Sum.forall, Sigma.forall, Prod.forall,
    Sum.elim_inl, Sum.elim_inr, AffineEquation.eval_push,
    AffineEquation.eval_sub, AffineEquation.eval_coordinate, sub_eq_zero]
  constructor
  · rintro ⟨⟨he, ht⟩, hg⟩
    exact ⟨fun j α => ⟨he j α, hg j α⟩, ht⟩
  · rintro ⟨hl, ht⟩
    exact ⟨⟨fun j α => (hl j α).1, ht⟩, fun j α => (hl j α).2⟩

def inputMap {i j} (α : i ⟶ j) (x : V i → S) : V j → S :=
  fun v => (D.lift α v).val.eval x

def extend (i : J) (x : V i → S) : D.Wire i → S :=
  fun c => c.2.2.val.eval (D.inputMap c.2.1 x)

def input (i : J) (w : D.Wire i → S) : V i → S :=
  fun v => w (D.copy (𝟙 i) (D.variableWire i v))

/-- The hypotheses here are precisely the polynomial diagram laws on the original
solution spaces; no ambient extension or solution reconstruction is assumed. -/
structure Laws : Prop where
  preserves : ∀ {i j} (α : i ⟶ j) (x : V i → S),
    (∀ q, ((D.presentation i).roots q).eval x = 0) →
    ∀ q, ((D.presentation j).roots q).eval (D.inputMap α x) = 0
  identity : ∀ i (x : V i → S), (∀ q, ((D.presentation i).roots q).eval x = 0) →
    D.inputMap (𝟙 i) x = x
  composition : ∀ {i j k} (α : i ⟶ j) (β : j ⟶ k) (x : V i → S),
    (∀ q, ((D.presentation i).roots q).eval x = 0) →
    D.inputMap (α ≫ β) x = D.inputMap β (D.inputMap α x)

omit [(j : J) → Fintype (V j)] [(j : J) → Fintype (Q j)] in
theorem extend_satisfies (h : D.Laws (S := S)) (i : J) (x : V i → S)
    (hx : ∀ q, ((D.presentation i).roots q).eval x = 0) :
    (D.gates i).Satisfies (D.extend i x) := by
  classical
  apply (D.satisfies_iff _ _).mpr
  constructor
  · intro j α
    exact (D.presentation j).extend_satisfies _ (h.preserves α x hx)
  · intro j β k α v
    change D.inputMap (β ≫ α) x v = D.inputMap α (D.inputMap β x) v
    rw [h.composition β α x hx]

omit [(j : J) → Fintype (V j)] [(j : J) → Fintype (Q j)] in
theorem input_satisfies (i : J) (w : D.Wire i → S) (hw : (D.gates i).Satisfies w) :
    ∀ q, ((D.presentation i).roots q).eval (D.input i w) = 0 := by
  classical
  exact (D.presentation i).input_satisfies _ (((D.satisfies_iff _ _).mp hw).1 i (𝟙 i))

omit [(j : J) → Fintype (V j)] [(j : J) → Fintype (Q j)] in
/-- The identity-arrow inputs force every copied wire, including every auxiliary wire. -/
theorem wire_forced (i : J) (w : D.Wire i → S) (hw : (D.gates i).Satisfies w) :
    D.extend i (D.input i w) = w := by
  classical
  obtain ⟨hl, ht⟩ := (D.satisfies_iff _ _).mp hw
  have hi (j : J) (α : i ⟶ j) :
      (D.presentation j).input (D.slice α w) = D.inputMap α (D.input i w) := by
    funext v
    have hv := ht i (𝟙 i) j α v
    rw [Category.id_comp] at hv
    change w (D.copy α (D.variableWire j v)) = D.inputMap α (D.input i w) v
    rw [hv]
    exact (D.presentation i).wire_forced _ (hl i (𝟙 i)) _ (D.lift α v).property
  funext ⟨j, α, t⟩
  change t.val.eval (D.inputMap α (D.input i w)) = D.slice α w t
  rw [← hi j α]
  exact ((D.presentation j).wire_forced _ (hl j α) t.val t.property).symm

def solutionEquiv (h : D.Laws (S := S)) (i : J) :
    {x : V i → S // ∀ q, ((D.presentation i).roots q).eval x = 0} ≃
      {w : D.Wire i → S // (D.gates i).Satisfies w} where
  toFun x := ⟨D.extend i x.val, D.extend_satisfies h i x.val x.property⟩
  invFun w := ⟨D.input i w.val, D.input_satisfies i w.val w.property⟩
  left_inv x := by
    apply Subtype.ext
    exact h.identity i x.val x.property
  right_inv w := Subtype.ext (D.wire_forced i w.val w.property)

omit [Fintype J] [(i j : J) → Fintype (i ⟶ j)] [(j : J) → Fintype (V j)] [(j : J) → Fintype (Q j)] in
theorem projection_extend (h : D.Laws (S := S)) {i j} (α : i ⟶ j) (x : V i → S)
    (hx : ∀ q, ((D.presentation i).roots q).eval x = 0) :
    projection S (fun j => (D.presentation j).Wire) α (D.extend i x) =
      D.extend j (D.inputMap α x) := by
  funext ⟨k, β, t⟩
  change t.val.eval (D.inputMap (α ≫ β) x) = t.val.eval (D.inputMap β (D.inputMap α x))
  rw [h.composition α β x hx]

omit [(j : J) → Fintype (V j)] [(j : J) → Fintype (Q j)] in
theorem projection_satisfies {i j} (α : i ⟶ j) (w : D.Wire i → S)
    (hw : (D.gates i).Satisfies w) :
    (D.gates j).Satisfies (projection S (fun j => (D.presentation j).Wire) α w) := by
  classical
  obtain ⟨hl, ht⟩ := (D.satisfies_iff _ _).mp hw
  apply (D.satisfies_iff _ _).mpr
  constructor
  · intro k β
    exact hl k (α ≫ β)
  · intro k β l γ v
    simpa only [projection, LinearMap.coe_mk, AddHom.coe_mk, copy, Category.assoc]
      using ht k (α ≫ β) l γ v

omit [(j : J) → Fintype (V j)] [(j : J) → Fintype (Q j)] in
theorem input_projection {i j} (α : i ⟶ j) (w : D.Wire i → S)
    (hw : (D.gates i).Satisfies w) :
    D.input j (projection S (fun j => (D.presentation j).Wire) α w) =
      D.inputMap α (D.input i w) := by
  classical
  obtain ⟨hl, ht⟩ := (D.satisfies_iff _ _).mp hw
  funext v
  have hv := ht i (𝟙 i) j α v
  rw [Category.id_comp] at hv
  change w (D.copy (α ≫ 𝟙 j) (D.variableWire j v)) = D.inputMap α (D.input i w) v
  rw [Category.comp_id, hv]
  exact (D.presentation i).wire_forced _ (hl i (𝟙 i)) _ (D.lift α v).property

def wireMap {i j} (α : i ⟶ j) : D.Wire j → D.Wire i :=
  fun c => D.copy (α ≫ c.2.1) c.2.2

def gateMap {i j} (α : i ⟶ j) : D.Gate j → D.Gate i :=
  fun c => ⟨c.1, α ≫ c.2.1, c.2.2⟩

omit [Fintype J] [(i j : J) → Fintype (i ⟶ j)] [(j : J) → Fintype (V j)] [(j : J) → Fintype (Q j)] in
@[simp] theorem gateMap_id (i : J) : D.gateMap (𝟙 i) = id := by
  funext ⟨j, α, t⟩
  simp [gateMap]

omit [Fintype J] [(i j : J) → Fintype (i ⟶ j)] [(j : J) → Fintype (V j)] [(j : J) → Fintype (Q j)] in
@[simp] theorem gateMap_comp {i j k} (α : i ⟶ j) (β : j ⟶ k) :
    D.gateMap α ∘ D.gateMap β = D.gateMap (α ≫ β) := by
  funext ⟨l, γ, t⟩
  simp [gateMap, Category.assoc]

omit [Fintype J] [(i j : J) → Fintype (i ⟶ j)] [(j : J) → Fintype (V j)] [(j : J) → Fintype (Q j)] in
@[simp] theorem wireMap_id (i : J) : D.wireMap (𝟙 i) = id := by
  funext ⟨j, α, t⟩
  simp [wireMap, copy]

omit [Fintype J] [(i j : J) → Fintype (i ⟶ j)] [(j : J) → Fintype (V j)] [(j : J) → Fintype (Q j)] in
@[simp] theorem wireMap_comp {i j k} (α : i ⟶ j) (β : j ⟶ k) :
    D.wireMap α ∘ D.wireMap β = D.wireMap (α ≫ β) := by
  funext ⟨l, γ, t⟩
  simp [wireMap, copy, Category.assoc]

/-- Strict linear maps on the entire compiler matrix spaces, including collisions
of arrow indices in arbitrary finite categories. -/
def matrixMap {i j} (α : i ⟶ j) :
    Matrix (GateSystem.Index (D.Wire i) (D.Gate i)) (GateSystem.Index (D.Wire i) (D.Gate i)) S →ₗ[S]
      Matrix (GateSystem.Index (D.Wire j) (D.Gate j)) (GateSystem.Index (D.Wire j) (D.Gate j)) S :=
  GateSystem.matrixPullback (D.wireMap α) (D.gateMap α)

omit [Algebra R S] [Fintype J] [(i j : J) → Fintype (i ⟶ j)]
  [(j : J) → Fintype (V j)] [(j : J) → Fintype (Q j)] in
@[simp] theorem matrixMap_id (i : J) : D.matrixMap (S := S) (𝟙 i) = LinearMap.id := by
  simp [matrixMap, GateSystem.matrixPullback_id]

omit [Algebra R S] [Fintype J] [(i j : J) → Fintype (i ⟶ j)]
  [(j : J) → Fintype (V j)] [(j : J) → Fintype (Q j)] in
@[simp] theorem matrixMap_comp {i j k} (α : i ⟶ j) (β : j ⟶ k) :
    (D.matrixMap (S := S) β).comp (D.matrixMap α) = D.matrixMap (α ≫ β) := by
  rw [matrixMap, matrixMap, GateSystem.matrixPullback_comp, wireMap_comp, gateMap_comp]
  rfl

omit [Fintype J] [(i j : J) → Fintype (i ⟶ j)] [Algebra R S] [(j : J) → Fintype (V j)] [(j : J) → Fintype (Q j)] in
@[simp] theorem matrixMap_one {i j} (α : i ⟶ j) : D.matrixMap (S := S) α 1 = 1 :=
  GateSystem.matrixPullback_one _ _

omit [Fintype J] [(i j : J) → Fintype (i ⟶ j)] [Algebra R S] [(j : J) → Fintype (V j)] [(j : J) → Fintype (Q j)] in
theorem matrixMap_assemble {i j} (α : i ⟶ j) (w : D.Wire i → S) :
    D.matrixMap α ((D.gates i).assemble w) =
      (D.gates j).assemble (projection S (fun j => (D.presentation j).Wire) α w) := by
  classical
  exact GateSystem.matrixPullback_assemble (D.gates i) (D.gates j)
    (D.wireMap α) (D.gateMap α) (fun _ => rfl) (fun _ => rfl) w

omit [Algebra R S] [(j : J) → Fintype (V j)] [(j : J) → Fintype (Q j)] in
theorem matrixMap_assemble_square {i j} (α : i ⟶ j) (w : D.Wire i → S) :
    D.matrixMap α ((D.gates i).assemble w * (D.gates i).assemble w) =
      (D.gates j).assemble (projection S (fun j => (D.presentation j).Wire) α w) *
        (D.gates j).assemble (projection S (fun j => (D.presentation j).Wire) α w) := by
  classical
  exact GateSystem.matrixPullback_assemble_square (D.gates i) (D.gates j)
    (D.wireMap α) (D.gateMap α) (fun _ => rfl) (fun _ => rfl) w

/-- Objectwise equivalence with the matrix-square sections. -/
def matrixSolutionEquiv (h : D.Laws (S := S)) (i : J) := by
  classical
  exact (D.solutionEquiv h i).trans (D.gates i).solutionEquiv

end CircuitDiagram
end
end FiniteDiagram

end Universality
