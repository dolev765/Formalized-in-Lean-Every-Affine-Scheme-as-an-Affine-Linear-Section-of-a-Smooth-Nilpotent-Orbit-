import Universality.Main
import Lean.Util.CollectAxioms

namespace Universality
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MvPolynomial
open SquareZeroGeometry
open GlobalSymplectic AffineForms
universe u

/-- Exact affine-linear universality over any commutative ring, with a relative symplectic orbit. -/
theorem affine_orbit_universality_explicit (k A : Type u)
    [CommRing k] [CommRing A] [Algebra k A] [Algebra.FinitePresentation k A] :

    -- 1. Finite equations and exact coordinate algebra
    ∃ (n : Type u) (_ : Fintype n) (_ : DecidableEq n)
      (Q : Type u) (_ : Fintype Q)
      (affineEquations : Q → MvPolynomial ((n ⊕ n) × (n ⊕ n)) k)
      (I : Ideal (MvPolynomial ((n ⊕ n) × (n ⊕ n)) k))
      (coordinateIso : A ≃ₐ[k] (MvPolynomial ((n ⊕ n) × (n ⊕ n)) k ⧸ I)),

      -- 2. Ambient space, affine section, orbit, and cell
      let ambient := Spec (.of (MvPolynomial ((n ⊕ n) × (n ⊕ n)) k))
      let L := Spec (.of (MvPolynomial ((n ⊕ n) × (n ⊕ n)) k ⧸ equationIdeal affineEquations))
      let X := Spec (.of (MvPolynomial ((n ⊕ n) × (n ⊕ n)) k ⧸ I))

      let Z : Matrix (n ⊕ n) (n ⊕ n) (MvPolynomial ((n ⊕ n) × (n ⊕ n)) k) :=
        fun i j => MvPolynomial.X (i, j)
      let squareZeroRelations := Ideal.span (Set.range
        (fun ij : (n ⊕ n) × (n ⊕ n) => (Z * Z) ij.1 ij.2))
      let S := Spec (.of (MvPolynomial ((n ⊕ n) × (n ⊕ n)) k ⧸ squareZeroRelations))

      let rankOpen : S.Opens := ⨆ (r : n → n ⊕ n) (c : n → n ⊕ n),
        PrimeSpectrum.basicOpen (((Z.map (Ideal.Quotient.mk squareZeroRelations)).submatrix r c).det)
      let O := rankOpen.toScheme
      let U := Spec (.of (MvPolynomial (n × n) k))

      let affineInclusion : L ⟶ ambient :=
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (equationIdeal affineEquations)))
      let orbitInclusion : O ⟶ ambient := rankOpen.ι ≫
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk squareZeroRelations))
      let cellInclusion : U ⟶ O := cellMorphism k n

      ∃ (toAffine : X ⟶ L) (toOrbit : X ⟶ O) (toCell : X ⟶ U)
        (schemeIso : Spec (.of A) ≅ X),

        -- 3. Affine linearity and the original scheme Spec A
        0 < Fintype.card n ∧
        (∀ q, (affineEquations q).totalDegree ≤ 1) ∧
        I = equationIdeal affineEquations ⊔ squareZeroRelations ∧

        schemeIso = Scheme.Spec.mapIso coordinateIso.symm.toRingEquiv.toCommRingCatIso.op ∧
        toAffine ≫ affineInclusion = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ∧

        -- 4. Both scheme-theoretic intersections and their embeddings
        IsClosedImmersion affineInclusion ∧
        IsImmersion orbitInclusion ∧

        IsPullback toAffine toOrbit affineInclusion orbitInclusion ∧
        IsPullback toAffine toCell affineInclusion (cellInclusion ≫ orbitInclusion) ∧
        toOrbit = toCell ≫ cellInclusion ∧

        IsClosedImmersion toOrbit ∧
        IsClosedImmersion toCell ∧
        IsClosedImmersion cellInclusion ∧

        -- 5. Field-valued orbit classification and relative dimensions over k
        (∀ (K : Type u) [Field K] [Algebra k K] (M : Matrix (n ⊕ n) (n ⊕ n) K),
          (∃ P Q : Matrix (n ⊕ n) (n ⊕ n) K,
            P * Q = 1 ∧ Q * P = 1 ∧ M = P * jordanCell * Q) ↔
            M * M = 0 ∧ M.rank = Fintype.card n) ∧

        SmoothOfRelativeDimension (2 * Fintype.card n ^ 2) (maximalRankStructureMap k n) ∧
        (IsField k → IrreducibleSpace O) ∧
        SmoothOfRelativeDimension (Fintype.card n ^ 2)
          (Spec.map (CommRingCat.ofHom (algebraMap k (MvPolynomial (n × n) k)))) ∧

        -- 6. Actual charts, overlaps, and tangent-space dualities
        ∃ (charts : ∀ e : Equiv.Perm (n ⊕ n),
              (permutationOpen k n e).toScheme ≅ Spec (.of (ChartRing k n)))

          (overlaps : ∀ e f : Equiv.Perm (n ⊕ n),
              (permutationOpen k n e ⊓ permutationOpen k n f).toScheme ≅
                Spec (.of (OverlapRing k n e f)))

          (form : Equiv.Perm (n ⊕ n) → LinearMap.BilinForm (ChartRing k n)
              (Derivation k (ChartRing k n) (ChartRing k n)))

          (perfect : ∀ _e : Equiv.Perm (n ⊕ n),
              Derivation k (ChartRing k n) (ChartRing k n) ≃ₗ[ChartRing k n]
                Module.Dual (ChartRing k n) (Derivation k (ChartRing k n) (ChartRing k n))),

          (⨆ e, permutationOpen k n e) = maximalRankOpen k n ∧

          (∀ e, (charts e).inv ≫ (permutationOpen k n e).ι =
            Spec.map (CommRingCat.ofHom (chartEmbeddingBase k n e).toRingHom)) ∧

          (∀ e f, (overlaps e f).hom ≫
            Spec.map (CommRingCat.ofHom (algebraMap (CoordinateRing k n) (OverlapRing k n e f))) =
              (permutationOpen k n e ⊓ permutationOpen k n f).ι) ∧

          -- 7. The symplectic form: formula, alternating, closed, perfect
          (∀ e, form e = canonicalTrace (chartT k n) (chartA k n)) ∧

          (∀ e D, form e D D = 0) ∧

          (∀ e D E F,
            D (form e E F) - E (form e D F) + F (form e D E) -
              form e ⁅D, E⁆ F + form e ⁅D, F⁆ E - form e ⁅E, F⁆ D = 0) ∧

          (∀ e, (perfect e).toLinearMap = form e) ∧

          -- Compatibility on chart overlaps
          (∀ e f,
            canonicalTrace (R := k)
              ((chartT k n).map (overlapChartMap k n e f e (overlapT_left_isUnit k n e f)))
              ((chartA k n).map (overlapChartMap k n e f e (overlapT_left_isUnit k n e f))) =
            canonicalTrace
              ((chartT k n).map (overlapChartMap k n e f f (overlapT_right_isUnit k n e f)))
              ((chartA k n).map (overlapChartMap k n e f f (overlapT_right_isUnit k n e f)))) ∧

          -- 8. The cell lies in this atlas and has zero pullback form
          cellInclusion = Spec.map (CommRingCat.ofHom (cellChartEval k n).toRingHom) ≫
            (orbitChartToPermutationIso k n (Equiv.refl _) ≪≫ charts (Equiv.refl _)).inv ≫
              (orbitChartOpen k n (Equiv.refl _)).ι ∧

          canonicalTrace (R := k)
            ((chartT k n).map (cellChartEval k n)) ((chartA k n).map (cellChartEval k n)) = 0 := by

  -- Common witnesses for all eight parts
  obtain ⟨r⟩ := affine_orbit_universality k A
  refine ⟨r.Index, inferInstance, inferInstance, r.Equation, inferInstance,
    r.affineEquations, r.sectionIdeal,
    r.coordinateIso, r.sectionToAffine, r.sectionToOrbit,
    r.sectionToCell, r.schemeIso, r.positive_size, r.affine_degree, ?_,
    r.schemeIso_from_coordinate, r.sectionToAmbient,
    r.affine_closed, maximalRankScheme_isImmersion k _,
    r.orbit_intersection, r.cell_intersection, r.sectionToOrbit_eq,
    r.section_closed_in_orbit, r.section_closed_in_cell, r.cell_closed_in_orbit,
    (fun K _ _ M => inJordanOrbit_iff_square_zero_rank M),
    r.orbit_smooth_dimension, r.orbit_irreducible, r.cell_smooth_dimension, ?_⟩

  -- Exact ideal equality
  · simpa only [squareZeroIdeal, genericMatrix] using r.ideal_eq

  -- Symplectic atlas and Lagrangian cell
  · refine ⟨r.symplectic.chartIso, r.symplectic.overlapIso, r.symplectic.form,
      r.symplectic.perfect, r.symplectic.covers, r.symplectic.chart_embedding,
      r.symplectic.overlap_embedding, r.symplectic.local_formula,
      (fun e D => r.symplectic.alternating e D),
      (fun e D E F => r.symplectic.closed e D E F),
      r.symplectic.perfect_form, r.symplectic.compatible, r.cell_chart_factorization,
      r.cell_isotropic⟩

end
end Universality

open Lean Elab Command in
run_cmd do
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let axioms ← collectAxioms ``Universality.affine_orbit_universality_explicit
  let unexpected := axioms.filter fun name => !allowed.contains name
  unless unexpected.isEmpty do
    throwError "Main theorem depends on unapproved axioms: {unexpected}"

#print axioms Universality.affine_orbit_universality_explicit
