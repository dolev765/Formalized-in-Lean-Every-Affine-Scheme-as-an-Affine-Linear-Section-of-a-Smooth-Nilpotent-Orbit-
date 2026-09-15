import Universality.Main
import Lean.Util.CollectAxioms

namespace Universality
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MvPolynomial
open SquareZeroGeometry
open GlobalSymplectic AffineForms
open AffineGeometry ExteriorGeometry
universe u

set_option maxHeartbeats 800000 in
/-- Exact affine-linear universality over any commutative ring, with a relative symplectic orbit. -/
theorem affine_orbit_universality (k A : Type u)
    [CommRing k] [CommRing A] [Algebra k A] [Algebra.FinitePresentation k A] :

    -- 1. Finite equations and exact coordinate algebra
    ∃ (n : Type u) (_ : Fintype n) (_ : DecidableEq n)
      (Q : Type u) (_ : Fintype Q)
      (affineEquations : Q → MvPolynomial ((n ⊕ n) × (n ⊕ n)) k)
      (I : Ideal (MvPolynomial ((n ⊕ n) × (n ⊕ n)) k))
      (coordinateEquiv : A ≃ₐ[k] (MvPolynomial ((n ⊕ n) × (n ⊕ n)) k ⧸ I)),

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

        schemeIso = Scheme.Spec.mapIso coordinateEquiv.symm.toRingEquiv.toCommRingCatIso.op ∧
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

      -- 6. Charts, overlaps, and tangent-space dualities
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

          -- 8. The cell lies in this atlas and its differential has Lagrangian image
          cellInclusion = Spec.map (CommRingCat.ofHom (cellChartEval k n).toRingHom) ≫
            (orbitChartToPermutationIso k n (Equiv.refl _) ≪≫ charts (Equiv.refl _)).inv ≫
              (orbitChartOpen k n (Equiv.refl _)).ι ∧

          canonicalTrace (R := k)
            ((chartT k n).map (cellChartEval k n)) ((chartA k n).map (cellChartEval k n)) = 0 ∧

          letI := cellChartAlgebra k n
          letI : IsScalarTower k (ChartRing k n) (CellRing k n) :=
            IsScalarTower.of_algHom (cellChartEval k n)
          Function.Injective (cellDifferential k n) ∧

          (∀ D : Derivation k (CellRing k n) (CellRing k n),
            (cellDifferential k n D).liftKaehlerDifferential =
              (D.liftKaehlerDifferential.restrictScalars (ChartRing k n)).comp
                (KaehlerDifferential.map k k (ChartRing k n) (CellRing k n))) ∧

          Function.Surjective (specializeChartDerivation k n) ∧

          (∀ D E : Derivation k (ChartRing k n) (ChartRing k n),
            cellOrbitForm k n (specializeChartDerivation k n D) (specializeChartDerivation k n E) =
              cellChartEval k n (form (Equiv.refl _) D E)) ∧

          (cellOrbitForm k n).orthogonal (LinearMap.range (cellDifferential k n)) =
            LinearMap.range (cellDifferential k n) ∧

          -- 9. Canonical tangent bundle and exterior-square differential form
          (∀ e, ∃ τ : pullback (orbitTangentProjection k n) (orbitChartMap k n e) ≅
              Spec (.of (MvPolynomial ((n × n) ⊕ (n × n)) (ChartRing k n))),
            τ.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap (ChartRing k n)
              (MvPolynomial ((n × n) ⊕ (n × n)) (ChartRing k n)))) =
                pullback.snd (orbitTangentProjection k n) (orbitChartMap k n e)) ∧
          ∃ ω : (structureSheafInType (CommRingCat.of (CoordinateRing k n))
              (⋀[CoordinateRing k n]^2 (KaehlerDifferential k (CoordinateRing k n)))).obj.obj
                (Opposite.op (maximalRankOpen k n)),
            (∀ (p : maximalRankOpen k n) (e : Equiv.Perm (n ⊕ n)) (he : p.val ∈ permutationOpen k n e),
              primeExteriorEquiv (CoordinateRing k n) k p.val (ω.val p) =
                kaehlerCanonicalTrace (PrimeLocalRing (CoordinateRing k n) p.val) k
                  ((chartT k n).map (primeChartEvaluation k n p.val e he))
                  ((chartA k n).map (primeChartEvaluation k n p.val e he))) ∧
            (∀ p : maximalRankOpen k n, IsClosed (exteriorGermEvaluation (CoordinateRing k n) k p.val (ω.val p))) ∧
            (∀ p : maximalRankOpen k n,
              deRhamTwo k (PrimeLocalRing (CoordinateRing k n) p.val) (orbitPrimeDifferentialBasis k n p)
                (primeExteriorEquiv (CoordinateRing k n) k p.val (ω.val p)) = 0) ∧
            kaehlerSectionPullback k (CoordinateRing k n) (GeneralLinearRing k n) (orbitCoordinateMap k n)
              (maximalRankOpen k n) ⊤ (fun q _ => conjugationToSquareZero_mem_maximalRank k n q) ω =
                StructureSheaf.toOpenₗ (GeneralLinearRing k n) (KaehlerTwoForms (GeneralLinearRing k n) k) ⊤
                  (-deRhamOne k (GeneralLinearRing k n) (generalLinearDeRhamBasis k n)
                    (maurerCartanPotential k n)) ∧
            cellInclusion ≫ rankOpen.ι =
              Spec.map (CommRingCat.ofHom (cellOrbitCoordinates k n).toRingHom) ∧
            kaehlerSectionPullback k (CoordinateRing k n) (CellRing k n) (cellOrbitCoordinates k n)
              (maximalRankOpen k n) ⊤ (fun q _ => cellOrbitCoordinates_mem_orbit k n q) ω = 0 ∧
            (∀ p : maximalRankOpen k n, Function.Bijective
              (exteriorGermEvaluation (CoordinateRing k n) k p.val (ω.val p))) := by

  -- Common witnesses for all parts
  obtain ⟨r⟩ := AffineOrbitRealization.nonempty k A
  refine ⟨r.Index, inferInstance, inferInstance, r.Equation, inferInstance,
    r.affineEquations, r.sectionIdeal,
    r.coordinateEquiv, r.sectionToAffine, r.sectionToOrbit,
    r.sectionToCell, r.schemeIso, r.card_index_pos, r.affineEquations_totalDegree, ?_,
    r.schemeIso_eq, r.sectionToAffine_comp,
    r.affineInclusion_isClosedImmersion, maximalRankScheme_isImmersion k _,
    r.orbit_intersection, r.cell_intersection, r.sectionToOrbit_eq,
    r.sectionToOrbit_isClosedImmersion, r.sectionToCell_isClosedImmersion,
    cellMorphism_isClosedImmersion k r.Index,
    (fun K _ _ M => inJordanOrbit_iff_square_zero_rank M),
    maximalRankScheme_dimension k r.Index,
    (fun h => by letI := h.toField; exact maximalRankScheme_irreducible r.Index),
    cellSource_dimension k r.Index, ?_⟩

  -- Exact ideal equality
  · simpa only [squareZeroIdeal, genericMatrix] using r.ideal_eq

  -- Symplectic atlas and Lagrangian cell
  · let ω := orbitSymplecticAtlas k r.Index
    refine ⟨ω.chartIso, ω.overlapIso, ω.form,
      (fun _ => localFormPerfect k r.Index), ω.covers, ω.chart_embedding,
      ω.overlap_embedding, ω.form_eq,
      (fun e D => ω.alternating e D), (fun e D E F => ω.closed e D E F),
      ω.perfect_form, ω.compatible, ω.cellMorphism_factors_identity,
      cell_pullback_form_zero k r.Index, ?_⟩
    letI := cellChartAlgebra k r.Index
    letI : IsScalarTower k (ChartRing k r.Index) (CellRing k r.Index) :=
      IsScalarTower.of_algHom (cellChartEval k r.Index)
    refine ⟨cellDifferential_injective k r.Index, cellDifferential_kaehler k r.Index,
      specializeChartDerivation_surjective k r.Index, ?_, cellDifferential_selfOrthogonal k r.Index,
      (fun e => ⟨orbitTangentChartIso k r.Index e, orbitTangentChartIso_over k r.Index e⟩),
      orbitKaehlerTwoForm k r.Index, orbitKaehlerTwoForm_chart k r.Index,
      orbitKaehlerTwoForm_isClosed k r.Index, orbitKaehlerTwoForm_deRhamTwo_eq_zero k r.Index,
      orbitKaehlerPullback_eq_deRham k r.Index, cellMorphism_squareZero k r.Index,
      orbitKaehlerTwoForm_cell_pullback k r.Index, orbitKaehlerTwoForm_perfect k r.Index⟩
    intro D E
    rw [ω.form_eq]
    exact cellOrbitForm_specialize k r.Index D E

/-- The polynomial compiler uses exactly one gate per multiplication node and size `s + 2m`. -/
theorem polynomial_orbit_realization (k V Q : Type u) [CommRing k] [Fintype V] [Fintype Q]
    (f : Q → MvPolynomial V k) :
    letI := Classical.decEq k
    letI := Classical.decEq V
    let P := ExpressionPresentation.ofPolynomials f
    let C := P.gates
    Function.Injective C.output ∧
    Set.range C.output = {t | ∃ a b, t.val = ArithmeticExpr.mul a b} ∧
    Fintype.card (GateSystem.Index P.Wire P.Gate) = P.nodes.card + 2 * Fintype.card P.Gate ∧
    0 < Fintype.card (GateSystem.Index P.Wire P.Gate) ∧
    (∀ q, (C.orbitAffinePolynomials q).totalDegree ≤ 1) ∧
    equationIdeal C.orbitPolynomials = equationIdeal C.orbitAffinePolynomials ⊔
      squareZeroIdeal k (GateSystem.Index P.Wire P.Gate) ∧
    Nonempty ((MvPolynomial V k ⧸ equationIdeal f) ≃ₐ[k]
      (MvPolynomial (GateSystem.OrbitCoord P.Wire P.Gate) k ⧸ equationIdeal C.orbitPolynomials)) := by
  classical
  let P := ExpressionPresentation.ofPolynomials f
  exact ⟨P.gates_output_injective, P.gates_output_range, P.card_index,
    ExpressionPresentation.polynomialIndex_card_pos f, P.gates.orbitAffinePolynomials_totalDegree,
    P.gates.orbitSectionIdeal_eq_squareZero,
    ⟨(ExpressionPresentation.polynomialMatrixCoordinateAlgEquiv f).trans P.gates.orbitCoordinateAlgEquiv⟩⟩

/-- The maximal-rank square-zero scheme represents `GL(2n)/Stab(J)` as an fppf sheaf quotient. -/
theorem homogeneous_space_quotient (k n : Type u)
    [CommRing k] [Fintype n] [DecidableEq n] :

    -- The explicit stabilizer subgroup
    (∀ (S : Type u) [CommRing S] (g : (Matrix (n ⊕ n) (n ⊕ n) S)ˣ),
      g ∈ jordanStabilizer n S ↔
        ∃ P Q : Matrix n n S, IsUnit P ∧ g.val = Matrix.fromBlocks P Q 0 P) ∧

    -- The smooth stabilizer group scheme and its product coordinates
    Nonempty (GrpObj (stabilizerOver k n)) ∧
    (letI := stabilizerGroupScheme k n
     Nonempty (yonedaGrpObj (stabilizerOver k n) ≅ stabilizerGroupFunctor k n)) ∧
    Nonempty (stabilizerScheme k n ≅
      pullback
        (Spec.map (CommRingCat.ofHom (algebraMap k (SmallGeneralLinearRing k n))))
        (Spec.map (CommRingCat.ofHom (algebraMap k (MatrixCoordinateRing k n))))) ∧
    SmoothOfRelativeDimension (2 * Fintype.card n ^ 2) (stabilizerOver k n).hom ∧
    (∀ (T : Scheme.{u}) (g : T ⟶ generalLinearScheme k n),
      (∃ f : T ⟶ stabilizerScheme k n, f ≫ stabilizerInclusion k n = g) ↔
        pointConjugator k n g ∈ jordanStabilizer n Γ(T, ⊤)) ∧
    (∀ T : Scheme.{u}, Function.Injective
      (fun f : T ⟶ stabilizerScheme k n => f ≫ stabilizerInclusion k n)) ∧

    -- The general linear scheme and its usual cosets on every test scheme
    (∀ T : Scheme.{u}, Function.Bijective (fun g : T ⟶ generalLinearScheme k n =>
      (generalLinearBase k n g, pointConjugator k n g))) ∧
    (∀ T : Scheme.{u}, Nonempty ((homogeneousCosets k n).obj (Opposite.op T) ≃
      (k →+* Γ(T, ⊤)) ×
        ((Matrix (n ⊕ n) (n ⊕ n) Γ(T, ⊤))ˣ ⧸ jordanStabilizer n Γ(T, ⊤)))) ∧
    (∀ (T : Scheme.{u}) (g : T ⟶ generalLinearScheme k n),
      homogeneousCosetsEquiv k n T (Quotient.mk _ g) =
        (generalLinearBase k n g,
          (QuotientGroup.mk (pointConjugator k n g) :
            (Matrix (n ⊕ n) (n ⊕ n) Γ(T, ⊤))ˣ ⧸ jordanStabilizer n Γ(T, ⊤)))) ∧

    -- The quotient map is induced by the conjugation morphism
    orbitProjection k n ≫ (maximalRankOpen k n).ι = conjugationToSquareZero k n ∧
    (∀ (T : Scheme.{u}) (g : T ⟶ generalLinearScheme k n),
      (homogeneousQuotientMap k n).app (Opposite.op T) (Quotient.mk _ g) =
        g ≫ orbitProjection k n) ∧
    (∀ (T : Scheme.{u}) (g : T ⟶ generalLinearScheme k n),
      (universalMatrix k n).map (affineCoordinates (g ≫ conjugationToSquareZero k n)) =
        (pointConjugator k n g).val * jordanCell * (pointConjugator k n g).inv) ∧

    -- Smoothness and faithful flatness of the quotient projection
    SmoothOfRelativeDimension (2 * Fintype.card n ^ 2) (orbitProjection k n) ∧
    Flat (orbitProjection k n) ∧ Surjective (orbitProjection k n) ∧

    -- Representability and the universal property of the fppf sheaf quotient
    Presieve.IsSheaf Scheme.fppfTopology (yoneda.obj (maximalRankScheme k n)) ∧
    (∀ (F : Scheme.{u}ᵒᵖ ⥤ Type u) (_ : Presieve.IsSheaf Scheme.fppfTopology F)
      (f : homogeneousCosets k n ⟶ F),
      ∃! g : yoneda.obj (maximalRankScheme k n) ⟶ F,
        homogeneousQuotientMap k n ≫ g = f) :=
  ⟨(fun _ _ g => mem_jordanStabilizer_iff n g),
    ⟨stabilizerGroupScheme k n⟩,
    ⟨yonedaGrpObjIsoOfRepresentableBy _ _ (stabilizerRepresentableBy k n)⟩,
    ⟨stabilizerProductIso k n⟩,
    stabilizerScheme_dimension k n, stabilizerInclusion_range k n,
    stabilizerInclusion_hom_injective k n,
    (fun T => (generalLinearHomEquiv k n T).bijective),
    (fun T => ⟨homogeneousCosetsEquiv k n T⟩),
    (fun _ g => homogeneousCosetsEquiv_mk k n g), orbitProjection_ι k n,
    (fun _ g => homogeneousQuotientMap_mk k n g),
    (fun _ g => conjugation_coordinates k n g),
    orbitProjection_dimension k n, (orbitProjection_faithfullyFlat k n).1,
    (orbitProjection_faithfullyFlat k n).2,
    orbit_fppf_isSheaf k n, homogeneousQuotient_fppf_universal k n⟩

/-- The canonical tangent scheme, its local trivializations, and the differential of conjugation. -/
theorem orbit_differential_geometry (k n : Type u)
    [CommRing k] [Fintype n] [DecidableEq n] :

    -- Spec of the symmetric algebra of the relative Kähler module
    orbitTangentScheme k n = pullback
      (Spec.map (CommRingCat.ofHom (algebraMap (CoordinateRing k n)
        (SymmetricAlgebra (CoordinateRing k n) (KaehlerDifferential k (CoordinateRing k n))))))
      (maximalRankOpen k n).ι ∧
    Surjective (orbitCommutatorMap k n) ∧
    orbitCommutatorMap k n ≫ orbitTangentProjection k n = orbitMatrixBundleProjection k n ∧
    (∀ e, ∃ σ : pullback (orbitTangentProjection k n) (orbitChartMap k n e) ⟶ orbitMatrixBundle k n,
      σ ≫ orbitCommutatorMap k n = pullback.fst (orbitTangentProjection k n) (orbitChartMap k n e)) ∧
    orbitCommutatorMap k n ≫
        pullback.fst (tangentProjection k (CoordinateRing k n)) (maximalRankOpen k n).ι =
      pullback.fst (commutatorBaseProjection k n) (maximalRankOpen k n).ι ≫ commutatorAffineMap k n ∧
    (∀ i j, commutatorCoordinateMap k n
        (SymmetricAlgebra.ι (CoordinateRing k n) _
          (KaehlerDifferential.D k (CoordinateRing k n) (universalMatrix k n i j))) =
      Symplectic.comm (fun i j => MvPolynomial.X (i, j))
        (coefficientMatrix k n (CommutatorRing k n)) i j) ∧
    (∀ e, ∃ τ : pullback (orbitTangentProjection k n) (orbitChartMap k n e) ≅
        Spec (.of (MvPolynomial ((n × n) ⊕ (n × n)) (ChartRing k n))),
      τ.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap (ChartRing k n)
        (MvPolynomial ((n × n) ⊕ (n × n)) (ChartRing k n)))) =
          pullback.snd (orbitTangentProjection k n) (orbitChartMap k n e)) ∧
    orbitProjectionTangentMap k n ≫ orbitTangentProjection k n =
      tangentProjection k (GeneralLinearRing k n) ≫ orbitProjection k n ∧
    (∀ (T : Scheme.{u}) (x : T ⟶ maximalRankScheme k n),
      Nonempty ({f : T ⟶ orbitTangentScheme k n // f ≫ orbitTangentProjection k n = x} ≃
        (letI := (affineCoordinates (x ≫ (maximalRankOpen k n).ι)).toAlgebra
         letI : Algebra k Γ(T, ⊤) :=
           ((affineCoordinates (x ≫ (maximalRankOpen k n).ι)).comp
             (algebraMap k (CoordinateRing k n))).toAlgebra
         Derivation k (CoordinateRing k n) Γ(T, ⊤)))) ∧
    (letI := (orbitCoordinateMap k n).toAlgebra
     letI := IsScalarTower.of_algHom (orbitCoordinateMap k n)
     orbitProjectionTangentMap k n ≫
       pullback.fst (tangentProjection k (CoordinateRing k n)) (maximalRankOpen k n).ι =
         tangentSchemeMap k (CoordinateRing k n) (GeneralLinearRing k n)) ∧

    -- A linear section of the commutator map on the orbit chart
    (chartTangentProjection k n).comp (chartTangentSection k n) = LinearMap.id ∧
    (∀ X : Matrix (n ⊕ n) (n ⊕ n) (ChartRing k n),
      derivMatrix (chartTangentProjection k n X) (generalChart (chartA k n) (chartT k n)) =
        Symplectic.comm X (generalChart (chartA k n) (chartT k n))) ∧

    -- The derivative of the coordinate map defining the quotient projection
    (∀ D : Derivation k (GeneralLinearRing k n) (GeneralLinearRing k n),
      derivMatrix D ((universalMatrix k n).map (orbitCoordinateMap k n)) =
        Symplectic.comm (rightMaurerCartan (generalLinearUnit k n) D)
          ((universalMatrix k n).map (orbitCoordinateMap k n))) ∧

    -- The Maurer–Cartan equation and exact pullback of the KKS form
    (∀ D : Derivation k (GeneralLinearRing k n) (GeneralLinearRing k n),
      D.liftKaehlerDifferential (maurerCartanPotential k n) =
        maurerCartanTrace (generalLinearUnit k n) jordanCell D) ∧
    (∀ D E : Derivation k (GeneralLinearRing k n) (GeneralLinearRing k n),
      derivMatrix D (maurerCartan (generalLinearUnit k n) E) -
        derivMatrix E (maurerCartan (generalLinearUnit k n) D) -
        maurerCartan (generalLinearUnit k n) ⁅D, E⁆ =
          -Symplectic.comm (maurerCartan (generalLinearUnit k n) D)
            (maurerCartan (generalLinearUnit k n) E)) ∧
    (∀ D E : Derivation k (GeneralLinearRing k n) (GeneralLinearRing k n),
      Symplectic.traceForm ((universalMatrix k n).map (orbitCoordinateMap k n))
        (rightMaurerCartan (generalLinearUnit k n) D) (rightMaurerCartan (generalLinearUnit k n) E) =
        -(D (maurerCartanTrace (generalLinearUnit k n) jordanCell E) -
          E (maurerCartanTrace (generalLinearUnit k n) jordanCell D) -
          maurerCartanTrace (generalLinearUnit k n) jordanCell ⁅D, E⁆)) :=
  ⟨rfl, orbitCommutatorMap_surjective k n, orbitCommutatorMap_over k n,
    (fun e => ⟨orbitCommutatorLocalSection k n e, orbitCommutatorLocalSection_comp k n e⟩),
    orbitCommutatorMap_affine k n, commutatorCoordinateMap_D k n,
    (fun e => ⟨orbitTangentChartIso k n e, orbitTangentChartIso_over k n e⟩),
    orbitProjectionTangentMap_over k n, (fun T x => ⟨orbitTangentHomEquiv k n T x⟩),
    orbitProjectionTangentMap_affine k n,
    chartTangentProjection_section k n, chartTangentProjection_derivative k n,
    orbitProjection_derivative k n, maurerCartanPotential_evaluation k n,
    maurerCartan_equation (generalLinearUnit k n),
    orbitProjection_KKS_exact k n⟩

/-- A canonical exterior-square Kähler section, with an invertible contraction and Lagrangian cell. -/
theorem orbit_global_symplectic_form (k n : Type u)
    [CommRing k] [Fintype n] [DecidableEq n] :

    -- The associated sheaf of the exterior square agrees with the regular-expression sheaf
    Nonempty (( (maximalRankOpen k n).isOpenEmbedding.sheafPullback (Type u)).obj
        (structureSheafInType (CommRingCat.of (CoordinateRing k n))
          (⋀[CoordinateRing k n]^2 (KaehlerDifferential k (CoordinateRing k n)))) ≅
      ((maximalRankOpen k n).isOpenEmbedding.sheafPullback (Type u)).obj
        (regularTwoFormSheaf k (CoordinateRing k n))) ∧
    (∀ p : maximalRankOpen k n,
      Function.Injective (kaehlerTwoEvaluation (PrimeLocalRing (CoordinateRing k n) p.val) k)) ∧

    ∃ ω : (structureSheafInType (CommRingCat.of (CoordinateRing k n))
        (⋀[CoordinateRing k n]^2 (KaehlerDifferential k (CoordinateRing k n)))).obj.obj
          (Opposite.op (maximalRankOpen k n)),
      (⨆ e, permutationOpen k n e) = maximalRankOpen k n ∧
      (exteriorSheafEvaluation (CoordinateRing k n) k).hom.app
        (Opposite.op (maximalRankOpen k n)) ω = orbitGlobalTwoForm k n ∧

      -- The wedge formula on the localizations and the chart maps
      (∀ (p : maximalRankOpen k n) (e : Equiv.Perm (n ⊕ n)) (he : p.val ∈ permutationOpen k n e),
        primeExteriorEquiv (CoordinateRing k n) k p.val (ω.val p) =
          kaehlerCanonicalTrace (PrimeLocalRing (CoordinateRing k n) p.val) k
            ((chartT k n).map (primeChartEvaluation k n p.val e he))
            ((chartA k n).map (primeChartEvaluation k n p.val e he))) ∧
      (∀ (p : maximalRankOpen k n) (e : Equiv.Perm (n ⊕ n)) (he : p.val ∈ permutationOpen k n e),
        (primeChartEvaluation k n p.val e he).comp (permutationChartEmbedding k n e) =
          IsScalarTower.toAlgHom k (CoordinateRing k n) (PrimeLocalRing (CoordinateRing k n) p.val)) ∧

      -- Closedness and an isomorphism from derivations to Kähler one-forms
      (∀ p, (exteriorGermEvaluation (CoordinateRing k n) k p.val (ω.val p)).IsAlt) ∧
      (∀ p, IsClosed (exteriorGermEvaluation (CoordinateRing k n) k p.val (ω.val p))) ∧
      (∀ p : maximalRankOpen k n,
        deRhamTwo k (PrimeLocalRing (CoordinateRing k n) p.val) (orbitPrimeDifferentialBasis k n p)
          (primeExteriorEquiv (CoordinateRing k n) k p.val (ω.val p)) = 0) ∧

      -- Equality of sheaf sections: π*ω = -d tr(J g⁻¹dg)
      kaehlerSectionPullback k (CoordinateRing k n) (GeneralLinearRing k n) (orbitCoordinateMap k n)
        (maximalRankOpen k n) ⊤ (fun q _ => conjugationToSquareZero_mem_maximalRank k n q) ω =
          StructureSheaf.toOpenₗ (GeneralLinearRing k n) (KaehlerTwoForms (GeneralLinearRing k n) k) ⊤
            (-deRhamOne k (GeneralLinearRing k n) (generalLinearDeRhamBasis k n)
              (maurerCartanPotential k n)) ∧
      (∀ p : maximalRankOpen k n, ∃ contraction :
          Derivation k (PrimeLocalRing (CoordinateRing k n) p.val) (PrimeLocalRing (CoordinateRing k n) p.val)
            ≃ₗ[PrimeLocalRing (CoordinateRing k n) p.val]
              KaehlerDifferential k (PrimeLocalRing (CoordinateRing k n) p.val),
        ∀ D E, E.liftKaehlerDifferential (contraction D) =
          exteriorGermEvaluation (CoordinateRing k n) k p.val (ω.val p) D E) ∧

      -- The global section itself pulls back to zero along the cell inclusion
      cellMorphism k n ≫ (maximalRankOpen k n).ι =
        Spec.map (CommRingCat.ofHom (cellOrbitCoordinates k n).toRingHom) ∧
      kaehlerSectionPullback k (CoordinateRing k n) (CellRing k n) (cellOrbitCoordinates k n)
        (maximalRankOpen k n) ⊤ (fun q _ => cellOrbitCoordinates_mem_orbit k n q) ω = 0 ∧

      -- The same zero pullback in chart coordinates
      letI := cellChartAlgebra k n
      letI := IsScalarTower.of_algHom (cellChartEval k n)
      kaehlerExteriorMap (ChartRing k n) (CellRing k n) k
        (kaehlerCanonicalTrace (ChartRing k n) k (chartT k n) (chartA k n)) = 0 := by
  refine ⟨⟨orbitExteriorSheafComparison k n⟩, primeTwoEvaluation_injective k n,
    orbitKaehlerTwoForm k n, permutationOpen_cover k n, orbitKaehlerTwoForm_evaluation k n,
    orbitKaehlerTwoForm_chart k n, (fun p e he => primeChartEvaluation_over k n p.val e he),
    ?_, orbitKaehlerTwoForm_isClosed k n, orbitKaehlerTwoForm_deRhamTwo_eq_zero k n,
    orbitKaehlerPullback_eq_deRham k n, ?_, cellMorphism_squareZero k n,
    orbitKaehlerTwoForm_cell_pullback k n, kaehlerCanonicalTrace_cell_pullback k n⟩
  · intro p
    rw [orbitKaehlerTwoForm_evaluation_point]
    exact orbitGlobalTwoForm_alternating k n p
  · intro p
    exact ⟨LinearEquiv.ofBijective (orbitKaehlerContraction k n p)
      (orbitKaehlerContraction_bijective k n p), orbitKaehlerContraction_pairing k n p⟩

end
end Universality

open Lean Elab Command in
run_cmd do
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``Universality.affine_orbit_universality, ``Universality.polynomial_orbit_realization,
      ``Universality.homogeneous_space_quotient,
      ``Universality.orbit_differential_geometry, ``Universality.orbit_global_symplectic_form] do
    let axioms ← collectAxioms name
    let unexpected := axioms.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError "{name} depends on unapproved axioms: {unexpected}"

#print axioms Universality.affine_orbit_universality
#print axioms Universality.polynomial_orbit_realization
#print axioms Universality.homogeneous_space_quotient
#print axioms Universality.orbit_differential_geometry
#print axioms Universality.orbit_global_symplectic_form
