import Universality
import Lean.Util.CollectAxioms

/-!
# Kernel dependency audit

Run `lake env lean Universality/Audit.lean` after `lake build`.
This command checks the exported theorem and its principal geometric certificates.
It fails if any transitively used axiom lies outside Lean's standard classical basis;
in particular, a proof containing `sorry` fails this audit.
-/

open Lean Elab Command in
run_cmd do
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let declarations : Array Name := #[
    ``Universality.affine_orbit_universality_explicit,
    ``Universality.affine_orbit_universality,
    ``Universality.lagrangian_squareZero_orbit_universality,
    ``Universality.GateSystem.sectionToOrbit_isPullback,
    ``Universality.GateSystem.sectionToCell_isPullback,
    ``Universality.SquareZeroGeometry.maximalRankScheme_dimension,
    ``Universality.SquareZeroGeometry.maximalRankScheme_irreducible,
    ``Universality.SquareZeroGeometry.maximalRankScheme_isImmersion,
    ``Universality.SquareZeroGeometry.cellMorphism_isClosedImmersion,
    ``Universality.GlobalSymplectic.orbitSymplecticAtlas,
    ``Universality.GlobalSymplectic.cell_pullback_form_zero,
    ``Universality.inJordanOrbit_iff_square_zero_rank,
    ``Universality.inJordanOrbit_iff_rank_witness,
    ``Universality.standardKernelFlagEquiv,
    ``Universality.dualNumberRepresentationEquiv,
    ``Universality.dualNumber_not_field_quotient,
    ``Universality.ScalarSquareExpr.cannot_compute_mul,
    ``Universality.FiniteDiagram.finiteDiagram_orbit_universality,
    ``Universality.GateSystem.orbitAffinePolynomials_rational_bitSize]
  for declaration in declarations do
    unless (← getEnv).contains declaration do
      throwError "Audit target does not exist: {declaration}"
    let axioms ← collectAxioms declaration
    let unexpected := axioms.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError "{declaration} depends on unapproved axioms: {unexpected}"
    logInfo m!"{declaration}: {axioms}"
  logInfo m!"PASS: all {declarations.size} audited declarations use only the standard classical axioms."
