import Universality

/-!
# Verified theorem statements

Lean prints the public theorem, its complete realization certificate, and the
principal geometric statements. Run after `lake build`:

    lake env lean Universality/Statements.lean
-/

set_option format.width 100

#check @Universality.affine_orbit_universality
#print Universality.AffineOrbitRealization
#check @Universality.lagrangian_squareZero_orbit_universality
#check @Universality.GateSystem.sectionToOrbit_isPullback
#check @Universality.GateSystem.sectionToCell_isPullback
#check @Universality.SquareZeroGeometry.maximalRankScheme_dimension
#check @Universality.SquareZeroGeometry.cellMorphism_isClosedImmersion
#print Universality.GlobalSymplectic.AlgebraicSymplecticAtlas
#check @Universality.GlobalSymplectic.cell_pullback_form_zero
