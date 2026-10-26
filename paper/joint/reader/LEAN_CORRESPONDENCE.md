# JOINT supported formal scope

The preserved independent audit expanded the literal full terminal and all eleven outer target fields, including the seven core clauses. The actual source in lean/IsingBulk/Joint/Final/FullConclusion.lean is:

```lean
structure JointFullConclusion (corrH corrL : PhysicalField.CorrelationFamily)
    (mH mL : PhysicalField.MagnetizationFamily) : Prop where
  core : JointCoreConclusion corrH corrL mH mL
  positive_families : JointPositiveFamilyConclusion
  negative_families : JointNegativeFamilyConclusion
  negative_mixed_families : JointNegativeMixedFamilyConclusion
  actual_ratio_families : JointRatioFamilyConclusion
  family_orientations : JointFamilyOrientationConclusion
  mixed_family_orientations : JointMixedFamilyOrientationConclusion
  family_normalization : JointFamilyNormalizationConclusion
  arbitrary_positive_families : JointArbitraryPositiveFamilyConclusion
  arbitrary_negative_families : JointArbitraryNegativeFamilyConclusion
  regular_face_density : JointFaceDensityConclusion

theorem full_joint_conclusion {corrH corrL : PhysicalField.CorrelationFamily}
    {mH mL : PhysicalField.MagnetizationFamily}
    (hphys : PhysicalField.PublishedRealSpinFamily corrH corrL)
    (hfields : PhysicalField.PublishedRealGibbsFamily corrH corrL mH mL) :
    JointFullConclusion corrH corrL mH mL where
  core := joint_core_conclusion hphys hfields
  positive_families := joint_positive_family_conclusion
  negative_families := joint_negative_family_conclusion
  negative_mixed_families := joint_negative_mixed_family_conclusion
  actual_ratio_families := joint_ratio_family_conclusion
  family_orientations := joint_family_orientation_conclusion hphys
  mixed_family_orientations := joint_mixed_family_orientation_conclusion
  family_normalization := joint_family_normalization_conclusion
  arbitrary_positive_families := joint_arbitrary_positive_family_conclusion
  arbitrary_negative_families := joint_arbitrary_negative_family_conclusion
  regular_face_density := joint_face_density_conclusion

```

`PublishedRealSpinFamily corrH corrL` and `PublishedRealGibbsFamily corrH corrL mH mL` concern the same real two-coupling correlations and magnetizations across every positive finite ratio, not unrelated choices on each ray. Joint complex holomorphy, full odd/nonzero-even sums, all mixed compact-normal derivatives and boundary obstructions are internally constructed outputs; physical identification remains conditional on those two real premises.

Geometry exports the two physical components of the unsquared spectral complement, exact ratio pullbacks, contractibility, pseudoconvex exhaustion and correct product-modulus inequalities. Boundary/continuation clauses cover every physical frontier, actual nonramified transversals, all positive-ratio slices and reachable unramified continuations. Isotropic descendants use exact normalized identities, disk biholomorphism and LT covering/deck translations; there is no global exterior single-valued beta. Physical clauses retain all lattice sites, onsite1/1−M², plus-state subtraction, bilateral HT and right-sided LT field derivatives, and beta=z/(2J).

The quantitative fields retain one common compact-family tube before every mixed derivative order and particle index, nonzero leading amplitudes, actual complex-ratio families, orientation transport, arbitrary-family analytic inverses with exact recovery, and same-face fixed-B density. The selected negative Taylor order may depend on the family parameter; no uniformity over all primes or through Im B=0 is asserted. The negative coefficient predicate exports sufficient selected exponential growth and radius zero, not every sharper manuscript scalar equivalence. Weighted W and normalized physical X satisfy X=(highPrefactor/amp)W; their boundary derivatives are the finite Leibniz convolution, not unchanged coefficientwise sharp asymptotics.

The manuscript-only auxiliary scalar equivalents, complete shifted-cell enumeration and unified isotropic local presentation remain preserved manuscript mathematics. This ledger states the supported actual formal scope, not a literal encoding of every auxiliary display. No fresh Lean elaboration, compilation, kernel replay, original theorem reproof or independent human certification is claimed.
