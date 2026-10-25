# Quantitative orientation transport for JOINT Theorem 1.1(4)

This is an author-development proof map, not an independent audit.

## Literal objects and scope

The endpoints below concern `FormFactors.highNormalizedBulk` and
`FormFactors.lowNormalizedBulk`, including the original complete sums and
physical prefactors. Reflection uses the published real-spin interface already
used in the joint physical identification; exchange of axes needs no such
additional input. No theorem infers line nonextension from ambient nonextension.

`Transverse/FamilyOrientations.lean` defines `swappedFamily` and
`reflectedFamily`. The latter is `q ↦ star (curve (star q))`, reflecting BOTH
the edge variable and the complex family variable. Its parameter type may be
any complex normed space with isometric conjugation, in particular every
finite complex parameter polydisk. Uniform transport itself only needs a star
operation on the parameter set.

## Genuine analyticity under reflection

`Transverse/AnalyticReflection.lean` constructs `reflectedMultilinear` by
conjugating every source slot and the output of a complex continuous
multilinear map. Both conjugations are necessary for complex multilinearity.
`reflectedMultilinear_norm_le` proves the operator-norm bound.
`analyticAt_star_star` constructs the reflected convergent power series,
transfers its convergence radius by the coefficient norm bound, and transfers
the actual sums using `HasSum.star`. Consequently
`reflectedFamily_analyticAt` is genuine joint `AnalyticAt`, not merely scalar
analyticity, an antiholomorphic map, or an assumed reflected-family interface.

## Exact jets and common estimates

* `iteratedDeriv_swapped_curve` and `iteratedDeriv_reflected_curve` first
  establish equality of the actual physical germs using openness of the
  physical domain and continuity of the curve, and only then differentiate.
* `iteratedDeriv_reflected_curve_norm` is equality of norms for every order.
  Thus all common derivative bounds transfer with exactly the same constants.
* `uniform_scaled_jets_swapped` preserves a common scaled limit.
* `uniform_scaled_jets_reflected` conjugates the complete complex scale,
  limit, edge approach path, and family parameter. In particular there is no
  discarded phase in a negative-even or opposite-half-plane endpoint.
* `highNormalizedBulk_uniform_scaled_swapped`,
  `lowNormalizedBulk_uniform_scaled_swapped`,
  `highNormalizedBulk_uniform_scaled_reflected`, and
  `lowNormalizedBulk_uniform_scaled_reflected` discharge the symmetry input
  for the literal actual susceptibilities.
* `isCompact_reflected_parameters` preserves compactness;
  `reflected_closedBall` preserves the radius of each closed parameter ball.
  For a finite product with the maximum norm, these are the common polydisks.
* `swappedFamily_high_iff`, `swappedFamily_low_iff`,
  `reflectedFamily_high_iff`, and `reflectedFamily_low_iff` preserve the same
  physical domain, not just the ambient spectral complement.

These transport lemmas take a proved oriented uniform limit as their source,
not a conjectured estimate of the transformed function. Their geometric
premise is the actual common physical-side tube supplied by the family-side
modules. They are intended to be assembled with the positive odd/even,
negative-even, and negative-odd actual-family theorems. They do not themselves
replace those substantive oriented estimates, the selected-point density
proof, or the independent equal-coupling mechanism.

## Other mandatory actual family attachments authored here

* `FormFactors/ComplexRatioPhysicalSide.lean` proves a common product radius
  for the actual positive-edge ratio family, membership in the same physical
  domain iff the raw edge coordinate has positive imaginary part, and actual
  frontier membership of EVERY nearby complex-ratio center.
* `FormFactors/ComplexRatioNegativeSide.lean` proves the identical actual
  statement for the raw negative edge `C+B-b=u`, preserving `Im B < 0`.
  This is the negative-even low-temperature normalization, not the scaled
  negative-odd coordinate.
* `Negative/FamilyNormalizedJets.lean` exports
  `compact_negative_high_normalized_boundary_jets`, a common uniform limit
  for every derivative of the literal high-temperature normalized bulk along
  the actual inward negative ray. Its named boundary function
  `normalizedHighBoundaryJet` is the exact finite Leibniz convolution of the
  analytic physical unit with the actual complete boundary derivative sum.
  No new bound, side-membership or convergence conclusion is assumed.

All declarations in this map were compiled by the pinned strict
`coordination/COMPILE_ONE.sh` route. This map does not assert an optional
second zero-radius theorem for the normalized formal series; the manuscript
transfers that nonextension by division by its nonzero physical unit.

## Explicit final bundles and all ambient mixed tails

`FamilyOrientationConclusion.joint_family_orientation_conclusion` is used
explicitly by `Final/FullConclusion.family_orientations`. Besides the exact
common-tube fields, its `uniform_swap_approach` and
`uniform_reflected_approach` fields use actual eventual membership and
continuity along the common approach. Thus the negative-odd side
`Im (B(u,eta)*u)>0` is not incorrectly required to be independent of eta.

`MixedReflection.iteratedFDeriv_star_star` proves the entire reflected
continuous multilinear derivative map under finite `ContDiffAt`;
`norm_iteratedFDeriv_star_star` proves exact operator-norm equality. The
proof uses a genuine conjugate-linear continuous map on multilinear maps
and induction with the semilinear chain rule. It does not assume unproved
joint power-series analyticity of the contour integral.

`FamilyMixedOrientation.mixedPhysicalFamilyOrientationTransport_of_symmetries`
uses actual physical germ equality and the mixed identities. Its tail fields
preserve the identical all-order summable majorants and common tube radius.
Its `tails_swap_on` and `tails_reflected_on` also allow arbitrary actual
approach sets in the full joint parameter space, so family-dependent sides
are included without replacing them by an eta-independent half-plane.

`FamilyMixedOrientationConclusion.joint_mixed_family_orientation_conclusion`
instantiates this interface with literal `highFullParticle` and
`lowFullParticle`, using the exact swap/conjugation and finite smoothness
theorems of `FamilyParticleSymmetry`. The conjugation ultimately uses the
actual coefficient and physical-prefactor identities in
`FormFactors/ParticleConjugation`, with no real-spin premise. The theorem
is explicitly used by `Final/FullConclusion.mixed_family_orientations`.

## Selected points on every regular face

`Geometry/FaceDensityConclusion.joint_face_density_conclusion` supplies the
explicit local-face quantifier, rather than only global frontier density.
`selectedTransferFace D B0 eps` requires the same physical frontier, a genuine
prime-selected regular edge, exactly fixed B0, and the same endpoint eps.
Every neighborhood of every regular transfer face contains such a point;
both endpoint signs and both half-plane orientations are covered. Every
regular boundary point uses this chart or its axis-exchanged chart.
