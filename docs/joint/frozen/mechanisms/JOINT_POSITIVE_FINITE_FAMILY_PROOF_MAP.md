# Positive regular-edge compact-family finite remainder

Author development map, not an independent audit. All modules below were strictly compiled with pinned Lean 4.34.1, warnings as errors, and canonical output.

## Mathematical scope and exact quantifiers

The common convention is a complex normed parameter space E, a compact set Q in E, and genuinely jointly analytic functions B,S : complex × E → complex at every (0,eta), eta in Q. The only central scalar conditions are Im B(0,eta)>0 and S(0,eta) != 0. B is never frozen in the transverse coordinate. The selected free phase b satisfies |b|<1. All bounds and radii precede eta in the conclusion.

1. `RegularEdges/FamilyFiniteAnalytic.lean`: `familyEdgeAmplitude`, `familyEdgeDenominator`, and `familyEdgeJet` are the literal baseline factors, with eta inserted. Their joint analyticity is derived at every real angular configuration. These are not replacement model kernels.
2. `FamilyFiniteAway.lean`: `familyAngularJet_continuousAt` and `compact_family_constrained_jet_bound` give a common full-density jet bound on any compact angular subset with actual lattice-product nonvanishing. `compact_family_nonresonant_integral_bound` applies this to the entire constrained cube when continuedRoot(b)^(n+1) != 1. This bound holds on a common full complex disk.
3. `FamilyFiniteGap.lean`: `compact_family_root_gap` proves the actual common root gap c(Im u+q²) <= 1-|root|. `compact_family_shapeDenominator_gap` gives c(t²+||x||²) <= |denominator| for the genuinely varying B on u=i*t².
4. `FamilyFiniteLocal.lean`: `compact_family_local_factors` gives common analytic neighborhoods and amplitude-jet bounds. `compact_family_shape_derivative_neighborhood` proves the exact density-derivative/Vandermonde/rational-numerator identity on one common neighborhood, before all derivative orders.
5. `FamilyFiniteShape.lean`: `compact_family_shape_local_bounds` gives common continuity and amplitude bounds in the Euclidean constrained shape variables. `compact_family_actualLocal_eq` identifies the actual local derivative integral with the literal local jet integral for all eta and all j on common radii.
6. `FamilyFiniteHigher.lean`: if n>=1 and 2*(j+1)<=(n+1)*n, `compact_family_higher_pointwise_bound` cancels the actual Vandermonde order against the actual denominator gap. `compact_family_higher_integral_bound` combines this local estimate with the compact-away estimate over the complete constrained cube. It does not invoke fiber-dependent eventual integrability or decomposition.
7. `FamilyFiniteComplement.lean`: `compact_family_complement_integral_bound` bounds the literal cutoff complement on a common complex disk.
8. `FamilyFiniteCoefficients.lean`: `compact_family_upper_data` produces one disk with actual analyticity and physical scalar positivity/nonvanishing. `compact_family_coefficient_jet_identity` proves exact differentiation under the full constrained integral on that common upper disk, for every n and j, with the original factorial/angular normalization. `compact_family_nonresonant_coefficient_bound` and `compact_family_higher_coefficient_bound` are bounds for literal derivatives of `angularCoefficient`, not only integrands.
9. `FamilyFiniteSums.lean`: `compact_family_finite_coefficient_bounds` and `compact_family_finite_derivative_sum_bound` choose one delta,C before eta,t,n,j for any finite particle-index set F and every j<=J, assuming only that each n in F is nonresonant or satisfies the higher-degree criterion at J. Thus the complete lower plus higher finite remainder is bounded, including every derivative through J.
10. `FamilyFiniteDecomposition.lean`: `edgeConstrainedJet_upper_continuous` derives actual angular continuity of every jet directly from joint analytic density on the upper side. `compact_family_full_decomposition` proves the exact full = inverse-square-root(n+1) times actual local + complement decomposition with one radius before eta. This is the common-family replacement for the old fiber-dependent eventual decomposition.

## Assembly interface

The leading family worker consumes `compact_family_shape_local_bounds`, `compact_family_actualLocal_eq`, `compact_family_complement_integral_bound`, `compact_family_full_decomposition`, and `compact_family_coefficient_jet_identity` to attach the uniform scaled local limit to the full literal coefficient.

The transverse/full-sum worker consumes `compact_family_finite_derivative_sum_bound` with its separately proved selected parity and first-resonant arithmetic. The all-index Gaussian mixed tail is a distinct theorem from the holomorphy worker. This map does not claim that finite bounds alone prove the full physical asymptotic or nonextension.

## Reproduction

From project/lean run `../../coordination/COMPILE_ONE.sh IsingBulk/Joint/RegularEdges/<module>.lean` in the listed dependency order. Final frozen clean verification and independent mathematical audit are separate obligations; no such audit credit is claimed here.
