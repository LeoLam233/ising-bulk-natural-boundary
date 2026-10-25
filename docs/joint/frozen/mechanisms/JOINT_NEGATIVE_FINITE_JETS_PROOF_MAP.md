# Actual negative-edge finite coefficient jets

Author-development proof map. No independent audit credit is asserted.

`Negative/FamilyFiniteJets.lean` derives joint complex Frechet smoothness of the literal continued angular coefficient at a negative regular edge, at every finite order. The proof starts from `continuedAngularDensity_negative_joint_analyticAt`, compactness of the full angular box, and `FormFactors.compact_analytic_integral_contDiffAt`. It retains the original factorial and angular normalization and the full onsite multiplier. It does not assume an analytic integral or a derivative-exchange conclusion.

The coefficient is then composed with arbitrary jointly analytic `curve : complex × E → Coupling` and multiplied by the literal `amp^(n+1)`. No finite-dimensional or proper-space assumption on the complex family parameter E is imposed; the compact integral is differentiated in the actual finite-dimensional coupling space before composition.

Exports:

- `continuedAngularCoefficient_negative_contDiffAt n j hn hS hedge hb hB`.
- `weighted_coefficient_negative_joint_contDiffAt n j hn hc ha hS hedge hb hB`.
- `parameterDeriv_contDiffAt` and `jointParameterJet_contDiffAt`: the actual scalar parameter jet is jointly smooth, using its neighborhood equality with the appropriate Frechet derivative evaluation.
- `compact_joint_continuous_zero_difference`: one full complex disk controls the difference from the center for all members of a compact family. The premise is genuine joint continuity, not merely separately continuous fibers.
- `compact_family_weighted_negative_jet_limit`: uniform inward real approach of each actual weighted odd coefficient derivative, suitable directly for the uniform particle-series Tannery theorem.

`Negative/FamilyFinitePrefixes.lean` packages any finite set of odd free-angle indices and all derivatives through a fixed J on one common complex disk, before eta, particle index and derivative order. The endpoint `compact_family_weighted_negative_finite_jets` controls the literal derivative difference, not a model or formal coefficient.

The central hypotheses are only actual analytic family data, S nonvanishing, the literal negative face identity A+T=bS, |b|<1 and Im(-T/S)>0. Uniform full-particle tails, physical upper-side identities and the full derivative-series limit are separate assembly inputs supplied by the negative and transverse workers.

These declarations intentionally assert genuine joint finite-order complex smoothness, rather than claiming an unproved multivariable power-series analyticity theorem for the compact integral. This is sufficient for the actual joint jet continuity and compact-family uniform limit used downstream.

Reproduce with `../../coordination/COMPILE_ONE.sh IsingBulk/Joint/Negative/FamilyFiniteJets.lean` and then the analogous command for `FamilyFinitePrefixes.lean`, from project/lean. Final clean frozen verification remains separate.
