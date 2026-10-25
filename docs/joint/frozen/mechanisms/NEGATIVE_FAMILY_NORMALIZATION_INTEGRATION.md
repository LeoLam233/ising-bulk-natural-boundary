# Generic-family normalization attachment

Author source integration and implementation, 2026-10-23 15:57 UTC. This is
not an independent audit, fresh checker receipt, or whole-project build.

## Exact clause and original mismatch

JOINT Theorem 1.1(4), PDF p.2 (`JOINT.txt:63–68`), requires local uniformity
for compact admissible subfamilies of bounded holomorphic complex-parameter
families on common polydisks in a regular-edge chart. Section 7.1, PDF p.55
(`JOINT.txt:3148–3167`), changes any nonramified transversal to its actual edge
coordinate. Section 5, PDF pp.25 and 39 (`JOINT.txt:1341–1373,2200–2217`),
uses the variable complex anisotropy in that coordinate. Lemma 7.1 is the
additional actual-ratio specialization, not a replacement for arbitrary families.

Before this repair, `Final/PositiveFamilyConclusion.lean:22,44,66` and
`Final/NegativeFamilyConclusion.lean:36–39` assumed exact normalized edge germs.
`Transverse/CurveCoordinates.lean:49,75` provided scalar inverses only;
`FormFactors/ComplexRatio.lean:126–136` provided the special ratio family only.
Conjoining those with orientation transport did not construct a common joint
inverse for an arbitrary original holomorphic family.

## Actual common analytic construction

`Transverse/FamilyNormalizationLocal.lean` proves the true augmented-map IFT
for `(z,eta) ↦ (f(z,eta),eta)`, using the actual triangular Fréchet derivative
and its explicit bijectivity. The parameter space may be any complete complex
normed space, so all finite complex polydisks are included.

`Transverse/FamilyNormalization.lean:16–23` defines `FamilyNormalization`.
`exists_familyNormalization` (line 27) constructs it from only joint analyticity
at `(0,eta0)`, `f(0,eta0)=0`, and nonzero scalar z derivative. It chooses a
single radius BEFORE all parameter values, derivatives, or particle indices.
The inverse is jointly analytic on the entire product disk, preserves eta,
satisfies both exact inverse identities, and fixes every selected center.

`FamilyNormalization.normalizedFamily`, `normalized_analyticAt_center`, and
`original_recovered` retain the original curve exactly, rather than substituting
an unrelated local family. `FamilyNormalizationAttachment.lean` shrinks the
same inverse disk into the original curve's actual analytic-center neighborhood.
No familywise analyticity or normalization is added as an extra premise.

`FamilyNormalizationDeriv.lean` additionally proves the exact derivative-product
identity and nonvanishing of the inverse derivative at every selected center.
This helper is available but not claimed necessary for the current final proof
closure; the two inverse identities are already retained in its structure.

The scope is genuinely LOCAL, as in the manuscript: one common product disk
at an arbitrary parameter center, followed by EVERY compact admissible subset
of its parameter disk. No global inverse over a disconnected parameter domain
or uniformity through a zero edge derivative is asserted.

## Actual negative-odd attachment

`Negative/FamilyArbitraryPhysical.lean:25` proves
`IsingBulk.Joint.Negative.arbitrary_negative_high_family_estimates`.
The inputs are the original joint analytic curve, actual S/nonzero and negative
B sign at its base, fixed prime phase, and original scaled-edge zero/nonzero
derivative. The normalization N is constructed BEFORE any compact Q.

The output explicitly recovers the original curve on the common source disk
(lines 31–33). Every compact Q in that parameter disk with actual selected
edge-zero, frontier, S, noncritical p, and negative B center conditions receives
`Transverse.NegativeHighFamilyEstimates` (lines 34–40). These are admissibility
conditions on ORIGINAL centers, not exact normalized germs or estimate premises.

The amplitude is internally fixed to `i*S*sqrt(-B)`. Its actual joint analyticity
is proved, and its square equals p exactly. No amplitude existence, square-root
choice, physical side, coefficient range, transport, or estimate is assumed.
The conclusion includes the true complete coefficient obstruction, uniform
boundary limits of the literal normalized physical susceptibility, and all
ambient mixed derivatives of literal physical particle tails.

The final Prop bundle is `JointArbitraryNegativeFamilyConclusion`, proved by
`joint_arbitrary_negative_family_conclusion` in `Negative/FamilyArbitraryConclusion.lean`.
The generic inverse Prop bundle is `JointFamilyNormalizationConclusion`, proved
by `joint_family_normalization_conclusion` in `Transverse/FamilyNormalizationConclusion.lean`.
Both must be USED in the final conjunction, alongside the three positive/even
arbitrary-family attachments owned by the transversal author.

## Orientation interface note

The old `PhysicalFamilyOrientationTransport.uniform_reflected` takes a physical
side U independent of eta. The negative-odd side `Im(B(u,eta)*u)>0` varies with
eta. The existing primitive
`Transverse.highNormalizedBulk_uniform_scaled_reflected` instead requires only
common physical membership and continuity ALONG the approach ray; the negative
family has precisely that common inward ray. The geometry author has been
notified to expose this compatible version in the final orientation Prop.
No new singularity estimate is missing at this interface.

## Verification

Strict pinned module compilation completed for FamilyNormalizationLocal,
FamilyNormalization, FamilyNormalizationDeriv, FamilyNormalizationConclusion,
FamilyArbitraryPhysical, and FamilyArbitraryConclusion. Attachment helpers were
strictly compiled by their author. No protected baseline source was edited.
No heavy closure scan, full build, fresh checker, or independent audit was run.

At 15:58 UTC, source inspection confirmed actual `full_joint_conclusion` proof calls to `joint_family_normalization_conclusion` and `joint_arbitrary_negative_family_conclusion` at `Final/FullConclusion.lean:43,45`, not merely imports. This is a source integration observation, not a fresh whole-root verification.

At 15:59 UTC, the geometry author strictly compiled the orientation repair:
`PhysicalFamilyOrientationTransport.uniform_swap_approach` and
`uniform_reflected_approach` use actual uniform eventual physical membership
and continuity along the approach. The mixed version now also accepts an
arbitrary joint set `W ⊆ ℂ × E` through `tails_swap_on` and
`tails_reflected_on`, preserving the same summable envelopes. Thus the
eta-dependent negative-side interface caution above is resolved.

## Canonical negative root and odd sign covariance (15:59 UTC)

The new arbitrary-family attachment chooses
`Transverse.negativeEvenParticleRoot K = i*S(K)*sqrt(-transferB(K))`.
The name originates in the even shift, but the proven square-root property is
not parity-specific: `negativeEvenParticleRoot_sq` proves its square equals p
for every K (`Transverse/FamilyNegativeEvenIdentity.lean:17–23`). Its joint
analyticity on the negative-B chart is proved at lines 36–44, and nonvanishing
from S≠0 and Im(-B)>0 at lines 25–32. In `FamilyArbitraryPhysical.lean:69–75`
these facts are actually used with the normalized original family.

It is NOT silently equated to `S*sqrt(B)`. In the negative-B orientation those
two branch expressions may differ by sign, and the argument is sign-covariant:

* `Negative.negative_high_weighted_particle_eq`,
  `FamilyPhysicalSum.lean:24–35`, proves the literal physical coefficient
  identity for ANY a satisfying a²=p:
  a*(p^m*fullCoefficient(2*m+1)) = a^(2*m+1)*continuedAngularCoefficient(2*m).
* `weightedPhysicalHigh`, lines 12–13, is exactly a times the complete physical
  odd series. Thus a→−a negates every odd term and the whole weighted sum.
* `weightedPhysicalHigh_eq_normalized`, lines 17–22, retains the exact physical
  factor: W_a=(a/highPrefactor)*highNormalizedBulk. The reverse multiplier is
  highPrefactor/a. Changing a's sign negates BOTH that multiplier and W_a, so
  their product is the SAME literal normalized physical susceptibility.
* `normalizedHighBoundaryJet`, `FamilyNormalizedJets.lean:15–23`, differentiates
  the complete multiplier-times-weighted-sum product by the finite Leibniz
  convolution. Both differentiated factors acquire one minus sign, which
  cancel in every summand, not only in the zeroth derivative.
* The coefficient obstruction theorem accepts arbitrary analytic amp with
  amp²=p; its actual scalar residue/model uses the same chosen amp. Replacing
  amp by its negative changes all odd coefficients by the same global sign,
  never by particle-dependent phases. Norm growth and radius zero are unchanged.

Accordingly the arbitrary negative-odd theorem uses the canonical root's own
proved hypotheses and actual physical identities. It does not require an
unproved branch equality or discard an odd-particle phase.
