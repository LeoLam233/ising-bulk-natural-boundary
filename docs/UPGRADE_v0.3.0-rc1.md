# Mathematical change report

Candidate pair: **manuscript v0.1-rc5 / Lean v0.3.0-rc1**, developed from intake commit `84e528bde0da0990f203e36c1b5d92430bda1637`. The manuscript source and mathematical implementation are committed at `a79c2f5701111b5234bbc0ff8481e75aec8c21d0`. Later commits bind verification, documentation and receipts. No frozen tag, original paper asset or historical audit verdict is changed.

## 1. E3 replacement: completed internal proof

The old canonical endpoints genuinely required `PublishedTWFixedOrderInput`. It was not an axiom, so the baseline core axiom union did not establish its absence.

The new geometric argument works at any positive dispersion level `0<S<2` and non-Nickel point. For a nonnegative active-vector zero combination:

1. A pair coefficient would force two reciprocal coordinates to have negative imaginary parts, impossible on the unit torus.
2. A positive product coefficient makes every corresponding dispersion weight positive and the relevant coordinates strictly lower.
3. With both products positive, the common imaginary ratio and strict lower-dispersion ratio injectivity force constant x and y tuples. Their products imply x^N=y^N=1, giving a Nickel equation.
4. With only one product positive, all other coordinates are +1; the -1 alternative contradicts S>0. The lower coordinates again coincide and have product one. Since +1 is an Nth root, this also gives a Nickel equation.
5. Without product coefficients, dispersion-only coefficients vanish since both imaginary coordinates cannot be zero for 0<S<2.

Thus all coefficients vanish. Finite-dimensional convex separation gives a quantitative active-factor separator at each torus point. The existing analytic complement core is generalized only in its dimension/geometry input; original selected-chart theorem signatures remain proved compatibility wrappers. It retains actual angular weights, inactive-factor regularity, damped half-line exponentials, all generated transpose-IBP coefficient derivatives, auxiliary integrability, source differentiation interchange, finite smooth torus refinement and seam lifts.

For ell active factors and j fixed parameter derivatives, the auxiliary cost is R^j. Taking q=ell+j+1 IBP steps leaves the integrable radial tail R^-2 dR. The original normalized **offsite double integral** is bounded directly. No abstract bounded surrogate or stronger published neighborhood theorem replaces it.

The chosen radius r(epsilon) is held fixed while taking each complex derivative. Strict trace margin supplies a genuine local analytic neighborhood and the existing radius-independence theorem identifies its derivative with the actual exterior form factor. Prime-family arithmetic excludes every lower even Nickel order. Finite lower-order/derivative windows admit a common positive approach interval; no bound uniform over infinitely many orders is asserted.

The full-site identity `C_N^std=f00^(N)+2T_N` and the separate internal onsite bound remain intact. The canonical route proves T_N directly; optional published full-site transfer theorems are retained only for comparison.

Actual integration:

```text
NonNickelGeometry
  -> generic Complement* source estimates
  -> NonNickelRadialBounds
  -> LowerOrderTransfer / LowerOrderFixedRadius
  -> LowerEvenSum / FIRST
  -> UpperNoncancellation
  -> theorem_nb / theorem_nb_physical
```

Both canonical NB conclusions retain their original observable, full exterior domain, dense family and physical-sheet scope. `theorem_nb` has no external premise; `theorem_nb_physical` retains E1/E2 and positive coupling. FIRST also drops E3. The compiled dependency control traverses **types and proof bodies**, bans the E3 predicates and published-transfer helpers, and requires the internal separator/IBP/radial-bound route. A negative control introduces an unused E3 parameter on an otherwise valid NB wrapper and must be rejected.

The gradient method is an acknowledged precedent of [Tracy–Widom 2014, published pp.1127–1131](https://www.math.ucdavis.edu/~tracy/selectedPapers/2010s/CV100.pdf). Removing this premise is an internal reconstruction/formalization improvement, not a claim to have invented that method.

## 2. Proposition 6.1: completed strengthening, existing formal support

Baseline Lean already proves `selected_actual_pair_bounds` with `1+C/N` throughout the actual protected c/N disk. The manuscript's branch–compact statement was weaker.

Keep the true branch root w at its **disk-point** value. Its positive W-imaginary margin keeps it in the closed lower unit disk. The compact radial-center root z0 lies in a fixed compact subset of that half-disk excluding ±1. Uniformly, either |z0|<=1-g or Im(z0)<=-g, which implies |1-z0 w|>=g for every such w. Compact root motion alone gives |z-z0|<=L/N. After reducing disk constant, |1-zw|>=g/2, and the exact identity

```text
A(z,w)-A(z0,w) = (z-z0)(1-w^2) / ((1-zw)(1-z0w))
```

gives |A(z,w)|<=1+4L/(g^2 N). No square-root branch displacement enters. Existing compact-image theorems cover transition supports and root-group membership; perturbed compact roots need not be inside the unit disk. The later square-completion budget remains, using a permissible weaker bound.

## 3. Closed amplitude and normalization: completed specified identities

Hermite orthogonality evaluates the Gaussian Vandermonde integral as (2pi)^(N/2) times the product of m!, m=1,...,N. Separating the unit mean coordinate and then the zero-sum radial coordinate gives the **same** angular constant

```text
C_N = (2pi)^((N-1)/2) product(m!, m=1..N)
      / (sqrt(N) 2^(a0-1) Gamma(a0)).
```

Substitution into the proved beta period gives manuscript (B.1), a factorial/elementary expression for L_beta with the original continuation of (-i d)^(-a0). The original positive-integral nonvanishing proof is preserved.

| Coefficient | Single-chart convention / total |
|---|---|
| One chart, kth complex derivative | L_beta |
| One chart, original radial singular power | A_chart=L_beta exp(i k theta_*) sqrt(pi)/Gamma(a0) |
| Complete fixed-order offsite T_N | 2A_chart; derivative coefficient 2L_beta |
| Full-site C_N^std | 4A_chart; derivative coefficient 4L_beta |
| Normalized physical bulk X | derivative coefficient 4M²(s_*)L_beta |
| Physical chi | additionally multiply by the chosen local inverse-temperature factor |

For the expressly defined principal-power expression R_N(vartheta) obtained from [McCoy–Maillard 2012 (69)–(70)](https://arxiv.org/pdf/1203.1456), Appendix F proves `A_chart=R_N(-theta_*)=-i R_N(theta_*)`. The radial variables agree to first order: epsilon_review=epsilon/(1+epsilon). This real change cannot remove a phase discrepancy. The review's cosine relation alone does not specify its angle sign, power continuation or total-chart convention. An unconditional identity between its complete printed observable and the complete internal amplitude is therefore **not claimed**.

The Hermite proof and mean/hyperplane decomposition are analytic. Exact Gaussian moment determinants and an independent N=2 direct shape integral corroborate them; 80-digit arithmetic compares unsimplified and closed coefficients at selected N=22,26,34,58. These executed checks are not substituted for the analytic proof. This new evaluation is not exported as a Lean factorial theorem.

## 4. Smoothness and arc geometry: completed with scoped constants

At a selected point the actual bulk kth complex derivative diverges with nonzero inverse-square-root coefficient. A real C^k extension agreeing on the exterior would have bounded kth derivative on the radial curve. Lean proves this implication using restriction of complex Fréchet derivatives to real scalars, not an assertion that real smoothness implies holomorphy. The canonical `theorem_selected_no_Ck_extension` discharges TAIL internally.

For prime p>=11, set h=2pi/p and use the adjacent angle pairs jh,(j+1)h. Their selected arguments t_j satisfy:

- t_j is at least (j+1/2)h, by concavity of cosine.
- Consecutive gaps are less than 3h/2.
- The first angle is at most sqrt(5/2)h, by convexity of cos(sqrt(u)).
- The final distance to pi/2 is at most 5h/4.

After sign and conjugation images, every circular gap is at most sqrt(10)h. Therefore every open arc of length ell>2sqrt(10)pi/p contains a selected image point of derivative order k=2p²-1. Bertrand's prime bound gives `k<max(968,320pi²/ell²)`. The point and finite prime are chosen before all point-dependent constants.

The prime number theorem additionally gives the **asymptotic** leading ceiling `(80pi²+o(1))/ell²` as ell tends to zero. The bare constant 80pi² is not a uniform finite covering guarantee. An exact rational certificate exhibits ell=8/5 centered at the positive real axis: the proposed ceiling lies between k(11)=241 and k(13)=337, but the p=11 real-axis gap exceeds 8/5. This refutes that finite covering shortcut for this family, not every possible stronger regularity theorem.

The all-arc corollary and quantitative prime geometry are manuscript-only. The formal counterpart is the actual selected-point real Ck obstruction. A boundary trace without an agreeing exterior extension, a single finite order at every boundary point, and degenerate endpoint amplitude statements are outside the claim.

## 5. Targeted exposition and remaining boundaries

Lemma 4.3 includes the strict ratio derivative and complete single-product case. Proposition 8.2 explains polynomial finite-jet costs, the Hessian operator-norm factor and uniform decay in the actual particle/parameter window. Appendix D spells out the Jacobian/Lie product calculation for real cutoffs. Existing labels, microcore +4, rational-weight exponents, pair slack, parameter-selection order, contour normalization and working tail estimates are retained.

No unresolved load-bearing obligation is added by these improvements. E1/E2 remain explicit physical premises. The literature's unspecified global amplitude conventions remain unresolved and no such identity is used. New factorial/covering exports in Lean, exhaustive priority clearance and independent human/group validation are not claimed. The unchanged baseline tail has not received a new independent human rederivation.

Exact successes, failures, commands and unavailable checks are in [validation](../release/next/VALIDATION.json); [the consistency audit](CONSISTENCY_AUDIT_v0.3.0-rc1.md) is a separate mandatory acceptance stage. Historical release and audit identities remain as listed in [VERSIONS](VERSIONS.md).
