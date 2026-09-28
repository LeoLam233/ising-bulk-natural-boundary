# Attempted routes, quantitative obstructions, and self-audit

Run `ISING-CR0-20260927-ba3792d2458a`. These are public mathematical work notes and evidence limits, not a private reasoning transcript.

## 1. Particle-by-particle product bounds

For \(|s|\ge r>1\), the root estimate gives \(|h_{jk}|,|y_j|\le H_r\). Directly multiplying all pair bounds gives \(H_r^{n^2}/n!\), which does not establish convergence for \(H_r>1\). This is a failure of that bound, not divergence of the susceptibility. The finite determinant identity reduces the bound to \(n^{n/2}H_r^{2n}/n!\), and this does prove normal convergence of the entire exterior series. That repair was carried through analytically and checked numerically.

Near the boundary, however, even the repaired majorant is inadequate. For \(n=2m\),

\[
 \frac{n^{n/2}H^{2n}}{n!}
 \le \left(\frac{e^2H^4}{2m}\right)^m
 \le \frac{(e^2H^4/2)^m}{m!}.
\]

The resulting sum has an upper bound of exponential size in \(H^4\), with \(H\asymp(r-1)^{-1}\). It is important not to misread this as an actual asymptotic for \(X\). It is only a very large upper bound. It neither proves nor disproves the tail condition in the main report.

The ratio in the proved tail estimate becomes useful only beyond indices proportional to \(H^4\). A fixed cutoff \(2p\) cannot be held beyond this moving threshold as the circle is approached. Cauchy estimates for \(k\) derivatives in a disk of radius proportional to \(r-1\) add \((r-1)^{-k}\) factors; they do not remove the exponential upper bound.

## 2. Absolute-value estimates already fail at fixed order

For the two-particle formula at \(s=e^{u+i\pi/3}\),

\[
 A=\cosh u+i\sqrt3\sinh u.
\]

Near \(\phi=\pi/2+t\),

\[
 A-\cos\phi=1+t+i\sqrt3u+O(u^2+|t|^3).
\]

Thus the unnormalized integrand is asymptotic to

\[
 2^{-5/2}(t+i\sqrt3u)^{-5/2}.
\]

After taking absolute values, this gives the rigorous scaling

\[
 \lim_{u\downarrow0}u^{3/2}
 \frac1{2\pi}\int_0^\pi
 \left|\sin^2\phi\,(A-\cos\phi)\,y(s,\phi)^5\right|d\phi
 =C_{\rm abs}>0,
\]

\[
 C_{\rm abs}=\frac{2^{-5/2}}{2\pi}3^{-3/4}
   \frac{\sqrt\pi\,\Gamma(3/4)}{\Gamma(5/4)}.
\]

The local change of variable \(t=\sqrt3u\,v\), a lower/upper comparison with \(|t+iu|^{-5/2}\), and boundedness away from the edge justify this limit. Its value is evaluated in `residue_checks.json`. In contrast, \(e^{i\pi/3}\notin\mathcal N_2\), whose real parts are only \(-1,0,1\), and the fixed-order regularity theorem applies. The signed integral is regular while its absolute-integrand bound diverges.

The actual non-interval quadrature in `chi2_checks.json` shows this cancellation: between \(u=0.03\) and \(u=0.0003\), the absolute integral grows from about 5.60 to about 5692, whereas the signed values remain of order 0.1. The scaled absolute values approach the positive constant above. These computations do not establish a continuation theorem; they test the analytically identified mechanism that invalidates a simple dominated-convergence approach.

For higher even orders there are related balanced edge configurations, with some angles near each of the two branch-edge angles. Pair factors between opposite edges can be large while same-edge Vandermonde factors vanish. A rough balanced scaling suggests that absolute estimates remain problematic at all even orders. This higher-order observation was **not** promoted to an all-order asymptotic theorem. The two-particle example alone rigorously demonstrates the problem with that method.

## 3. Fixed-order stationary classification is not an infinite-tail estimate

The local TW argument has at most \(n^2+2\) potentially singular factors before localization: two product denominators, \(n(n-1)\) pair denominators, and \(n\) propagator denominators. Its integration-by-parts count and partition constants depend on \(n\). The finite-order proof in the supplement carefully keeps \(n\) fixed.

At the prime-root points, the cyclotomic argument gives a first singular coefficient and also an exponential separation bound for nonresonant candidate values. It does not produce a lower bound on every relevant local gradient in a form that, after differentiating the localized integrals and summing the cover, is summable in \(n\). Attempting to insert only the distance of the nearest Nickel value into the fixed-order theorem leaves all these other constants uncontrolled.

For resonant higher indices, the same point can be a fixed-order singularity with a higher local exponent. Knowing separately that individual higher-order derivatives have finite limits is still insufficient to bound their infinite sum. A proposed proof must handle nonresonant near-singular indices and resonant indices together, with explicit summability or another noncancellation mechanism. This run does not have such a bound.

## 4. Algebraic series and a considered arithmetic shortcut

The onset \(F_n=O(s^{-n^2})\) explains why many low-temperature coefficients can be obtained from a few particle terms. It does **not** create gaps in the full susceptibility series: each fixed term has infinitely many later coefficients. Therefore a lacunary-series natural-boundary theorem cannot be applied just to the sequence of particle onsets.

The standard Pólya–Carlson alternative for a power series with integer coefficients requires radius of convergence exactly one in that integer-coefficient variable. The integer-coefficient low-temperature variable mentioned in BG PDF p. 6 is \(v=1/(4s^2)\). The target circle becomes \(|v|=1/4\), not \(|v|=1\). Passing to \(q^2=1/s^2\) moves the circle to one but loses integrality; the exact coefficients computed in this run already exhibit denominators. Thus this theorem, with its stated hypotheses, supplies no shortcut here. No specialized generalized arithmetic continuation theorem was imported.

## 5. Positivity has a limited useful scope

On real \(s>1\), every BG even-particle integrand is nonnegative. This permits the full-function lower bound at \(s=1\), and evenness transfers it to \(-1\). At a nonreal prime root approached radially, the integrands and their high derivatives are complex. Their real-temperature positivity is not a positivity inequality for the boundary derivatives. The nonzero local coefficient of a first particle term therefore does not imply a lower bound for the full complex sum.

Likewise, the absence of an additional class of fixed-order singularities is not the absence of cancellation by an infinite sum. The explicit square-root-plus-polynomials identity in the main report demonstrates the logical gap even when all later summands are entire.

## 6. Dependency audit

**Exterior conclusion:** BG's physical full expansion + TW's even determinant identity + the inside-root lemma + Hadamard + normal convergence. This chain uses no boundary lemma, no numerical fitting, and no unknown tail hypothesis.

**Full singularities at \(\pm1\):** the same physical expansion + real positivity + the analytically proved two-particle critical lower asymptotic + the exact evenness symmetry. The lower amplitude is not advertised as the exact full amplitude.

**Prime-root fixed-order reconstruction:** the explicitly normalized fixed-order contour formula + TW's local nonstationary proof + cyclotomic uniqueness + simple-pole residue reduction + dominated convergence for a fixed derivative. The two contour displacements and their scalar factor are displayed in the supplement. These claims have not been independently audited; they are this run's finite-order reconstruction. In particular they should not be mistaken for a full-susceptibility conclusion.

**Conditional natural boundary:** the fixed-order reconstruction + the unproved condition \((T_p)\). The latter is an assumption in the conditional theorem, not a conclusion of any earlier bound.

**Numerics:** floating-point computations check particular identities, branches, signs, and asymptotic scalings. They contain no interval certificates and no unbounded-order computation. Exact polynomial and rational computations certify only their stated finite identities. None is used as a substitute for the infinite-tail estimate.

## 7. Final mathematical obstacle

The unproved condition is

\[
 \lim_{u\downarrow0}u^{1/2}
 \frac{d^{2p^2-1}}{du^{2p^2-1}}
 \sum_{n>2p,\ n\text{ even}}F_n(e^{2\pi ia/p}e^u)=0
\]

for the selected dense family, or a suitable replacement noncancellation argument. No existing bound in this run proves it, and no explicit holomorphic continuation of the actual full sum disproves the target.

This is a mathematical stopping point for the chosen route. It is not a claim that further research is impossible, that all alternatives were exhausted, or that a historical open-problem label prevents a solution. All identified finite computations used for the route were actually executed. Further comparison or hint-assisted continuation must be a new phase preserving this frozen output.
