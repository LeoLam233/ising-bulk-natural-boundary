# Complete-amplitude identification: manuscript rc6 / Lean v0.3.0-rc2

The unscaled identification of the printed McCoy–Maillard scalar with the complete fixed-order susceptibility amplitude is false on the selected distinct, nonzero-angle family. The exact conversion on the physical exterior germ is

\[
A_{\rm full}=4A_{\rm chart}=4R_N(-\theta_*)=-4iR_N(\theta_*).
\]

Here `R_N` means the right-hand side evaluated with the principal numerator power and the positive geometric denominator. This resolves the mathematical comparison without assigning an unstated convention to the authors. A single-pinch interpretation of the printed scalar is consistent with this calculation; a complete amplitude requires the degeneracy sum. The original positive-period nonvanishing argument and every production Lean theorem source are retained.

The implemented proof is [Proposition F.1](../paper/next/manuscript.tex) and the preceding normalization calculation. The preserved starting candidate is commit `dd977048c2380e775d83b97ae1fba354c04c349a`, manuscript v0.1-rc5 / Lean v0.3.0-rc1. [Baseline identities](../provenance/AMPLITUDE_BASELINE.json) bind its artifacts. The research branch is `research/amplitude-identification-20261017`; the existing review branch and PR #3 receive the verified result.

## Observable and source closure

The [journal PDF of McCoy–Maillard](https://www.lptmc.jussieu.fr/files/maillard/PUB2/The_Importance_Ising.pdf), printed pp.798 and 801, was retrieved and inspected directly. The amplitude is journal **(70)** and arXiv **(69)**; the angle relation is journal (71), arXiv (70). Their low-temperature (45) puts the magnetization squared outside the particle sum. It therefore uses the full-site normalized particle coefficient, rather than the physical susceptibility or a single contour chart.

The review points to [Orrick–Nickel–Guttmann–Perk (2001)](https://arxiv.org/pdf/cond-mat/0103074v1) for its integrals. Equations (1.10), (3.13), and (3.17)–(3.20) fix the complete angular torus, `1/N!`, `N-1` measures `d phi/(2 pi)`, the constraint `sum phi=0 mod 2 pi`, the one-body factors `1/sinh gamma`, the full factor `(1+Z)/(1-Z)`, and the squared pair factor. At isotropy its anisotropy parameter has `cot(alpha_aniso)=1`; that symbol is unrelated to the geometric angle here. This identifies its `hat chi_N`, the review's `chi_N`, and our `C_N^std` for every even N.

[Boukraa et al. (2008), (4)–(9)](https://arxiv.org/pdf/0808.0763v1) gives a second explicit representation with the same normalization. Its `w=s/[2(1+s^2)]` obeys `1/(2w)=S=s+s^-1`. Its `x_i` is our interior root `z_i`; its `y_i` includes the numerator `2w` and equals `1/sinh gamma_i`. It is not our double-contour coordinate named `y_i`.

For `N=2p`, our angles correspond to the review's indices `j=2a`, `l=2b`. Both are nonzero and below N/4. Their sum is even and cannot equal `N/2=p`, so the review's even-order excluded index sum is not being used. The printed plus sign in its (64) conflicts with the explicit roots immediately after it and the cosine relation. The actual integral and Orrick et al. (3.24) give `S_*=cos(alpha)+cos(beta)`. The comparison uses this verified relation and records the source inconsistency rather than importing the sign.

## Branch, local coefficient, and completeness

Fix `s_*=exp(i theta_*)`, `0<theta_*<pi/2`, and approach along `s=(1+epsilon)s_*`. Then `Im S>0`. With `W=S-cos(phi)`, the physical root continued from real low temperature is

\[
z=(W+\sqrt{W-1}\sqrt{W+1})^{-1}.
\]

Both square roots are principal. The equation `z+z^-1=2W` prevents a unit-circle crossing in the upper W half-plane. Continuation from positive real W fixes `|z|<1`; the imaginary part of that equation then gives `Im z<0`. At `phi=±alpha`, its limit is `exp(-i beta)`, so `gamma=i beta`. This determines the physical phase without relying on the cosine relation alone.

Implicit differentiation of `cos u=S-cos phi`, with `gamma=i u`, gives

\[
u_{\phi\phi}=-H/\sin^3\beta,\qquad
s_*u_s=-2i\sin\theta_*/\sin\beta,
\quad H=S_*(1-\cos\alpha\cos\beta)>0.
\]

In constrained coordinates `tau_N=-sum(tau_i,i<N)`, the linear angular term cancels and `1-Z=Q epsilon-i d sum(tau_i^2)+higher terms`, with `Q=2N sin(theta_*)/sin(beta)>0` and `d=H/(2 sin(beta)^3)>0`. The one-body phase and the pair phases multiply to one for even N. The numerator tends to two. The chart prefactor is exactly `2 pi K_beta`; the mean/hyperplane volume factor is already in the angular constant. The existing finite-jet estimates control the replacement by this normal form.

There are four signed angular centers: `+alpha,-alpha,+beta,-beta`. The periodic constraint admits all four. Reversal preserves the real measure and squared Vandermonde; the closed coefficient is symmetric in alpha and beta. They have the same phase and add. An all-equal center is fixed by particle permutations; no additional factorial occurs. The two lower double-contour charts give `T_N^(k)~2L_beta epsilon^-1/2`; the exact identity `C_N^std=f00^(N)+2T_N`, with bounded onsite derivatives, independently forces `4L_beta` for the complete observable. Thus the count does not assume that an angular partition has no remainder.

If `f^(k)(epsilon)=B epsilon^-1/2+o(epsilon^-1/2)`, repeated integration gives a Taylor polynomial of degree at most `k-1` and fractional coefficient `B sqrt(pi)/Gamma(k+1/2)`. Integrability supplies the endpoint derivatives; the integral Taylor remainder controls the little-o. Consequently

\[
A_{\rm chart}=s_*^kL_\beta\sqrt\pi/\Gamma(a_0),\qquad
a_0=k+1/2,\quad \nu=k-1/2.
\]

Substitution of (B.1) gives magnitude exactly `|R_N|` and phase `(-1)^k exp(i pi a0/2)=exp(-i pi nu/2)`, since k is odd. The principal positive-angle expression has phase `exp(i pi nu/2)`. This proves both conversions, including the factor `-i`.

A separate direct integration check divides `r^(2k)/(q+b r^2)` into a polynomial and a residual arctangent, continued from positive b to `b=-i d`. Its fractional term is `(pi/2)(-1)^k q^(k-1/2)b^(-k-1/2)`. Combining it with the constrained Gaussian Vandermonde integral gives the same magnitude and phase. This is a second local coefficient derivation; it does not replace the existing proof of the remainder bounds.

All branches of the displayed half-integer powers have the same magnitude. Neither choosing the other angle sign nor changing a power branch can multiply that magnitude by four. Hence an unscaled complete-amplitude identification is excluded even though the review does not select an angle sign in its cosine equation.

## Conversion table and physical factors

The review's low-temperature variable is `delta=1-s_*/s=epsilon/(1+epsilon)`. Its first derivative is one, so it changes the radial Taylor polynomial and preserves the first fractional coefficient. For a general local coordinate `x=lambda delta+O(delta^2)`, the coefficient acquires the continued factor `lambda^-nu`.

| Observable on the specified germ | Coefficient of delta^nu | kth complex s-derivative coefficient |
|---|---|---|
| One chart | A_chart=R_N(-theta_*) | L_beta |
| Lower double-contour T_N | 2 A_chart | 2 L_beta |
| Full offsite normalized particle coefficient 2T_N | 4 A_chart | 4 L_beta |
| Full-site C_N^std=review chi_N | 4 A_chart | 4 L_beta |
| Physical normalized bulk X=beta_phys^-1 chi | 4 M²(s_*) A_chart | 4 M²(s_*) L_beta |
| Physical chi | 4 beta_phys(s_*) M²(s_*) A_chart | 4 beta_phys(s_*) M²(s_*) L_beta |

The physical bulk rows use the already proved FIRST, lower-order and all-j absolute-tail estimates, and E1/E2 for physical identification. The origin term is smooth at the selected point. Product-rule terms of lower derivative order do not alter the leading singular coefficient. The last row multiplies by inverse temperature itself; it does not divide by inverse temperature or change the independent differentiation variable.

The continuation from `M²→1` at infinity gives

\[
M^2(s_*)=(2\sin2\theta_*)^{1/4}e^{i(\pi/8-\theta_*/2)}.
\]

In the right half-plane, `beta_phys(s_*)=arsinh(s_*)/(2J)` is the continuation from positive real inverse temperature. These analytic nonzero factors are absent from the review's normalized particle coefficient. Changing to a temperature coordinate additionally requires its local-coordinate Jacobian and branch.

## Evidence, limits, and original-source access

[The executable checks](../checks/amplitude_identification/check_amplitude.py) perform nine exact symbolic identities, an exact cyclotomic four-center enumeration at p=11, three 90-digit full-observable quadratures against Orrick et al. (1.13), and specified root/phase samples. The general proof is in Proposition F.1. Quadratures and samples do not prove a uniform analytic remainder or a complete all-N classification.

The journal PDF SHA-256 is `f7ee4da7456c5698ce3889eb0243fc9be2b45024a44bde934db3c8c0d8101350`; the arXiv v1 PDF hash is `72b77a9f3e439e85549a8ecec170a278d4e1beb2ca12326bea4e39e48fa43e5a`. [The source index](../checks/amplitude_identification/SOURCES.json) records all four inspected papers, exact page locators, hashes and access limitations. Third-party PDFs are not redistributed in this repository.

Nickel's 1999 and 2000 publisher endpoints were attempted through the web reader, ordinary HTTP retrieval in Windows and WSL, and the normal browser. They returned errors or an HTML CAPTCHA page rather than paper content. No challenge was solved. Metadata and focused author/institutional searches supplied no accessible original text. Windows TLS retrieval of the institutional review PDF initially failed; retrieval with the ordinary WSL trust store succeeded without disabling TLS verification.

Accordingly no claim is made about Nickel's original intended definition of an elementary amplitude, an original-paper error, or a source convention that could not be read. That historical access limit does **not** leave the conversion of the actually inspected printed formula and full observable open: the cited integral fixes the observable, and the proof computes its coefficient. Degenerate angles, endpoints, other sheets, odd-particle amplitudes, and exhaustive priority are outside this result. The factorial/literature identities and radial Taylor reconstruction are manuscript results, not additional Lean exports. No independent human validation has occurred.
