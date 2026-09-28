# Self-check and claim ledger

Run: `ISING-CR0-20260927-27b6b643611a`. This is the same solver's self-check, not an independent referee report or formal proof verification.

## Analytical checks

| Claim | Audit performed and hypotheses retained | Result scope |
|---|---|---|
| Physical normalization | Rechecked BG2008v1 equations (2), (4)–(9), pp. 2–3, in supplied text and original page renders. The quantity is `X=beta^{-1} chi`, includes the origin, and has prefactor `(1-s^{-4})^{1/4}` in the low-temperature phase. | Imported exact source identity S1; not a numerical reconstruction of the microscopic model. |
| Global branch | Verified `a(s)` cannot belong to `[-2,2]` for `|s|>1`; a unit root for `q` would put `a=cos(phi)+cos(psi)` in that interval. Simplicity and uniqueness patch the inside root, without assuming a global square-root branch. | Analytical proof on the entire exterior. |
| Ellipse estimate | If `|q|>=1/|s|`, the two semiaxes of `(q+q^{-1})/2` are at most half the semiaxes for `s+s^{-1}`. The norm triangle inequality would imply `1<=1/2+1/(|s|+|s|^{-1})<1`. | Strict bound `|q|<1/|s|`. |
| Infinite exterior sum | Used the supplied even-order determinant identity, not a naive independent bound on all pairs. Row norms give `n^{n/2}B^n`, with an additional `B^n` from the single factors. For `n=2m`, `(2m)^m/(2m)!<=2^m/m!`. | Normal convergence on every exterior compact set; no uniform boundary statement. |
| Holomorphy and infinity | All integrand denominators are nonzero in the exterior; parameter integration and Weierstrass apply using the explicit majorant. The prefactor is its convergent binomial branch. At infinity the majorant is `O(s^{-4})`. | Full target part 1, conditional only on accepted source representation S1/S2. |
| Critical lower bound | Recomputed the `n=2` reduction, its factor `1/(4 pi)`, scale `phi=sqrt(2 mu)v`, and beta integral `2/3`. Nonnegative real physical integrands permit a bound on the entire sum. | Full `X` is singular at `+1`; symmetry gives `-1`. No matching critical upper bound or full amplitude claimed. |
| Evenness | With even `n`, simultaneous angle shift by `pi` preserves the total-angle constraint and sends `q,y` to `-q,-y`; all products in `A_n` are invariant. | `X(-s)=X(s)` for the continued germ. |
| First prime order | The cyclotomic automorphism is permitted because `gcd(n,p)=1`. At `2p`, the relation has at most six coefficient positions, so for `p>=7` a missing position forces its multiple of `Phi_p` to vanish. | General proof for every selected prime root, beyond the finite exact tests. |
| Cutoff/contour bridge | Distinguished smooth angular cutoffs from holomorphic functions: no deformation of the cutoff is assumed. Residues are taken in the other variables, then uniform fixed-exterior Fourier estimates justify the Abel limit. One normalized measure is assigned per contour variable. | Transfers the specified angular remainder to the shape of the supplied TW integral. |
| TW localization | Re-read pp. 4–8. Its proof uses the active local cone; it still applies to patches excluding zero-cone tuples even when the boundary point is globally a Nickel candidate. Radius may depend on `s`. Constants and derivative orders are fixed at each fixed `n`. | Fixed-order control only. No `n`-uniform version imported. |
| Equal-angle saddle | Checked implicit derivatives, Vandermonde degree, the positive even-order numerator coefficient, and the scale exponent. At derivative order `k=n^2/2-1` the scaled radial majorant decays as `r^{-2}`. Lower pole powers have a common majorant and vanish after scaling. | The claimed nonzero derivative limit for the finite partial sums. |
| Noncancellation within the finite integral | The zero-cone classification leaves only the negative-angle tuple at `n=2p`; the even remainder cutoff vanishes there. The two angular saddle contributions are identical by reflection and add. The beta amplitude has no zero. | Finite partial sum singularity, not infinite sum singularity. |
| Restricted local tail | `C_0` is chosen on a fixed analytic factor neighborhood before decreasing `delta`; thus the condition `2 C_0 delta<1` is not circular. The fixed derivative order is that of the first sector, not the much higher sector's singular derivative. The crude Vandermonde/volume estimate is summable as `rho^{n^2}n^{2k}/n!`. | Only the stated equal-angle neighborhoods of higher resonant sectors. Their complements are not estimated. |
| Conditional natural boundary | If (T) holds at all selected prime roots, the finite coefficient survives; local invertibility of the prefactor transfers the obstruction to `X`. Density then implies the exact no-disk assertion at every circle point. | Conditional theorem. (T) remains unproved. |
| Cancellation example | The Taylor truncation makes each `Q_m` flat at 1, while `z^{m^4}` dominates the finite polynomial on every interior compact disk. The series telescopes to zero even though each finite partial sum retains its leading singularity. | Exact logical counterexample to an invalid inference, not an Ising counterexample. |
| Low-temperature coefficients | Fixed order starts at degree `n^2`, as shown by constrained Vandermonde Fourier orthogonality. Thus degrees below 16 receive only the two-particle term. The exact symbolic integral agrees with the reported rational coefficients. | Exact finite coefficient statement, not a Pólya–Carlson or natural-boundary argument. |

The standard mathematics used includes the holomorphic implicit-function and identity theorems, holomorphic parameter integration, Weierstrass normal convergence and Cauchy differentiation on interior compact sets, Hadamard's determinant inequality, Fourier inversion for smooth periodic functions with absolutely summable coefficients, the residue theorem, dominated convergence with displayed majorants, elementary cyclotomic field automorphisms, and the beta integral with its explicitly specified continuation. Specialized local contour estimates are imported only as S3 with the source locations given in `RESULT.md`.

## Actual computational coverage

`check_kernel_identity.py` runs sixteen deterministic 90-digit tests at four exterior parameters and four even particle numbers. Its final version also checks the strict inverse-modulus root bound. This is a floating-point diagnostic, not an interval proof or exhaustive sampling.

`check_two_particle.py` evaluates eight positive-real quadratures at `epsilon=10^{-j}`, `j=1,2,3,4,6,8,10,12`, using 85 digits and a scale-aware interval split. The analytical domination proof is separate; the output does not certify an error interval.

`check_exact.py` uses rational/symbolic polynomial arithmetic for the coefficients through degree 14, sixty-two prime/root pair tests over `p=7,11,13,17,19`, and six exact boundary-flat jets. The general claims are proved independently; exact finite tests alone do not quantify over all primes or degrees.

`check_local_model.py` uses 100 digits at four `(p,j)` pairs to check the implicit derivatives and a one-dimensional radial beta integral. It does **not** perform the full `n=14`, `22` or `26` multidimensional susceptibility integrals. Derivative orders 97, 241 and 337 refer to the local model formula, not a numerical differentiation of the entire susceptibility.

`check_cutoff_bridge.py` evaluates the constant-cutoff `n=2` normalization at three periodic grid sizes and four contour radii. It does not test arbitrary nonanalytic cutoffs or prove the Abel-limit estimates. All 512-grid discrepancies pass the code's `1e-11` diagnostic threshold.

`check_cancellation.py` provides twenty-five 100-digit illustrations of the explicit construction. Its convergence and cancellation are established by the written argument, not by extrapolating these values.

Every research program has JSON output and captured standard output. `audit_outputs.py` checks these pairs for equality, the finite assertions, the coefficient transcription, and the outcome/log structure. Its output is an artifact consistency check, not an additional proof certificate. The two scripts revised during final review were actually rerun; those revisions and reruns are recorded.

## Deliberately unclaimed steps

There is no proved boundary-uniform estimate for the complementary higher-particle integrals at the chosen prime roots. The exterior exponential majorant deteriorates too rapidly and does not establish (T). The fixed-order TW estimates have no particle-uniform constants supplied or derived here. Numerical series behavior, a fixed-order singular locus, a general regular-singular ODE assumption, and positivity at complex temperature have not been substituted for this missing step.

There is no claimed proof that all possible approaches have been exhausted. This is a substantive partial investigation with an explicit mathematical stopping point. The correct overall outcome remains **PARTIAL**.
