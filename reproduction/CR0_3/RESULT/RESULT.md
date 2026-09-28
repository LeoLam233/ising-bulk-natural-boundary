# Independent Ising susceptibility investigation — frozen-stage result

Run ID: **ISING-CR0-20260927-27b6b643611a**

Claimed outcome: **PARTIAL**

| Full-scope component | Status in this run |
|---|---|
| Single-valued holomorphy of the physical germ on \(D=\{|s|>1\}\) | **proved**, using the supplied exact form-factor representation |
| The unit circle is a natural boundary for the full bulk susceptibility | **unresolved** |

The second status is not a disproof. This run proves exterior convergence, two singularities of the **full** function, a dense family of singularities of suitable **finite particle partial sums**, and a restricted higher-particle local-tail estimate. The complementary infinite tail remains uncontrolled. A precise sufficient condition for the natural-boundary conclusion is stated below; it is not silently assumed.

## 1. Object, branch, and imported premises

The physical object is the dimensionless connected susceptibility in the positive-field-limit pure phase of the infinite isotropic ferromagnetic square-lattice model:

\[
\mathcal X(s)=\beta^{-1}\chi(s)
=\sum_{x\in\mathbb Z^2}
 \bigl(\langle\sigma_0\sigma_x\rangle_+-m(\beta)^2\bigr),
\qquad s=\sinh(2\beta J)>1.
\]

The sum includes the origin and both lattice directions. The question is whether its real low-temperature germ has a single-valued holomorphic continuation \(X\) to all of \(D\), and whether no disk centered at any point of \(|s|=1\) supports a holomorphic function agreeing with \(X\) on its exterior intersection.

I work with \(X\), not with an independently continued inverse-temperature factor. On the physical interval \(\chi=\beta X\); no assertion about a global complex branch of \(\beta(s)\) is needed. Put

\[
M_2(s)=(1-s^{-4})^{1/4},
\]

with its binomial-series branch, equal to \(m^2\) on \(s>1\). It is single-valued, holomorphic, and nonzero on \(D\).

The following are the load-bearing supplied source premises. Mathematical statements derived later are distinguished from these imports.

| ID | Imported statement and scope | Supplied location |
|---|---|---|
| S1 | The zero-field connected bulk susceptibility has the low-temperature even-particle expansion \(\mathcal X=M_2\sum_{n\ge2,\ n\text{ even}}\widetilde\chi^{(n)}\), with the constrained angular integrals specified below. This identifies the physical germ, not its complex boundary. | BG2008v1, pp. 2–3, equations (1)–(9), particularly (4)–(9). The low-temperature magnetization normalization is also explicit in TW2014v1, p. 2. |
| S2 | For even particle number and real physical temperature, the pair-factor matrix obeys \(\det(h_{ij})=\prod_{i<j}h_{ij}^2\). Its alternative sine/hyperbolic-sine expression is the pair factor used in S1. | TW2014v1, Appendix A, p. 9, the determinant identity above (7) and the identity below (7). |
| S3 | Localized double-contour integrals with the TW denominator structure have bounded derivatives of every fixed order when zero is absent from the convex hull of the active normal vectors. The constants are for a **fixed** particle number and fixed localization. | TW2014v1, Sect. III, pp. 4–8, Lemmas 1–3; Appendix B, pp. 10–11; Appendix C, pp. 11–12. |

S1 and S2 are accepted exact source results; the microscopic form-factor derivation is not reproduced from first principles here. The appendix `LOCAL_SADDLE.md` derives the cutoff/residue conversion needed to apply S3 to S1, rather than equating source symbols with different normalizations.

No general regular-singular differential-equation theorem for every particle number is assumed. TW's actual theorem on p. 8 is a fixed-even-order \(C^\infty\) boundary statement; the stronger analytic-continuation discussion on p. 3 invokes an additional regular-singular-equation premise. That extra premise is unnecessary for this run.

BG's numerical spectra and discussion in Sect. 7 and the conclusion, pp. 31–35, and the Landau discussion in Appendix B, pp. 38–47, are not imported as a theorem excluding cancellation in an infinite sum. Its Appendix E, pp. 52–54, gives local power-counting information with express qualifications. TW p. 2, footnote 1, separately identifies infinite-sum cancellation as an issue requiring proof. The report below addresses that issue explicitly rather than deciding the question by the wording of an abstract or conclusion.

## 2. An unambiguous exterior representation

Write

\[
a(s)=s+s^{-1},\qquad Z(\phi,s)=a(s)-\cos\phi.
\]

Define \(q(\phi,s)\) to be the unique root with modulus less than one of

\[
q+q^{-1}=2Z.
\tag{1}
\]

Set

\[
y(\phi,s)=\frac{2q}{1-q^2},\qquad
H_{ij}^2=\frac{4\sin^2((\phi_i-\phi_j)/2)q_iq_j}{(1-q_iq_j)^2},
\qquad R_n=\frac{1+\prod_iq_i}{1-\prod_iq_i}.
\]

For even \(n\ge2\), define

\[
A_n(s)=\frac1{n!}\int_{[0,2\pi]^{n-1}}
 \left(\prod_i y_i\right) R_n
 \left(\prod_{i<j}H_{ij}^2\right)
 \prod_{i=1}^{n-1}\frac{d\phi_i}{2\pi},
\quad \phi_n=-\sum_{i<n}\phi_i\pmod{2\pi}.
\tag{2}
\]

Thus \(A_n\), not TW's separately named \(\chi^{(n)}\), denotes the \(n\)-particle term throughout the principal argument. With \(w=1/[2(s+s^{-1})]=s/[2(1+s^2)]\), equations (1)–(2) agree near large positive \(s\) with BG (5)–(9): its \(x_i\) is \(q_i\), its \(y_i\) is \(y_i\), and its squared fermionic factor is the product in (2). Consequently S1 identifies

\[
X(s)=M_2(s)\sum_{n\ge2,\ n\text{ even}}A_n(s)
\tag{3}
\]

with the specified physical germ. There is no separate added origin term in this normalization; the full lattice sum is already represented in (2)–(3).

### 2.1 The root exists globally and has a useful bound

For \(|s|>1\), \(a(s)\notin[-2,2]\): if \(a\) belonged to that interval, both roots of \(s^2-as+1=0\) would have modulus one. Hence \(Z(\phi,s)\notin[-1,1]\) for real \(\phi\). The two roots in (1) are distinct, have product one, and neither lies on the unit circle. Exactly one is inside. Simplicity gives local holomorphy, and uniqueness patches the local choices to a globally single-valued holomorphic root on \(D\). This avoids a hidden square-root monodromy convention.

In fact,

\[
\boxed{|q(\phi,s)|<|s|^{-1}}.
\tag{4}
\]

Here is an elementary proof. Fix \(r=|s|>1\), put \(A=r+r^{-1}\), \(B=r-r^{-1}\), and use the real elliptical norm

\[
\|z\|_r=\sqrt{(\Re z/A)^2+(\Im z/B)^2}.
\]

Then \(\|a(s)\|_r=1\). Suppose \(|q|=\rho\ge r^{-1}\). Since \(\rho<1\), the real and imaginary semiaxes of \((q+q^{-1})/2\) are at most \(A/2,B/2\), respectively. Thus \(\|Z\|_r\le1/2\), while \(\|\cos\phi\|_r\le1/A\). The triangle inequality would give

\[
1=\|a\|_r\le\|Z\|_r+\|\cos\phi\|_r
\le\tfrac12+\frac1A<1,
\]

a contradiction. This proves (4).

### 2.2 Normal convergence of the infinite particle sum

For \(|s|\ge r>1\), define

\[
B_r=\frac{2r}{r^2-1},\qquad C_r=\frac{r^2+1}{r^2-1}.
\]

Equation (4) gives
\(|y_i|\le B_r\), \(|H_{ij}|\le B_r\), and \(|R_n|\le C_r\) for every even \(n\ge2\). To use S2, choose local square roots of the individual \(q_i\) and set

\[
H_{ij}=\frac{2\sin((\phi_i-\phi_j)/2)\sqrt{q_i}\sqrt{q_j}}{1-q_iq_j}.
\]

Changing the sign of an individual square root conjugates \(H\) by a diagonal sign matrix; its determinant is unchanged. Moreover, after factoring \(\sqrt{q_i}\) from row and column \(i\), the determinant has an expression using only the globally defined \(q_i\). The product of squared entries does too. The identity theorem therefore continues S2 from the physical interval to all of \(D\), for each fixed real angle tuple:

\[
\prod_{i<j}H_{ij}^2=\det H.
\]

Hadamard's determinant bound now gives

\[
|\det H|\le n^{n/2}B_r^n,
\qquad
|A_n(s)|\le C_r\frac{n^{n/2}B_r^{2n}}{n!}.
\tag{5}
\]

This use of the determinant is essential: simply bounding the pair product independently would give a much worse exponent in the particle number.

For \(n=2m\),

\[
\frac{(2m)^m}{(2m)!}\le\frac{2^m}{m!},
\]

because \((2m)!/m!=\prod_{j=m+1}^{2m}j\ge m^m\). Hence

\[
\boxed{\displaystyle
\sum_{n\ge2,\ n\text{ even}}|A_n(s)|
\le C_r\bigl(e^{2B_r^4}-1\bigr),\qquad |s|\ge r>1.}
\tag{6}
\]

For fixed \(n\), (2) is a holomorphic parameter integral: its integrand is jointly continuous on the compact angle torus and locally in \(s\), holomorphic in \(s\), and its denominators are nonzero by (4). Equations (5)–(6) give a summable uniform majorant on every exterior compact set. The Weierstrass theorem therefore proves that (3) is holomorphic on \(D\). Cauchy's formula also gives normal convergence after every fixed number of derivatives on smaller exterior compact sets.

All branches in (3) are globally specified. Agreement with S1 near large positive \(s\) identifies the continuation with the required physical germ, rather than a different solution of an auxiliary equation. This proves **part 1 of the target**. The same bounds show \(X(s)=O(s^{-4})\) as \(s\to\infty\); there is a removable point at infinity in the coordinate \(t=1/s\).

## 3. Full-function singularities at \(s=1\) and \(s=-1\)

These assertions concern the entire sum, not just a form factor.

For real \(s>1\), every integrand in (2) is nonnegative: \(q_i,y_i,R_n\) are positive and the pair factors are squared real quantities. Therefore

\[
X(s)\ge M_2(s)A_2(s).
\tag{7}
\]

For two particles, put \(\phi_2=-\phi_1=-\phi\). Both \(q\)'s and \(y\)'s coincide. Direct simplification of (2) gives

\[
A_2(s)=\frac1{4\pi}\int_{-\pi}^{\pi}
\frac{Z\sin^2\phi}{(Z^2-1)^{5/2}}\,d\phi,
\quad Z=s+s^{-1}-\cos\phi.
\tag{8}
\]

Let \(\mu=s+s^{-1}-2=(s-1)^2/s\). Then \(Z=1+\mu+1-\cos\phi\). With \(\phi=\sqrt{2\mu}\,v\), dominated convergence gives

\[
\mu A_2(s)\longrightarrow
\frac1{8\pi}\int_{\mathbb R}\frac{v^2}{(1+v^2)^{5/2}}\,dv
=\frac1{12\pi}.
\tag{9}
\]

For the domination, use \(1-\cos\phi\ge2\phi^2/\pi^2\), \(\sin^2\phi\le\phi^2\), and a fixed bound on \(Z\) for \(0<\mu\le1\). After scaling this gives a constant multiple of \(v^2/(1+c v^2)^{5/2}\), integrable on the real line. Thus (9) is an analytical limit, not a fit to quadrature data.

Since \(M_2(1+\epsilon)\sim\sqrt2\epsilon^{1/4}\), (7)–(9) imply

\[
\liminf_{\epsilon\downarrow0}\epsilon^{7/4}X(1+\epsilon)
\ge\frac{\sqrt2}{12\pi}>0.
\tag{10}
\]

In particular the full function is unbounded at 1 and has no holomorphic extension there. Equation (10) is a lower bound, not a claim to have computed the full leading critical amplitude or a matching upper bound.

For even \(n\), changing \(s\) to \(-s\) and each angle to \(\phi_i+\pi\) preserves the constraint modulo \(2\pi\). It sends \(Z,q,y\) to \(-Z,-q,-y\). The even number of \(y\) factors, the pair squares, and the product in \(R_n\) are unchanged. Thus

\[
A_n(-s)=A_n(s),\qquad X(-s)=X(s).
\tag{11}
\]

This is a symmetry of the continued function, not a substitution of an antiferromagnetic physical problem. It transfers the nonextendability to \(-1\). Complex conjugation similarly commutes with these functions. These two full-function singularities alone do not make the circle a natural boundary.

## 4. A dense fixed-order obstruction and a conditional natural-boundary theorem

The detailed proof is in `LOCAL_SADDLE.md`. Its main steps and the exact conclusion are recorded here so the role of each limiting operation is visible.

For a nontrivial prime-order root \(\zeta=e^{2\pi i j/p}\), \(p\ge7\), the first possible even Nickel order is \(N=2p\). This follows from the cyclotomic automorphism fixing \(n\)-th roots but squaring \(p\)-th roots when \(p\nmid n\). At order \(2p\), the only possible pair of root real parts averaging to \(\Re\zeta\) consists of two copies of \(\Re\zeta\). The coefficient proof uses the irreducibility of \(1+z+\cdots+z^{p-1}\) and the fact that a relation here has at most six coefficient positions.

For fixed \(n\), a smooth, simultaneous-angle-reflection-invariant cutoff \(\psi\) admits the normalized identity

\[
A_n[\psi]=O_n[\psi]+2\lim_{r\uparrow1}U_{n,r}[\psi].
\tag{12}
\]

Here \(O_n\) is the origin form factor, and \(U_{n,r}\) is the off-origin double-contour integral with factor
\((\prod x_i+\prod y_i)/[(1-\prod x_i)(1-\prod y_i)]\). One normalized measure \(dx/(2\pi i x)\) is used per contour variable. The appendix derives (12) by residues, absolutely convergent spatial Fourier/geometric sums on exterior compact sets, and an Abel limit. It does not deform a nonanalytic angular cutoff as though it were holomorphic.

S3 then makes the fixed-order origin term smooth away from \(\pm1,\pm i\). For \(n<N\), there is no zero-cone configuration at \(\zeta\). For \(n=N\) in the upper half-circle, the only zero-cone tuple is all \(x_i=y_i=\zeta^{-1}\). A cutoff that excludes the all-\(+\theta\) and all-\(-\theta\) angle neighborhoods consequently leaves a remainder with bounded derivatives of every fixed order. This proves the required fixed-order global remainder statement, rather than assuming that a local saddle must survive integration.

In one of the two saddle neighborhoods, write \(\zeta=e^{i\theta}\), \(0<\theta<\pi\), \(s=(1+\epsilon)\zeta\), and \(\phi_i=\theta+u_i\) with \(\sum_i u_i=0\). Put

\[
Q=\sum_i u_i^2,\qquad \Delta=\prod_{i<j}(u_i-u_j),\qquad b=\frac{\cos\theta}{2\sin\theta}.
\]

Implicit differentiation of \(\cosh\gamma=a-\cos\phi\), with \(\gamma(0,0)=i\theta\), yields

\[
\sum_i\gamma_i-in\theta=2n\epsilon-i\cot\theta Q
 +O(\epsilon^2+\epsilon|u|+|u|^3).
\]

The numerator factors as \(\Delta^2 B(\epsilon,u)\), with
\(B(0,0)=2^{-n(n-1)}(\sin\theta)^{-n^2}>0\) for even \(n\). If \(k=n^2/2-1\), differentiating \(k\) times and scaling \(u=\sqrt\epsilon v\) gives a nonzero coefficient proportional to

\[
J_{n,\theta}=\int_{\mathbb R^{n-1}}
 \frac{\Delta(v)^2}{(n-ibQ(v))^{k+1}}\,dv
=Z_n n^{-1/2}(-ib)^{-(n^2-1)/2}
 \frac{\sqrt\pi}{\Gamma(k+1)}\ne0,
\tag{13}
\]

where \(Z_n=\int e^{-Q(v)}\Delta(v)^2\,dv>0\). The differentiated scaled integrand has an integrable radial majorant proportional to \(r^{-2}\) at infinity. The two saddle coefficients are equal by angle reflection and therefore add. Combining this with (12) and S3 proves

\[
\boxed{\displaystyle
\sqrt\epsilon\frac{d^k}{d\epsilon^k}
P_N((1+\epsilon)\zeta)\longrightarrow C_{p,j}\ne0,
\quad P_N=\sum_{\substack{2\le n\le N\\n\text{ even}}}A_n,
\quad N=2p,\ k=N^2/2-1.}
\tag{14}
\]

Thus these finite partial sums have genuine singularities, with the local half-integer power \((N^2-3)/2\). The selected roots are dense in the circle. This is a finite-order result; \(P_N\) is not substituted for \(X/M_2\).

There is also a restricted infinite-tail result. For higher resonant sectors \(n=mN\), \(m\ge2\), restrict each integral to a sufficiently small equal-angle patch \(Q\le\delta^2\). For the **fixed** derivative order \(k=N^2/2-1\), the appendix proves constants \(C_k\) and \(\rho<1\), independent of \(n\), such that

\[
\sup_{0<\epsilon<\epsilon_0}|\partial_\epsilon^k I_{n,\delta}|
\le C_k\frac{n^{2k}}{n!}\rho^{n^2}.
\tag{15}
\]

The Vandermonde factor is essential to this summable bound. It covers only those patches, not the entire higher-particle integrals.

Now set

\[
R_N(s)=\sum_{n>N,\ n\text{ even}}A_n(s).
\]

**Conditional theorem.** If, for every selected prime root, one can prove

\[
\boxed{\displaystyle
\sqrt\epsilon\,\frac{d^k}{d\epsilon^k}
R_N((1+\epsilon)\zeta)\longrightarrow0,
\quad N=2p,\ k=N^2/2-1,}
\tag{T}
\]

then the full \(X\) has the unit circle as a natural boundary.

Indeed, (14) and (T) make the corresponding derivative of \(X/M_2\) unbounded at every selected root. The prefactor is locally analytic and nonvanishing there, so a holomorphic extension of \(X\) would contradict that unboundedness. Any disk giving continuation at an arbitrary circle point would also give continuation at a selected root inside a smaller part of that disk, contradicting density. This proves the exact universal no-disk statement in the task **under (T)**.

**Condition (T) is unresolved.** Equation (15) removes a controlled part of it. The complementary regions of the higher resonant sectors, and the other higher sectors, remain. No assertion that their normalized derivative tends to zero is made.

## 5. Why the present estimates do not settle (T)

As \(r\downarrow1\), the constants in (6) behave as \(B_r\asymp(r-1)^{-1}\), \(C_r\asymp(r-1)^{-1}\). The resulting bound is of the form

\[
O\bigl((r-1)^{-1}\exp(C(r-1)^{-4})\bigr),
\]

not a uniform boundary majorant. Cauchy derivative estimates insert additional inverse powers of the distance to the circle. They justify interior termwise differentiation but not (T). The factorial becomes an effective crude tail bound only at particle scales that diverge as the boundary is approached; it cannot control a tail starting at the fixed \(N=2p\) in (T).

A concrete difficulty in the complementary regions is already visible in (1): at a nonexceptional circle point, angles can solve \(a-\cos\phi=1\) or \(-1\), giving limiting \(q=1\) or \(-1\). The single factors and certain pair denominators then lose their pointwise bounds. For each fixed particle number, the TW cone argument handles these regions by localization and nonstationary integration. This run has not obtained summable particle-uniform constants for those operations. The local estimate (15) deliberately stays away from these regions and cannot stand in for their treatment.

Nor does increasing fixed-order smoothness by itself prevent cancellation. The following explicit construction shows the logical problem even when every finite partial sum retains the same leading singularity.

### An exact cancellation example, not an Ising counterexample

In \(|z|<1\), let \(\alpha=1/2\), \(Q_0=1\), and for \(m\ge1\) set

\[
L_m=m^2,\qquad K_m=m^4,\qquad
Q_m(z)=z^{K_m}\sum_{j=0}^{L_m-1}
 \binom{K_m+j-1}{j}(1-z)^j.
\]

Since the sum truncates the Taylor series of \(z^{-K_m}\) about \(z=1\),

\[
Q_m(z)=1+O((1-z)^{L_m}).
\]

Define

\[
f_0(z)=(1-z)^\alpha,\qquad
f_m(z)=(1-z)^\alpha\bigl(Q_m(z)-Q_{m-1}(z)\bigr).
\]

For \(|z|\le r<1\),
\(|Q_m(z)|\le r^{m^4}\exp(O_r(m^2\log m))\), a summable bound. Hence \(\sum f_m\) converges normally inside the disk. But it telescopes:

\[
\sum_{m=0}^{M}f_m=(1-z)^\alpha Q_M(z)
=(1-z)^\alpha+O((1-z)^{\alpha+M^2}),
\qquad \sum_{m=0}^{\infty}f_m=0.
\tag{16}
\]

Every finite partial sum is singular at 1 with the same leading half-integer power. Every tail term is smoother than that leading power; for \(m\ge2\) its first possible noninteger power is \(\alpha+(m-1)^2\), and the leading coefficient is nonzero. Nonetheless the total is identically zero and extends everywhere. This is not the Ising susceptibility and does not disprove the target. It disproves the inference from normal interior convergence plus increasingly weak finite-order singularities to noncancellation of the full sum.

## 6. Exact and numerical self-checks

No numerical experiment is used as a proof of the universal analytical statements. All mathematical bounds above and in the appendix are analytical. The scripts are deterministic and need no random seed, network, downloaded data, or package installation.

As a normalization check, put \(t=1/s\). Direct expansion of (2), followed by elementary Fourier orthogonality of the squared Vandermonde, gives for each even \(n\)

\[
A_n(t)=2^{-n(n-1)}t^{n^2}+O(t^{n^2+2}).
\tag{17}
\]

To see the coefficient, \(q=t/2+O(t^2)\), \(y=t+O(t^2)\), and \(H_{ij}^2=t^2\sin^2((\phi_i-\phi_j)/2)+O(t^3)\). The constrained average of the squared unit-circle Vandermonde is \(n!\): in its determinant expansion, Fourier orthogonality forces the two permutations to coincide. Dividing by \(n!\) and by \(2^{n(n-1)}\) proves the leading coefficient. Evenness removes the next odd power. The normal convergence already proved permits coefficient extraction term by term near \(t=0\).

In particular, all coefficients below degree 16 come from \(M_2A_2\). Exact rational symbolic calculation gives

\[
X(t)=\frac{t^4+t^6}{4}
+\frac{13(t^8+t^{10})}{32}
+\frac{139(t^{12}+t^{14})}{256}+O(t^{16}).
\tag{18}
\]

This is an exact finite coefficient calculation, not a long-series inference about the boundary. No integer-coefficient premise in the unscaled coordinate \(t\) has been established.

The retained checks are:

| Program | What its saved output actually checks |
|---|---|
| `check_kernel_identity.py` | Sixteen high-precision finite branch, determinant/product, and Hadamard-bound checks, with real, negative, imaginary and genuinely complex exterior parameters. |
| `check_two_particle.py` | Eight high-precision quadratures of (8), testing the analytical limits (9)–(10). The predicted limits are approximately 0.02652582384865 and 0.03751317983988. |
| `check_exact.py` | Exact coefficients (18), exact finite prime-pair checks, and exact vanishing jets for six polynomials in (16). |
| `check_local_model.py` | Four high-precision checks of the implicit energy derivatives and the nonzero radial beta integral, at derivative orders 97, 241 and 337. These evaluate the local model, not the complete high-dimensional integrals. |
| `check_cutoff_bridge.py` | Periodic double-precision quadrature for the independently normalized \(n=2\) residue/Abel identity, at three grid sizes and four contour radii. It checks normalization; it is not an interval certification of the cutoff theorem. |
| `check_cancellation.py` | Twenty-five illustrative evaluations of the explicit telescoping construction. Its validity follows from the proof around (16), not these floating-point values. |

Each has its own JSON output and captured standard output. `SELF_CHECK.md` records the final audit of their scope. None constitutes a proof-assistant or independent referee validation.

## 7. Access, normalization, and termination limitations

The source PDFs, their supplied mechanical text files, the administrative tool, and newly written output were the only mathematical materials accessed. No external links, references, search services, connectors, remote computation, prior conversations, saved project memory, or other agents were used. No prior solution or comparison material was recognized or received. Ordinary prior mathematical knowledge was used; inaccessible pretraining history cannot be audited.

There was a disclosed access deviation: general environment-provided PDF operating guidance outside `INPUT/` was read. It contained operational instructions, not Ising research. It was disclosed to the user and logged. The initial extraction also used Python without `-B` before the packet instruction was read; it imported only the standard library, and the actual input-inventory verification found no input changes. Subsequent Python invocations used `-B`.

Offline behavior was voluntary at the protocol level. Network blocking was not tested, and no claim is made that it was technically enforced. The filesystem was not demonstrated to be restricted to the two task directories. The visible conversation contained this fresh task, but no technical certificate of memory or training isolation exists. Initial setup reads were logged retrospectively; the exact start time is unknown. The action log is a concise task-level record, not a complete filesystem audit or private reasoning transcript. See `RUN_RECORD.json` and `PROVENANCE.md`.

An apparent scalar ambiguity in the displayed TW double-contour normalization was avoided by using BG for the physical normalization and deriving one normalized contour measure per variable in the cutoff bridge. The original display was checked in the PDF; it was not silently rewritten and then attributed verbatim to the source. This does not affect the fixed-order cone estimate, and is not treated as a disproof of the target.

The input verification actually returned `INPUT_INTEGRITY_OK` for 13 manifest-listed files. The final verification and freeze are administrative integrity operations only; they do not validate mathematics or isolation.

**Termination reason.** The stopping point is a specific mathematical impasse, not the fact that the question may be difficult or historically unsolved, and not an asserted failure of Python or the supplied files. The fixed-order arithmetic, contour matching, local coefficients, restricted local tail, exterior convergence, critical lower bound, and associated executable checks have been carried out. The remaining task is to control the complementary higher-particle boundary derivative in (T), or otherwise rule out its cancellation of (14). The known compact-exterior estimate and fixed-order localization estimates do not provide that control. No exhaustion of all possible proof methods is claimed. The full natural-boundary statement must therefore remain **unresolved**, and this stage ends with **PARTIAL** before any comparison or feedback.

## Supplied references

**BG2008v1** — S. Boukraa et al., *Experimental mathematics on the magnetic susceptibility of the square lattice Ising model*, supplied arXiv:0808.0763v1, 6 August 2008, 54 PDF pages.

**TW2014v1** — C. A. Tracy and H. Widom, *On the Singularities in the Susceptibility Expansion for the Two-Dimensional Ising Model*, supplied arXiv:1403.3966v1, 16 March 2014, 13 PDF pages.

Bibliographic identifiers are not additional accessed inputs. No links or cited external works were retrieved.
