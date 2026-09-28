# Ising CR0 independent run: partial result

**Run ID:** `ISING-CR0-20260927-ba3792d2458a`  
**Outcome:** `PARTIAL`  
**Exterior analyticity:** `proved`, using the explicitly identified source representations below.  
**Natural boundary of the full bulk susceptibility:** `unresolved`.  
**Disproof:** none.

The proof of exterior analyticity concerns the entire infinite even-particle sum, not just its individual terms. The boundary work establishes singularities of the full function at two points, reconstructs a dense family of first-occurring fixed-particle singularities, and isolates a precise **unproved infinite-tail estimate** that would imply the requested natural boundary. That estimate is not silently assumed.

This is a solver's mathematical claim, not an independent audit verdict. The supplied freezing tool validates neither mathematics nor isolation.

## 1. Exact object and information boundary

The model is the isotropic ferromagnetic nearest-neighbor square-lattice Ising model with the energy and pure phase specified in `INPUT/TASK.md`. On the real low-temperature interval,

\[
s=\sinh(2\beta J)>1,\qquad
\mathcal X(s)=\beta^{-1}\chi(s)
 =\sum_{(M,N)\in\mathbb Z^2}
   \big(\langle\sigma_{0,0}\sigma_{M,N}\rangle_+-m^2\big).
\]

The origin and every lattice direction are included. The object continued below is **\(\mathcal X\)**, not a diagonal sum and not \(\chi\) with an additional possibly multivalued inverse-temperature factor. Write \(X\) for its exterior continuation.

The requested domain is \(D=\{|s|>1\}\). A natural boundary would mean that no disk centered at any point of \(|s|=1\) supports a holomorphic function agreeing with \(X\) on its intersection with \(D\).

Only the supplied packet was used as research material. No network request, connector, other conversation, project memory, remote computation, external agent, source-paper link, or cited bibliography item was accessed. There is one disclosed administrative exception: a system-required local PDF-handling instruction file outside the packet was read. It contained operational PDF instructions, not an Ising result or mathematical hint. This was disclosed immediately and is recorded as a deviation. Technical network and filesystem isolation were **not** established. Details and logging limitations are in `ACCESS_LIMITATIONS.md` and `RUN_RECORD.json`.

## 2. Source premises and their actual scope

All locations below refer to the **included v1 PDFs**. Their printed page numbers agree with PDF page numbers for the locations used here. The companion text files were navigation aids. The load-bearing representation and determinant formulas were checked in locally rendered original pages.

**BG2008v1:** S. Boukraa et al., *Experimental mathematics on the magnetic susceptibility of the square lattice Ising model*, included arXiv:0808.0763v1.

* PDF pp. 2–3, equations (2), (4)–(9): the connected bulk susceptibility, its low-temperature even-particle expansion, the normalized \((n-1)\)-angle integrals, and the branch reached from small \(w\).
* PDF pp. 52–53, Appendix E: a local power-counting discussion, including the circle exponent \((n^2-3)/2\). Its broader applicability is expressly tentative in that appendix. A power count alone is not used as a proof of an infinite-sum natural boundary.
* PDF pp. 31–35, Section 7 and conclusion: finite-series/power-spectrum evidence and statements about cancellation becoming unlikely. Those are **not** adopted as a proof that an infinite tail cannot cancel a singularity.

**TW2014v1:** C. A. Tracy and H. Widom, *On the Singularities in the Susceptibility Expansion for the Two-Dimensional Ising Model*, included arXiv:1403.3966v1.

* PDF p. 1, equation (1), and p. 2: the same connected bulk object and \(m^2=(1-s^{-4})^{1/4}\).
* PDF p. 9, Appendix A: the real low-temperature Fredholm/form-factor representation, the **even-dimensional identity** \(\det(h_{jk})=\prod_{j<k}h_{jk}^2\), and the equivalent formulas for the pair factor \(h\). This finite-dimensional identity is a load-bearing imported premise in the exterior proof. I do not reprove the underlying Ising correlation representation from the Gibbs measure.
* PDF pp. 5–8, Lemmas 1–3 and the theorem; pp. 10–12, Appendices B–C: a fixed-order nonstationary/localization argument and \(C^\infty\) boundary regularity away from the Nickel set. The proof applies for each fixed even particle number. It supplies **no estimate uniform in particle number**.
* PDF p. 3: the authors discuss a stronger analytic-continuation conclusion under regular-singular differential-equation considerations. I use only the proved \(C^\infty\) statement/local estimates, not an unproved all-order Fuchsian premise.
* PDF p. 2, footnote 1: the infinite-sum cancellation issue is explicitly distinguished from the existence of fixed-order singularities. The diagonal susceptibility mentioned on that page is not the target here.

The physical representations just listed are imported published premises. The exterior normal-convergence proof, quantitative majorant, branch bookkeeping, prime-index arithmetic, and detailed local calculations below are derivations in this run. The standard tools used are complex-parameter integration, the identity theorem, Hadamard's determinant inequality, the Weierstrass theorem for normally convergent holomorphic series, Cauchy's theorem/estimates, dominated convergence, cyclotomic irreducibility and its elementary Galois automorphisms, algebraic-integer norms, and the beta integral. Their relevant hypotheses are given where used.

## 3. A single consistent normalization

For \(s\in D\), put

\[
 A=s+s^{-1},\qquad w=\frac1{2A}=\frac{s}{2(1+s^2)},\qquad
 M_2(s)=\exp\left(-\frac14\sum_{j=1}^\infty\frac{s^{-4j}}j\right).
\tag{3.1}
\]

Thus \(M_2=(1-s^{-4})^{1/4}\), positive on real \(s>1\), and \(M_2\) is a nonvanishing, single-valued holomorphic function on \(D\). It is \(m^2\), not \(m\). The series in (3.1) fixes the branch without a choice of \(\log s\).

For a real angle \(\phi\), set \(z=A-\cos\phi\). Let \(\sigma(z)=\sqrt{z^2-1}\) be the branch on \(\mathbb C\setminus[-1,1]\) satisfying \(\sigma(z)\sim z\) at infinity. Define

\[
 x(s,\phi)=z-\sigma(z)=\frac1{z+\sigma(z)},\qquad
 y(s,\phi)=\frac1{\sigma(z)}=\frac{2x}{1-x^2}.
\tag{3.2}
\]

Equivalently, \(x\) is the unique root of

\[
 x+x^{-1}=2(A-\cos\phi)
\tag{3.3}
\]

with \(|x|<1\). On the physical interval \(x=e^{-\gamma}\), \(\gamma>0\), \(y=1/\sinh\gamma\). Equations (3.2) are exactly BG (8)–(9) with the low-temperature small-\(w\) branch; the factors of \(2w\) cancel to give the displayed \(z\)-formulas.

For each even \(n\ge2\), integrate \(\phi_1,\ldots,\phi_{n-1}\) with normalized measure \(d\phi_j/(2\pi)\), and set \(\phi_n=-\sum_{j<n}\phi_j\) modulo \(2\pi\). Write \(x_j=x(s,\phi_j)\), \(y_j=y(s,\phi_j)\), \(P=\prod_jx_j\), and

\[
 h_{jk}^2=\frac{4\sin^2((\phi_j-\phi_k)/2)x_jx_k}{(1-x_jx_k)^2}.
\]

The BG coefficient, denoted **\(F_n\)** in this report, is

\[
 F_n(s)=\frac1{n!}\int_{[0,2\pi]^{n-1}}
       \left(\prod_{j=1}^ny_j\right)
       \frac{1+P}{1-P}
       \prod_{j<k}h_{jk}^2
       \prod_{j=1}^{n-1}\frac{d\phi_j}{2\pi}.
\tag{3.4}
\]

The imported physical identity is

\[
 \mathcal X(s)=M_2(s)\sum_{n=2,4,6,\ldots}F_n(s),\qquad s>1.
\tag{3.5}
\]

BG's \(\widetilde\chi^{(n)}\) is our \(F_n\). TW's origin-separated \(\chi^{(n)}\) is **not** silently identified with \(F_n\). In particular, no extra \(1-M_2\) is added to (3.5): its origin contribution is already included. A normalized double-contour version useful for the boundary analysis is separately derived in `BOUNDARY_DERIVATION.md`.

## 4. Proof of the full exterior-analyticity claim

### 4.1. The branch has no exterior obstruction

The Joukowski map \(s\mapsto s+s^{-1}\) maps \(|s|>1\) bijectively onto \(\mathbb C\setminus[-2,2]\). Consequently \(A-\cos\phi\notin[-1,1]\) for every real \(\phi\). The two roots in (3.3) cannot have modulus one; their product is one, so precisely one lies inside the unit disk. The root is simple, since a repeated root would be \(\pm1\). It is therefore a single-valued holomorphic function of \(s\). It is never zero. This also follows directly from the branch of \(\sigma\) in (3.2).

A useful stronger bound is

\[
 |x(s,\phi)|<|s|^{-1}.
\tag{4.1}
\]

Here is a geometric proof with no numerical premise. For \(r=|s|>1\), let \(E_r\) be the closed ellipse with semiaxes \(r+r^{-1}\) and \(r-r^{-1}\). The point \(A=s+s^{-1}\) is on its boundary. Put \(b=x^{-1}\), so \(|b|>1\). If \(|b|\le r\), then \(b+b^{-1}\in E_r\), by nesting of these confocal ellipses. Also \(2\cos\phi\) lies strictly inside \(E_r\), since \(2<r+r^{-1}\). But (3.3) gives

\[
 A=\tfrac12(b+b^{-1})+\tfrac12(2\cos\phi),
\]

which would be strictly inside the convex ellipse. This is impossible. Thus \(|b|>r\), proving (4.1).

For \(|s|\ge r>1\), set

\[
 H_r=\frac{2r}{r^2-1},\qquad
 R_n(r)=\frac{1+r^{-n}}{1-r^{-n}}.
\tag{4.2}
\]

Then

\[
 |y_j|\le H_r,\qquad |h_{jk}|\le H_r,\qquad
 \left|\frac{1+P}{1-P}\right|\le R_n(r)\le R_2(r).
\tag{4.3}
\]

The use of \(|h_{jk}|\) in (4.3) is harmless: locally choose consistent square roots of the \(x_j\). Their signs do not affect \(\prod h_{jk}^2\). The global integrand (3.4) has no square-root ambiguity at all.

### 4.2. Why a bound on each pair separately is insufficient, and its replacement

Bounding the product of all pair factors separately would give something of size \(H_r^{n(n-1)}\), which need not be summable when \(H_r>1\). Instead use the identity stated in TW Appendix A, p. 9. For real \(s>1\), its pair factor is

\[
 h_{jk}=\frac{\sin((\phi_j-\phi_k)/2)}
                  {\sinh((\gamma_j+\gamma_k)/2)}
       =\frac{2\sin((\phi_j-\phi_k)/2)\sqrt{x_jx_k}}{1-x_jx_k},
\]

exactly the BG pair factor. For **even \(n\)**,

\[
 \prod_{j<k}h_{jk}^2=\det[h_{jk}]_{j,k=1}^n.
\tag{4.4}
\]

For a fixed tuple of real angles, analytically continue this identity locally in \(s\); the identity theorem continues it throughout \(D\). Changing a local choice of square roots conjugates the matrix by a diagonal sign matrix and changes neither determinant nor the squared product. Only the even-dimensional identity is being used.

Hadamard's inequality applies to this finite complex matrix. Each row has Euclidean norm at most \(\sqrt n H_r\). Therefore

\[
 \left|\prod_{j<k}h_{jk}^2\right|
 \le n^{n/2}H_r^n,
\]

and, since the normalized angular domain has measure one,

\[
 \boxed{\quad
 |F_n(s)|\le R_2(r)\frac{n^{n/2}H_r^{2n}}{n!},
 \qquad |s|\ge r>1,\quad n\ge2\text{ even}.
 \quad}
\tag{4.5}
\]

### 4.3. Infinite-sum convergence, not just termwise analyticity

For each fixed \(n\), (3.4) has a holomorphic integrand with no zero denominator for \(s\in D\). On each compact subset, (4.3) bounds it by an integrable constant. The standard holomorphic-parameter integration theorem makes \(F_n\) holomorphic on \(D\).

Put \(a_n=n^{n/2}H_r^{2n}/n!\). For even \(n\),

\[
 \frac{a_{n+2}}{a_n}
 =\frac{H_r^4(1+2/n)^{n/2}}{n+1}
 \le\frac{eH_r^4}{n+1}.
\tag{4.6}
\]

Thus the numerical majorant in (4.5) is summable for every fixed \(r>1\). Given a compact \(K\subset D\), choose \(1<r\le\min_{s\in K}|s|\). The Weierstrass theorem now gives normal convergence of \(\sum_{n\text{ even}}F_n\) on \(K\), and a holomorphic, single-valued sum on **all of \(D\)**. Multiplication by (3.1) preserves these properties. Equation (3.5) identifies this sum with the physical real-temperature germ. This proves part 1 of the task.

There is also an explicit tail bound. If even \(N\) satisfies \(\rho=eH_r^4/(N+1)<1\), then

\[
 \sum_{n=N,N+2,\ldots}|F_n(s)|
 \le\frac{R_2(r)\,N^{N/2}H_r^{2N}/N!}{1-\rho},
 \qquad |s|\ge r.
\tag{4.7}
\]

All quantifiers here keep \(r>1\) fixed. No assertion of uniformity as \(r\downarrow1\) has been made.

## 5. Normalization and series checks near infinity

For each fixed \(n\), \(x\sim(2s)^{-1}\), \(y\sim s^{-1}\), and \(h_{jk}\sim s^{-1}\sin((\phi_j-\phi_k)/2)\). Consequently

\[
 F_n(s)=2^{-n(n-1)}s^{-n^2}+O(s^{-n^2-1}).
\tag{5.1}
\]

The leading coefficient follows exactly from

\[
 \int_{\sum\phi_j=0}\prod_{j<k}|e^{i\phi_j}-e^{i\phi_k}|^2
       \prod_{j<n}\frac{d\phi_j}{2\pi}=n!.
\tag{5.2}
\]

For completeness, expand the two Vandermonde determinants as sums over permutations \(\sigma,\tau\). After imposing \(\phi_n=-\sum_{j<n}\phi_j\), a term integrates to zero unless \(\sigma(j)-\tau(j)\) is constant in \(j\). Its sum is zero, so the constant is zero and \(\sigma=\tau\). Exactly \(n!\) terms remain. Equation (5.1) follows, equivalently \(F_n(w)=2^n w^{n^2}+\cdots\).

The identity

\[
 F_n(-s)=F_n(s)\quad(n\text{ even})
\tag{5.3}
\]

can be proved directly, not guessed from a finite series. The inside-root branch satisfies

\[
 x(-s,\phi)=-x(s,\phi+\pi),\qquad
 y(-s,\phi)=-y(s,\phi+\pi).
\]

Shift all angles by \(\pi\). The constraint modulo \(2\pi\) is preserved for even \(n\), the product of \(y\)-signs is positive, \(P\) is unchanged, and every squared pair factor is unchanged. Since \(M_2(-s)=M_2(s)\), the full function is even too. In particular the remainder in (5.1) can be sharpened to even powers.

The whole sum is holomorphic at infinity with \(X(\infty)=0\). One way to see that higher orders do not spoil a fixed low-temperature coefficient is to use, for sufficiently small \(|s|^{-1}\), the separate-pair bound, which now has a constant smaller than one and gives a normally summable \(O(C^{n^2}|s|^{-n^2})\) estimate. Thus all \(n\ge4\) contribute \(O(s^{-16})\).

A self-written exact-rational calculation from the two-particle integral gives, with \(q=1/s\),

\[
 X(s)=\frac{q^4}{4}+\frac{q^6}{4}
      +\frac{13q^8}{32}+\frac{13q^{10}}{32}
      +\frac{139q^{12}}{256}+\frac{139q^{14}}{256}
      +O(q^{16}).
\tag{5.4}
\]

In \(v=q^2/4\), these coefficients are \(4,16,104,416,2224,8896\) at powers \(v^2,\ldots,v^7\). No outside series was obtained or compared. These are exact finite consequences of (3.4), not evidence by themselves for a natural boundary. The leading \(q^4/4\) also agrees with the origin term \(1-M_2\) to its leading order; no origin term was added twice.

## 6. Two unconditional singularities of the full susceptibility

For real \(s>1\), every factor of the integrand in (3.4), apart from pair factors that are squared, is positive. Hence \(F_n(s)\ge0\) and

\[
 X(s)\ge M_2(s)F_2(s).
\tag{6.1}
\]

For \(n=2\), put \(\phi_2=-\phi_1\). Then \(x_1=x_2\), \(y_1=y_2\), \(h_{12}=\sin\phi\,y\), and \((1+x^2)/(1-x^2)=\coth\gamma\). Therefore

\[
 F_2(s)=\frac1{4\pi}\int_{-\pi}^{\pi}
 \frac{\sin^2\phi\,(A-\cos\phi)}
      {((A-\cos\phi)^2-1)^{5/2}}\,d\phi,
\quad s>1.
\tag{6.2}
\]

Let \(s=e^u\), \(u>0\). Then \(A=2\cosh u\). Rescale \(\phi=ut\). Pointwise,

\[
 u^3\frac{\sin^2(ut)(2\cosh u-\cos(ut))}
 {((2\cosh u-\cos(ut))^2-1)^{5/2}}
 \longrightarrow\frac{t^2}{(2+t^2)^{5/2}}.
\]

Dominated convergence is justified as follows. For \(|\phi|\le\pi\),

\[
 2(\cosh u-1)\ge u^2,\qquad
 1-\cos\phi\ge2\phi^2/\pi^2,\qquad |\sin\phi|\le|\phi|.
\]

For bounded small \(u\), the numerator's \(2\cosh u-\cos\phi\) is bounded and the squared-root denominator is bounded below by a constant times \((u^2+\phi^2)^{5/2}\). Extending the scaled integrand by zero outside \([-\pi/u,\pi/u]\) gives an integrable majorant \(C t^2/(1+t^2)^{5/2}\). It follows that

\[
 \lim_{u\downarrow0}u^2F_2(e^u)
 =\frac1{4\pi}\int_{\mathbb R}\frac{t^2\,dt}{(2+t^2)^{5/2}}
 =\frac1{12\pi}.
\tag{6.3}
\]

Since \(M_2(e^u)\sim\sqrt2\,u^{1/4}\),

\[
 \liminf_{u\downarrow0}u^{7/4}X(e^u)
 \ge\frac{\sqrt2}{12\pi}>0.
\tag{6.4}
\]

In particular \(X\) cannot have a holomorphic continuation through \(s=1\). Equation (5.3) gives the same conclusion at \(s=-1\). Equation (6.4) is a **lower bound**, not a claim to have found the exact full critical amplitude or full critical expansion. This run does not separately settle \(s=\pm i\) for the full function.

## 7. A dense set of first fixed-particle obstructions

The fixed-order Nickel set is

\[
 \mathcal N_n=\left\{\zeta\in\mathbb T:
  \Re\zeta=\tfrac12\big(\cos(2\pi j/n)+\cos(2\pi k/n)\big)
  \text{ for some }j,k\right\}.
\tag{7.1}
\]

Choose an odd prime \(p\ge5\), \(1\le a\le(p-1)/2\),

\[
 \theta=2\pi a/p,\qquad \zeta=e^{i\theta},\qquad n_0=2p.
\tag{7.2}
\]

These points and their conjugates are dense in the unit circle. There are arbitrarily large primes, and the mesh of the corresponding angle grid is \(2\pi/p\).

### 7.1. First possible even particle number

If \(p\nmid n\), an equality in (7.1) at \(\zeta\) is impossible. In \(\mathbb Q(\zeta_{pn})\), a cyclotomic automorphism can fix every \(n\)-th root and send \(\zeta_p\) to \(\zeta_p^2\), by the Chinese remainder theorem. It would force \(\cos(2\theta)=\cos\theta\). For a nontrivial prime-order root with \(p\ge5\), this is impossible: the only real solutions of \(2c^2-1=c\) are \(c=1,-1/2\), corresponding to orders one and three. Thus \(p\mid n\), and the first possible even index is \(2p\). It does occur, using the same \(p\)-th root for both cosines.

At \(n=2p\) the cosine pair is unique: both cosines must be \(\cos\theta\). To prove this, express a \(2p\)-th root as \(\epsilon\zeta_p^b\), \(\epsilon=\pm1\). A putative equality gives an integer polynomial relation

\[
 \epsilon(\zeta_p^b+\zeta_p^{-b})+
 \eta(\zeta_p^c+\zeta_p^{-c})-
 2(\zeta_p^a+\zeta_p^{-a})=0.
\]

Reduce exponents modulo \(p\). The polynomial has degree at most \(p-1\), so it is an integer multiple of \(1+t+\cdots+t^{p-1}\). Its value at one is \(2\epsilon+2\eta-4\in\{0,-4,-8\}\). Divisibility by \(p\ge5\) forces that value to be zero, \(\epsilon=\eta=1\), and the polynomial itself to be zero. Equality of coefficients forces both \(b,c\) to be \(\pm a\), proving uniqueness.

This is an all-prime argument. `check_cyclotomic.py` independently checks the corresponding polynomial identities exactly for \(p=5,7,11,13,17,19\) and every even index up to \(2p\). The finite computation is a check, not the proof of the universal assertion.

### 7.2. Fixed-order regularity and local singularity

The detailed divisor/localization and residue derivation is in `BOUNDARY_DERIVATION.md`. It keeps the BG full coefficient normalization and uses the **local argument** of TW, not an all-order differential-equation claim. Its conclusions are:

* Each \(F_n\), for fixed even \(n\), has bounded derivatives of every fixed order at a boundary point outside \(\mathcal N_n\).
* At (7.2), all even \(n<2p\) are therefore regular in that sense.
* At \(n=2p\), there is a unique nonstationary-criterion failure in the double-contour representation. A local residue calculation reduces its singular part to twice the single constrained-angle saddle at \(\phi_j=-\theta\). The corresponding \(+\theta\) saddle in (3.4) has the same coefficient.

Here is the coefficient calculation, also displayed in detail in the supplement. Put \(s=\zeta e^u\), \(u>0\), and \(\phi_j=-\theta+v_j\), \(\sum v_j=0\). With \(Q(v)=\sum v_j^2\), \(\Delta(v)=\prod_{j<k}(v_j-v_k)\), and \(c=\cot\theta\ne0\),

\[
 \gamma(\zeta e^u,-\theta+v)
 =i\theta+2u+iv-i\cot\theta\,v^2
    +O(u^2+u|v|+|v|^3),
\]

\[
 1-P=2nu-icQ(v)+O(u^2+u|v|+|v|^3).
\tag{7.3}
\]

For even \(n\), the phases from the \(y\)-factors and the squared pair factors cancel. The single-saddle integrand, including normalized measure and \(1/n!\), has leading form

\[
 \frac{2B_n\Delta(v)^2}{2nu-icQ(v)}\,dv_1\cdots dv_{n-1},
 \qquad
 B_n=\frac1{n!(2\pi)^{n-1}2^{n(n-1)}\sin^{n^2}\theta}>0.
\tag{7.4}
\]

Let

\[
 k=\frac{n^2}2-1,\qquad \nu=\frac{n^2-1}2=k+\frac12.
\]

The positive angular constant \(J_n\) is defined by polar coordinates for \(Q\) on the hyperplane:

\[
 \int_{\mathbb R^{n-1}}\Delta(v)^2 f(Q(v))\,dv
 =J_n\int_0^\infty r^{n^2-2}f(r^2)\,dr.
\tag{7.5}
\]

It is finite and strictly positive; the Vandermonde is a nonzero polynomial on this hyperplane. Differentiating (7.4) \(k\) times and rescaling \(v=\sqrt u\,t\) gives the single-saddle coefficient

\[
 C_{n,\theta}=
 B_n(-1)^k J_n\Gamma(\nu)\sqrt\pi\,
 (2n)^{k-1/2}(-ic)^{-\nu}\ne0.
\tag{7.6}
\]

The branch in this expression has \(\arg(-ic)=-\operatorname{sgn}(c)\pi/2\). It follows from the convergent radial beta integral

\[
 \int_0^\infty\frac{r^{n^2-2}}{(2n-icr^2)^{k+1}}\,dr
 =\tfrac12(2n)^{-1/2}(-ic)^{-\nu}B(\nu,1/2).
\tag{7.7}
\]

For fixed \(n,\theta\), \(|1-P|\ge C(u+Q)\) in a sufficiently small saddle neighborhood. Thus the differentiated, scaled integrand is dominated by an integrable multiple of \(\Delta(t)^2/(1+Q(t))^{k+1}\). Lower-pole derivative terms are bounded. This proves the local coefficient, not just an exponent count. The localization/residue argument in the supplement then gives the fixed-coefficient assertion

\[
 \lim_{u\downarrow0}u^{1/2}
  \frac{d^k}{du^k}F_{2p}(\zeta e^u)
 =2C_{2p,\theta}\ne0,
 \qquad k=2p^2-1.
\tag{7.8}
\]

This is a **fixed-order** singularity. It does not establish (7.8) for \(X/M_2\). The constants, localization neighborhoods, and derivative order in the argument depend on \(p\). In particular, none of the local domination statements permits summing over unbounded particle number.

## 8. The precise conditional natural-boundary theorem

For the points (7.2), define the normally convergent exterior tail

\[
 T_p(s)=\sum_{n>2p,\ n\text{ even}}F_n(s),\qquad k_p=2p^2-1.
\]

A sufficient missing estimate is

\[
 \boxed{\quad
 \lim_{u\downarrow0}u^{1/2}
       \frac{d^{k_p}}{du^{k_p}}T_p(\zeta e^u)=0
 \quad}\tag{T_p}
\]

for every selected prime root. A stronger sufficient estimate would be a uniform bound on that derivative, or summable upper bounds

\[
 \sum_{n>2p,\ n\text{ even}}
   \sup_{0<u<u_p}
   \left|\frac{d^{k_p}}{du^{k_p}}F_n(\zeta e^u)\right|<\infty.
\tag{8.1}
\]

**Neither \((T_p)\) nor (8.1) is proved in this run or imported from the supplied papers.** For every fixed \(u>0\), differentiation of the tail is justified by exterior normal convergence; taking its boundary limit is the unproved step.

Conditionally on \((T_p)\), (7.8) and the regularity of the finitely many lower terms imply

\[
 \lim_{u\downarrow0}u^{1/2}\frac{d^{k_p}}{du^{k_p}}
      \left(\frac{X(\zeta e^u)}{M_2(\zeta e^u)}\right)
 =2C_{2p,\theta}\ne0.
\tag{8.2}
\]

At a nontrivial odd-prime root, \(M_2\) extends locally and is nonzero. If \(X\) had a holomorphic continuation there, the quotient would too, and its derivative with respect to the local analytic coordinate \(u\) would be bounded. This contradicts (8.2). Complex conjugation supplies the lower semicircle. The selected roots are dense, so singularity at all of them rules out a continuation disk centered at **any** point of the circle: such a disk contains a smaller disk centered at one of the dense singular points.

This proves the stated **conditional implication**, not its missing hypothesis. The full natural-boundary status remains `unresolved`.

## 9. Why the remaining estimate has not been justified

The detailed unsuccessful routes and checks are recorded in `METHOD_LIMITS.md`. The main issues are mathematical, not a claim that the problem is impossible or that all methods have been exhausted.

First, (4.5) is an interior estimate. As \(r\downarrow1\), \(H_r\sim(r-1)^{-1}\), and the useful ratio cutoff in (4.6) moves out to particle numbers of order \((r-1)^{-4}\). For example, using \(n!\ge(n/e)^n\) gives the coarse global bound

\[
 \sum_{n\text{ even}}|F_n(s)|
 \le R_2(r)\left(\exp\left(\frac{e^2H_r^4}{2}\right)-1\right).
\tag{9.1}
\]

It proves convergence for every \(r>1\), but says nothing useful about \((T_p)\). Cauchy differentiation only adds more inverse powers of the distance to the circle.

Second, taking absolute values in the real-angle integral before passing to the circle loses essential contour cancellation even at fixed order. For \(F_2\) at \(s=e^{u+i\pi/3}\), the limiting branch edge is \(\phi=\pi/2\). Its integrand has the local form of a nonzero multiple of \((t+i\sqrt3u)^{-5/2}\). The integral of the absolute value consequently grows like \(u^{-3/2}\), although this is not a two-particle Nickel point. A self-written quadrature shows the signed integral approaching a finite complex value while the absolute integral has precisely that large growth. The analytic local estimate, not the quadrature, explains why naive absolute dominated convergence fails.

Third, exact arithmetic separates nonresonant Nickel values from a prime root, but does not bound the constants in the high-dimensional nonstationary estimates. If \(p\nmid n\), a nonzero cyclotomic algebraic integer of degree \(d=(p-1)\varphi(n)\) and conjugate moduli at most eight yields

\[
 \left|\cos\theta-\tfrac12(\cos(2\pi j/n)+\cos(2\pi k/n))\right|
 \ge\tfrac14\,8^{-(d-1)}.
\tag{9.2}
\]

The derivation is in the supplement. This is a useful all-index separation bound, but it is not a summable derivative bound for the integrals. The TW argument uses particle-number-dependent partitions, gradients, and repeated integration by parts. I have not obtained estimates for these quantities that establish (8.1) or the weaker \((T_p)\).

Finally, fixed-term singularity plus normal interior convergence is logically insufficient. In \(|z|<1\), let \(g(z)=\sqrt{1-z}-1=\sum_{m\ge1}c_m z^m\). Then

\[
 g(z)+\sum_{m\ge1}(-c_m z^m)=0.
\tag{9.3}
\]

The first term has a boundary branch point, every later term is a polynomial, and the series converges normally in the disk. The infinite tail nevertheless cancels the branch point. Mapping \(z=\zeta/s\) gives the same example in an exterior domain. This is **not** an Ising counterexample; it identifies the invalid interchange that must be excluded by a model-specific tail argument.

## 10. Computations and their evidentiary status

Every research program was written in this run and is included under `code/`. Results and actual standard-output captures are under `calculations/`.

| Program | Actual calculation | Status |
|---|---|---|
| `check_exterior.py` | Sixteen even-matrix determinant/product checks at four real/complex exterior parameters; 9,216 inside-root samples; evaluations of the proved tail formula | 90-digit floating-point diagnostics, not interval certification |
| `check_cyclotomic.py` | Cyclotomic-polynomial remainder tests for six primes, all lower even indices, and the first index | Exact integer polynomial arithmetic; finite scope only |
| `check_lowtemp.py` | Full \(X\) coefficients through \(q^{14}\), from \(F_2\) and the proved onset of higher orders | Exact rational arithmetic |
| `check_chi2.py` | Critical \(F_2\) scaling and signed-versus-absolute boundary quadrature | 65-digit non-validated quadrature |
| `check_local_model.py` | Prime-root saddle integrand ratios and radial beta-integral checks | 95-digit floating-point diagnostics; no evaluation of the infinite tail |
| `check_residues.py` | Center-pole and propagator residues; center-coordinate Jacobians; evaluation of the absolute-integral constant | Exact symbolic identities, plus one floating-point constant |

The determinant checks had relative residuals below approximately \(1.1\times10^{-82}\) in these samples. They do not prove the determinant identity; the identity is the explicitly imported TW premise. At \(u=10^{-4}\), the computed \(u^2F_2(e^u)\) was approximately \(0.0265258200082\), approaching the analytically proved \(1/(12\pi)\). These finite computations test formulas, phases, and normalizations. No finite number of them is used to certify a universal natural boundary.

## 11. Self-checks and remaining scope

The following pitfalls were checked explicitly: the use of \(\beta^{-1}\chi\), the full spatial sum and origin, BG versus TW coefficient normalizations, the \(m^2\) branch, the restriction of the determinant identity to even order, uniformity on compact exterior sets, the distinction between \(C^\infty\) and holomorphic continuation, the nonzero local coefficient rather than power counting alone, and the absence of a justified boundary/infinite-sum interchange.

The fixed-order contour reconstruction is written out in `BOUNDARY_DERIVATION.md`, including the signs and factor of two in the local residue. It is not independent confirmation by another solver. All new mathematical claims remain open to audit. The proof of part 1 and the full-function singularities in Section 6 do not depend on accepting that additional fixed-order reconstruction: even without it they remain valid partial results, and the natural-boundary claim would still be unresolved.

The indispensable unproved step for this route is \((T_p)\), or another argument that prevents an infinite tail from canceling the dense fixed-order obstructions. Failure of the current estimates is not a disproof of the target. No continuation disk for the actual full \(X\) has been constructed.

## 12. End of this phase

The stopping reason is a concrete mathematical impasse: there is no established particle-number-uniform boundary control for the indicated tail derivatives. The finite arithmetic, one-dimensional quadratures, local normal form, and exterior estimates that were executable along this route have been carried out. I do not claim to have exhausted alternative mathematical methods. No known historical status of the problem is used as a reason that a solution is impossible.

The action log is a concise, partly retrospective access/evidence record, not a private reasoning transcript or a complete operating-system audit. The observed OS clock began on 27 September 2026, whereas the conversational date instruction says 28 September 2026; no network time check was made. Input integrity was actually checked with the supplied tool. No comparison answer, hint, or feedback was received before freezing. After freezing, this phase ends and these results are not to be overwritten.
