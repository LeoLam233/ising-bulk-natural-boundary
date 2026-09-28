# Ising CR0 independent investigation — frozen-phase report

**Run ID:** `CR0-20260927T183258Z-f97a2fc7`  
**Claimed outcome:** **PARTIAL**  
**Exterior analyticity:** **proved**, using the supplied real-temperature correlation representation as an imported premise.  
**Unit-circle natural boundary for the full bulk susceptibility:** **unresolved**.

This report proves the exterior part of the specified statement, proves actual noncontinuability of the full function at two boundary points, and gives additional analytic and algebraic partial results. It does **not** claim that the natural-boundary statement is false. Nor does it infer that it is true from the existence of this task, from a finite-order calculation, or from the wording of an experimental conclusion in a source.

All references below are to the two supplied versions, with **one-based PDF page numbers**. No bibliography item or source URL was retrieved. “Proved” describes the claims of this run, not an independent audit verdict.

## 1. Exact object, branches, and results

The starting quantity is

\[
 X(s)=\sum_{(M,N)\in\mathbb Z^2}
 \bigl(\langle\sigma_{00}\sigma_{MN}\rangle_+-m(\beta)^2\bigr),
 \qquad s=\sinh(2\beta J)>1.
\]

The phase is the positive-field-limit phase. The origin, both axes, and all other lattice directions are included. With the field convention in the task, the physical response on the real interval is \(\chi=\beta X\). No complex branch of \(\beta(s)=\operatorname{arsinh}(s)/(2J)\) is used in the construction below. In particular, a possible logarithmic branch issue for \(\beta\) is not silently transferred to, or removed from, the target \(X\).

Put

\[
 D=\{s:|s|>1\},\qquad A(s)=s+s^{-1},\qquad
 P(s)=(1-s^{-4})^{1/4}
 =\exp\left[-\frac14\sum_{j\geq1}\frac{s^{-4j}}j\right].                 \tag{1.1}
\]

Thus \(P=m^2\), not \(m\), on the real low-temperature interval. This formula fixes a single-valued holomorphic, nowhere-zero branch on \(D\), positive on \(s>1\).

The substantive conclusions are:

* The physical germ has a single-valued holomorphic continuation to all of \(D\). In fact the connected correlation expansion is normally summable jointly over even particle order and all lattice sites on every compact subset of \(D\) (§§3–4).
* \(X(-s)=X(s)\). For real \(\varepsilon\downarrow0\),
  \[
  \liminf_{\varepsilon\downarrow0}\varepsilon^{7/4}X(1+\varepsilon)
       \ \geq\ \frac{\sqrt2}{12\pi}>0.                                  \tag{1.2}
  \]
  Consequently the **full** \(X\) has no holomorphic extension at \(s=1\) or \(s=-1\). Equation (1.2) is a lower bound, not an assertion of the exact full critical amplitude (§5).
* Each fixed-site correlation, and each fixed-particle coefficient at a fixed site, can be continued locally across \(|s|=1\) away from \(\{1,-1,i,-i\}\) by an explicit contour deformation. This does not justify summing the continued correlations over all sites (§7).
* A dense set of Nickel **candidates** has an exactly determined first possible even particle order and a unique cosine-pair configuration at that order (§8). “Candidate” is deliberately distinguished from a proved singularity of the full function.
* A precise conditional noncancellation criterion would imply the full natural boundary. The boundary-uniform tail estimate in that criterion is not established here. A local saddle model gives the expected finite-order exponent but is not substituted for a whole-integral singular-amplitude proof (§§9–10).

## 2. Imported premises and their actual scope

### 2.1 Real-temperature correlation formula

The main specialized premise used to identify the analytic construction with the physical object is **TW2014v1, Appendix A, PDF p. 9, equation (7)** and the determinant identity immediately preceding it. For real \(s>1\), \(N\geq0\), and integer \(M\), the paper gives

\[
 \langle\sigma_{00}\sigma_{MN}\rangle
 =P(s)\sum_{p\geq0,\ p\ {
m even}}
 \frac1{p!}\int_{[-\pi,\pi]^p}
       \prod_{j<k}h(\theta_j,\theta_k)^2
       \prod_j\frac{e^{iM\theta_j-N\gamma(\theta_j)}}{
                         \sinh\gamma(\theta_j)}
       \prod_j\frac{d\theta_j}{2\pi},                                  \tag{2.1}
\]

where the empty term is 1,

\[
 \cosh\gamma(\theta)=A(s)-\cos\theta,\qquad \gamma(\theta)>0
 \quad(s>1,\ \theta\in\mathbb R),
\]

and

\[
 h(\theta,\phi)=
 \frac{\sin((\theta-\phi)/2)}{\sinh((\gamma(\theta)+\gamma(\phi))/2)},
 \qquad \det[h(\theta_j,\theta_k)]=\prod_{j<k}h(\theta_j,\theta_k)^2
 \quad(p\text{ even}).                                                \tag{2.2}
\]

The first expression for \(h\) on that page has an apparent removable quotient; the displayed alternative identity on the same page gives (2.2). The usual spatial reflections supply negative \(N\). The even two-spin correlation is the same in the two pure zero-field phases, while the subtracted square is the stated spontaneous-magnetization square. The magnetization formula and parameter conversion are on **TW p. 2**; the susceptibility normalization is on **TW p. 1, equation (1)**.

I accept this supplied exact physical representation. I do not rederive it from the lattice Hamiltonian, nor retrieve the books or papers cited by its authors. What is derived below is the required global analytic and convergence control, including the infinite spatial and particle sums.

### 2.2 Independent normalization check from the other supplied paper

**BG2008v1, PDF pp. 2–3, equations (4)–(9)** gives the full low-temperature bulk form-factor expansion, with angular measures \(d\phi/(2\pi)\), the constraint that the sum of the phases is zero, and

\[
 w=\frac{s}{2(1+s^2)}=\frac1{2A(s)}.
\]

In this report its particle variables are converted as

\[
 x_j^{\rm BG}=q_j=e^{-\gamma_j},\qquad
 y_j^{\rm BG}=b_j=\frac1{\sinh\gamma_j},\qquad
 R^{(p)}=\frac{1+\prod_jq_j}{1-\prod_jq_j}.                              \tag{2.3}
\]

The functions \(S_p\) defined in §4.3 are precisely the full-bulk angular terms \(\widetilde\chi^{(p)}\) in that convention. They are not the same grouping as TW's off-origin terms.

### 2.3 What the boundary source results do and do not supply

**TW2014v1, PDF p. 8, Theorem**, for each *fixed even* order, proves \(C^\infty\) extension to the unit circle away from its Nickel set. The definition of the set and the distinction between \(C^\infty\) and analytic continuation are on **p. 3**. The stronger discussion of analytic continuation on that page additionally invokes regular-singular differential-equation behavior. I do not silently replace the stated \(C^\infty\) theorem by an unconditional analytic-extension theorem.

The localization constants in **TW pp. 6–8, Lemmas 1–3**, are not a supplied estimate uniform in particle order. The footnote on **TW p. 2** explicitly identifies the infinite-sum cancellation issue. The diagonal-susceptibility result mentioned on the same page is about a different observable and is not imported as a theorem about this bulk sum.

**BG pp. 33 and 35** discuss finite series, Fourier diagnostics, and increasing evidence against cancellation. **BG p. 46** concerns the geometry and sheet dependence of finite-order Landau configurations. These do not constitute a uniform bound on the infinite tail used in §10. **BG Appendix E, pp. 52–54, especially (E.1) and p. 53**, gives a power-counting treatment of exponents and explicitly qualifies the general exponent discussion. I use it as a comparison with the independently calculated local model, not as a proof of the missing infinite-sum assertion.

A contour-normalization caution is documented in §12.1. All normalization-dependent conclusions use (2.1) and are cross-checked against BG's angular formulas.

## 3. A global small root and a square-root-free determinant

### Lemma 3.1 — global root

For \(s\in D\), \(A(s)\notin[-2,2]\). Indeed, writing \(s=re^{i\alpha}\),

\[
 \operatorname{Im}A(s)=(r-r^{-1})\sin\alpha.
\]

If this vanishes with \(r>1\), then \(s\) is real and \(|A(s)|=r+r^{-1}>2\). Consequently

\[
 T(s,\theta)=A(s)-\cos\theta\notin[-1,1]
 \quad(\theta\in\mathbb R).
\]

For any \(T\notin[-1,1]\), the equation

\[
 q+q^{-1}=2T                                                        \tag{3.1}
\]

has exactly one root with \(|q|<1\). A unit-modulus root would force \(T\in[-1,1]\); the product of the two roots is 1. The small root is locally holomorphic by the implicit-function theorem, since \(q\neq\pm1\). Uniqueness glues these local roots into a single-valued holomorphic function of \(T\). Define

\[
 q(s,\theta)=\text{that small root},\qquad
 b(s,\theta)=\frac{2q(s,\theta)}{1-q(s,\theta)^2}.                        \tag{3.2}
\]

For \(s>1\) these are \(e^{-\gamma}\) and \(1/\sinh\gamma\). No global choice of \(\log q\) or \(\sqrt q\) is needed.

### Lemma 3.2 — determinant conversion

For a tuple \(\theta_1,\ldots,\theta_p\), put \(q_j=q(s,\theta_j)\) and

\[
 L_{jk}=\frac{2q_j\sin((\theta_j-\theta_k)/2)}{1-q_jq_k}.                 \tag{3.3}
\]

On the physical interval, if

\[
 B_{jk}=\frac{2\sin((\theta_j-\theta_k)/2)}{1-q_jq_k},
\]

then \(h=\operatorname{diag}(\sqrt{q_j})B\operatorname{diag}(\sqrt{q_j})\) and \(L=\operatorname{diag}(q_j)B\). Thus \(\det L=\det h\). For even \(p\), the supplied identity (2.2) gives

\[
 \det L=
 \prod_{j<k}
 \frac{4q_jq_k\sin^2((\theta_j-\theta_k)/2)}{(1-q_jq_k)^2}.               \tag{3.4}
\]

For each real tuple both sides are holomorphic in \(s\in D\), so the identity theorem extends (3.4) throughout \(D\). The matrix \(B\) is antisymmetric, hence odd-order determinants vanish. Formula (3.3), unlike an entrywise square-root expression, is globally single-valued.

Replacing one \(\theta_j\) by \(\theta_j+2\pi\) changes the signs of the corresponding row and column of \(L\); its determinant is unchanged. This double sign change is important for the contour argument below.

## 4. Proof of the full exterior analyticity statement

### 4.1 Fixed-particle correlation coefficients

Define, for even \(p\geq2\) and integers \(M,N\),

\[
 C_p(M,N;s)=\frac1{p!}
 \int_{[-\pi,\pi]^p}\det L\,
 \prod_{j=1}^p
 \left[e^{iM\theta_j}q_j^{|N|}b_j\frac{d\theta_j}{2\pi}\right].           \tag{4.1}
\]

Every finite-dimensional integral is holomorphic on \(D\): its integrand is holomorphic in \(s\), continuous on the real integration torus, and locally uniformly bounded there. For real \(s>1\), (2.1) yields

\[
 \langle\sigma_{00}\sigma_{MN}\rangle_+-P(s)
   =P(s)\sum_{p\geq2,\ p\ {
m even}} C_p(M,N;s).                        \tag{4.2}
\]

The next estimate proves all the infinite-sum interchanges needed here and for the lattice sum.

### 4.2 A joint, locally uniform summability bound

Let \(K\Subset D\) be arbitrary. The distance of \(A(K)\) from \([-2,2]\) is positive. Since

\[
 |\cos(u+iv)-\cos u|\leq e^{|v|}-1,
\]

one can choose \(\delta>0\), with a slightly larger strip also available, so that

\[
 A(s)-\cos\theta\notin[-1,1]
 \quad(s\in K,\ |\operatorname{Im}\theta|\leq\delta).
\]

The same holds on a small open neighborhood of \(K\). Compactness, periodicity in the real part, and Lemma 3.1 give

\[
 |q(s,\theta)|\leq\rho<1
 \quad(s\in K,\ |\operatorname{Im}\theta|\leq\delta).                    \tag{4.3}
\]

Set

\[
 W=\frac{2\rho}{1-\rho^2},\qquad
 H=\frac{2\rho\cosh\delta}{1-\rho^2}.
\]

On the product of these strips, \(|b_j|\leq W\) and \(|L_{jk}|\leq H\). Hadamard's determinant inequality, applied to the row Euclidean norms, gives

\[
 |\det L|\leq p^{p/2}H^p.                                             \tag{4.4}
\]

For \(M\neq0\), shift each angular contour by \(i\,\operatorname{sgn}(M)\delta\). The integrand in (4.1) is holomorphic throughout the swept strips. It is \(2\pi\)-periodic in every angular variable: the determinant double sign change noted after (3.4), integer \(M\), and periodic \(q,b\) establish this. Opposite vertical sides therefore cancel. The shift contributes \(e^{-p\delta|M|}\). For \(M=0\) leave the contours real. It follows that

\[
 |C_p(M,N;s)|\leq
 \frac{p^{p/2}}{p!}(HW)^p e^{-p\delta|M|}\rho^{p|N|},\qquad s\in K.       \tag{4.5}
\]

Summing the two geometric series over **all** integers gives

\[
 \sum_{M,N\in\mathbb Z}|C_p(M,N;s)|
 \leq\frac{p^{p/2}}{p!}(HW)^p
 \frac{1+e^{-p\delta}}{1-e^{-p\delta}}
 \frac{1+\rho^p}{1-\rho^p}
 \leq G_K\frac{p^{p/2}}{p!}(HW)^p,                                    \tag{4.6}
\]

where, uniformly for even \(p\geq2\),

\[
 G_K=\frac{1+e^{-2\delta}}{1-e^{-2\delta}}
      \frac{1+\rho^2}{1-\rho^2}<\infty.
\]

Finally \(p!\geq(p/e)^p\), so the \(p\)-th root of the last particle-order factor is at most \(eHW/\sqrt p\), which tends to zero. Thus

\[
 \sum_{p\geq2,\ p\ {\rm even}}\sum_{M,N\in\mathbb Z}
       |C_p(M,N;s)|
\]

converges uniformly for \(s\in K\). This is an actual joint majorant, not a fixed-order convergence assertion.

### Theorem 4.3 — exterior part of the target

The function

\[
 X_D(s)=P(s)\sum_{p\geq2,\ p\ {\rm even}}
                  \sum_{M,N\in\mathbb Z}C_p(M,N;s)                     \tag{4.7}
\]

is single-valued and holomorphic throughout \(D\), by locally uniform convergence of holomorphic functions. On every real \(s>1\), absolute convergence permits summing (4.2) over every lattice site, and the result is precisely the target \(X(s)\). Thus (4.7) is the required continuation of its physical germ. Since \(D\) is connected, the identity theorem gives uniqueness among holomorphic functions on this domain agreeing with the germ.

The origin has not been dropped: (2.1) at \((0,0)\), together with \(\langle\sigma_{00}^2\rangle=1\), gives

\[
 P(s)\sum_{p\geq2,\ p\ {\rm even}}C_p(0,0;s)=1-P(s).                   \tag{4.8}
\]

This identity extends from the real interval to \(D\). It also provides a sensitive normalization check.

### 4.3 Full-bulk angular terms and a second majorant

Let

\[
 S_p(s)=\sum_{M,N\in\mathbb Z}C_p(M,N;s).
\]

For fixed \(p\), the angular integrand is smooth and periodic. Fourier inversion for the pushforward under addition of the angles, justified also by (4.5), evaluates the sum over \(M\) by setting

\[
 \theta_p=-\sum_{j=1}^{p-1}\theta_j\pmod{2\pi}.
\]

The absolutely convergent sum over \(N\) is \(\sum_{N\in\mathbb Z}Q^{|N|}=(1+Q)/(1-Q)\), where \(Q=\prod_jq_j\). Hence

\[
 S_p(s)=\frac1{p!}\int_{\mathbb T^{p-1}}
     \det L\,\prod_{j=1}^p b_j\,
     \frac{1+Q}{1-Q}\prod_{j=1}^{p-1}\frac{d\theta_j}{2\pi},\qquad
 X_D=P\sum_{p\geq2,\ p\ {\rm even}}S_p.                                \tag{4.9}
\]

Substituting \(2w=1/A(s)\) into BG equations (8)–(9), first near large positive \(s\), gives exactly (2.3). Analytic continuation then preserves that normalization. The square of BG's fermionic factor is (3.4). Thus (4.9) independently matches its full-bulk equation (5), including the factorial, all angular factors, and the origin-inclusive grouping.

For a compact \(K\), a real-angle bound \(\rho_K<1\) alone now suffices. With \(W_K=2\rho_K/(1-\rho_K^2)\),

\[
 |S_p(s)|\leq\frac{p^{p/2}}{p!}W_K^{2p}
                       \frac{1+\rho_K^p}{1-\rho_K^p}.                 \tag{4.10}
\]

This supplies a shorter normal-convergence proof starting from BG's real-temperature bulk expansion. It is consistent with, but does not replace the stronger joint lattice estimate (4.6).

### 4.4 Evenness and complex conjugation

Under \(s\mapsto-s\) and a simultaneous shift of all real angles by \(\pi\), uniqueness of the small root gives

\[
 q(-s,\theta+\pi)=-q(s,\theta),\qquad b(-s,\theta+\pi)=-b(s,\theta).
\]

The matrix \(L\) changes to \(-L\). For even \(p\), its determinant, the product of the \(b_j\)'s, and the signs from \(e^{iM\theta_j}q_j^{|N|}\) have total sign +1. Periodicity permits the angular shift. Since \(P(-s)=P(s)\), (4.7) proves

\[
 X_D(-s)=X_D(s).                                                      \tag{4.11}
\]

The same transformation proves evenness of every individual \(S_p\).

Uniqueness of the same root and conjugation of the real-angle integrals similarly give \(X_D(\overline s)=\overline{X_D(s)}\).

## 5. Two proved singular boundary points of the full susceptibility

For real \(s>1\), all \(q_j,b_j\) in (4.9) are positive, \(0<Q<1\), and \(\det L=\prod_{j<k}h_{jk}^2\geq0\). Therefore every \(S_p(s)\geq0\), and

\[
 X(s)\geq P(s)S_2(s).                                                \tag{5.1}
\]

For \(p=2\), \(\theta_2=-\theta_1\), and writing \(\theta=\theta_1\),

\[
 h_{12}=\frac{\sin\theta}{\sinh\gamma(\theta)},\qquad
 \frac{1+q^2}{1-q^2}=\coth\gamma(\theta).
\]

Thus

\[
 S_2(s)=\frac1{4\pi}\int_{-\pi}^{\pi}
 \frac{\sin^2\theta\,[A(s)-\cos\theta]}
      {([A(s)-\cos\theta]^2-1)^{5/2}}\,d\theta.                         \tag{5.2}
\]

All roots in this real integral are positive. Put

\[
 d=A(s)-2=\frac{(s-1)^2}{s}>0.
\]

Using \(v=\sin(\theta/2)\), evenness of the integrand gives

\[
 S_2(s)=\frac4\pi\int_0^1
 \frac{v^2\sqrt{1-v^2}\,(1+d+2v^2)}
 {(d+2v^2)^{5/2}(2+d+2v^2)^{5/2}}\,dv.                                \tag{5.3}
\]

Set \(v=\sqrt{d/2}\,u\) and extend the resulting integrand by zero beyond \(u=\sqrt{2/d}\). Then

\[
 dS_2(s)=\frac4{\pi2^{3/2}}
 \int_0^{\sqrt{2/d}}
 \frac{u^2\sqrt{1-du^2/2}\,(1+d+du^2)}
 {(1+u^2)^{5/2}(2+d+du^2)^{5/2}}\,du.                                 \tag{5.4}
\]

For \(v_0=d+du^2\geq0\), \((1+v_0)/(2+v_0)^{5/2}\leq2^{-5/2}\). Consequently the integrand is dominated by a constant times \(u^2/(1+u^2)^{5/2}\), an integrable function on \([0,\infty)\). Dominated convergence and

\[
 \int_0^\infty\frac{u^2}{(1+u^2)^{5/2}}\,du=\frac13
\]

give the **proved two-particle asymptotic**

\[
 S_2(s)\sim\frac1{12\pi d},\qquad s\downarrow1.                         \tag{5.5}
\]

Since \(P(1+\varepsilon)\sim(4\varepsilon)^{1/4}\) and \(d\sim\varepsilon^2\), (5.1) proves (1.2). A holomorphic extension at 1 would be bounded on a sufficiently small closed disk around 1, contradicting this radial divergence. Evenness proves the same nonextension at \(-1\).

No positivity argument has been extended to non-real temperature. No claim is made here that a single two-particle term dominates the full function there. In particular, this section does not settle \(\pm i\), let alone the rest of the circle.

## 6. A further normalization check: exact coefficients near infinity

Let \(u=1/s\). Uniformly for real angles and sufficiently small \(|u|\), the root formula has \(q=O(u)\), \(b=O(u)\), and every squared pair factor in (3.4) is \(O(u^2)\). The constants can be chosen independently of particle order. From (4.9), for some \(c,C\) and sufficiently small fixed \(r\) with \(cr<1\),

\[
 |S_p(1/u)|\leq \frac C{p!}(c|u|)^{p^2},\qquad |u|\leq r.               \tag{6.1}
\]

The exponent is \(p(p-1)\) from pair factors plus \(p\) from the weights. The factor \((1+Q)/(1-Q)\) is uniformly bounded for even \(p\geq2\). In particular,

\[
 \sum_{p\geq4,\ p\ {\rm even}}S_p(1/u)=O(u^{16}),                     \tag{6.2}
\]

by factoring out \(|u|^{16}\) in the normally convergent majorant. This also proves holomorphy at infinity and makes the following finite coefficient calculation relevant to the **full** function, not merely to a truncation.

In (5.2), put \(c_\theta=\cos\theta\). Its integrand becomes the normalized angular average of

\[
 \frac{u^4}{2}(1-c_\theta^2)(1-c_\theta u+u^2)
 \left[1-2c_\theta u+(c_\theta^2+1)u^2-2c_\theta u^3+u^4\right]^{-5/2}.
\]

Expand by the binomial theorem and use the exact moments

\[
 \frac1{2\pi}\int_{-\pi}^{\pi}\cos^{2j}\theta\,d\theta
 =\frac{\binom{2j}{j}}{4^j},\qquad
 \int_{-\pi}^{\pi}\cos^{2j+1}\theta\,d\theta=0.
\]

The rational-arithmetic script `code/series_check.py` implements these identities without numerical fitting. Combining (6.2) and \(P=(1-u^4)^{1/4}\), it gives

\[
\begin{aligned}
 S_2(1/u)&=\tfrac14(u^4+u^6)+\tfrac{15}{32}(u^8+u^{10})
                 +\tfrac{175}{256}(u^{12}+u^{14})+O(u^{16}),\\
 X_D(1/u)&=\tfrac14(u^4+u^6)+\tfrac{13}{32}(u^8+u^{10})
                 +\tfrac{139}{256}(u^{12}+u^{14})+O(u^{16}).             \tag{6.3}
\end{aligned}
\]

The output is `evidence/exact_series.json`. Independent high-precision quadrature of (5.2) at \(s=4,8,16,32\) checks the order of the discarded remainder; it is not the proof of (6.3). No closed form for all coefficients is inferred from this short exact list.

## 7. Local continuation of fixed-site correlations — a distinct partial result

This section is useful both for interpreting the particle grouping and for seeing exactly where a spatial infinite sum can obstruct continuation.

### Proposition 7.1

Every \(C_p(M,N;s)\) for fixed \(p,M,N\), and the complete fixed-site correlation given by its normally convergent Fredholm series, extends holomorphically through any

\[
 \zeta\in\mathbb T\setminus\{1,-1,i,-i\}.
\]

### Proof

First let \(\operatorname{Im}\zeta>0\) and set \(a_0=A(\zeta)\in(-2,2)\setminus\{0\}\). Choose any sufficiently small \(\eta>0\), and replace the real angular contour by

\[
 \theta(t)=t+i\eta\sin t,\qquad -\pi\leq t\leq\pi.                     \tag{7.1}
\]

For exterior \(s\) near \(\zeta\), \(\operatorname{Im}A(s)>0\). Throughout the homotopy from the real contour to (7.1),

\[
 \operatorname{Im}\{A(s)-\cos(t+iv)\}
 =\operatorname{Im}A(s)+\sin t\sinh v>0,
 \quad v\text{ between }0\text{ and }\eta\sin t.                        \tag{7.2}
\]

Thus the small root and all integrands remain holomorphic, with no pair denominator zero. The contour deformation is legitimate separately in each variable.

At \(s=\zeta\), the imaginary part in (7.2) is strictly positive except at \(t=0,\pi\) (with \(-\pi\) identified with \(\pi\)). None of the corresponding values of \(T\) is \(\pm1\), because \(a_0\neq0,\pm2\). The limiting roots satisfy \(|q|<1\) except at exactly one of these angular points. If \(a_0>0\) it is \(t=0\), where \(T=a_0-1\in(-1,1)\); if \(a_0<0\) it is \(t=\pi\), where \(T=a_0+1\in(-1,1)\). At this one point the limiting unit root \(q_*\) satisfies \(q_*^2\neq1\).

It follows on the entire compact deformed contour that \(q^2\neq1\) and, for any two contour points, \(q_iq_j\neq1\): equality would require both roots to have unit modulus, and then their product is \(q_*^2\neq1\). All roots are simple. The implicit-function theorem, compactness, and uniqueness on overlapping local patches extend the chosen root along this contour to a common neighborhood of \(s=\zeta\). The denominators keep a positive lower bound there.

Parameterize the deformed integrals by the real variables \(t_j\). The Jacobians, \(q,b,L\), and, for fixed \(M,N\), \(e^{iM\theta}q^{|N|}\), have finite uniform bounds. Hadamard's estimate again bounds the \(p\)-th Fredholm coefficient by \(p^{p/2}B_{M,N}^p/p!\). Hence the particle sum remains normally convergent in that neighborhood. Also \(P\) has a local analytic nonzero extension because \(\zeta^4\neq1\).

For a lower-half-circle point, use \(\theta(t)=t-i\eta\sin t\) and the analogous lower-half-plane argument, or conjugation. This proves the proposition.

The resulting bound contains factors such as \(e^{\eta|M|}\) and possibly \(\sup|q|^{|N|}\). It is **not** a summable spatial bound uniform over \(\mathbb Z^2\). Consequently this proposition is not a continuation theorem for the full bulk susceptibility.

## 8. Dense candidate geometry with exact first-order information

For an even particle count \(p\), define the Nickel set as in TW p. 3:

\[
 E_p=\left\{\zeta\in\mathbb T:
 2\operatorname{Re}\zeta=
 \cos(2\pi j/p)+\cos(2\pi k/p)\text{ for some integers }j,k\right\}.      \tag{8.1}
\]

The following statements concern this **algebraic set**. They do not assert a full-function singularity at every point in it.

### Proposition 8.1 — a dense family and its first possible even order

Let \(q\geq7\) be prime, \(1\leq\ell\leq q-1\), and

\[
 \zeta=\exp(2\pi i\ell/q).
\]

Then \(\zeta\in E_p\), for even \(p\), if and only if \(q\mid p\). In particular its first such order is \(p_0=2q\). The union of these points over the primes is dense in \(\mathbb T\).

If \(q\mid p\), both cosines in (8.1) can simply be chosen equal to \(\operatorname{Re}\zeta\). Conversely, suppose \(q\nmid p\). Because \(q\) is prime, \(\gcd(p,q)=1\). In the cyclotomic field of \(pq\)-th roots of unity, the Chinese remainder theorem gives an automorphism exponent \(r\) with

\[
 r\equiv1\pmod p,\qquad r\equiv2\pmod q,\qquad \gcd(r,pq)=1.
\]

It fixes both \(p\)-th-root cosines but sends \(\cos(2\pi\ell/q)\) to \(\cos(4\pi\ell/q)\). These are different: equality would require \(2\ell\equiv\ell\) or \(-\ell\pmod q\), impossible for nonzero \(\ell\) and \(q\geq7\). This contradicts (8.1).

For density, take arbitrarily large primes and choose \(\ell\) nearest to \(q\alpha/(2\pi)\) for a desired angle \(\alpha\). The angular error is at most \(\pi/q\); exclusion of \(\ell=0\) does not affect density. Unboundedness of primes suffices.

### Proposition 8.2 — uniqueness of the first-order cosine pair

At \(p_0=2q\), every solution of

\[
 \cos(\pi j/q)+\cos(\pi k/q)=2\cos(2\pi\ell/q)                          \tag{8.2}
\]

has **both** cosines equal to \(\cos(2\pi\ell/q)\).

Write \(\xi=e^{2\pi i/q}\), \(d=(q+1)/2\), and use \(e^{\pi i/q}=-\xi^d\). After multiplying (8.2) by 2, it becomes

\[
 (-1)^j(\xi^{dj}+\xi^{-dj})+
 (-1)^k(\xi^{dk}+\xi^{-dk})-2\xi^\ell-2\xi^{-\ell}=0.                  \tag{8.3}
\]

Reduce exponents modulo \(q\). The coefficient vector has support at at most six positions. A polynomial of degree at most \(q-1\) vanishing at \(\xi\) is a scalar multiple of
\(1+x+\cdots+x^{q-1}\). Because \(q\geq7\), at least one coefficient of (8.3) is zero, so this scalar is zero. Its coefficient sum is then
\(2(-1)^j+2(-1)^k-4=0\), which forces \(j,k\) even. All remaining positive support must be at \(\ell,-\ell\), proving the assertion.

The exact integer-arithmetic diagnostic in `code/exact_geometry.py` verifies the first-order uniqueness for 71 targets at \(q=7,11,13,17,19,23,29,31\), and checks the CRT automorphisms for the lower even orders. The proofs above are universal; finite enumeration is only a check.

### 8.3 Relation to the supplied fixed-order theorem

Define the origin-excluded normalized term

\[
 T_p(s)=\tfrac12\bigl(S_p(s)-C_p(0,0;s)\bigr).
\]

Appendix A of TW, PDF p. 10, derives this spatial grouping by summing the four quadrants and subtracting the duplicated axes. With ordinary contour measures its integrand is the one treated in the TW theorem, up to a nonzero constant depending only on \(p\); see §12.1. Such a constant cannot change fixed-order \(C^\infty\) regularity. Proposition 7.1 shows that the added origin coefficient is analytic at the prime-root points under consideration. Therefore the TW theorem implies that, at one of these points, every \(S_p\) with \(p<p_0\) has bounded derivatives of each fixed order as the point is approached from the exterior.

This removes a *finite-head* regularity issue. It supplies neither the nonzero singular amplitude of \(S_{p_0}\) nor the required control of the infinitely many terms with \(p>p_0\).

## 9. A local singular model: what was actually derived

Take an upper-half-plane prime-root point \(\zeta=e^{i\alpha}\), with \(0<\alpha<\pi\), \(\alpha\neq\pi/2\), and \(p\alpha\in2\pi\mathbb Z\). Near the equal-angle configuration \(\theta_j=\alpha\), on the exterior sheet,

\[
 \gamma=i\alpha,\qquad
 \partial_t\gamma\bigl(\zeta(1+t),\alpha\bigr)\big|_{t=0}=2,\qquad
 \gamma_\theta=-i,\qquad \gamma_{\theta\theta}=-2i\cot\alpha.             \tag{9.1}
\]

These follow by implicit differentiation of \(\cosh\gamma=A(s)-\cos\theta\); the derivative in \(t\) uses \(A'(\zeta)=1-\zeta^{-2}\). For angular perturbations \(\delta_j\) with \(\sum\delta_j=0\),

\[
 \sum_j\gamma_j-p\,i\alpha
 =2pt-i\cot\alpha\sum_j\delta_j^2
       +O(t^2+|t|\,\|\delta\|+\|\delta\|^3).                            \tag{9.2}
\]

The numerator pair factors have leading product equal to a nonzero constant times

\[
 \Delta(\delta)^2=\prod_{j<k}(\delta_j-\delta_k)^2.                       \tag{9.3}
\]

The \(b_j\)'s are finite and nonzero there, while the leading singular part of \((1+Q)/(1-Q)\) is twice the reciprocal of the quadratic expression in (9.2). Thus the formal local model is a Vandermonde-square numerator over a nondegenerate quadratic denominator on a \((p-1)\)-dimensional constraint space.

Here is an exact calculation for the corresponding positive radial model, separately from any unproved localization statement about the Ising integral. On

\[
 H_p=\{\delta\in\mathbb R^p:\sum_j\delta_j=0\},
\]

with its induced Euclidean measure, let

\[
 I_p(t)=\int_{\|\delta\|<1\atop\delta\in H_p}
                  \frac{\Delta(\delta)^2}{t+\|\delta\|^2}\,d\delta,
 \qquad t>0.
\]

The squared Vandermonde has degree \(p(p-1)\). Its angular integral \(a_p\) on the unit sphere in \(H_p\) is finite and strictly positive. Consequently, with

\[
 \nu=\frac{p^2-1}{2},\qquad k=\frac{p^2-2}{2}\quad(p\text{ even}),
\]

polar coordinates give

\[
 I_p(t)=\frac{a_p}{2}\int_0^1\frac{v^{\nu-1}}{t+v}\,dv.
\]

Differentiate \(k\) times at \(t>0\), scale \(v=tu\), and use the beta integral. Its hypotheses are \(\nu>0\) and \(k+1-\nu=1/2>0\). This proves

\[
 \lim_{t\downarrow0}t^{1/2}I_p^{(k)}(t)
   =(-1)^k\frac{a_p}{2}\Gamma(\nu)\Gamma(1/2)\neq0.                     \tag{9.4}
\]

The resulting local exponent is \(\nu-1=(p^2-3)/2\), agreeing with the equal-angle power count in BG Appendix E. For the first prime example \(p=14\), the relevant derivative order is already \(k=97\).

**Limitation of this derivation.** Equations (9.1)–(9.4) are not, by themselves, a theorem that the entire \(S_p\) has a nonzero singular coefficient of that form. One must justify the actual localized complex contour, remainder estimates, treatment of all other singular configurations, and the aggregate amplitude on the physical exterior sheet. The prime-root uniqueness result simplifies this issue but does not replace those analytic steps. In particular, a positive angular constant for the radial model is not automatically a positivity theorem for the full complex-temperature integral. This finite-order completion is left explicitly unproved here.

## 10. Conditional natural-boundary theorem and the unresolved tail

### Proposition 10.1 — sufficient radial noncancellation criterion

Let \(Z\subset\mathbb T\setminus\{1,-1,i,-i\}\) be dense. For every \(\zeta\in Z\), suppose there exist a finite even cutoff \(p_0\), an integer \(k\geq0\), and a nonzero \(c_\zeta\) such that, writing \(s=\zeta(1+t)\),

\[
 \lim_{t\downarrow0}\sqrt t\,\frac{d^k}{dt^k}
              \sum_{2\leq p\leq p_0,\ p\ {\rm even}}S_p(s)=c_\zeta,     \tag{10.1}
\]

and

\[
 \lim_{t\downarrow0}\sqrt t\,\frac{d^k}{dt^k}
              \sum_{p>p_0,\ p\ {\rm even}}S_p(s)=0.                    \tag{10.2}
\]

Then the unit circle is a natural boundary for the **full** \(X_D\) in the exact sense of the task.

Indeed, \(P\) has a nonzero analytic branch in a disk about such a \(\zeta\). An extension of \(X_D\) would extend \(X_D/P\) and give a bounded \(k\)-th derivative along the short radial segment. Equations (10.1)–(10.2) contradict that bound. Thus every point of \(Z\) is a nonextension point. A disk giving continuation at any other point of the circle would contain a smaller disk about some \(\zeta\in Z\), giving the same contradiction. This proves the conditional statement.

For positive \(t\), differentiation of the infinite sum is legitimate by the normal convergence already proved on compact subsets of \(D\), or by Cauchy estimates on a slightly larger compact subset. That fact does not establish either boundary limit.

A concrete stronger sufficient condition for (10.2) is

\[
 \sum_{p>p_0,\ p\ {\rm even}}
 \sup_{0<t<t_0}
 \left|\frac{d^k}{dt^k}S_p(\zeta(1+t))\right|<\infty                    \tag{10.3}
\]

for some \(t_0>0\) depending on \(\zeta\). A direct proof of the weaker limit (10.2) would also suffice and need not establish (10.3).

### 10.2 Why the proved exterior bound does not supply this condition

For \(\zeta=e^{i\alpha}\), evaluate the small root at \(\theta=\alpha\). By (9.1),

\[
 q(\zeta(1+t),\alpha)=e^{-i\alpha}(1-2t+O(t^2)).
\]

If \(\rho(t)=\sup_{\theta\in\mathbb R}|q(\zeta(1+t),\theta)|\), then
\(1-\rho(t)^2\leq4t+O(t^2)\). The quantity
\(W(t)=2\rho(t)/(1-\rho(t)^2)\) in (4.10) therefore grows at least as a positive constant times \(t^{-1}\). The bound involves \(W(t)^{2p}\), as well as a geometric denominator tending to zero. Its normal convergence for each positive distance from the circle does not give a bound uniform down to \(t=0\). Using a Cauchy disk of radius proportional to that distance additionally introduces inverse powers of \(t\) for derivatives.

This is a precise failure of the available estimate, not evidence that the actual tail is large. It is entirely consistent with much smaller actual coefficients arising from oscillation and determinant cancellation. Such cancellation would have to be controlled uniformly in particle order to prove (10.2).

TW's fixed-order integration-by-parts argument uses a positive separation of a convex hull from zero, a localization cover, and a number of integrations depending on the relevant variables and derivative order. The supplied proof does not bound all these constants in the required infinite-order sum. At a prime-root candidate, higher multiples of \(2q\) are also Nickel orders, and other orders have nearby candidate sets. Establishing fixed-order smoothness or a higher formal exponent for every term is not the missing uniform estimate.

### 10.3 An exact counterexample to the *inference*, not to Ising

Normal convergence inside the domain, entire individual tail terms, and even quadratic growth of their vanishing orders do not logically prevent an infinite tail from cancelling a boundary singularity.

To see this, let \(|z|<1\),

\[
 g(z)=(1-z)^{1/2}=\sum_{j\geq0}a_jz^j,
 \qquad
 B_n(z)=-\sum_{j=n^2}^{(n+1)^2-1}a_jz^j,\quad n=0,1,2,\ldots.
\]

Every \(B_n\) is a polynomial; for \(n\geq1\) it vanishes to order at least \(n^2\) at zero. On \(|z|\leq r<R<1\), Cauchy's coefficient bound for \(g\) gives \(\|B_n\|\leq C_{r,R}(r/R)^{n^2}\). Thus the series is normally convergent, with a stronger-than-factorial interior decay in this index. Nevertheless,

\[
 g(z)+\sum_{n\geq0}B_n(z)=0,
\]

although \(g\) has a square-root branch point at 1 and each polynomial tail term is analytic across 1. Taking \(z=\zeta/s\) gives the same phenomenon in an exterior disk. This explicitly invalidates an attempted inference from termwise boundary information plus interior normal convergence. It is **not** a representation of the Ising model and is not a disproof of the target.

## 11. Computations and self-checks: exact versus numerical evidence

All programs were written during this run under `RUN_OUTPUT/code/`. No research code or dataset outside the supplied packet was read. No package was installed. The executed numerical programs use installed NumPy and mpmath; the exact geometry and series programs use ordinary integer or rational arithmetic. Versions are recorded in `evidence/self_checks.json` and `evidence/setup.json`.

The following are diagnostics, not substitutes for the proofs:

* `self_checks.py` checks the determinant/product conversion at particle counts 2, 4, 6, 8 and real, complex, and negative-real exterior parameters using 65-digit arithmetic. The largest recorded relative discrepancy is approximately \(2.682\times10^{-59}\). It also checks contour shifts and the origin Fredholm normalization numerically. The contour-shift changes are at most approximately \(1.10\times10^{-17}\) in the tested double integrals.
* The origin Nyström check at \(s=1.08\) initially has error about \(4.45\times10^{-6}\) at 96 nodes. This was not hidden or called accurate. `refine_checks.py` improves the node count to 192 and 384, with recorded discrepancies about \(9.21\times10^{-11}\) and \(1.24\times10^{-14}\). Initial outputs remain present.
* The critical quadrature checks \(12\pi d S_2\to1\), and compares the original angular integral with the independently rescaled integral. At \(s-1=10^{-5}\), the recorded ratio is approximately \(0.999999998215134\). The proof is dominated convergence in §5, not this observation. Some initial endpoint square-root evaluations leave imaginary residuals around \(10^{-101}\); they are preserved and explicitly recorded as numerical roundoff, not physical imaginary parts or certified error intervals.
* `exact_geometry.py` performs exact finite cyclotomic reductions for 71 selected targets. `series_check.py` computes the rational coefficients in (6.3) by exact angular moments. Their universal uses depend on the analytic and algebraic proofs in §§6 and 8, not extrapolation from finite checks. `series_numeric_crosscheck.py` separately checks the finite two-particle series against quadrature, with the residual scaling as \(u^{16}\) in the tested range.

`boundary_contour_check.py` additionally checks the fixed-site contour in §7 at, outside, and slightly inside \(\exp(2\pi i/7)\), following the quadratic roots continuously rather than selecting the small root again after crossing. It checks the origin identity and a fixed-site correlation; it does not compute an infinite spatial sum. Its data are in `evidence/boundary_contour_check.json`.

The PDF renders under `pdf_views/` are offline views of supplied pages, not additional research inputs. Load-bearing formulas were checked against original PDF images rather than silently trusting damaged text extraction. No OCR was used.

## 12. Source normalization, access limitations, and final unresolved steps

### 12.1 The contour normalization was not silently guessed

With ordinary unnormalized contour differentials, converting (2.1) to \(p\) x-contours and \(p\) y-contours introduces \((2\pi i)^{-2p}\). One y-residue obeys

\[
 \frac1{2\pi i}\oint\frac{y^{N-1}}{D(x,y;s)}\,dy
       =\frac{q(x)^N}{\sinh\gamma(x)},\qquad
 D(x,y;s)=A(s)-\tfrac12(x+x^{-1})-\tfrac12(y+y^{-1}).
\]

For real \(s>1\), one may choose the circles close enough to the unit circle to enclose all the small roots and avoid pair poles. Writing \(X_0=\prod x_j\) and \(Y_0=\prod y_j\), the origin-excluded quadrant sum replaces \(\prod x_j^M y_j^N\) by

\[
 \frac{2(X_0+Y_0)}{(1-X_0)(1-Y_0)}.
\]

Consequently \(T_p=(S_p-C_p(0,0))/2\) has the same contour integrand as TW's displayed \(\chi^{(p)}\), with prefactor \(1/[p!(2\pi i)^{2p}]\) in these ordinary measures. In the included **TW PDF p. 3**, the displayed prefactor reads \(1/[p!(2\pi i)^p]\); **p. 10, equation (8)** also has a prefactor that should not be used without redoing the measure conversion. I did not determine whether an implicit measure convention or a printing error was intended. The discrepancy is a temperature-independent nonzero factor at each fixed order and does not affect the fixed-order regularity statement used in §8.3.

No normalization-dependent claim in this report uses that printed contour prefactor or uses a potentially rescaled infinite sum from it. The actual physical construction uses TW's explicit real angular equation (7), includes the origin by (4.8), and agrees independently with BG equations (4)–(9). Failure of a printed prefactor, if indeed a printing error, would not disprove the target object.

### 12.2 Access and logging limitations

The information boundary was observed for mathematical work: only the supplied papers and task files, ordinary mathematical knowledge, installed runtimes/libraries, and this run's own output were used. No web/search, connector, remote computation, prior conversation, project memory, external agent, or delegated subagent was accessed. The supplied source identifiers were not opened.

There is one disclosed **procedural deviation**: a higher-priority environment requirement caused the local PDF-handling skill `[LOCAL_PATH_REDACTED]` to be read. It lies outside `INPUT/` and `RUN_OUTPUT/`. It supplied operational PDF instructions, not an Ising result or a mathematical hint. This was disclosed to the user immediately after the read and entered in the log. No other local research material or prior solution was encountered.

Network isolation was **not technically established or tested**. The fact that the task prohibited network use is not evidence that network access was disabled. Filesystem access likewise was not confined by a demonstrated sandbox; the procedural skill read itself demonstrates an outside read was possible. Ordinary runtime files necessarily loaded by Python, NumPy, mpmath and the PDF renderer were not audited individually. The tools and hash checks do not certify isolation.

The visible conversation is this task; no memory-retrieval tool or other conversation was used. The backend's context initialization, hidden service configuration, and the contents of prior model training cannot be independently audited here. I recognized general Ising terminology and ordinary background, but no prior solution to the full target was recognized or used. No specialized remembered solution or unavailable research theorem was used to close a decisive gap.

The earliest extraction and ordered setup reads were logged retrospectively with unknown exact times. Some related actions and reads were initially grouped. Large initial text displays were visibly truncated; focused rereads and authoritative PDF views were used for the load-bearing passages. The action log and supplementary action index are evidence/access records authored by this run, not a complete system-level file-access trace or an independently trusted timestamp service. Host clock readings are recorded as readings, not independently calibrated UTC. The full tool transcript is not exported by an available transcript-export facility.

### 12.3 Remaining gaps and reason for stopping this phase

The exact full natural-boundary claim remains unresolved in this run. The specific unfinished steps are:

1. Promote the local finite-order analysis at a dense chosen family, such as the prime-root family, to a rigorously nonzero whole-integral exterior-sheet singular amplitude, with its required derivative limit (10.1). The local radial model and the finite-order source statements are not silently treated as that proof.
2. Prove the infinite-tail limit (10.2), or another noncancellation argument of comparable full scope. The stronger bound (10.3) is one explicit sufficient estimate, not an established result. The actual compact-set majorants fail to deliver it for the reasons in §10.2.

Even granting the standard fixed-order Nickel singular-amplitude assertion would leave the second step unproved. Conversely, failure of these estimates is not a counterexample to \(X_D\)'s natural boundary.

The stopping reason is this **specific mathematical impasse after the displayed derivations and self-checks**, not the reputation or age of the question. No execution-time, memory, or computation-budget exhaustion is claimed. Actual hard resource limits beyond observed command behavior are unknown; no attempted numerical or exact computation here ended in a resource failure. The finite computations were completed, the initially inadequate normalization quadrature was refined, and no identified finite calculation is being handed back as a substitute for the missing analytic argument.

This phase is to be frozen before any comparison material or feedback is received. The original frozen result is not to be overwritten by later comparison, continuation, or repair.
