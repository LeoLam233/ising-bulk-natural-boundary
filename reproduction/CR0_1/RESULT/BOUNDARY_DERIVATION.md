# Fixed-order boundary reconstruction and its limit

Run `ISING-CR0-20260927-ba3792d2458a`.

This supplement concerns **fixed even particle number**. Its last section states precisely why it does not prove a natural boundary for the infinite sum. Notation \(F_n,M_2,A,x,y\) is as in `RESULT.md`; \(F_n\) is the BG full coefficient, including its origin contribution.

## A. A normalized full double-contour formula

Use different letters for contour coordinates and for the inside root: \(z_j,t_j\) are contour coordinates, while \(x(s,\phi)\) remains the root from the main report. Set

\[
 D(z,t;s)=A-\tfrac12(z+z^{-1})-\tfrac12(t+t^{-1}),
\]

\[
 V(z)=\prod_{j<k}\frac{z_j-z_k}{1-z_jz_k},\quad
 Z=\prod_jz_j,\quad T=\prod_jt_j,\quad R(q)=\frac{1+q}{1-q}.
\]

For fixed even \(n\), the formula to be used is

\[
 F_n(s)=\frac1{n!}\oint\cdots\oint
 V(z)V(t)R(Z)R(T)
 \prod_{j=1}^n
 \frac{dz_j}{2\pi i z_j}\frac{dt_j}{2\pi i t_j}\frac1{D(z_j,t_j;s)}.
\tag{A.1}
\]

Every contour is positively oriented \(|z_j|=|t_j|=r<1\), with \(r\) sufficiently close to one for the chosen exterior \(s\). In a small neighborhood of any exterior parameter, one common \(r\) works. Thus the contour integral defines a holomorphic function there.

Here is the normalization derivation rather than an identification with TW's \(\chi^{(n)}\). TW Appendix A, PDF p. 9, gives the real low-temperature coefficient of the correlation for \(N\ge0\) as

\[
 C_n(M,N)=\frac1{n!}\int
 e^{iM\sum\phi_j}\prod_j e^{-N\gamma_j}y_j
 \prod_{j<k}h_{jk}^2\prod_j\frac{d\phi_j}{2\pi}.
\tag{A.2}
\]

It also gives the identity

\[
 h_{jk}^2=
 \frac{e^{-\gamma_j}-e^{-\gamma_k}}{1-e^{-\gamma_j-\gamma_k}}
 \frac{z_j-z_k}{1-z_jz_k},\qquad z_j=e^{i\phi_j}.
\tag{A.3}
\]

The elementary factorization

\[
 tD(z,t;s)=-\tfrac12(t-e^{-\gamma(z)})(t-e^{\gamma(z)})
\]

has residue \(1/\sinh\gamma(z)\) for \(1/(tD)\) at the inside root. Thus the normalized double-contour expression for (A.2), for \(M,N\ge0\), is the right side of (A.1) with \(R(Z)R(T)\) replaced by \(Z^M T^N\). The factors \(dz/(2\pi iz)\), \(dt/(2\pi it)\) arise one by one from the angular measure and Cauchy's residue formula. All are displayed in (A.1).

Reflection in \(M\) follows by replacing every angle by its negative in (A.2), and use \(|N|\) to reflect in \(N\). Summing the reflected geometric factors gives

\[
 \sum_{M,N\in\mathbb Z}Z^{|M|}T^{|N|}=R(Z)R(T).
\]

The fixed-order correlation terms decay sufficiently fast for this manipulation on a real low-temperature interval: the angular integrands extend to a small strip and their Fourier coefficients in \(M\) decay exponentially; \(|e^{-\gamma}|\) is uniformly smaller than one and controls \(N\). Alternatively, on the smaller contours the geometric sums themselves are absolutely and uniformly convergent. Summing first in \(N\), and then summing the absolutely convergent Fourier series in \(M\), imposes \(\sum\phi_j=0\) and recovers exactly the BG integral (3.4). The identity theorem extends (A.1) to \(D\).

No interchange with an infinite sum over \(n\) is required here. The full physical identity (3.5) is independently supplied by BG; the exterior normal convergence of that sum was proved in the main report.

**Normalization warning.** TW's displayed origin-separated contour coefficient is not used for the scalar normalization of (A.1). In particular, the factor printed as \((2\pi i)^{-n}\) on TW PDF p. 3 is not silently substituted for the explicitly normalized \(2n\) contour measures here. The divisor structure and local regularity argument are insensitive to such a fixed nonzero scalar. This run does not need to adjudicate a correction to that display.

## B. What the TW localization proof gives for this numerator

The singular factors in (A.1) are the same ones treated by TW PDF pp. 3–8:

\[
 (1-Z)^{-1},\ (1-T)^{-1},\
 (1-z_jz_k)^{-1},\ (1-t_jt_k)^{-1},\ D(z_j,t_j;s)^{-1}.
\tag{B.1}
\]

The remaining numerator, including \((1+Z)(1+T)/(ZT)\) and the two Vandermondes, is smooth on a neighborhood of the torus. The estimates in TW Lemma 3 use only bounded derivatives of this smooth numerator. They therefore apply to (A.1), not just to the numerator of the origin-separated coefficient.

For clarity, the part of the local criterion needed here is described explicitly. At a torus point, let

\[
 \alpha_j=\Im z_j^0,\qquad \beta_j=\Im t_j^0.
\]

Near an upper-semicircle parameter, the singular factors lead to nonnegative combinations of the vectors

\[
 X=\sum_j e_j,\quad Y=\sum_j f_j,\quad
 X_{jk}=e_j+e_k,\quad Y_{jk}=f_j+f_k,\quad
 Z_j=\alpha_j e_j+\beta_j f_j,
\tag{B.2}
\]

where \(e_j,f_j\) are the coordinate vectors of the two angle spaces. A vector is present only when its corresponding denominator in (B.1) vanishes in the limiting configuration. For \(Z_j\), the condition is

\[
 \Re z_j^0+\Re t_j^0=2\Re\zeta.
\tag{B.3}
\]

If zero is not in the convex hull of the present vectors, compactness gives a positive lower bound for the length of their nonnegative combinations, relative to the sum of the coefficients. This lower bound persists under small perturbations. The Laplace-integral representations of the singular denominators then have a phase with this nonzero gradient. Repeated integration by parts gives arbitrarily many inverse powers of the auxiliary radial variable. A fixed number of derivatives in \(s\) adds only a fixed polynomial factor and can be handled by further integrations by parts. This is the proof of TW Lemmas 2–3 and Appendix B. It yields bounds for every fixed derivative order, uniform as the contours tend to the torus from the permitted side.

The resulting local conclusion does not require the global assumption that \(\zeta\) is outside the Nickel set. It only requires that **the particular local configuration** have no positive convex dependence. This is an immediate local version of the same proof. A finite partition of unity then gives a \(C^\infty\) contribution from any compact set of such configurations. No uniformity in dimension is part of this statement.

## C. Classification of the possible stationary configurations

For completeness, specialize the geometric proof in TW Lemma 1 rather than treating a necessary Landau equation as sufficient.

Assume \(\zeta\ne\pm1,\pm i\), so no singular \(Z_j\) is the zero vector. A nontrivial nonnegative relation among (B.2) must contain some \(Z_j\), because every other vector has nonnegative coordinates and a positive coordinate.

If \(X_{jk}\) occurs, canceling its two positive coordinates requires \(\alpha_j,\alpha_k<0\). But the presence of this vector means \(z_j^0z_k^0=1\), which implies \(\alpha_j+\alpha_k=0\). This is impossible. Thus no \(X_{jk}\) occurs in the relation; similarly no \(Y_{jk}\) does.

At least one of \(X,Y\) must occur. Suppose it is \(X\). Then all \(Z_j\) occur and every \(\alpha_j<0\).

If \(Y\) also occurs, every \(\beta_j<0\) and the ratios \(\alpha_j/\beta_j\) are equal. These ratios determine each pair uniquely under (B.3) when \(C=2\Re\zeta\ne0\). To check the monotonicity explicitly, put \(a=\Re z\), \(b=C-a=\Re t\), with both points on the lower semicircle. The squared ratio is

\[
 \frac{1-a^2}{1-b^2},\qquad
 \frac{d}{da}\log\frac{1-a^2}{1-b^2}
 =-\frac{2C(1-ab)}{(1-a^2)(1-b^2)},
\]

which has a strict sign. Thus all \(z_j^0\) are equal and all \(t_j^0\) are equal. The occurrence of \(X,Y\) requires \(Z=T=1\), making these values \(n\)-th roots of unity.

If \(Y\) does not occur, all \(\beta_j=0\), so all \(t_j^0=\pm1\). The sign of \(\Re\zeta\ne0\) makes these signs the same. Then (B.3) and \(\alpha_j<0\) make all \(z_j^0\) equal to an \(n\)-th root. For even \(n\), both possible values \(\pm1\) are also \(n\)-th roots. The case starting with \(Y\) is symmetric.

It follows that outside \(\mathcal N_n\), every configuration is nonstationary in this sense. This proves the fixed-order \(C^\infty\) statement for our full coefficient via Section B.

Now set \(n=2p\), \(\zeta=e^{i\theta}\) as in the main report. Its cyclotomic uniqueness lemma says both cosine values must equal \(\cos\theta\). The cases with one coordinate equal to \(\pm1\) are excluded. The lower-half-plane requirement picks the unique possible stationary point

\[
 z_j^0=t_j^0=e^{-i\theta}\quad\text{for every }j.
\tag{C.1}
\]

Conversely this point has a positive relation in (B.2): equal coefficients on \(X,Y\) are canceled by equal positive coefficients on the \(Z_j\). Thus it is the only local region still requiring analysis. Everywhere outside a small neighborhood of (C.1), all fixed-order derivatives are bounded.

This classification is **for fixed \(n=2p\)**. It is not a uniform classification or estimate for an infinite tail.

## D. Local residue reduction, including the factor of two

All pair denominators \(1-z_jz_k\), \(1-t_jt_k\) are nonzero at (C.1). Also the zeros of each \(D_j\) are simple in its own \(t_j\)-coordinate since \(\sin\theta\ne0\). Thus their local residues are ordinary simple-pole residues, not a formal power-counting substitution.

Write \(s=\zeta e^u\), \(u>0\), and use local complex angles \(z_j=e^{i\phi_j}\), \(t_j=e^{i\psi_j}\), close to \(-\theta\). On the original inside contours, all these angles have imaginary part \(\epsilon>0\), with \(\epsilon\) sufficiently small compared with \(u\). The local \(D_j=0\) root is

\[
 \psi_j=i\gamma(s,\phi_j),\qquad
 \gamma(\zeta, -\theta)=i\theta.
\]

In particular, for real \(v\) small,

\[
 \psi_j(\zeta e^u,-\theta+v)
 =-\theta+2iu-v+\cot\theta\,v^2
    +O(u^2+u|v|+|v|^3).
\tag{D.1}
\]

For \(\Im\phi_j=\epsilon\), its imaginary part is approximately \(2u-\epsilon\), which is above the original \(\psi_j\)-contour if \(\epsilon<u\). Move the local \(\psi_j\)-contour upward by a small fixed amount. The product pole \(T=1\) is not crossed: with all other \(t\)-coordinates inside the unit disk, its solution for the remaining coordinate is outside. Pair poles are absent in this neighborhood. The residue of \(d\psi_j/(2\pi D_j)\) is

\[
 \frac{i}{\sin\psi_j}=\frac1{\sinh\gamma_j}=y_j.
\]

Only the term taking all \(n\) such residues can retain the stationary configuration. The other terms and the local contour-closing faces miss at least one of the required divisors; they are regular by the local argument of Section B, or have denominators bounded away from zero on the displaced part. Thus, modulo a contribution with bounded derivatives of every fixed order, the original integral is the local \(\phi\)-integral of

\[
 \frac1{n!}\left(\prod y_j\right)\prod h_{jk}^2 R(Z)R(P)
            \prod_j\frac{d\phi_j}{2\pi}.
\tag{D.2}
\]

One can implement these local deformations in nested polydiscs. First choose the relative-angle neighborhood, then larger real center and \(\psi\)-intervals so the \(D\)-roots stay away from the latter endpoints. Choose a smooth cutoff in the relative variables equal to one near zero. The shell where this cutoff changes misses (C.1), and is treated by Section B. The center endpoints can be chosen farther from zero than a constant times the square of the relative-angle radius; neither center pole is then at an endpoint. This makes the local closing faces regular and avoids interpreting a nonholomorphic cutoff as a holomorphic contour amplitude.

Now write

\[
 \phi_j=-\theta+v_j+\frac{t}{n},\qquad
 \sum_jv_j=0.
\]

Using \(v_1,\ldots,v_{n-1},t\) as coordinates has Jacobian one. Initially \(v_j\) are real and \(\Im t=n\epsilon\). Because \(n\theta\) is a multiple of \(2\pi\), \(Z=e^{it}\). The factor \(R(Z)\) has residue \(2i\) at \(t=0\). The competing pole of \(R(P)\) is locally above the original center contour:

\[
 1-P=2nu+it-i\cot\theta\,Q(v)+\cdots,
\]

so its root is approximately \(t=2inu+\cot\theta Q\). Move the center contour downward to a small fixed negative imaginary part. Crossing the \(R(Z)\)-pole gives

\[
 -i\operatorname{Res}_{t=0}R(e^{it})=2
\]

for the normalized measure \(dt/(2\pi)\); the sign is from the downward contour displacement. At the residue, \(t=0\), all angles are real and satisfy the BG constraint. On the displaced center contour both center denominators are bounded away from zero for sufficiently small \(u\); its contribution is analytic. The relative-angle shell is again a nonstationary contribution.

Therefore the singular part of \(F_n\) is **twice** the localized constrained-angle integral near \(\phi_j=-\theta\). This agrees with the two equal saddles \(\phi_j=\pm\theta\) visible in the BG representation.

As an elementary sign check, the linearized center integral is exactly

\[
 \int_{\mathbb R}\frac{4\,dt}{2\pi(\delta-it)
              (2nu-\delta+it-icQ)}
 =\frac4{2nu-icQ},\qquad 0<\delta<2nu.
\tag{D.3}
\]

The single BG saddle has \(2/(2nu-icQ)\), hence the factor two. This check does not replace the preceding localization; it verifies its scalar and orientation.

## E. The local coefficient, with convergence of the differentiated integral

Use the single constrained saddle \(\phi_j=-\theta+v_j\), \(\sum v_j=0\). The implicit equation

\[
 \cosh\gamma=s+s^{-1}-\cos\phi
\]

gives at \(u=v=0\)

\[
 \gamma=i\theta,\quad \partial_u\gamma=2,\quad
 \partial_v\gamma=i,\quad \partial_v^2\gamma=-2i\cot\theta.
\]

This proves (7.3). Put \(g(u,v)=1-P\). For a fixed sufficiently small neighborhood,

\[
 g(u,v)=a u-icQ(v)+O(u^2+u|v|+|v|^3),\quad a=2n>0,\ c=\cot\theta\ne0,
\]

\[
 |g(u,v)|\ge C_{n,\theta}(u+Q(v)),\qquad u\ge0.
\tag{E.1}
\]

Indeed the real and imaginary parts of the leading terms control \(u\) and \(Q\), while the remainder is arbitrarily small relative to \(u+Q\) after choosing the neighborhood sufficiently small. The constants in (E.1) depend on \(n,\theta\).

The numerator has an exact factor \(\Delta(v)^2\) times an analytic function: each sine difference has a simple zero on its coincidence hyperplane, while the pair denominators are nonzero. At the origin,

\[
 y_j\longrightarrow\frac1{i\sin\theta},\qquad
 h_{jk}\sim\frac{v_j-v_k}{2i\sin\theta}.
\]

The total phase is

\[
 (-i)^n(-1)^{n(n-1)/2}=(-1)^{n^2/2}=1
\]

for even \(n\). The leading amplitude is therefore the positive number \(B_n\) in (7.4). Since \(R(P)=2/g-1\), the local singular part can be written

\[
 L_n(u)=\int\chi(v)\Delta(v)^2\frac{2B(u,v)}{g(u,v)}\,dv,
 \qquad B(0,0)=B_n,
\tag{E.2}
\]

where \(\chi\) equals one near zero and has sufficiently small compact support. The omitted \(-1\) part is regular.

Set \(k=n^2/2-1\), \(\nu=(n^2-1)/2\). In the \(k\)-th derivative of (E.2), the unique term with denominator power \(k+1\) is

\[
 2(-1)^k k!\int\chi(v)\Delta(v)^2
 \frac{B(u,v)(\partial_u g(u,v))^k}{g(u,v)^{k+1}}\,dv.
\tag{E.3}
\]

Every other term has denominator power at most \(k\), multiplied by bounded analytic derivatives for this fixed \(n,k\). Such terms are bounded in absolute value by a constant times

\[
 \int_{|v|<b}\frac{|\Delta(v)|^2}{(u+Q(v))^k}\,dv.
\]

In polar coordinates its large-relative-to-\(\sqrt u\) radial exponent is \(n^2-2-2k=0\), so this integral stays bounded as \(u\downarrow0\). Contributions from the cutoff shell are regular as well.

For (E.3), set \(v=\sqrt u\,t\). The total measure-and-Vandermonde degree is \(n^2-1\). Multiplication by \(u^{1/2}\) removes exactly the remaining negative power of \(u\). Equation (E.1) gives the integrable majorant

\[
 C\frac{|\Delta(t)|^2}{(1+Q(t))^{k+1}}.
\]

Its radial power at infinity is \(-2\). Dominated convergence therefore yields

\[
 \lim_{u\downarrow0}u^{1/2}L_n^{(k)}(u)
 =2B_n(-1)^k k!a^k
  \int_{\mathbb R^{n-1}}
       \frac{\Delta(t)^2}{(a-icQ(t))^{k+1}}\,dt.
\tag{E.4}
\]

The angular integral is \(J_n>0\). With \(\nu=k+1/2\), the radial beta evaluation gives

\[
 \int_0^\infty\frac{r^{2\nu-1}}{(a-icr^2)^{k+1}}\,dr
 =\frac12a^{-1/2}(-ic)^{-\nu}
       \frac{\Gamma(\nu)\Gamma(1/2)}{\Gamma(k+1)}.
\]

One may first prove the beta identity with a positive real quadratic coefficient and then continue that coefficient to \(-ic\). Throughout that continuation, avoid the negative real axis; the denominator has no positive-real \(r\) zero and the integral is dominated uniformly in a neighborhood of the final coefficient. Thus the continuation and the displayed branch are justified, not an oscillatory-integral guess.

Combining with (E.4) yields exactly \(C_{n,\theta}\) in (7.6). It cannot be zero: \(B_n,J_n,a,\Gamma(\nu),\Gamma(1/2)\) are positive, \(c\ne0\), and the complex power is nonzero. The global local-residue factor from Section D is two, giving (7.8). Derivatives of lower order are bounded by the same radial estimates. Complex conjugation gives the corresponding fixed-order obstruction on the lower semicircle.

The exponent \((n^2-3)/2=k-1/2\) agrees with the circle power count in BG Appendix E, but here nonvanishing of the coefficient and convergence of the decisive differentiated local integral are checked separately.

## F. Quantitative arithmetic beyond the first index

The prime-index lemma can be strengthened to a separation bound for nonresonant indices. For \(p\nmid n\), define

\[
 \lambda=2(\zeta_p^a+\zeta_p^{-a})
        -(\zeta_n^j+\zeta_n^{-j}+\zeta_n^k+\zeta_n^{-k}).
\]

It is a nonzero algebraic integer in \(K=\mathbb Q(\zeta_{pn})\), of degree \(d=(p-1)\varphi(n)\). Its field norm is a nonzero rational integer. Every conjugate has modulus at most eight, so

\[
 1\le|N_{K/\mathbb Q}\lambda|
 \le |\lambda|8^{d-1}.
\]

Since \(\lambda=4[\cos\theta-(\cos(2\pi j/n)+\cos(2\pi k/n))/2]\), this proves (9.2). For \(p\mid n\), the same estimate with \(d=\varphi(n)\) applies whenever the particular pair is not an exact equality. This uses only an elementary algebraic-integer norm, not a remembered specialized Diophantine theorem about Ising singularities.

This bound is exponential in a quantity growing with \(n\). It does not bound the local convex-hull constants, partition derivatives, or differentiated integrals in the sum. No convergence of a boundary derivative series is inferred from it.

## G. What this reconstruction does and does not conclude

The fixed-order calculation gives a dense set of singularities among the **individual** \(F_n\), with a first even index \(2p\) and a nonzero coefficient for the indicated derivative. The local proof uses compactness only after \(n\) is fixed. Its contour widths, derivative estimates, and positive angular integrals are not controlled uniformly in \(n\).

For the full object one must still bound

\[
 u^{1/2}\frac{d^{2p^2-1}}{du^{2p^2-1}}
       \sum_{n>2p,\ n\text{ even}}F_n(\zeta e^u)
\]

as \(u\downarrow0\), or supply some other noncancellation argument. The task cannot be marked proved by replacing this expression with the sum of its fixed-term limits. Normal convergence on compact subsets of \(|s|>1\) does not justify that replacement. This is the precise unresolved step retained in the frozen result.
