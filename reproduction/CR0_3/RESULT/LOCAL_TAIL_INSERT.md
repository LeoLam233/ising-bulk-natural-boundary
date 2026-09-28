## 7. A uniformly controlled part of the higher-particle tail

There is a genuine, but restricted, tail bound available from the same local analysis. Fix a prime root \(\zeta=e^{i\theta}\), \(N=2p\), and the **fixed** derivative order \(k=N^2/2-1\). For each higher resonant sector \(n=mN\), \(m\ge2\), take just the neighborhood of the equal-angle saddle with

\[
\phi_i=\theta+u_i,\quad \sum_i u_i=0,\quad Q(u)\le\delta^2.
\]

Insert a smooth cutoff between zero and one, equal to one on \(Q\le\delta^2/2\) and supported in \(Q\le\delta^2\). Denote this localized integral by \(I_{n,\delta}\). A corresponding estimate holds at \(-\theta\).

**Restricted tail lemma.** There exist \(\delta>0\), \(\epsilon_0>0\), \(0<\rho<1\), and a constant \(C_k\), depending on the fixed root and derivative order but not on \(n\), such that

\[
\sup_{0<\epsilon<\epsilon_0}
\left|\frac{d^k}{d\epsilon^k}I_{n,\delta}((1+\epsilon)\zeta)\right|
\le C_k\frac{n^{2k}}{n!}\rho^{n^2},\qquad n=mN,\ m\ge2.
\tag{22}
\]

The notation means radial differentiation of the localized integral, with its angular cutoff held fixed. Therefore this selected sum of higher-order local neighborhoods has a uniformly bounded \(k\)-th derivative and cannot cancel (2).

Here are the uniformity details. Choose an initial fixed angular neighborhood and an exterior radial interval so small that each local \(q\), \(y\), and pair denominator is analytic and bounded away from its inappropriate branch points or zeros. The exact factorization (17) then gives, for \(0\le j\le k\),

\[
|\partial_\epsilon^j B_n(\epsilon,u)|
\le C_k n^{2j} C_0^{n^2},
\tag{23}
\]

for a fixed \(C_0\ge1\). To see this, factor out each \((u_i-u_j)^2\); the remaining pair factor and its reciprocal are bounded on a fixed small neighborhood, as are the single-variable factors. Logarithmic differentiation involves at most a constant times \(n^2\) factors. Repeated differentiation a fixed number \(j\) of times proves (23). First choose this neighborhood and \(C_0\), and only afterwards decrease \(\delta\); thus the later choice of \(\delta\) is not circular.

For the product denominator, write \(L_n=\sum_i\gamma_i-in\theta\). Uniformly on these patches,
\(\Re L_n\ge c n\epsilon\). At \(\epsilon=0\),
\(\Im L_n=-\cot\theta Q+O(\delta Q)\). Also the derivative \(\partial_\epsilon\gamma(0,u)\) is real for all angles in the patch, so the change of this imaginary part is \(O(n\epsilon^2)\). For \(n\epsilon\) below a sufficiently small fixed constant, these facts give

\[
|1-e^{-L_n}|\ge c'(n\epsilon+Q),
\]

by the same two-region argument as (18), keeping \(|\Im L_n|\) away from a nonzero multiple of \(2\pi\). For larger \(n\epsilon\), the bound \(\Re L_n\ge c n\epsilon\) instead keeps the product denominator away from zero. Since each fixed derivative of \(L_n\) is \(O(n)\), both regimes imply

\[
|\partial_\epsilon^j R_n|\le C_j n^j(1+Q^{-j-1})
\quad(Q>0,\ 0\le j\le k).
\tag{24}
\]

The singular bound at \(Q=0\) is only an integrable majorant, not a claim that \(R_n\) is infinite there for positive \(\epsilon\).

Combine (23) and (24) by Leibniz's rule. Put \(\nu=n(n-1)\). On \(Q\le\delta^2<1\),
\(|\Delta(u)|^2\le2^\nu Q^{\nu/2}\). For the higher sectors in question, \(\nu/2\ge k+1\). The domain is contained in a box of volume at most \((2\delta)^{n-1}\) in the independent \(u\)-coordinates. It follows that

\[
\int_{Q\le\delta^2}\Delta(u)^2(1+Q^{-k-1})\,du
\le 2^{n^2}\delta^{n^2-3-2k}.
\tag{25}
\]

Together with the normalization \(1/[n!(2\pi)^{n-1}]\), this gives (22) after choosing \(\delta\) so that \(2C_0\delta<1\) and absorbing the fixed factor \(\delta^{-3-2k}\) into \(C_k\).

**What (22) omits.** These are only small equal-angle neighborhoods in the higher resonant sectors. The complement in each such sector and all other higher particle sectors remain in the full tail. The local lemma does not supply a partition of that complement with summable derivative estimates. In particular, the fixed-order nonstationary constants from TW have not been bounded uniformly across that complement. No conclusion about the entire \(R_N\) follows by discarding it.
