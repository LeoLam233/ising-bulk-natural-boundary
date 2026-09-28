# From an equal-angle saddle to a finite-particle singularity

Run: `ISING-CR0-20260927-27b6b643611a`.

**Scope.** This is a fixed-particle argument, not a proof of a natural boundary for the infinite susceptibility. The final infinite-tail estimate is stated, not proved. The physical normalization and exterior convergence used here are established in `RESULT.md`. All page numbers below refer to the supplied PDFs; their printed page numbers agree at the cited locations.

## 1. Notation and the assertion proved here

For even particle number \(n\ge2\), let \(A_n\) be exactly the integral denoted \(\widetilde\chi^{(n)}\) in BG2008v1, equations (5)–(9), pp. 2–3. Write

\[
a=s+s^{-1},\quad Z(\phi,s)=a-\cos\phi,
\quad q+q^{-1}=2Z,\quad |q|<1,
\quad y=\frac{2q}{1-q^2}.
\]

The branch is the one specified in `RESULT.md`. Define the square of the pair factor without a square-root ambiguity by

\[
h_{ij}^2=
\frac{4\sin^2((\phi_i-\phi_j)/2)q_iq_j}{(1-q_iq_j)^2}.
\]

Thus

\[
A_n(s)=\frac1{n!}\int_{\mathbb T^{n-1}}
 \Bigl(\prod_i y_i\Bigr)
 \Bigl(\prod_{i<j}h_{ij}^2\Bigr)
 \frac{1+\prod_iq_i}{1-\prod_iq_i}\,
 \prod_{i=1}^{n-1}\frac{d\phi_i}{2\pi},
\qquad \phi_n=-\sum_{i<n}\phi_i\pmod{2\pi}.
\tag{1}
\]

Let \(p\ge7\) be prime and let \(\zeta=e^{2\pi i j/p}\), \(1\le j<p\). Put

\[
N=2p,\qquad k=N^2/2-1,\qquad P_N=\sum_{\substack{2\le n\le N\\n\text{ even}}}A_n.
\]

The claim of this appendix is

\[
\lim_{\epsilon\downarrow0}\sqrt\epsilon\,
 \frac{d^k}{d\epsilon^k}P_N((1+\epsilon)\zeta)
 =C_{p,j}\ne0.
\tag{2}
\]

This proves that these finite partial sums do not extend holomorphically at the indicated points. It does **not** interchange a boundary limit with the infinite particle sum. The proof uses the local nonstationary estimate in TW2014v1, Sect. III, pp. 4–8, as a supplied analytical result. Its application to cutoffs is spelled out below.

## 2. An arithmetic selection of boundary points

The fixed-order Nickel candidate set in TW2014v1, p. 3, is

\[
\mathcal N_n=\left\{z\in\mathbb T:
 2\Re z=\cos(2\pi u/n)+\cos(2\pi v/n)
 \text{ for some }u,v\right\}.
\tag{3}
\]

If \(p\nmid n\), the equality in (3) cannot hold for \(z=\zeta\). Indeed, its right side is in \(\mathbb Q(\xi_n)\), whereas its left side is \(\xi_p^j+\xi_p^{-j}\). In \(\mathbb Q(\xi_{np})\), the Chinese remainder theorem supplies an automorphism fixing \(\xi_n\) and sending \(\xi_p\) to \(\xi_p^2\). The equality would force

\[
\cos(2\pi j/p)=\cos(4\pi j/p),
\]

which is impossible for prime \(p\ge7\) and \(j\not\equiv0\pmod p\). Here we used only the usual automorphisms of a cyclotomic field, obtained by raising roots to powers coprime to their order. Consequently the first possible **even** order is \(N=2p\), and it is a candidate order by taking the two real parts in (3) equal to \(\Re\zeta\).

There is a useful uniqueness statement at this order. Every \(2p\)-th root is \(\pm\xi_p^r\). If two such roots have real parts with sum \(2\Re\zeta\), then both real parts equal \(\Re\zeta\). To prove it, multiply the real-part relation by two and express it as

\[
\varepsilon_1(\xi_p^{r_1}+\xi_p^{-r_1})+
\varepsilon_2(\xi_p^{r_2}+\xi_p^{-r_2})-
2(\xi_p^j+\xi_p^{-j})=0,
\qquad \varepsilon_i\in\{-1,1\}.
\]

Reduce exponents modulo \(p\). The resulting polynomial of degree at most \(p-1\) has at most six nonzero coefficient positions. Since \(p\ge7\), at least one position is zero. The only rational relation between \(1,\xi_p,\ldots,\xi_p^{p-1}\) is a multiple of \(1+z+\cdots+z^{p-1}\). All coefficients must therefore vanish individually. The coefficients at \(j\) and \(-j\) then force both positive pairs to be the same pair \(\{j,-j\}\). This proves the assertion.

The union of the nontrivial prime-order roots for \(p\ge7\) is dense in the circle: there are arbitrarily large primes, and the angular mesh of the \(p\)-th roots is \(2\pi/p\). Removing the root 1 does not change this density.

## 3. A normalized cutoff/residue bridge

This section relates (1) to the **shape** of the contour integrand to which the TW nonstationary proof applies. It does not identify different source particle normalizations by name alone.

For \(x_i=e^{i\phi_i}\), set

\[
S_n(\phi;s)=\prod_i y_i\prod_{i<j}h_{ij}^2.
\]

Let \(\psi\) be a smooth function on the full \(n\)-torus with
\(\psi(-\phi)=\psi(\phi)\). Define

\[
c_n^\psi(M,L;s)=\frac1{n!}
 \int_{\mathbb T^n}\psi(\phi)S_n(\phi;s)
 e^{iM\sum_i\phi_i}\Bigl(\prod_iq_i\Bigr)^L
 \prod_i\frac{d\phi_i}{2\pi},\qquad L\ge0.
\tag{4}
\]

The simultaneous reflection of all angles gives
\(c_n^\psi(-M,L)=c_n^\psi(M,L)\). Define negative \(L\) by reflection. For fixed \(s\) in the exterior, the angle integrand is smooth, all \(|q_i|\) have a common bound less than one, and repeated integration by parts in one angle bounds Fourier coefficients by

\[
|c_n^\psi(M,L;s)|\le C_{n,b,s}(1+|M|)^{-b}(1+L)^b\rho^{nL},
\quad \rho<1,
\tag{5}
\]

with any fixed integer \(b\). Bounds are uniform for \(s\) on an exterior compact set. Hence the double sum over \(M,L\) is absolutely convergent when \(b>1\). Fourier inversion in the total-angle variable, followed by the geometric sum in \(L\), gives precisely the cutoff version of (1):

\[
A_n[\psi]=\sum_{M,L\in\mathbb Z}c_n^\psi(M,|L|;s),
\qquad O_n[\psi]=c_n^\psi(0,0;s).
\tag{6}
\]

Here \(A_n[\psi]\) means insertion of \(\psi\) restricted to the constraint torus in (1).

For completeness, use **one normalized measure per contour variable**:
\(d\nu(x)=dx/(2\pi i x)\). Set

\[
D(x,y;s)=a-\tfrac12(x+x^{-1})-\tfrac12(y+y^{-1}),
\]

\[
\mathcal P(x,y)=\prod_{i<j}
 \frac{x_i-x_j}{1-x_ix_j}\frac{y_i-y_j}{1-y_iy_j},
\quad X_* =\prod_i x_i,\quad Y_* =\prod_i y_i.
\]

For radius \(r<1\) sufficiently close to one (depending on an exterior compact set), define

\[
\begin{split}
O_{n,r}[\psi]&=\frac1{n!}\int_{C_r^{2n}}
 \psi(\arg x)\,\mathcal P(x,y)
 \prod_i\frac{d\nu(x_i)d\nu(y_i)}{D(x_i,y_i;s)},\\
U_{n,r}[\psi]&=\frac1{n!}\int_{C_r^{2n}}
 \psi(\arg x)\,\mathcal P(x,y)
 \frac{X_*+Y_*}{(1-X_*)(1-Y_*)}
 \prod_i\frac{d\nu(x_i)d\nu(y_i)}{D(x_i,y_i;s)}.
\end{split}
\tag{7}
\]

These integrals use the ordinary contour orientation. The apparent pair denominators in the residue-reduced expression have removable zeros. Explicitly, writing \(q_i=q(x_i;s)\), subtraction of the two equations defining \(q_i\) gives

\[
\frac{q_i-q_j}{1-q_iq_j}\frac{x_i-x_j}{1-x_ix_j}
=-\frac{(x_i-x_j)^2}{x_ix_j}
 \frac{q_iq_j}{(1-q_iq_j)^2}=h_{ij}^2.
\tag{8}
\]

The root \(q(x;s)\) is analytic in an annulus about the unit \(x\)-circle for fixed exterior \(s\), and \(|q|<r\) when \(r\) is sufficiently close to one. The identity

\[
yD(x,y;s)=-\tfrac12(y-q(x;s))(y-q(x;s)^{-1})
\]

shows that the residue of \(dy/(yD)\) at \(y=q\) is \(1/\sinh\gamma=2q/(1-q^2)\). Pair poles and product poles are outside the \(y\)-contours; the point \(y=0\) is removable for nonnegative spatial powers. Thus taking the \(n\) residues produces (4) on the slightly displaced \(x\)-contours, with the asserted normalized measures.

The elementary identity

\[
\frac4{(1-X_*)(1-Y_*)}-\frac2{1-X_*}-\frac2{1-Y_*}
=2\frac{X_*+Y_*}{(1-X_*)(1-Y_*)}
\tag{9}
\]

is the spatial summation of all sites except the origin, using the two reflections. For \(\psi\) not analytic in its angle arguments, contour deformation of \(\psi\) is **not** being asserted. Instead take \(r\uparrow1\). After residues, the same Fourier estimate (5), now uniformly for \(r\) close to one, follows by differentiating the smooth angle amplitude: factors \(r^{nM}\) are at most one for \(M\ge0\), and derivatives of the remaining \(q^L\) give only polynomial factors in \(L\). This justifies the Abel limit of the quadrant sums, uniformly on exterior compact sets. It proves

\[
O_n[\psi]=\lim_{r\uparrow1}O_{n,r}[\psi],\qquad
A_n[\psi]=O_n[\psi]+2\lim_{r\uparrow1}U_{n,r}[\psi].
\tag{10}
\]

Uniformity on exterior compact sets also permits holomorphic differentiation before these limits.

**Source-normalization caution.** The supplied TW2014v1 p. 3 prints a factor \((2\pi i)^{-n}\) with \(2n\) contour variables, and its Appendix A p. 10 contains another displayed contour prefactor. There is an apparent scalar-normalization ambiguity if all those displays are read as ordinary unnormalized contour integrals. Equation (7) above is normalized independently by the explicit residue calculation, and BG (4)–(9) is the normalization of the physical quantity throughout this run. Only the fixed-order contour **shape and local estimates** from TW are used below; they are unchanged by a nonzero scalar depending on \(n\). This observation is not a disproof of the physical target or an input-integrity failure.

## 4. The imported local estimate and its precise application

The local mechanism in TW2014v1 Sect. III, Lemmas 1–3, pp. 4–8, and Appendix B, pp. 10–11, is the following. At a limiting torus point the potentially singular denominators in (7) have normal vectors

\[
X=(1,\ldots,1;0,\ldots,0),\quad
Y=(0,\ldots,0;1,\ldots,1),
\]

\[
X_{ij}=e_i+e_j,\quad Y_{ij}=e_{n+i}+e_{n+j},\quad
Z_i=\alpha_i e_i+\beta_i e_{n+i},
\quad \alpha_i=\Im x_i,\quad\beta_i=\Im y_i.
\tag{11}
\]

A vector is included only when its denominator can become singular. In particular,
\(X\) requires \(X_*=1\), \(X_{ij}\) requires \(x_ix_j=1\), and \(Z_i\) requires
\(\Re x_i+\Re y_i=2\Re\zeta\). The sign convention in (11) is for an upper-half-circle \(\zeta\) approached from the exterior.

If zero is not in the convex hull of these vectors on a compactly supported local patch, the exponential-denominator representation and integration by parts in that proof bound the localized integral and **each fixed derivative in \(s\)** uniformly as \(s\) approaches \(\zeta\), with \(r\) sufficiently close to one. This conclusion depends on the local cone condition, not on a global name for \(\zeta\). It therefore also applies away from the exceptional patches when \(\zeta\) is a Nickel point. Its constants depend on \(n\), the patch, and derivative order. No bound uniform in \(n\) is imported.

Here is the cone classification needed for the present application. Suppose a nontrivial nonnegative combination of the vectors in (11) is zero. If an \(X_{ij}\) has positive coefficient, cancellation of its two positive components forces both \(\alpha_i,\alpha_j<0\), contradicting \(x_ix_j=1\) and hence \(\alpha_i+\alpha_j=0\). The same excludes every \(Y_{ij}\). Some \(Z_i\) must occur, and then \(X\) or \(Y\) must occur because \((\alpha_i,\beta_i)\ne(0,0)\) away from \(\zeta=\pm1,\pm i\).

If both \(X,Y\) occur, all \(\alpha_i,\beta_i<0\), and cancellation forces a common ratio \(\alpha_i/\beta_i\). With \(c=\Re\zeta\ne0\), set \(u=\Re x\), \(v=2c-u=\Re y\). The logarithmic derivative of the positive ratio is

\[
\frac d{du}\log\frac{\sqrt{1-u^2}}{\sqrt{1-v^2}}
=-\frac{2c(1-uv)}{(1-u^2)(1-v^2)}\ne0.
\tag{12}
\]

The allowed interval is connected, so the ratio fixes \(u,v\). All the \(x_i\) equal one root and all the \(y_i\) equal one root; the product constraints make them \(n\)-th roots of unity. If only \(X\) occurs, all \(y_i=1\) or all \(y_i=-1\), and all \(x_i\) again equal an \(n\)-th root; for even \(n\), the common \(y\) is also an \(n\)-th root. The case with only \(Y\) is symmetric. This reproduces the part of TW Lemma 1 needed here, with the elementary monotonicity calculation made explicit.

For the origin integral in (7), the vectors \(X,Y\) are absent. The preceding argument then excludes a zero cone **everywhere** when \(\zeta\notin\{\pm1,\pm i\}\). Consequently \(O_n[\psi]\) and every fixed derivative are bounded at any such \(\zeta\), for any smooth cutoff.

For even \(n<N=2p\), Section 2 excludes every Nickel configuration. Thus (10) and the local estimate show that \(A_n\) and every fixed derivative are bounded at \(\zeta\).

For \(n=N\), write \(\zeta=e^{i\theta}\), \(0<\theta<\pi\). Section 2's uniqueness result, together with the negative imaginary parts in the cone classification, shows that the **only** zero-cone tuple is

\[
x_1=\cdots=x_N=y_1=\cdots=y_N=e^{-i\theta}.
\tag{13}
\]

Choose smooth angle cutoffs \(\psi_+\) and \(\psi_-\), each equal to one on a smaller neighborhood of the tuple with every angle \(+\theta\) or every angle \(-\theta\), respectively. Their supports can be disjoint; take \(\psi_-(\phi)=\psi_+(-\phi)\). Then
\(\psi_0=1-\psi_+-\psi_-\) is even and vanishes in a full neighborhood of (13) in the \(x\)-coordinates. A finite partition of its support has no zero cone. Therefore

\[
A_N[\psi_0]=A_N-A_N[\psi_+]-A_N[\psi_-]
\tag{14}
\]

has bounded derivatives of every fixed order at \(\zeta\). This is the global fixed-order remainder control, and is why an isolated local calculation alone is not being promoted to a full-integral singularity without a justification.

## 5. The local derivative computation

The following calculation works for any even \(n\) and angle \(0<\theta<\pi\) with \(n\theta\in2\pi\mathbb Z\) and \(\cos\theta\ne0\). Let

\[
t=\sin\theta>0,\quad c=\cos\theta,\quad
s=(1+\epsilon)e^{i\theta},\quad
\phi_i=\theta+u_i,\quad u_n=-\sum_{i<n}u_i,
\]

\[
Q(u)=\sum_{i=1}^n u_i^2,\qquad
\Delta(u)=\prod_{i<j}(u_i-u_j),\qquad b=\frac c{2t}.
\]

There is a local analytic \(\gamma=-\log q\) with \(\gamma(0,0)=i\theta\). Implicit differentiation of \(\cosh\gamma=a-\cos\phi\) gives

\[
\gamma_\epsilon=2,\qquad \gamma_u=-i,\qquad
\gamma_{uu}=-2i\cot\theta
\quad\text{at }(\epsilon,u)=(0,0).
\tag{15}
\]

Consequently, after imposing \(\sum_i u_i=0\),

\[
L:=\sum_i\gamma_i-in\theta
=2n\epsilon-i\cot\theta Q(u)
+O(\epsilon^2+\epsilon|u|+|u|^3),
\qquad R_n=\coth(L/2).
\tag{16}
\]

The remaining numerator has the exact factorization

\[
S_n(\phi;s)=\Delta(u)^2 B(\epsilon,u),
\qquad
B(0,0)=B_0=\frac1{2^{n(n-1)}t^{n^2}}>0.
\tag{17}
\]

In (17), \(B\) is analytic near the origin. The positivity of its value is worth checking: \(y_i\to-i/t\), while \(h_{ij}\sim(u_i-u_j)/(2it)\). For even \(n\), the phases \((-i)^n\) and \((-1)^{n(n-1)/2}\) multiply to \(+1\).

The radial parameter \(\epsilon>0\) is on the exterior side. For a sufficiently small fixed real-angle patch,

\[
|L(\epsilon,u)|\ge c_0(\epsilon+Q(u)),\quad c_0>0.
\tag{18}
\]

To justify (18), at \(\epsilon=0\) the local energies are purely imaginary and the first nonzero constrained imaginary part in (16) is a nonzero definite quadratic form. Also \(\partial_\epsilon\Re\gamma\) is positive uniformly near each saddle angle, as follows from (15) and continuity. Thus \(\Re L\ge c_1\epsilon\); the imaginary part controls \(Q\) when \(Q\) dominates \(\epsilon\), with the higher-order terms absorbed by shrinking the patch. These two regions give (18).

Let \(I_{n,+}=A_n[\psi_+]\). Put
\(k=n^2/2-1\), \(\ell=(n^2-1)/2\). Differentiate \(k\) times at \(\epsilon>0\), then set \(u=\sqrt\epsilon v\). The highest pole term comes from differentiating \(1/(L/2)\) each time; all other terms vanish after the indicated normalization. The result is

\[
\lim_{\epsilon\downarrow0}\sqrt\epsilon\,
\frac{d^k I_{n,+}}{d\epsilon^k}
=\frac{(-1)^k k!n^k B_0}{n!(2\pi)^{n-1}}\,J_{n,\theta},
\tag{19}
\]

\[
J_{n,\theta}=\int_{\mathbb R^{n-1}}
\frac{\Delta(v)^2}{(n-ibQ(v))^{k+1}}\,dv.
\tag{20}
\]

Here no unproved exchange at infinity is needed. Equation (18), the exact Vandermonde factor in (17), and bounded fixed derivatives of the analytic factors give, after scaling, a constant multiple of

\[
\frac{\Delta(v)^2}{(1+Q(v))^{k+1}}
\]

as a dominating integrable function. The dimension is \(n-1\), the Vandermonde degree is \(n(n-1)\), and \(2(k+1)=n^2\); the radial integral at infinity therefore decays as \(\int^\infty r^{-2}\,dr\). At zero it is integrable as well. More explicitly, a term with a lower pole power \(j+1\le k+1\) can be put under the same majorant by using \((\epsilon+Q(u))^{k-j}\le C\) on the fixed patch; after scaling its extra factor tends to zero pointwise when \(j<k\). Analytic (nonpole) terms are handled in the same way. Dominated convergence proves (19).

## 6. Nonzero amplitude and addition of the two saddles

Define the positive finite Gaussian integral

\[
Z_n=\int_{\mathbb R^{n-1}}e^{-Q(v)}\Delta(v)^2\,dv>0.
\]

Ellipsoidal polar coordinates and the beta integral yield

\[
J_{n,\theta}=
Z_n\,n^{-1/2}(-ib)^{-\ell}
\frac{\sqrt\pi}{\Gamma(k+1)}\ne0.
\tag{21}
\]

The power is evaluated with \(\arg(-ib)=\mp\pi/2\) for \(b\gtrless0\). To verify (21), the radial power is \(r^{2\ell-1}\). Substitution \(q=r^2\) gives the beta integral with parameters \(\ell\) and \(1/2\). The formula first holds for a positive coefficient of \(q\) in the denominator and extends analytically to the nonzero imaginary coefficient \(-ib\); there is no pole on the positive integration ray, and the integral is absolutely convergent. All other factors in (21) are nonzero.

The saddle at \(-\theta\) has \(\gamma_u=+i\), but its linear terms again cancel under the angle constraint. It has the same quadratic form, the same \(B_0\), the same measure orientation and the same coefficient (19). Equivalently, simultaneous angle reflection makes the two localized integrals identical. Thus they **add**, rather than cancel.

Combining (14), the bounded lower particle orders, and twice (19) proves (2), with

\[
C_{p,j}=2\frac{(-1)^k k!N^k B_0}{N!(2\pi)^{N-1}}J_{N,\theta}
\ne0
\]

in the upper half-circle. The lower half follows by complex conjugation. A holomorphic extension would have bounded derivatives along this radial approach, contradicting (2).

The implied fractional local power is \((n^2-3)/2=k-1/2\), agreeing with the Case 2 power count in BG2008v1, Appendix E, pp. 52–53. The argument above supplies the nonzero local coefficient and the fixed-order remainder control used here; it does not rely on treating that paper's general power-counting discussion as a theorem about the infinite sum.

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

## 8. The exact remaining step

Let

\[
F=X/(1-s^{-4})^{1/4}=\sum_{n\ge2,\ n\text{ even}}A_n,
\qquad R_N=\sum_{n>N,\ n\text{ even}}A_n.
\]

Both functions are holomorphic in the exterior, and the series can be differentiated on its compact subsets. A sufficient missing estimate, at every selected prime root, is

\[
\boxed{\displaystyle
\sqrt\epsilon\,\frac{d^k}{d\epsilon^k}
R_N((1+\epsilon)\zeta)\longrightarrow0,
\quad N=2p,\quad k=N^2/2-1.}
\tag{T}
\]

Under (T), equation (2) remains nonzero for \(F\). The prefactor is locally analytic and nonvanishing at these roots, so \(X\) cannot extend there. Their density then proves the target natural-boundary statement at every circle point.

**(T) has not been proved in this run.** All applications of TW in this appendix keep the particle number fixed. Their constants and localization neighborhoods are not controlled as \(n\to\infty\). The exterior Hadamard estimate in `RESULT.md` is not a substitute for (T). Therefore the status of the full natural-boundary claim remains `unresolved`.
