# JOINT common real physical interface

Reviewed 2026-10-23. The independent complex coordinates are doubled couplings
(z,w)=(2 beta Jx,2 beta Jy). The physical input is real only, positive,
noncritical, and uniform over all finite positive lambda=Jy/Jx.

## Exact reviewed primary results

- Bugrij–Lisovyy, arXiv:0708.3643v1, equations (21)–(25), (30)–(32), and
  particularly (35)–(39). The anisotropic finite-cylinder form factors at
  arbitrary separation have anisotropy exponent N^2/2; both phases and the
  low-temperature zero-particle term are explicit. The paper notes their
  infinite-circumference limits. The local reviewed files are the existing
  verified source copies in the preceding ANISO audit, BugrijLisovyy.pdf/txt.
- Iorgov–Lisovyy, arXiv:1012.2856, Theorem 6.1, equations (6.6)–(6.7), and
  Remark 6.2. Theorem 6.1 proves the finite-lattice factorization; its following
  paragraph describes xi_T -> 1, nu -> 0 and continuous momenta. Remark 6.2
  supplies the paramagnetic vacuum/zero-mode change and odd particle parity.
  No joint susceptibility continuation is imported from the remark's analytic
  continuation of finite-lattice matrix elements. Reviewed IorgovLisovyy.pdf/txt
  in the existing ANISO audit source copies.
- Raoufi, arXiv:1710.07608v1, Theorem 1, assumptions C1–C4 on page 3.
  The group Gamma is explicitly an arbitrary vertex-transitive subgroup.
  For unequal positive horizontal/vertical nearest-neighbor couplings take
  translations, not all lattice automorphisms. Nonnegativity, translation
  invariance, nearest-neighbor irreducibility and finite incident sum hold for
  every Jx,Jy>0. Translation-invariant spin-flip invariant cylinder limits have
  the same two-spin correlations as the plus state. This does not equate their
  magnetizations or their connected susceptibilities. Reviewed Raoufi.pdf/txt.
- Camia–Garban–Newman, arXiv:1205.6612v4 (17 June 2013), Theorem 1.5, page 3,
  and Corollary 1.6, page 4. Read the official version at
  https://arxiv.org/pdf/1205.6612v4 . The theorem permits arbitrary nonnegative
  edge interactions and nonnegative, site-dependent fields. The corollary
  permits a nonempty set of pinned plus spins and gives log-partition
  third-derivative nonpositivity. Thus GHS is not restricted to equal couplings.

## Lean boundary

PhysicalField/RealFamily.lean defines `PublishedRealSpinFamily` as the exact
baseline `PublishedRealSpinFormFactors` for EVERY lambda>0, evaluated on ONE
common correlation family indexed by independent real pairs. No analytic
regularity of that family is assumed. `PublishedRealGibbsFamily` similarly uses
one energy-coupling magnetization family for all Jx>0 and lambda>0, and the SAME
correlations. The inherited Gibbs-field condition explicitly lists finite
marginals, finite local field tilt, monotonicity, nonnegative covariances,
pinned-volume comparison, GHS concavity, and thermodynamic limits. It contains
no susceptibility summability, derivative, or complex conclusion. These
published real Gibbs representation conditions are a separate visible input;
they are not inferred merely from a zero-field form-factor identity.

The precise infinite-plane real form-factor representation is the allowed
published real interface reused unchanged from the baseline. JOINT section
3.1 explains its cylinder-limit and state identification. No new axiom or
joint analytic statement is added. Baseline finite-law differentiation and
thermodynamic squeeze are actual proofs, reused by PhysicalField/Identification.
The new identification proves absolute full-lattice covariance summability and
identifies the literal joint contour sum on every positive real pair, using
lambda=y/x. The LT sum subtracts M^2 at EVERY site, including onsite 1-M^2.
The energy field h enters via eta=beta h; the theorem proves the ordinary HT
and right plus-phase LT derivative beta X only on physical real rays.
