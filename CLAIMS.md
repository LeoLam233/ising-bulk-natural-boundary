# Claims and quantifiers: manuscript v0.1-rc5 / Lean v0.3.0-rc1

The object is the zero-field isotropic infinite square-lattice connected bulk response `X=beta_phys^(-1) chi`, continued from the low-temperature pure phase. It includes all sites and the full even-particle expansion. The magnetization branch `M^2=(1-s^-4)^(1/4)` tends to one at infinity.

For each fixed selected prime point, `N0=2p`, `k=N0^2/2-1` and `s_epsilon=(1+epsilon)s_*`, the whole first form factor has `T_N0^(k)=2 L_beta epsilon^(-1/2)+o(epsilon^(-1/2))` with nonzero coefficient. Every higher even order and every `0<=j<=k` enter the absolute-tail little-o. Lower even orders have bounded fixed-order derivatives by the internal offsite nonstationary proof. Bounds may depend on point, particle order and derivative order; finite windows admit common positive thresholds. The contour radius is held fixed during each complex derivative.

The physical normalized bulk has leading derivative coefficient `4 M^2(s_*) L_beta`. Local analytic nonzero inverse-temperature factors transfer the obstruction to each chosen physical germ. A global single-valued inverse-temperature branch on the entire exterior is not asserted.

The canonical `IsingBulk.Final.theorem_nb` has no E1, E2, E3 or external tail premise. `theorem_nb_physical` retains E1/E2 and positive coupling. FIRST has no E3 parameter. Retained published comparison interfaces are excluded from the canonical compiled type/body dependency graph by `InternalRegularity.lean`; an axiom-only query cannot establish removal of an explicit parameter.

Proposition 6.1 bounds branch–compact pairs by `1+C/N` on the actual protected disk. Only the compact root is displaced; the branch stays at its disk-point value in the closed lower unit disk. Existing weaker downstream estimates remain valid.

The factorial expression evaluates the same single-chart coefficient with the original continuation. Complete offsite and full-site coefficients have multiplicities two and four. McCoy–Maillard (69) matches the specified single-chart expression at inverse angle with the stated principal power; no claim is made that the source explicitly selects that branch or includes the full chart sum in its printed amplitude.

Corollary 9.4 excludes a real smooth extension agreeing on an exterior neighborhood through every nonempty boundary arc. For angular length `ell`, any prime `p>=11` with `2 sqrt(10) pi/p<ell` supplies a selected obstruction of order `2p^2-1`. An elementary sufficient ceiling is `max(968,320 pi^2/ell^2)`. The asymptotic leading constant `80 pi^2` additionally uses the prime number theorem; it is not a uniform finite-length bound. No claim concerns a boundary trace without an agreeing exterior extension or one finite derivative order at every point.

The selected-point real `C^k` obstruction is formalized. The factorial evaluation, finite-prime covering and full quantitative physical arc statement are manuscript-only. Original formal nonvanishing and tail arguments remain. These are internally checked candidate claims, not independent human certification. [Versions](docs/VERSIONS.md) · [Executed checks](release/next/VALIDATION.json).
