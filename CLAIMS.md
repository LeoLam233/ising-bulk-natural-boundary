# Claims and quantifiers

**Current status (7 October 2026).** The mathematical claims below belong to the frozen AI-assisted candidate manuscript v0.1-rc4. The internal form-factor / higher-tail chain is formalized and kernel-verified in [Lean v0.2.1](https://github.com/LeoLam233/ising-bulk-natural-boundary/releases/tag/v0.2.1), with E1/E2/E3 retained as explicit external literature premises. This separate formalization release does not relabel the manuscript; independent human expert validation and peer review remain outstanding. See [current repository / Lean status](release/CURRENT_STATUS.json).

The manuscript studies `X = beta_phys^{-1} chi`, with the pure-phase connected bulk susceptibility continued from real `s>1`, and `M²=(1-s^{-4})^{1/4}` on the exterior branch. It does not replace the observable by diagonal susceptibility.

For each **fixed** selected nonaxis point `s_*`, let `N_0=2p`, `k=N_0²/2-1` and `s_epsilon=(1+epsilon)s_*`. The manuscript's two central claims are

\[
\partial_s^k T_{N_0}(s_\varepsilon)=2L_\beta\varepsilon^{-1/2}+o(\varepsilon^{-1/2}),\quad L_\beta\ne0,
\]
\[
\sum_{N>N_0,\ N\ \mathrm{even}}|\partial_s^j T_N(s_\varepsilon)|=o(\varepsilon^{-1/2}),\quad 0\le j\le k.
\]

Constants may depend on the fixed point and finite `k`; no single derivative order or positive amplitude bound over the whole dense family is required. The infinite even-particle sum and all required lower derivatives are included. The first term means the **whole** form-factor integral, not only a formal saddle model. The tail includes all angular supports and all higher even orders.

Together with the stated exterior normal convergence, finite lower-order smoothness and the local nonzero physical prefactor, these imply the proposed natural-boundary conclusion. The manuscript claims these ingredients; the release records do not independently certify them.

The W1 repairs in version 0.1-rc3 preserve these claims and quantifiers. Its [scoped audit record](provenance/W1_REPAIR_AUDIT.md) does not certify the full theorem.

Separate statuses: (i) candidate manuscript theorem, (ii) solver's audit/reconstruction verdict, (iii) receiver's executed checks, (iv) external theorem used within its scope. These must not be substituted for one another. See the [evidence limits](LIMITATIONS.md) and [proof guide](docs/PROOF_GUIDE.md).

The `0.1-rc4` W2 revision preserves the theorem, point family, derivative range and particle windows. It makes the K/Stokes pair interface explicit; see [W2 provenance](provenance/W2_REPAIR_AUDIT.md). No full-original-torus uniform pair estimate or external certification is claimed.
