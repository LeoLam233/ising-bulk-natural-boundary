# Low-temperature natural boundary

**Ordered pure phase · complete connected bulk magnetic susceptibility**

This is the **low-temperature proof**, a distinct development within the [two-proof Ising repository](../README.md). It concerns the zero-field, isotropic, infinite square-lattice Ising model for (J>0).

The observable is the **pure-phase connected** bulk sum
\[
\mathcal X_\mathrm{low}(s)=\sum_{(m,n)\in\mathbb Z^2}
\bigl(\langle\sigma_{00}\sigma_{mn}\rangle_{+}-M(s)^2\bigr),
\qquad M(s)^2=(1-s^{-4})^{1/4}.
\]
Here (s=\sinh(2\beta J)>1) on the physical low-temperature interval. The normalized susceptibility is analytically continued from the ordered pure-phase germ to the exterior domain **(|s|>1)**, with **(|s|=1)** as its natural boundary. The physical (eta) factor is treated on the corresponding local temperature branches.

The proof includes **every lattice site** and the **complete infinite even-particle form-factor expansion**, after separating the spontaneous-magnetization term. The current manuscript is version `v0.1-rc6`, alongside Lean `v0.3.0-rc2`.

## Read the low-temperature proof

| Resource | Location |
|---|---|
| Mathematical manuscript | [Low-temperature manuscript PDF](../paper/next/manuscript.pdf) · [TeX](../paper/next/manuscript.tex) |
| Lean proof and build entry | [`IsingBulk.lean`](../lean/IsingBulk.lean) · [`Audit.lean`](../lean/Audit.lean) |
| Main natural-boundary theorem | [Low-temperature final proof modules](../lean/IsingBulk/Final/) |
| Reproducible validation | [Lean build guide](../lean/README.md) · [Version records](../docs/VERSIONS.md) |
| Mathematical scope | [Claim and quantifier ledger](../CLAIMS.md) · [Proof guide](../docs/PROOF_GUIDE.md) |
| Earlier releases and provenance | [Release notes](../RELEASE_NOTES.md) · [Audit history](../audits/README.md) |

The low-temperature mathematical development has its own source identity, version history and review record. Its final proof does not follow from the high-temperature result.

## Relation to the other proof

The [high-temperature proof](../high-temperature/README.md) studies the **disordered-phase complete susceptibility**, with the full **odd-particle** expansion and an analytic germ on **(|s|<1)**. The two proofs share foundational Lean modules without merging their physical observables or final natural-boundary theorems.

[中文说明](README.zh.md) · [Repository home](../README.md)

The [low-temperature citation](CITATION.cff) preserves the original manuscript citation, separately from the high-temperature result.
