# A candidate natural-boundary proof for the bulk Ising susceptibility

**Development candidate: manuscript v0.1-rc6 / Lean v0.3.0-rc2 · 17 October 2026 · Dehao Lin**

[中文说明](README.zh.md) · [Candidate manuscript](paper/next/manuscript.pdf) · [TeX](paper/next/manuscript.tex) · [Proof guide](docs/PROOF_GUIDE.md) · [Mathematical changes](docs/AMPLITUDE_IDENTIFICATION_v0.3.0-rc2.md) · [Version identities](docs/VERSIONS.md)

This branch contains an implemented next-version candidate for the zero-field, isotropic, infinite square-lattice **bulk** susceptibility continued from its low-temperature pure-phase exterior germ. It is prepared for mathematical review; no independent human expert validation or peer review is claimed.

The new canonical normalized-series theorem has **no E3 premise**. Physical identification retains **E1 and E2**, the correlation representation and spontaneous magnetization. The actual lower even orders are bounded internally on their original offsite contours. The old published full-site comparison helpers remain available but are absent from canonical transitive proof dependencies. [Exact assumptions](CLAIMS.md) · [External sources](provenance/EXTERNAL_PREMISES.md).

The verified rc5 / Lean v0.3.0-rc1 candidate remains at [`dd977048`](https://github.com/LeoLam233/ising-bulk-natural-boundary/tree/dd977048c2380e775d83b97ae1fba354c04c349a). This revision adds the normalization result below and preserves its production Lean sources byte for byte. New manuscript, source correspondence and acceptance receipts have distinct identities.

## Changes

- Internal non-Nickel gradient separation and fixed-radius integration by parts replace E3 in FIRST, finite lower-order noncancellation and both natural-boundary endpoints.
- Proposition 6.1 states the stronger branch–compact bound `1+C/N` on the protected `c/N` disk. Baseline Lean already proves this stronger bound; downstream budgets are retained.
- Proposition F.1 resolves the complete-amplitude comparison: on the selected physical exterior germ, `A_full=4R_N(-theta_*)=-4i R_N(theta_*)`. The printed scalar is one chart; the complete full-site coefficient has four equal signed contributions. Observable definitions, local variables, power branches and physical prefactors are derived. The formula is arXiv (69), journal (70).
- Corollary 9.4 excludes real smooth extension through every nonempty boundary arc. A finite-prime criterion gives an elementary `O(ell^-2)` derivative ceiling. The coefficient `80*pi^2` is only an asymptotic leading constant, not a uniform finite covering bound.
- Lean proves the actual selected-point real `C^k` obstruction. The factorial evaluation, complete-amplitude conversion and quantitative finite-prime covering remain analytic manuscript results.

For each fixed selected point, `N0=2p`, `k=N0^2/2-1` and `s_epsilon=(1+epsilon)s_*`, the load-bearing claims remain `T_N0^(k)=2 L_beta epsilon^(-1/2)+o(epsilon^(-1/2))` with nonzero `L_beta`, and the absolute sum of every higher even form-factor derivative is `o(epsilon^(-1/2))` for all `0<=j<=k`. Constants may depend on the fixed point and finite derivative order. All lattice separations and the entire even-particle expansion are included.

## Verification

[Current status](release/CURRENT_STATUS.json), [executed receipts](release/next/VALIDATION.json), and the [mandatory consistency audit](docs/CONSISTENCY_AUDIT_v0.3.0-rc2.md) control verification claims for this candidate. Earlier PASS verdicts and release receipts apply only to their own inputs.

The Linux/WSL gate builds the complete root, audits axioms, checks exact endpoint types and origins, runs positive/negative controls, traverses compiled types **and proof bodies** for E3, and runs `leanchecker --fresh --verbose IsingBulk`. Cached dependency binary/source correspondence remains trusted; Mathlib is not rebuilt from source. Build and replay use the same kernel. [Lean reproduction](lean/README.md) · [Evidence limits](LIMITATIONS.md).

From the repository root:

```sh
python -m pip install -r requirements.txt
python scripts/reproduce.py
python checks/next_version/run_checks.py --output .local/next-checks.json
python checks/amplitude_identification/check_amplitude.py --output .local/amplitude-checks.json
python scripts/build_candidate_paper.py
python scripts/verify_candidate.py
```

The PDF builder requires an existing `pdflatex`; it updates only the candidate under `paper/next/` and scratch files under `.local/`.

## Frozen releases

The original **manuscript v0.1-rc4** assets remain at [paper/manuscript.pdf](paper/manuscript.pdf), [paper/manuscript.tex](paper/manuscript.tex) and [paper/LABEL_INDEX.json](paper/LABEL_INDEX.json). This is the later ORCID/bibliography editorial artifact, distinct from the immutable rc4-tag PDF. [The version ledger](docs/VERSIONS.md) records both hashes. The immutable **Lean v0.2.1** tag remains `de23d9475744fb4625666142d5a03b3d688195e6`, with E1/E2/E3 in its historical endpoints. This upgrade does not move tags, overwrite frozen assets, publish a release or merge into `main`.

Former current-facing Lean records are byte-preserved under [lean/history/v0.2.1](lean/history/v0.2.1/README.md). All old audits, reconstruction records, research history, release records and their original verdicts retain their historical scope. The [old expert brief](docs/expert_brief.pdf) describes rc4/v0.2.1. The root `MANIFEST.json` and `scripts/verify_repository.py` are the historical rc4 snapshot check, expected to report a mismatch on later trees. The candidate uses `release/next/MANIFEST.json` and `scripts/verify_candidate.py`.

[Research history and failed attempts](research-history/README.md) · [Historical audits](audits/README.md) · [Source history](provenance/SOURCE_PROVENANCE.md) · [Prior art](provenance/PRIOR_ART.md).

Dehao Lin is the named human author and public contact, ORCID [0009-0001-4551-8490](https://orcid.org/0009-0001-4551-8490). Generative AI contributed extensively. [Authorship](AUTHORSHIP.md). Code: [MIT](LICENSE); project prose: [CC BY 4.0](LICENSE-DOCUMENTATION.md); [third-party notices](THIRD_PARTY_NOTICES.md).
