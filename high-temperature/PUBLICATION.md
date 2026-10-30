# High-temperature result: publication and verification identity

This result concerns the **complete bulk magnetic susceptibility of the disordered
high-temperature phase**, with the full infinite positive odd-particle expansion.
The [low-temperature result](../low-temperature/README.md) has its own manuscript,
connected pure-phase observable, even-particle expansion and endpoint.

| Artifact | Identity |
|---|---|
| Mathematical manuscript | HT-1.0, 17 October 2026 |
| Human-author publication edition | 21 October 2026; [PDF](../archive/manuscripts/pre-eight-2026-10-30/paper/ht/publication/manuscript.pdf), [editorial identity](../archive/manuscripts/pre-eight-2026-10-30/paper/ht/publication/EDITORIAL.json), [build record](../archive/manuscripts/pre-eight-2026-10-30/paper/ht/publication/BUILD.json) |
| Frozen audited manuscript | [Unchanged TeX/PDF](../archive/manuscripts/pre-eight-2026-10-30/paper/ht/frozen/); source SHA-256 `128739407e585457b38d150bd5a74514d8567b5a936c8b4bc2a5c613b1962c65` |
| Audited mathematical Lean project | `HT_STANDALONE_20261020T1747Z` |
| Baseline low-temperature library tree | `ca47fde26285028603c7e87a9893aad31933b526` |
| Source inventory | [1,079 unchanged baseline files and 447 exact additions](../HT_1747_OVERLAY_MANIFEST.json); all 1,521 files of the original standalone project are present byte-identically |
| Lean runtime | 4.34.1, compiler commit `5045d0056413266e57c625dcd7c365b10e377c52` |
| Mathlib | `d13f23b723b8a846827a245b89c10fc7d3f11612`, with all nine dependencies pinned in the unchanged [manifest](../lean/lake-manifest.json) |
| Distinct release | [high-temperature-v1.0.0-lean1747](https://github.com/LeoLam233/ising-bulk-natural-boundary/releases/tag/high-temperature-v1.0.0-lean1747) |

## The exact theorem and physical input

The final theorem is
[`publishedPhysicalSusceptibility_germ_natural_boundary`](../lean/IsingBulk/HT/Final/PublishedPhysicalTheorem.lean).
For every positive real coupling `J` and every `chi` satisfying the explicitly
defined [published angular susceptibility representation](../lean/IsingBulk/HT/Final/PublishedAngularInput.lean),
it proves a function analytic throughout `|s| < 1`, equal to `chi` at **every**
real `0 < s < 1`, with no local interior analytic extension through **any**
unit-circle point. The adjacent theorem transfers this conclusion to `chi`
itself when its disk analyticity is explicitly supplied.

The physical input is the classical real-temperature, full-bulk odd-particle
form-factor identity, including the inverse-temperature normalization. It is
not a premise asserting FIRST, TAIL, convergence, contour equality, analyticity
or a natural boundary. The Gibbs-state identification is external statistical
mechanics, exactly as stated. [Orrick et al. (2001)](https://arxiv.org/abs/cond-mat/0103074)
and [Boukraa et al. (2008)](https://arxiv.org/abs/0808.0763) are the controlling sources.

The compiled [AuditHT](../lean/AuditHT.lean) checks theorem types, allowed logical
axioms and actual transitive type/proof dependencies. It requires the full-site
Fourier/angular bridge and both signs of the odd FIRST/TAIL developments, and
rejects dependencies on the low-temperature final natural-boundary theorems or
their E1/E2/E3 physical interfaces.

## Reproduce and inspect evidence

From `lean/`, run these exact commands with the pinned runtime and dependencies:

```sh
lake -f lakefile.toml build IsingBulk Audit
lake -f lakefile.ht.toml -R -H build IsingBulkHT AuditHT
lake -f lakefile.ht.toml env lean -j1 -DwarningAsError=true AuditHT.lean
lake -f lakefile.ht.toml env leanchecker --fresh --verbose IsingBulkHT
```

For source-only high-temperature verification, start with zero project `.olean`
files and run the high-temperature commands before the low-temperature regression,
or use a separate clean checkout. Pinned dependency caches may be reused.
[The receipt-producing runner](../scripts/run_high_temperature_verification.py)
checks this starting condition and pinned dependencies, then saves commands,
raw stdout/stderr, exit codes, timings, runtime identity and source hashes.

The [original HT acceptance workflow](../.github/workflows/ht-lean-acceptance.yml)
is preserved byte-identically from the integration kit. The additional
[unified publication workflow](../.github/workflows/unified-publication-acceptance.yml)
executes HT verification and a separate LT build/audit/fresh replay in the final
combined tree. The release attachments preserve the actual local and GitHub
execution evidence; successful past audit receipts are not substituted for these runs.

## Independent AI audit attachments

The following original archives are attached separately to the high-temperature
release, keeping large evidence archives and compiled `.olean` artifacts out
of the production source tree:

- [Pro/coordinated source audits](https://github.com/LeoLam233/ising-bulk-natural-boundary/releases/download/high-temperature-v1.0.0-lean1747/HT_Lean_1747_1_Source_Audits.zip)
- [Pro/coordinated execution logs](https://github.com/LeoLam233/ising-bulk-natural-boundary/releases/download/high-temperature-v1.0.0-lean1747/HT_Lean_1747_2_Execution_Logs.zip)
- [Original final-gate receipt](https://github.com/LeoLam233/ising-bulk-natural-boundary/releases/download/high-temperature-v1.0.0-lean1747/HT_Lean_1747_3_Original_Receipt.zip)
- [Independent Codex audit and execution evidence](https://github.com/LeoLam233/ising-bulk-natural-boundary/releases/download/high-temperature-v1.0.0-lean1747/HT_LEAN_1747_AUDIT_20261021.zip)

These audits reported `EXHAUSTED` within their documented scopes. They are AI
investigations, not independent human peer review. The release asset checksum
manifest binds the original archives and the new publication verification receipts.

Human author and contact: Dehao Lin, School of Physics, Sun Yat-sen University;
ORCID [0009-0001-4551-8490](https://orcid.org/0009-0001-4551-8490);
lindh9@mail2.sysu.edu.cn. [Citation](CITATION.cff), [MIT code license](../LICENSE),
[CC BY 4.0 authored manuscript/documentation license](../LICENSE-DOCUMENTATION.md).
