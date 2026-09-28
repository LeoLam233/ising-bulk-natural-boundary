# Finite checks and their limits

`python scripts/reproduce.py` runs six byte-identical historical scientific scripts after copying each to a fresh `.local/checks-*` directory. It compares their outputs with recorded fixtures. No source paper is parsed or proved by these scripts. The supported environment is CPython 3.11+ with pinned NumPy 2.3.5, SymPy 1.14.0 and mpmath 1.3.0; the exact release-run versions appear in the [run record](../release/REPRODUCTION_RECORD.json).

| ID | Executed scope | What is not established |
|---|---|---|
| v7_core | 2,100 selected points across 22 primes at first order; four N=2 quadratures; chart/amplitude diagnostics; finite pair grids | All primes, every order and continuous-domain uniformity. Exact first-order checks are assertions; grids and quadratures are diagnostics. |
| v7_normalization | Nine N=2 quadratures (three configurations and three mesh sizes) | Interval error bounds or all-N normalization. |
| v7_additional | Finite Nickel thresholds, field/amplitude bookkeeping and endpoint checks | A complete tail proof. Text is compared with the historical receiver rerun. |
| v6_diagnostics | Three N=2 checks, 523 finite point-family configurations, field and phase comparisons | A proof from numerical absence of counterexamples. Historical v6 file hashes are metadata, not hashes of v0.1. |
| mr1_algebra | Symbolic identities with Boolean assertions | Analytic-domain hypotheses of the identities. |
| mr1_coupled | Actual coupled-field diagnostics, including a deliberately failing naive-field negative control | Uniform support/disk and coarea claims. N=6 is a toy dimension; N=24 is an actual first tail dimension. |

`SCRIPT_ORIGINS.json` records source hashes and fixture identities. Original script bytes are unchanged. Most numerical outputs do not contain rigorous mathematical assertions. A successful run is labelled `REPRODUCED_FINITE_CHECK`, never “proof verified.”

The comparison uses relative and absolute tolerances of 1e-10 for numeric scalar/complex values and exact equality for Boolean/text/structural data. These are transport/replay tolerances, not a claim of interval certification. Declared metadata keys (including old source-file hashes) are ignored; current source identity is checked separately by `verify_repository.py`. Initial string comparisons exposed only floating-tail differences up to 1.40e-17 and absent v6 source-file metadata; this adjustment and the actual outputs are recorded.

Optional `--only ID ...` limits the selection. A nonzero subprocess exit, timeout, missing output or comparison difference produces a nonzero wrapper exit. Historical CR0 scripts supplied under `reproduction/` are supplementary and are not automatically executed by this command. Copy a historical run to scratch before executing its code because it may write beside itself.
