# Research history: discovery, failed attempts, audits and formalization

> **Scope warning.** The preserved [initial Codex session](original-session/README.md) documents only the first autonomous exploration (reported as lasting more than ten hours). Its 38 checkpoints, nine route categories, and 27 classes of failures or limitations **are not totals for the entire Ising project**. The end product was an **initial proof prototype**, internally marked `PROVISIONAL CENTRAL CLOSURE`. It was **not** the current manuscript, a final theorem, or independently certified mathematics.

## Reading routes

1. [Research journey](RESEARCH_JOURNEY.md): what was tried, why the approach changed, and why the second prime family was eventually combined with the contour method.
2. [Failure and repair ledger](FAILURE_AND_REPAIR_LEDGER.md): falsified intermediate claims, unsupported transfers, and candidate repairs; these statuses are not interchangeable.
3. [Checkpoint timeline](CHECKPOINT_TIMELINE.md): first-session snapshots v1–v38, not a minute-by-minute execution record.
4. [Original session evidence](original-session/README.md): a verbatim retrospective, archive identity, file indices and preservation policy.
5. [Original-to-later crosswalk](ORIGINAL_TO_LEAN_CROSSWALK.md): provisional, evidence-linked mapping to later adversarial audits, manuscript repairs, and Lean; **not** an equivalence proof between versions.

## Distinct historical phases

| Phase | What belongs here | Present evidence boundary |
|---|---|---|
| I — Original autonomous Codex session | Initial P2-5 selection, 11 considered targets, nine research routes, v1–v38, initial proof prototype | Original retrospective preserved here. It was reconstructed from saved files, not a verbatim chat or timing log. |
| II — Adversarial audits and mathematical repairs | Subsequent manuscript revisions and adversarial criticism, including W1/W2 | See [audit ledger](../audits/VERSION_LEDGER.md), [W1 repairs](../provenance/W1_REPAIR_AUDIT.md), [W2 repairs](../provenance/W2_REPAIR_AUDIT.md). These events are **not** in the original-session archive. |
| III — Lean formalization and semantic checks | Lean developments, kernel replay, controls and explicit E1/E2/E3 premises | See [Lean scope](../lean/README.md) and [current status](../release/CURRENT_STATUS.json); a successful kernel check applies to its formal statement and premises, not to unexamined semantics. |
| IV — Current integrated assessment | Mathematical status after later reviews and remediation | See the versioned repository [README](../README.md), [limitations](../LIMITATIONS.md) and [v0.2.1 remediation](../REMEDIATION_v0.2.1.md). No independent human peer review is asserted. |

## Rules for interpreting history

- **Historical claims are not retroactive current claims.** Titles such as `proof`, `certificate`, `PASS` or `closed` have only the scope given at their original time and input version.
- **Record failures without rewriting them as successes.** The fact that a later repair was proposed, internally accepted or implemented must be separately evidenced.
- **Preserve originals.** The original retrospective is stored as a byte-preserving copy; the raw 38 checkpoint ZIPs are catalogued but not distributed on this branch pending an independent release/privacy/provenance review. See [original-session README](original-session/README.md).
- **Do not add effort counts.** Checkpoints are archival events, not calls, tokens, agents, hours, or total attempted proofs. The duration is an operator-reported approximate duration, not established by a timestamped transcript.
- **Differentiate verification levels.** Finite Python diagnostics, derivations in notes, AI hostile audits, Lean checking, and independent human refereeing establish different things.

This section is a research-process transparency resource. It does not amend the frozen manuscript, formal statements, releases, or existing audit reports.
