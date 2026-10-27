# Foundational Pfaffian source provenance

Upstream: https://github.com/hkjtsgmc79-boop/colombo-odd-lean

Frozen upstream commit: `9f57b40c7ce9837966c701193bbfec71ed38ae2e`.

Copyright 2026 Qianli Ma; Apache-2.0 (included LICENSE-Colombo.txt).

Only generic signed-matching Pfaffian/minor-summation infrastructure is reused. GeneralADPf and GeneralADMS are namespaced under IsingBulk.Preferred22.PfaffianFoundation; Congruence is the initial algebraic portion of OddPfaffianSquare, ported from Real to Complex. No Colombo conclusion, analytic positivity result, Ising endpoint or tail estimate is imported. The pinned LT Lean/Mathlib environment is unchanged.

PROVENANCE.json records exact SHA-256 of each upstream source. Porting changes are namespace/import updates, Complex specialization of the final congruence module, and compiler-required syntax/API updates. All adapted source is compiled by the same Lean kernel.

The initial ADPf file was inspected but is not included (the unused adaptation is preserved at `work/logs/algebra_unused_ADPf.lean`, outside the authoritative source tree): none of its declarations are required. GeneralADPf imports the corresponding Mathlib matrix/tactic infrastructure directly. Congruence stops immediately before upstream `det_pivotBlock`; the determinant-square/analytic continuation portions are not reused. All source-specific four-point algebra, all-even product induction, zero-pair argument and physical specialization are new proofs in Preferred22/Pfaffian.lean.
