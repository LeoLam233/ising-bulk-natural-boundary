# Lean candidate v0.3.0-rc1

The internal form-factor and absolute-tail chain now has an internally proved lower-order replacement for E3. The manuscript snapshot is **v0.1-rc5**, `source_snapshot/manuscript-rc5.tex`, byte-identical to `paper/next/manuscript.tex` at the commit in `SOURCE.json`. The rc4 snapshot and historical v0.2.1 records remain separate. [Versions](../docs/VERSIONS.md).

Canonical endpoints:

- `IsingBulk.First.theorem_first`: actual first singularity, lower derivatives and all lower even orders, with no E3 premise.
- `IsingBulk.Final.theorem_tail_with_summability`: positive-parameter summability and all-j absolute higher-tail little-o.
- `IsingBulk.Final.theorem_nb`: normalized exterior natural boundary, with no external physics, E3 or tail premise.
- `IsingBulk.Final.theorem_nb_physical`: physical-germ identification and boundary conclusion, with E1/E2 and positive coupling only.
- `IsingBulk.Final.theorem_selected_no_Ck_extension`: actual selected-point real finite-order obstruction, TAIL discharged internally.

Published full-site interfaces and transfer helpers remain comparison theorems. `InternalRegularity.lean` traverses compiled types and proof bodies, excludes them from FIRST/NB dependencies, and requires reachability of the internal separator/global-IBP/radial-bound route. An axiom-only query cannot detect an explicit theorem parameter.

The runtime remains Lean 4.34.1, commit `5045d0056413266e57c625dcd7c365b10e377c52`; all nine dependency revisions are unchanged. There are 1,074 production subtree modules plus the public root. Accepted source identities are in `ci/accepted_identity.json`; [validation](../release/next/VALIDATION.json) records exact executions and runtime identity.

With exact Linux/WSL runtime and pinned dependency sources/cache:

```bash
python3 tools/continuation/preflight.py --lean-bin "$LEAN_BIN" --output "$PREFLIGHT_RECEIPT"
python3 ci/verify_payload.py --expected-id "$PROOF_ID" --dependencies
python3 control_packet/continuation/run_manifest_controls.py
python3 control_packet/continuation/run_remediation_controls.py
python3 tools/continuation/final_gate.py --lean-bin "$LEAN_BIN" --approved-preflight "$PREFLIGHT_RECEIPT" --logs "$NEW_LOG_DIRECTORY" --threads 2 --execute
```

Supply actual paths and the reviewed proof ID. Preflight receipt and log paths must be new. The heavy gate requires a source-only project with `.lake/packages` as its only Lake entry. It builds the full public root and Audit, elaborates 18 exact endpoints, runs seven Lean positive/negative controls including no-E3 traversal, and performs fresh official kernel replay. The 13 manifest and 13 production-verifier controls are separate checks. No `lake update` is required.

The axiom policy remains `propext`, `Classical.choice`, `Quot.sound`. Tracked dependency sources and namespace scans are checked. Cached binary/source correspondence remains trusted; this is not a Mathlib source rebuild or second kernel implementation. Accepted pins are inside Git. No independent human review is claimed.

The production-verifier command above executes 12 cases before a compiled project tree exists. After the build, execute the complete 13-case variant with `python3 control_packet/continuation/run_remediation_controls.py --shadow-tree .lake/build/lib/lean/IsingBulk`. The additional case supplies a complete compiled namespace in a dependency cache and requires rejection before loading it. The local receipt uses a healthy compiled project tree for this foreign-namespace test; it does not claim a separate semantic mutant was built.

The factorial amplitude and finite-prime covering are manuscript-only. [Coverage](COVERAGE.md) distinguishes them from the real Ck endpoint. [History](history/v0.2.1/README.md) preserves old counts, E3 premises and verdicts. The v0.2.0 publication machinery is not a publisher for this candidate.
