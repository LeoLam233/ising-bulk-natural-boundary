# Current control launcher

The launcher uses explicit `-f lakefile.toml` and absolute pinned Lean, a sanitized environment with both cache paths disabled, and before/after proof/verification/runtime identity binding. Heartbeat, recursion, timeout, memory, interruption and import failures invalidate a negative control even when an unsolved-goal diagnostic also appears. Historical receipts remain evidence of their exact earlier execution, not of unchanged helper source.

# Proposed continuation verification controls

Status: coordinator reviewed the proposed scope. On 2026-10-06 all 13 isolated
Python manifest controls and all five ordinary Lean controls passed on their
first runs. Raw evidence is in
`results/manifest-20261006T115328Z-dbeffebc/summary.json` and
`results/lean-20261006T115519Z-787352ea/summary.json`. The three intentional-invalid
proofs reached exactly their expected mathematical failure locations. This
packet is ordinary verification development, not a formal audit or a
final-candidate acceptance receipt.

All files and generated results stay below `control_packet/continuation/`.
The intentional-invalid examples are outside the `IsingBulk` and `Audit` library
roots. They must never be added to a production import, production-module
inventory, theorem/claim count, or the proof-critical source manifest. The
positive interface fixture imports the public root; production does not import
any fixture. The runners do not write, patch, forge, or mutate `.olean` files.
No altered-import-metadata route is used.

## Focused Lean controls

Only run this command under the coordinator's explicit compile lease, after
the current public root and its production imports have been compiled:

    python3 control_packet/continuation/run_lean_controls.py --lean-bin-dir /workspace/scratch/e6e0818fcb8f/ising_recovery_runtime_20261003T1833Z/lean-4.34.1-linux/bin

Every invocation uses `lake env lean -j1 -DwarningAsError=true`, without an
output `.olean` or a whole-project build. Raw command, stdout, stderr, elapsed
time, source SHA-256, parsed diagnostics, and control verdict are retained in a
new timestamped results directory. The runner stops at the first unexpected
outcome. An invalid fixture counts as rejected only if Lean exits with status 1
and the expected diagnostic points to its marked mathematical proof location.
Timeouts, missing imports, unknown constants/tactics, tool failures, and other
unexpected diagnostic locations do not count as successful negative controls.

1. `PositiveArithmetic.lean`: expect exit 0, proving `2 + 2 = 4` with `rfl`.
2. `PositiveInterfaces.lean`: expect exit 0 through `import IsingBulk`. Explicit
   application types retain the strict-to-weak window direction, eventual
   summability and actual intermediate `tsum` little-o, the literal all-order
   infinite sum of derivative norms, and the existing TW/E1/E2 boundaries of
   the final two natural-boundary endpoints.
3. `InvalidArithmetic.lean`: the false equation `0 = 1` must fail at the marked
   `rfl`, with a `Tactic ... rfl ... failed` diagnostic.
4. `InvalidStrictWindow.lean`: `2 ≤ 2` is deliberately used to prove `2 < 2`.
   Expect `Type mismatch` at the marked `exact h`. This detects the reversed
   weak-to-strict endpoint step, which production does not use.
5. `InvalidCancellation.lean`: the deliberately false equality
   `‖1 + (-1)‖ = ‖1‖ + ‖-1‖` must leave `unsolved goals` at the marked declaration
   or proof point. Its left side is zero and its right side is two. This
   distinguishes a norm of a cancelled sum from an absolute sum.

These are ordinary source elaboration/proof-rejection controls. They do not
test kernel rejection of forged proof objects or replace full kernel replay.
The expected diagnostic fingerprints were validated in the recorded cheap run:
arithmetic at line 4 (`rfl` failed), strict window at line 5 (type mismatch),
and cancellation at line 6 (unsolved goal `False`).

## Bounded payload-manifest controls

    python3 control_packet/continuation/run_manifest_controls.py

This command creates a four-file isolated payload: a copy of the positive
arithmetic source and copies of the current three Lean/Lake pin files. It
does not copy or change production source. Each mutation receives its own new
directory; no original or earlier result is deleted. The verifier inventories
every regular file, including hidden files, and rejects symlinks, unsafe paths,
duplicate entries/JSON keys, missing or extra files, byte-count differences,
and hash differences.

Expected outcomes are exact error codes, not merely a nonzero subprocess exit:

- Untouched payload: `PASS`, exit 0.
- Same-length source-byte mutation: `SHA256_MISMATCH` for `IsingBulk/Control.lean`.
- Same-length Lean pin mutation: `SHA256_MISMATCH` for `lean-toolchain`.
- Missing source: `MISSING_FILE` for `IsingBulk/Control.lean`.
- Additional hidden input: `UNDECLARED_FILE` for `.hidden-proof-input.txt`.
- Changed manifest bytes: `MANIFEST_ID_MISMATCH`.
- Source and manifest coherently rehashed together: `MANIFEST_ID_MISMATCH`
  against the original independently retained expected manifest ID.
- Bad digest with a deliberately supplied test pin: `SHA256_MISMATCH`.
- Omitted manifest entry with a test pin: `UNDECLARED_FILE`.
- Duplicate path with a test pin: `DUPLICATE_PATH`.
- Traversal path with a test pin: `UNSAFE_PATH`.
- Invalid JSON with a test pin: `MANIFEST_PARSE_ERROR`.
- Duplicate JSON key with a test pin: `DUPLICATE_JSON_KEY`.

“With a test pin” deliberately bypasses only the outer identity mismatch for
that synthetic case, to exercise the inner inventory/schema/hash check.
It is not the operational way to authorize an altered candidate manifest.
All negative cases must exit 1 with the exact expected code and path, and
empty stderr. Unparseable output or any other failure is a harness failure.

`payload_manifest.py` can also snapshot or verify an explicitly staged payload:

    python3 control_packet/continuation/payload_manifest.py snapshot --payload-root STAGED_PAYLOAD --manifest NEW_MANIFEST.json
    python3 control_packet/continuation/payload_manifest.py verify --payload-root STAGED_PAYLOAD --manifest REVIEWED_MANIFEST.json --expected-id TRUSTED_SHA256

The expected ID must come from the reviewed freeze receipt, not from an
unchecked incoming manifest. The snapshot command refuses to overwrite an
existing manifest. This verifier binds exact bytes/inventory; it does not
authenticate who approved the expected ID or decide the final production
payload's completeness. The coordinator must establish that scope separately.

## Evidence limits and subsequent work

These controls prepare a small part of the required inexpensive preflight.
They do not establish whole-project clean-build/cache independence, production
root reachability in a fresh checkout, full kernel replay, the reachable axiom
census, manuscript correspondence, dependency provenance, workflow/context
validity, actual branch CI entry into Lean, or any formal audit round verdict.
Those obligations remain explicit and separate. The manifest tests do not
replace an actual stale-cache or undeclared-dependency attack.

Keep two different identities: the reviewed proof-critical payload identity
and the complete release tree identity. This packet is verification tooling;
its synthetic four-file manifest is neither of those final candidate IDs.
Do not infer that a tooling-only or release-only edit changes the production
proof payload. Bind each receipt to the actual scope it checked.

## Targeted post-audit controls

`PositiveInterfaces.lean` now also applies the exact FIRST type with its E3
premise and the complete TAIL type with positive-parameter norm summability.
`E3Guard.lean` checks the actual E3 non-Nickel guard by definitional equality,
proves the selected point is Nickel at order 2p, and refutes a guard-less
comparison premise from FIRST. Its three named theorems are checked against
the approved logical axiom set. This is a narrow E3 regression.

`run_remediation_controls.py` invokes the production `ci/verify_payload.py`
on isolated copies for coherent source/manifest tampering, dependency HEAD,
tracked-file and Lake-override changes, and project namespace shadowing.
The existing manifest/toy controls are retained with their bounded scope.
