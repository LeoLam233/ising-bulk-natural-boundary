# HT22 author controls ledger — 2026-10-27 20:01 UTC

This is implementation/acceptance infrastructure, **not an independent final
audit**. The originally referenced `notes/CONTROLS_LEDGER.md` was absent when this
session recovered. This ledger is maintained inside the assigned controls area.

## Recovered evidence and repair

- `runs/20261027T194733Z_development/receipt.json`: complete helper-based
  development PASS, all five negative fixtures, old-route kernel acceptance.
- `runs/20261027T194858Z_development/receipt.json`: portable-mode FAIL because a
  sparse output `IsingBulk/` directory shadowed the complete input namespace.
- Fixed portable mode by materializing only the namespace ancestors needed by
  owned control outputs and shallow-linking all other clean-built siblings.
  Borrowed objects remain read-only; no original proof source was changed.
- `runs/20261027T195559453194Z_development/receipt.json`: correct preflight FAIL
  on the absent, unused development Cli package output path. Supply only existing
  directories to `--lean-path`; no Lean execution occurred on this failure.
- `runs/20261027T195619671580Z_development/receipt.json`: complete portable
  development PASS, confirming the repair without rebuilding dependencies.
- `runs/20261027T200053568517Z_development/receipt.json`: latest complete portable
  development PASS against the strengthened current scripts; 57 policy cases and
  six runner tests passed, with no source changes during execution. Still not a
  frozen final clean-build/replay acceptance receipt.

## Current controls

- Three positive Lean modules, thirteen exact named axiom reports, five exact
  exit-1 `Type mismatch` fixtures, and a deliberately kernel-valid old endpoint
  bypass. The latter must later fail policy for actual forbidden reachability.
- 57 synthetic graph-policy cases (including removing every mechanism only from
  the main theorem's subclosure) and six bounded filesystem/generator unit tests.
  Synthetic tests are not evidence that the actual final graph passes.
- Immutable source manifest digest; string or `{sha256,size}` digest entries;
  exact pre/post source checks; all graph/types/summary inputs and Lean binary
  pinned pre/post; complete expanded local-type report required.
- Separate exact `f001_natural_boundary` closure inside the complete aggregate
  proof-term/support graph. `MAIN_MECHANISM_GROUPS` in `route_policy.py` records
  consumed whole constrained deformation, odd first-border/minor algebra,
  mixed covariance/signed coarea, true scalar transport/Piola, actual near/far
  envelopes, consumed V jets and covariance-Cauchy route, inverse/germ bridge.
- Aggregate-only obligations additionally include physical identities, exact
  FIRST/full limit, lattice summability and the sharp R/reciprocal-R/G export.
  No claim is made that this separately exported sharp table is the main proof's
  chosen route; the main uses the covariance-Cauchy sourceResidual jets instead.
- Main actual odd algebra consumes `odd_constantBorderFirst_determinant`;
  demanding the unconsumed last-border corollary would be an incorrect main gate.
- Graph generator verifies untouched RootWalker from the pinned Git commit, or
  from embedded `PROTECTED_BASELINE.json` (commit, SHA256, Git blob) in snapshots
  without `.git`. Drivers enable full proof printing, maxRecDepth 100000 and
  maxHeartbeats 0, but generation does not execute them.

## Exact remaining queue — not yet authorized to execute heavy work

1. Coordinator freezes the final complete source/config/protected baseline and
   all controls scripts/fixtures. Runtime generated drivers/reports are outputs,
   not source-manifest members.
2. On the explicitly authorized heavy verification environment **LDH only**,
   make the isolated same-source clean strict build using `lakefile.ht22.toml`,
   root `IsingBulkHT22`, audit root `AuditHT22`, and all required additive support.
   Build protected `IsingBulk.HT.Final.FullNaturalBoundary` only as the bypass
   fixture dependency; this does not authorize its production proof use.
3. Generate final and bypass graph drivers in that copied campaign:
   `make_graph_driver.py --case final --module IsingBulkHT22 --output ... --graph-base ...`
   and `--case bypass --output ... --graph-base ...`.
   Execute unchanged RootWalker there against the identical clean-built objects.
   Retain driver receipts, full `.graph.jsonl`, `.types.jsonl`, `.summary.json`,
   exact environment/command/exit receipts and source manifest hashes.
4. Execute final portable controls:

   ```sh
   python3 verification_controls/run_controls.py --phase final --no-deps \
     --lean "$PINNED_LEAN" --lean-path "$CLEAN_LEAN_PATH" \
     --frozen-manifest SOURCE_MANIFEST.json \
     --final-root IsingBulk.HT22.ht22_full_target \
     --final-graph-base "$FINAL_GRAPH_BASE" --bypass-graph-base "$BYPASS_GRAPH_BASE"
   ```

   `--physical` is automatic for the final-root policy and also enforces the
   separate main subclosure. No redundant third heavy extraction is necessary.
5. Separately establish official fresh kernel replay, protected-source identity,
   exact expanded-scope review and three independently sealed full-scope audits
   against the identical frozen source. Author controls do not replace them.

**Blocked action:** clean build/full graph extraction/fresh replay/final controls
against those reports. **Target:** explicitly authorized LDH. **Reason/status:**
heavy verification authorization is currently pending/not granted in this task;
no heavy local replacement was attempted. Actual main mechanism reachability,
old-route policy rejection on the actual scanner output, final same-source
controls and independent final audits remain unestablished.
