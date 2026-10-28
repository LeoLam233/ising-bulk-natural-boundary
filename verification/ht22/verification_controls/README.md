# HT22 effective author-built controls

These files are implementation controls, **not** any of the three independent
final Lean audits. Development receipts do not count as final-source acceptance.
No old tracked source is changed. Production roots must not import `Controls`.

## Proved scientific controls

- `Controls/Basic.lean`: the **actual** exterior and punctured-interior extension
  predicates admit every entire constant; zero is not a natural-boundary
  observable. Zero correlations and arbitrary origin-deleted correlations cannot
  satisfy the actual `PublishedRealHTSpinFormFactors`. Deleting the origin changes
  the convergent full bulk by exactly one, so equality is impossible.
- `Controls/Scope.lean`: literal new endpoint specializations for both physical
  functions, every positive coupling, both boundary signs, all four axes; exact
  nonzero physical beta normalization; exact full-lattice real-physics application.
  At `J=0` the literal beta-inclusive observable is zero and extends everywhere,
  giving a genuine countermodel to omitting the positive-coupling hypothesis.
- `Controls/FiniteTruncation.lean`: for **every** fixed number `m` of actual odd
  angular terms, its finite prefix cannot equal the actual infinite exterior
  source on the open exterior. Choose prime `p≥2m+6`, `a=1`; the effective sign is
  positive, every retained lower term has epsilon-scaled derivative limit zero,
  but the actual full source has the new proved nonzero prime limit. Equality on
  the open exterior would identify derivatives locally and contradict limit
  uniqueness. This is not a merely syntactic infinite-vs-finite type check.

The negative Lean fixtures attempt to insert the rejected replacement into its
positive type. Their expected type-mismatch exits are auxiliary typing controls;
the mathematical impossibility is established by the corresponding positive
countermodel theorem, not inferred from a failed tactic search.

## Reproduce development controls

From the campaign directory:

```sh
python3 verification_controls/run_controls.py --phase development
```

It compiles only the three scoped modules and their stale imports through the
strict incremental helper. It retains positive exits, all five expected nonzero
Lean exits, the old-route bypass's expected **zero** kernel exit, and policy unit
controls. Logs and receipts are under `verification_controls/runs/`.

**Do not invoke while other authors are changing dependencies.** A failed or
changed-dependency prerequisite is not counted as an expected negative control.

## Old-route dependency control

`fixtures/OldRouteBypass.lean` deliberately proves the new actual bulk's boundary
claim by the old HT endpoint. This is mathematically valid and kernel-compiles;
it is **contractually forbidden** as an independent F001 proof. The final
RootWalker report of `AuditSentinel.oldRouteBypass` must be rejected by policy.
Merely importing an old file is not a reason for rejection: only constants
reachable through actual type, value, inductive and recursor-rule support edges
are used.

Use the protected, unchanged `repository/verification/lt22/RootWalker.lean`
scanner, whose `audit_graph NAME to "BASE"` emits `BASE.graph.jsonl`,
`BASE.types.jsonl`, `BASE.summary.json`. Run full graph extraction only in the
assigned heavy verification environment after freezing. Append the scanner's
unchanged body (minus its `import Lean`, after ensuring `import Lean` is among
imports) and the desired `audit_graph` command to a generated scratch driver;
for the bypass, include its complete unchanged fixture body with its imports
moved to the import header. Do not modify protected RootWalker or proof source.

```sh
python3 verification_controls/route_policy.py /path/final \
  --root IsingBulk.HT22.ht22_full_target --physical
# Must return 0.
python3 verification_controls/route_policy.py /path/bypass \
  --root AuditSentinel.oldRouteBypass
# Must return nonzero AND report forbidden old proof-route reachables.
```

The policy checks exact rooted closure, missing edges/support, stored theorem
values, reported counts, axioms (`propext`, `Classical.choice`, `Quot.sound` only),
unsafe/partial nodes, required new first/lower/full-tail theorems, actual real
physical dependencies, and forbidden old completed endpoints. Additional required
mechanism declarations can be passed with repeated `--require NAME` after the
final manuscript crosswalk is fixed.

`--physical` also checks the **separate exact rooted subclosure** of
`IsingBulk.HT22.Final.f001_natural_boundary` inside the complete aggregate graph.
It follows every type/value/structural edge anew from that root: unrelated
aggregate fields cannot satisfy its gates. `MAIN_MECHANISM_GROUPS` in
`route_policy.py` names the required whole-torus deformation, actual odd
first-border identity and sharp ordinary marked minors, literal mixed covariance,
signed coarea, true scalar/Piola transport, actual near/far envelopes, consumed
all-order angular V jets, covariance-Cauchy route, continued inverse and physical
germ bridge. All are proof-term dependencies, never import-list requirements.

The sharp R/reciprocal-R/G table is required as an **aggregate quantitative
export**, not falsely claimed as the main proof's chosen route. The main instead
uses the protected covariance-Cauchy sourceResidual jets. Similarly the actual
main consumes the first-border determinant identity, not the unused last-border
corollary. The exact expanded-type report must match the local rooted closure.
These gates are automated minimum requirements, not a replacement for semantic
review of all manuscript obligations. Actual graph reachability is still pending.

`test_route_policy.py` uses explicitly **synthetic** small graphs to show the gate
rejects missing first/tail, hidden axioms via all three edge types, unresolved
structural support, old endpoint use, unsafe/partial and hidden theorem values.
These unit tests are not evidence about the actual final proof closure. They
also reject each required mechanism when present only as an unrelated aggregate
field. `test_controls_runner.py` checks immutable manifests, namespace overlays,
and snapshot baseline/scanner identity without executing any Lean or heavy job.

## Mandatory final frozen rerun

A source manifest is a JSON object `{"files": {"campaign/relative/path": "sha256", ...}}`
(with paths relative to this campaign, without a literal `campaign/` prefix).
Values may instead be `{"sha256":"...","size":123}` as in SOURCE_MANIFEST.json.
It must include all HT22 `.lean` source and roots, all control fixtures/scripts,
the nested `IsingBulk/HT22.lean` aggregate, exact HT22 config/toolchain/lockfile,
the protected RootWalker scanner, and the coordinator's complete protected-source
inventory. Generated runtime drivers and reports are excluded from source freeze;
their hashes belong to run receipts. The manifest itself is pinned before work,
so changing both it and its source cannot evade the after-check.
The runner checks it before and after execution and rejects missing control or
HT22 source inputs. Graphs must come from the identical frozen source and exact
new clean build; the external heavy-job receipt must establish that provenance.
The controls runner records graph hashes but does not manufacture provenance.

```sh
python3 verification_controls/run_controls.py --phase final --no-deps \
  --lean "$PINNED_LEAN" --lean-path "$CLEAN_LEAN_PATH" \
  --frozen-manifest /path/frozen-sources.json \
  --final-root IsingBulk.HT22.ht22_full_target \
  --final-graph-base /path/final --bypass-graph-base /path/bypass
```

Portable mode requires only existing library directories in `CLEAN_LEAN_PATH`.
It builds the three controls into a shallow, read-only-linked namespace overlay,
never modifying the clean build or borrowed cache. The complete final positive
and negative diagnostics, all 13 named axiom reports, input/source/report/binary
hashes, and synthetic test receipts are retained. Expected negative exits must
be exactly 1 with the intended diagnostic, never a crash or prerequisite failure.

For a snapshot without `.git`, `make_graph_driver.py` accepts
`--protected-baseline PROTECTED_BASELINE.json`, or finds that file at the campaign
root. It verifies the pinned commit, scanner SHA256 and Git blob identity.
Generated drivers enable complete proof printing, maxRecDepth=100000 and
maxHeartbeats=0; generation does not run the scanner. Before executing the bypass
driver, the clean build must include its protected fixture-only dependency
`IsingBulk.HT.Final.FullNaturalBoundary`. This does not authorize use of that
endpoint in the production proof, which remains a policy rejection.

Final controls are not a substitute for the separate strict source-clean build,
fresh official kernel replay, protected-source identity checks, exact expanded
scope review, and three independently sealed full-scope adversarial audits.
