The post-audit gate rejects foreign `IsingBulk`/`Audit` namespaces anywhere under dependency build outputs before every environment-resolving stage. The project axiom audit runs as the declared Lake target `Audit`, whose per-module mappings bind project imports. Dependency source integrity uses the same checks as the production payload verifier.

# Current launch policy

The runner binds Lake to `-f lakefile.toml`, refuses an alternative root configuration, and rejects untracked overriding dependency configurations. It invokes pinned Lean and leanchecker by absolute paths. Subprocess environments clear inherited Lean/Lake and dynamic-loader overrides; the local artifact cache is explicitly disabled, the system cache directory is empty, and the system Lake configuration is `/dev/null` (empty input).

The generated endpoint fixture includes the literal `PositiveInterfaces.lean` proposition applications as well as names/origins/axioms. A separate bounded mathematical-control stage records proof, verification and runtime identities before and after execution. Resource/import failures do not count as successful mathematical negative controls.

These repairs change verification infrastructure, not mathematical payload. Current-round heavy evidence used equivalent explicitly guarded manual commands; no additional scientific build or replay is implied. The previous generic wrapper is not retrospectively certified by that manual run.

# Linux candidate verification preparation

These files prepare a reviewable Linux/WSL verification sequence. They do not
establish a final candidate gate or complete an adversarial audit round.
The user must decide the execution location before the heavy sequence starts.
No remote push, workflow execution, download, `lake update`, cache removal,
dependency repair, or system configuration change is performed by these tools.

## Files and evidence boundaries

- `endpoint_contract.json` records the frozen compiler/configuration/dependency
  pins and fourteen actual bridge/final declaration names, their source modules,
  and manuscript source labels. It preserves the conditional theorem alongside
  the tail-discharged endpoints; it does not certify statement equivalence.
- `source_references.json` maps every semicolon-separated ledger token to an
  actual declaration or production module. Preflight checks complete, unique
  token coverage, safe target names and module-file existence. The actual Audit
  output must contain every mapped declaration before that stage is accepted.
- `preflight.py` reads project sources, the manuscript, the claim ledger, frozen
  configuration, dependency Git revisions/clean tracked status, and the chosen
  runtime. Its only Lean/Lake invocations are `--version`. It checks root
  coverage and local source availability for imports, scans executable source
  text for the existing forbidden constructs, and checks declaration names and
  source-map entries lexically. Compiled type/origin checks remain separate.
- `final_gate.py` defaults to a plan. With explicit execution enabled, it runs
  a clean project build, `Audit.lean`, generated exact endpoint checks, six
  bounded mathematical controls, and the official `leanchecker --fresh --verbose IsingBulk`, in that order. Each stage
  has independent stdout/stderr, exact argv, exit status, elapsed time and
  Linux `wait4` RSS/CPU measurements. RSS is the maximum child/descendant RSS,
  not a sum of all simultaneously resident processes.

`Audit.lean` traverses axiom dependencies. It is not kernel proof replay.
`leanchecker --fresh` replays the final root's transitive safe, non-partial
constants into an empty environment through the pinned Lean kernel; it is not
an independent checker implementation. Its CLI does not implement `--help`
or `--version`; do not use those flags as a harmless checker preflight.

## Candidate identities

`PROOF_CRITICAL_PAYLOAD_ID` binds every production Lean source, the root imports,
the frozen configuration, source metadata/manuscript, compiler commit, and nine
dependency revisions/URLs. It deliberately excludes documentation and checking
scripts. `VERIFICATION_INPUT_ID` separately binds the actual scripts/contract,
`Audit.lean`, ledger and correspondence records, the two continuation scope/
source-correspondence documents, and authored `control_packet/continuation`
scripts and fixtures. Generated control results, logs, and Python bytecode are
excluded. `RUNTIME_ID` binds the actual
Lean/Lake/checker executables, their required Lean shared libraries, and version
outputs. None includes machine-specific absolute paths.

The execution wrapper compares all three identities against a preflight receipt
and rechecks them before and after every stage. Verification-source edits do
not change the mathematical payload ID. They require a refreshed preflight
receipt for this wrapper. This wrapper does not define a full release-tree ID
or decide how unrelated evidence should be invalidated.

## Preparation and cheap preflight

Use the actual chosen Linux runtime path, not a path copied from dot. The
official matching release is Lean 4.34.1, commit
`5045d0056413266e57c625dcd7c365b10e377c52`.
Python 3.10+, Git and the complete matching Lean runtime are required.

For the eventual heavy run, prepare a separate fresh source-only candidate
directory containing the reviewed source/configuration/records and these tools.
Supply the nine already-present exact pinned dependency trees under
`.lake/packages`; dependency caches may be retained. The wrapper does not copy,
install, download, delete or move anything to prepare that directory. It refuses
any other existing project `.lake` entry and stale source-sibling `.olean`
outputs. Keep generated receipts outside `tools/continuation`.

From the candidate project directory, these are the cheap commands:

```bash
python3 -I tools/continuation/preflight.py \
  --lean-bin "$LEAN_BIN" --output "$PREFLIGHT_RECEIPT"

python3 -I tools/continuation/final_gate.py --lean-bin "$LEAN_BIN"
```

Set `LEAN_BIN` and `PREFLIGHT_RECEIPT` to actual local paths first. The receipt
path must be new, with an existing parent directory. Default project location
is inferred from these scripts; `--project` can select an explicit candidate.
Do not run the preflight concurrently with proof/source changes.

Review the proof ID, verification ID, runtime ID, complete source hashes,
endpoint list, runtime identity, source correspondence and execution plan.
The historical count 9,125 is not hard-coded: the new candidate has additional
declarations, so its successful Audit reports the actual count.

## Heavy command: only after the location and run are authorized

```bash
python3 -I tools/continuation/final_gate.py \
  --lean-bin "$LEAN_BIN" \
  --approved-preflight "$PREFLIGHT_RECEIPT" \
  --logs "$NEW_LOG_DIRECTORY" --threads 1 --execute
```

The log directory must not already exist. The wrapper preserves all successful
and failed stages. It stops after a nonzero exit, missing success marker, or
changed input. A failed run is not silently resumed; retain its logs and prepare
a fresh candidate/run as appropriate to the actual failure. No new runtime or
memory setting is selected automatically. Check available WSL/Linux memory and
storage before approving the heavy run.

The execution sequence is precisely the following (`PINNED_BIN` is the
verified absolute runtime directory; `PYTHON` is the current interpreter):

```text
PINNED_BIN/lake -f lakefile.toml --no-cache build IsingBulk
PINNED_BIN/lake -f lakefile.toml --no-cache build Audit
PINNED_BIN/lake -f lakefile.toml env PINNED_BIN/lean -DwarningAsError=true <new-log-directory>/EndpointCheck.lean
PYTHON control_packet/continuation/run_lean_controls.py --lean-bin-dir PINNED_BIN
PINNED_BIN/lake -f lakefile.toml env PINNED_BIN/leanchecker --fresh --verbose IsingBulk
```

The generated endpoint fixture reads its literal interface assertions from the
explicitly selected `--project`. Run the tools copied inside that selected
candidate; external mixed-tree driver installations are rejected so controls
cannot import a different unbound helper set. `--project` selects that same
candidate when invoking its script from another working directory.

The source-only endpoint fixture logs exact compiled theorem types, checks
module origin and safe-theorem status, and rejects reachable axioms outside
`propext`, `Classical.choice`, `Quot.sound`. Its exact source is preserved in the
run directory. Lean compilation errors fail that stage rather than being
treated as evidence.

Success is reported as `CHECK_SEQUENCE_PASSED_NOT_AUDIT_ROUND`. This records only
the listed build, axiom, typed-endpoint, six mathematical-control and replay
checks. Broader mutation attacks, semantic/source review, any authorized CI
work, and formal audit adjudication remain separate; the script does not claim
completion of those activities.

Imported-object/source provenance and exact current-run cache/runtime hash binding require separate evidence; this wrapper does not by itself certify that association or finish R1.
