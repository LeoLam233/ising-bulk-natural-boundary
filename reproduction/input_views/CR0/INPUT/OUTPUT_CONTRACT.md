# Deliverables and freezing

Create a fresh sibling directory `RUN_OUTPUT/`, outside `INPUT/`. Keep the report, working calculations, self-written scripts, useful failed approaches, and actual outputs there. Do not write into the input tree. Use relative paths in shared records and omit credentials or unrelated personal/device information.

## Required files

1. **`RESULT.md`**: the exact target and outcome; a self-contained mathematical argument or delimited partial results; imported premises with source locations; the role of any computations; precise remaining gaps; and any relevant scope or access limitation. A restricted or conditional result must be labeled as such. English or Chinese is acceptable.
2. **`RUN_RECORD.json`**: use the schema below. Unknown observations remain `"unknown"`; do not guess model identities, runtime limits, timestamps, or technical isolation. Outcome labels are solver claims, not audit verdicts.
3. **`ACTION_LOG.jsonl`**: one JSON object per material read, tool action, computation, clarification, or access deviation. Each object has `time_utc`, `action`, `target`, `result`, and `access_class`. Allowed classes are `allowed_input`, `own_output`, `runtime`, and `deviation`. Disclose logging gaps or retrospective entries. This is a concise evidence/access log, not a request for private internal reasoning.

Optional supporting files include a TeX proof, programs, seeds, exact or numerical outputs, dependency versions, and an environment-provided visible action transcript. A result with no computation is acceptable if that is recorded. Do not include installed packages, unrelated caches, or other projects.

## Run record

Replace the explanatory placeholders with actual observations:

```json
{
  "run_id": "unique identifier for this attempt",
  "model_or_service": "reported identity or unknown",
  "started_utc": "ISO 8601 timestamp or unknown",
  "finished_utc": "ISO 8601 timestamp or unknown",
  "outcome": "PARTIAL",
  "scope": {
    "exterior_analyticity": "unresolved",
    "natural_boundary": "unresolved"
  },
  "input_verification": "performed with actual result, or not_performed with reason",
  "isolation": {
    "network": "observed enforcement or unknown",
    "filesystem": "observed enforcement or unknown",
    "memory_and_context": "observed setup or unknown"
  },
  "prior_exposure": "recognized material, none known, or unknown",
  "comparison_material_seen_before_freeze": false,
  "deviations": [],
  "logging_limitations": "actual limitations or none known",
  "remaining_gaps": ["precise mathematical gaps"],
  "termination_reason": "completed argument, actual resource limit, input obstacle, or precise mathematical impasse",
  "resource_limits": "observed limits or unknown"
}
```

The two scope entries use `proved`, `disproved`, or `unresolved`. `CLAIMED_PROOF` requires both full-scope entries to be `proved` and an empty remaining-gap list. `CLAIMED_DISPROOF` requires a claimed disproof of at least one full-scope target, not merely a failed proof strategy. `PARTIAL` preserves substantive unfinished work. `INPUT_BLOCKED` identifies an actual indispensable input/access obstacle; inability to find a proof is not missing input. These distinctions are self-reporting requirements, not a mathematical decision procedure.

`comparison_material_seen_before_freeze` accepts `true`, `false`, or `"unknown"`. An exposure does not prevent preservation of the work, but it prevents an unqualified claim of blindness.

If no live clock or contemporaneous logging was available, write `unknown` where needed and add a clearly labeled retrospective log entry. Never claim a log is complete merely because it exists.

## Freeze before any comparison

With an already installed Python 3.9 or later, run from `INPUT/`:

```text
python -B tools/packet_tools.py verify
python -B tools/packet_tools.py freeze --results ../RUN_OUTPUT --archive ../ISING_CR0_RUN_FROZEN.zip
```

Use a distinct archive name if one already exists. Stop editing `RUN_OUTPUT/` while freezing. The command verifies the input inventory, checks output structure, creates a new archive and `.sha256` receipt, and refuses to overwrite an existing archive or receipt. It reads only the specified input and result trees plus its ordinary runtime. It performs no mathematical verification and cannot certify isolation, honest logging, or a trusted timestamp.

Return all of:

- `ISING_CR0_RUN_FROZEN.zip` (or the distinct name actually chosen);
- its `.zip.sha256` receipt;
- a short handoff naming the run ID, claimed outcome, and any exposure or logging limitation.

The ZIP contains the required reports and all supporting output, a freeze record, and the input-manifest identity. Do not return only a summary or a PASS label.

If Python or file creation is unavailable, provide the complete required file contents and all supporting calculations to the operator without seeing comparison material. The operator can save and freeze those unchanged outputs. Record that this was operator-assisted; never fabricate tool output or a hash. If the PDF cannot be read, identify the exact missing/unreadable item. Do not silently fetch a replacement.

After freezing, preserve the archive and receipt. Any subsequent comparison, hint-assisted continuation, or correction belongs to a separately labeled phase and must not overwrite the first result.
