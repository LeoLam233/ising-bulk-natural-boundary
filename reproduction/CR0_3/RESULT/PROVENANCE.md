# Access, execution, and provenance

Run: `ISING-CR0-20260927-27b6b643611a`.

## Scope of inputs actually used

The uploaded archive was extracted into a fresh working root, with sibling `INPUT/` and `RUN_OUTPUT/` directories. `START_HERE.md` was read first after extraction, followed by the task, conventions, output contract, and reference instructions in the prescribed order. The manifest checker was actually run; its initial output is retained. The administrative tool and supplied source metadata were read. URLs and bibliography identifiers in the supplied documents were not followed.

The supplied TW2014v1 mechanical text was read in full, with further targeted rereads of the argument and appendices. BG2008v1 was read selectively: the definitions and introductory discussion, singularity evidence/conclusion, the relevant Landau cases in Appendix B, and Appendix E. The complete supplied PDF was available, but a claim to have read every line of all 54 pages is not made. Some broad console reads were truncated; the decisive definition and proof passages were reread in narrower ranges.

The original PDFs were accessed with installed PyMuPDF and rendered locally, without OCR. Retained renders are TW pages 2, 3, 8, 9, 10 and BG pages 2, 3, 4, 52, 53. Original image views inspected TW pages 2, 3, 8, 9, 10 and BG pages 2, 3, 52, 53. BG page 4 was rendered but not separately opened as an image. Rendered pages are copies of permitted input, not additional sources.

No search engine, web retrieval, connector, external mathematical source, other local research project, remote computation, prior conversation, project memory, external agent, or subagent was used. Ordinary existing mathematical knowledge was used. No task-specific prior solution, comparison artifact, or unsolicited hint was recognized or received before freezing. Inaccessible model training history is unknown and cannot be audited; this is not a claim of zero pretraining exposure to Ising mathematics.

## Disclosed deviations

General environment-provided PDF operating guidance (`PDF SKILL.md`) outside the input tree was read because of a service-level instruction. It concerned document operations, not Ising research. It was disclosed to the user immediately and logged. No links or research materials were accessed through that guidance. This access means an unqualified claim that literally every nonruntime file read was inside `INPUT/` or `RUN_OUTPUT/` would be false.

The initial archive-extraction invocation used Python without `-B` before the packet instruction had been read. It used only standard-library imports. Subsequent Python invocations used `-B`. The actual input verification found no changed or additional input files. This invocation deviation is logged retrospectively; no invented original timestamp is supplied.

## What isolation was and was not observed

No network operation was invoked in this run. Technical network blocking was not tested or established. The offline protocol was followed behaviorally; it is **not** represented as a firewall or air-gap certificate.

No task-only filesystem confinement was established. Tools could read the task files and the disclosed generic guidance; installed interpreters and libraries necessarily use their runtime files. No operating-system trace of every file open or attempted access was collected. No unrelated filesystem search was performed.

The visible conversation was the present fresh task. No other chat or project memory was requested, and no agent delegation was used. The service's internal context and training mechanisms are not independently auditable from this run. These limits do not imply that comparison material was actually accessed; they limit the strength of an isolation claim.

## Runtime, clock, and logging limits

Installed Python, mpmath, SymPy, NumPy, and PyMuPDF were used. No packages or data were downloaded or installed. `ENVIRONMENT.json` records versions actually read from the running modules. The research scripts are deterministic and use no random seeds.

Tools used for task execution were local command execution and local image viewing. The mathematical programs, their final sources, their actual JSON results, and captured standard output are retained. Utility operations such as extraction, inspection, and document writing used inline shell/Python commands; the action log summarizes them rather than providing a byte-for-byte export of every shell invocation. A full service/tool transcript was not exported. Earlier versions of the two scripts tidied in final review are not separately versioned; the small changes and actual reruns are logged, and the final executed versions are retained.

The log began after initial extraction and required reads. Those entries are explicitly retrospective, with the logging timestamp rather than a guessed event timestamp. Some closely related later reads/reviews are grouped or recorded shortly after the action. The exact task-start time is `unknown`. The log is an evidence/access record, not a complete forensic monitor and not a private reasoning transcript.

The runtime UTC clock observed during this task reports September 27, 2026; the service's stated conversation calendar date is September 28, 2026. No external clock was contacted to resolve the discrepancy. Run identifiers and log timestamps preserve the actual observed clock values, and are not trusted timestamp attestations. `finished_utc` is the observed time of final record preparation; the archive's freeze record separately reports the tool's observed freeze time.

No out-of-memory error, failed interpreter, failed required input read, or numerical timeout terminated the research. CPU, memory, context and service-wide hard limits were not independently measured. The stopping reason is the explicit remaining mathematical boundary-tail problem, not a fabricated runtime cap or the historical status of the problem.

## Record organization and freezing

`RESULT.md` is the principal report; `LOCAL_SADDLE.md` gives the detailed arithmetic, normalized cutoff bridge, saddle proof, and restricted local tail. `LOCAL_TAIL_INSERT.md` is the retained working insertion fragment; the integrated appendix is authoritative. `SELF_CHECK.md` separates analytical and computational coverage. The JSON diagnostics contain the actual finite results, not a universal mathematical verdict.

Before invoking freeze, the run record and action log are finalized and the actual input verification is repeated. The last in-tree freeze event records **invocation intent**, not an outcome that had not yet occurred. No edit is made to `RUN_OUTPUT/` during or after successful freezing. The administrative tool's returned status, the archive's `FREEZE_RECORD.json`, and its generated SHA-256 receipt are the evidence of actual freezing. The tool verifies inventory and output structure only, not mathematical correctness, isolation, log completeness, or a trusted time.

No comparison material is to be accepted between report preparation and freeze. This stage ends upon successful freeze. Any later comparison or correction must be a separate stage without overwriting the original archive or receipt.
