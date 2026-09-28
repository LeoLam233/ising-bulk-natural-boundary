# Access, environment, and logging limitations

Run `ISING-CR0-20260927-ba3792d2458a`.

## Observed actions

The uploaded archive was inspected for safe extraction paths and extracted into a work directory. `INPUT/START_HERE.md` was read first; `TASK.md`, `CONVENTIONS.md`, `OUTPUT_CONTRACT.md`, and `references/README.md` followed in the stated order. An output directory was created alongside `INPUT/`. The supplied verification tool was run from `INPUT/` with `python -B` and returned `INPUT_INTEGRITY_OK`, checking 13 files. Its actual standard output and return code are saved in `input_verification.txt`.

Research reads were limited to the supplied original PDFs, their supplied text extractions, and the packet's instructions. Source-paper links and bibliographies were not opened. Programs for the calculations were written under `RUN_OUTPUT/code/`; their actual outputs are included. Installed Python, mpmath, SymPy, and PyMuPDF were used. No packages were installed and no installed library sources, examples, caches, or unrelated research directories were searched for a solution.

## Administrative exception

The system required reading a local PDF-operation skill file outside the packet. That file was read once. It contained procedural advice about PDF rendering, inspection, and editing; no Ising mathematics or other research input was encountered there. The access was immediately disclosed to the user and is recorded conservatively with access class `deviation`. No additional outside skill files or examples were opened. Local primary-PDF rendering was then done with a self-written script and the installed PyMuPDF runtime.

This exception means the run should not be described as literally having read no file whatsoever outside the packet and runtime. It did not supply a prior solution, intermediate Ising lemma, or comparison result.

## Offline instruction versus technical enforcement

No web, network-search, connector, remote-computation, or outside-agent tool was called. No network request was deliberately made from code. There was no test of whether a network request would be blocked, and no firewall or network namespace was inspected. Consequently the **technical enforcement of network isolation is unknown**. An instruction not to go online is not a proof that networking was disabled.

The tools allowed filesystem access beyond the packet; the administrative exception demonstrates that the process was not proven to be confined to these directories. Only packet material, own outputs, necessary installed runtime files, and that exception were deliberately read. No OS-level filesystem isolation or syscall audit was established. Ordinary internal library cache behavior was not monitored and was not treated as mathematical evidence.

No other conversation, project memory, account-backed data, saved solution, or external agent was accessed. The current visible context contains this task and platform instructions; independent fresh-context initialization, backend state, model training contents, and any platform-side hidden mechanisms are not independently attestable. No prior complete solution of this task was recognized. General pretrained mathematical/Ising background may exist; no specialized remembered Ising result absent from the supplied sources was used as a decisive premise.

## Clock and resource observations

The first live OS UTC observation was `2026-09-27T18:28:56.042765+00:00`. Some extraction and setup reading had already occurred, so the exact start time is recorded as `unknown`. The conversational current-date instruction stated 28 September 2026. These disagree. Log timestamps are the actual observed, untrusted OS clock at log-append time; there was no network clock check and no trusted timestamp claim.

No enforced total wall-clock, memory, or token quota was measured or queried. The research did not end because an observed resource timeout made a pending finite calculation impossible. Long tool output sometimes displayed ellipses, notably the first attempted whole TW text display and portions of the BG pp. 42–45 display. The decisive pages and equations were subsequently read in smaller selections and, where load-bearing formulas were involved, checked in the original local PDF renders. Omitted text is not claimed to have been fully read merely because a command requested it.

## Evidence-log limitations

`ACTION_LOG.jsonl` is a concise manually maintained record, not a complete operating-system trace. The initial extraction and ordered instruction reads were recorded retrospectively after the live clock became available. Some source-view inspections, code creations, derivation milestones, and progress messages were logged after the corresponding visible action, and some were initially grouped by tool action. Retrospective additions are labeled as such. The timestamps generally mean log-entry creation, not independently measured execution start/finish.

The log does not contain a private reasoning transcript. It records material accesses, computations, derivations, writing, verification, known deviations, and freezing intent/results as far as the workflow permits. It cannot certify that unobserved platform behavior did not occur. The full source PDFs remain authoritative; rendered page files are only audit aids.

The run used no comparison paper, alternate solution, hint, or feedback before freezing. Source authors' own historical background and references, already present in the authorized packet, were read only as source material.

## Freeze semantics

The freeze command is to be logged **before** invocation as an intended next administrative action. No output is edited while freezing or afterward. Its actual tool response and the embedded `FREEZE_RECORD.json` establish whether the command succeeded; the pre-invocation log does not pretend to be an execution receipt. The archive's receipt is generated by the supplied tool, not invented by the solver. The tool checks input hashes and snapshots output structure; it does not validate mathematics, isolation, honesty, or a trusted timestamp.
