# Output inventory and reproduction

The authoritative mathematical outcome is in `RESULT.md`; the claim and access record is in `RUN_RECORD.json`; the chronological evidence/access record is `ACTION_LOG.jsonl`. The freeze tool adds its own `FREEZE_RECORD.json` and the input-manifest identity to the archive. None of these administrative checks independently validates a mathematical proof or technical isolation.

## Preserve this phase

Do not rerun scripts in the preserved original output directory. They append logs and some write fixed output filenames. Reproduction or later comparison should use a **new, separately labeled working copy**, with the same structure:

```text
new_phase_workspace/
    INPUT/       # unchanged original packet input
    RUN_OUTPUT/  # working copy, not the frozen original
        code/
        evidence/
        pdf_views/
```

The mathematical scripts require only Python and the already installed NumPy/mpmath versions recorded in `evidence/self_checks.json`. Exact arithmetic scripts use the Python standard library. No network access or package installation is part of reproduction. The optional PDF rendering script uses the installed PyMuPDF version reported by its original log entries.

From the new workspace, the main evidence commands are:

```text
python -B RUN_OUTPUT/code/self_checks.py
python -B RUN_OUTPUT/code/refine_checks.py
python -B RUN_OUTPUT/code/exact_geometry.py
python -B RUN_OUTPUT/code/series_check.py
python -B RUN_OUTPUT/code/series_numeric_crosscheck.py
python -B RUN_OUTPUT/code/boundary_contour_check.py
```

Some original matrix calculations were run with `OPENBLAS_NUM_THREADS=1`. Their floating-point results may vary in the last digits across library builds. No rigorous interval bounds were computed. There are no random seeds: the test angles and parameter choices are fixed in the scripts.

`render_sources.py` and `read_source_pages.py` accept only the two supplied source base names and explicitly requested page numbers. The original packet's text files were navigation aids; authoritative PDF renders were inspected without OCR.

`finalize_record.py` records this particular phase's observations and actual verification output. It is not a generic new-run initializer and should not be used to copy this run's claims into another run. `preflight.py` checks output structure and syntax, not mathematical truth. The official packet freeze tool, not these self-written scripts, produces the final archive and its SHA-256 receipt.

## Supporting evidence

`input_verify_initial.txt` and `input_verify_prefreeze.txt` contain actual packet-tool outputs. `self_checks.json` contains the original numerical diagnostics, including the initially inadequate near-critical quadrature. `refined_checks.json` preserves the subsequent refinement separately. `exact_geometry.json` and `exact_series.json` contain exact finite arithmetic outputs. `series_numeric_crosscheck.json` and `boundary_contour_check.json` are additional floating-point checks. Matching `*_stdout.txt` files preserve actual stdout/stderr for the research programs.

The fixed-site continuation diagnostic deliberately follows the root continuously into a small local disk across the circle. It does not evaluate the full bulk susceptibility inside the unit circle.

## Logging provenance

Initial setup actions were logged retrospectively, with unknown exact times. `evidence/visible_action_index.json` is a retrospective index of visible tool actions through the first report audit; it supplements the initially grouped entries, but is not a system-generated access trace. The log is not a transcript of private reasoning. Later report-writing, review, verification, and freeze-intent actions are recorded in the main log. Successful freezing is evidenced by the official tool's archive record and displayed execution result; the frozen log is not edited afterward to append a success claim.

No complete environment-level transcript export was available. Ordinary runtime reads, internal image mirroring by the display tool, and unavoidable runtime caching were not independently traced. This limitation is not a claim that unobserved research access occurred; it is a limit on what the record can certify.
