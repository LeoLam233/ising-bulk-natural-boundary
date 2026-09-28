# Reproduction and archive contents

This archive preserves one phase. **Do not run a program against the preserved original output directory**, because the programs save JSON and append to its action log. Reproduction should use a separate copy labeled as an audit/reproduction phase.

The freeze archive has `RESULT/` containing this run's output, plus `FREEZE_RECORD.json` and `INPUT_MANIFEST.sha256`. It does not need to redistribute the complete source PDFs: the original authorized `INPUT/` packet supplies them. The page renders in `source_views/` are the selected local audit aids actually generated during this run.

The mathematical files are `RESULT.md`, `BOUNDARY_DERIVATION.md`, and `METHOD_LIMITS.md`. The access and administrative records are `RUN_RECORD.json`, `ACTION_LOG.jsonl`, `ACCESS_LIMITATIONS.md`, `setup.json`, the verification outputs, and this file. `calculations/` contains actual saved JSON and standard-output captures, including an initial formatting preflight that found a subsequently corrected TeX typo.

## Installed dependencies actually used

Python standard library, mpmath, SymPy, and PyMuPDF (`fitz`). The observed versions are saved in `dependencies.json`. No package installation was performed. The calculation scripts do not use a network or external data source.

## Re-run the research calculations in a separate copy

From the copied result directory:

```text
python -B code/check_exterior.py
python -B code/check_cyclotomic.py
python -B code/check_lowtemp.py
python -B code/check_chi2.py
python -B code/check_local_model.py
python -B code/check_residues.py
```

Each script computes its output root from its own location. All six write under that copy's `calculations/` and append a new action to that copy's `ACTION_LOG.jsonl`. Floating-point outputs are diagnostics, not interval certificates. The two exact-arithmetic programs and symbolic residue identities have the finite scopes stated in their files.

`source_access.py` accesses only the two fixed source filenames in a sibling `INPUT/references/` tree. For example:

```text
python -B code/source_access.py text TW 7 8 9
python -B code/source_access.py render BG 2 3
```

Rendering needs PyMuPDF. The original PDFs, rather than their text extractions or the numerical checks, determine the source formulas.

`preflight.py` parses local output JSON and Python source and checks document formatting. It can also call the supplied packet tool's structural validator if the sibling `INPUT/` exists. Such checks are not mathematical validation. `prepare_record.py` is administrative and was used to write the final observed record; it is not a mathematical experiment and should not be used to relabel a reproduction as this independent run.

## Source-access and command-record limits

The initial archive extraction and early instruction reads were performed with short interpreter/shell commands before the action log was initialized. They were retrospectively recorded in the log; a byte-exact independent shell transcript was not produced. All research calculation programs actually used are preserved as files. Some later administrative writes and log appends were also issued as short visible interpreter/shell commands; the log is not an exhaustive syscall trace.

The standard-output captures correspond to the actual original executions. The scripts' JSON files contain the authoritative saved calculation results. A future execution will have different timestamps in its own log and may produce different last floating-point digits with different library versions; it must not overwrite the frozen original.
