# HT 1747 monorepo integration — publication checklist

This staging branch is based on the existing LT `main` commit `2cf997226db314ad52fa40a2ecda5439542606bf`. Its purpose is to publish the already audited HT Lean development **beside**, not inside, the LT proof chain.

## Source integration

- [x] Exact matching LT foundation established: `lean/IsingBulk` Git tree `ca47fde26285028603c7e87a9893aad31933b526`, unchanged in the frozen HT project.
- [x] Offline source overlay constructed and checked against the complete HT freeze: 397 HT-namespace modules, 35 new reusable proof modules, `IsingBulkHT.lean`, `AuditHT.lean`, and additive `lakefile.ht.toml`.
- [x] Rechecked the final transport archive: all 447 overlay payloads match their SHA-256 manifest; all 435 Lean overlay files are byte-identical to the independent Codex audit's frozen source project. Archive SHA-256: `6ee554b405591d182f437e5909843a44a2ad48111da59075176b8bbf665d180d`.
- [ ] Apply byte-identical overlay in this branch without modifying existing LT proof files, `IsingBulk.lean`, `Audit.lean`, `lakefile.toml`, `lake-manifest.json`, or Lean toolchain.
- [ ] Add HT-1.0 frozen TeX/PDF at `archive/manuscripts/pre-eight-2026-10-30/paper/ht/frozen/`; index LT and HT manuscripts separately.
- [ ] Add HT-only build/verification workflow and independent, bilingual LT/HT landing pages.

## Validation after source push

- [ ] Verify old LT tree byte identity and full frozen HT project source identity.
- [ ] Re-run `lake -f lakefile.toml build IsingBulk Audit` (LT regression).
- [ ] HT: `lake -f lakefile.ht.toml -R -H build IsingBulkHT AuditHT`.
- [ ] HT: strict `AuditHT.lean` check and official `leanchecker --fresh --verbose IsingBulkHT`.
- [ ] Review actual final theorem type, external physical input, no reachable HT project axioms, and absence of the LT final natural-boundary theorem in the HT transitive dependency closure.
- [ ] Review the staging PR file diff; preserve LT historical tags, release assets and versioned audit records.

## Publication metadata and release

- [x] User authorized MIT licensing for newly introduced HT Lean source files and CC BY 4.0 for author-created manuscript/documentation.
- [ ] Prepare the separate HT publication edition and confirm final author metadata; retain the audited frozen PDF/TeX bytes. User approved the LT-consistent attribution and licensing policy.
- [ ] Review version-specific citation and authorship metadata.
- [ ] Merge only after the final combined-checkout acceptance, then publish a distinct HT-scoped tag and attach the original independent audit receipts as versioned GitHub Release assets. Do not check large audit ZIPs or compiled .olean files into the production tree.

## Repository boundaries

```text
archive/manuscripts/pre-eight-2026-10-30/paper/next/                      LT manuscript, existing path retained
archive/manuscripts/pre-eight-2026-10-30/paper/ht/frozen/                 HT manuscript, audited bytes retained
lean/IsingBulk/{Algebra,...}/    existing LT/shared mathematical base
lean/IsingBulk/First/Regular*    34 new HT-required reusable proof modules
lean/IsingBulk/Analysis/BranchUpper.lean  1 reusable module
lean/IsingBulk/HT/              HT mathematical proof, 396 modules
lean/IsingBulk/HT.lean          HT sub-root
lean/IsingBulkHT.lean           HT build entry
lean/AuditHT.lean               HT audit entry
lean/lakefile.ht.toml            HT additive Lake configuration
docs/lt/ and docs/ht/           separate reader-facing guides
```

Do not rename shared Lean modules during the first HT release: their verified source hashes and transitive dependencies are frozen. The two mathematical end results and their physical observables are separately documented, and the HT endpoint does **not** invoke the LT final natural-boundary theorem.

The integration archive is prepared separately, with `integrate_ht1747.py` and SHA-256 verification. Its role is to transport exact frozen bytes into this branch; this checklist commit does not itself publish HT proof sources.

## Current publication state (2026-10-21)

Navigation and bilingual landing pages are committed to this **draft** PR; the audited HT source overlay is prepared but has **not** been pushed, so links from the landing page to HT source/manuscript remain pending. The combined checkout has **not** passed live GitHub Actions or a new source-integrated build yet. Do not merge or label this branch a published proof until the `integrate_ht1747.py` overlay is pushed and the listed checks are green. The provided `HT_1747_RUN_IN_CODEX_OR_LOCAL.sh` drives cloning, checks, tests, commit and push from a host with GitHub network access and Lean 4.34.1. Preserve the current LT base and its tags.
