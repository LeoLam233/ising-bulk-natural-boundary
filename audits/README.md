# Reading the historical audit records

These files are historical AI-generated or AI-assisted audit, receiver and editorial records supplied in this project. None is human peer review or current proof certification. Labels such as `PASS`, `CLOSED` or `SURVIVES` report the stated result of a particular check; they do not upgrade another version. The words `external` and `first_auditor` identify a receiving sequence or a separate AI session, not an independent human referee.

All existing audit views and the version ledger are preserved byte-for-byte from rc1. Earlier transformations used to create those public views remain documented in [VIEW_MANIFEST.json](../provenance/VIEW_MANIFEST.json); this index does not turn a derived view into an untouched original. Input identity and limitations must be read in the individual record; where a hash was absent, a version label alone is not a byte-identity certificate. Dates below come from explicit text, not filesystem timestamps.

| File | Explicit record date | Input / subject version | Record type |
|---|---|---|---|
| [v2_a1v2_reassessment.md](views/v2_a1v2_reassessment.md) | Not separately dated in this view | v2 | AI-assisted receiver / editorial record |
| [v2_external_reassessment.md](views/v2_external_reassessment.md) | 2026-09-24 | v2 | AI-assisted receiver / editorial record |
| [v2_two_audits_comparison.md](views/v2_two_audits_comparison.md) | Not separately dated in this view | v2 | AI-assisted receiver / editorial record |
| [v3_complex_disk_reassessment.md](views/v3_complex_disk_reassessment.md) | Not separately dated in this view | v3 | AI-assisted receiver / editorial record |
| [v4_glue_reassessment.md](views/v4_glue_reassessment.md) | Not separately dated in this view | v4 | AI-assisted receiver / editorial record |
| [v5_freeform_reassessment.md](views/v5_freeform_reassessment.md) | 2026-09-28 | v5 | AI-assisted receiver / editorial record |
| [v6_reassessment.md](views/v6_reassessment.md) | 2026-09-28 | v6 | AI-assisted receiver / editorial record |
| [v7_a1v2_auditor.md](views/v7_a1v2_auditor.md) | Not separately dated in this view | v7 | AI audit report |
| [v7_a1v2_receiver.md](views/v7_a1v2_receiver.md) | 2026-09-28 | v7 | AI-assisted receiver / editorial record |
| [v7_additional_auditor.md](views/v7_additional_auditor.md) | Not separately dated in this view | v7 | AI audit report |
| [v7_additional_receiver.md](views/v7_additional_receiver.md) | 2026-09-28 | v7 | AI-assisted receiver / editorial record |
| [v7_first_auditor.md](views/v7_first_auditor.md) | Not separately dated in this view | v7 | AI audit report |
| [v7_first_matrix.md](views/v7_first_matrix.md) | Not separately dated in this view | v7 | AI audit report |
| [v7_first_receipt.md](views/v7_first_receipt.md) | 2026-09-28 | v7 | AI-assisted receiver / editorial record |
| [v8_review_scope.md](views/v8_review_scope.md) | 2026-09-28 | v8 | AI-assisted receiver / editorial record |
| [v8_revision_notes.md](views/v8_revision_notes.md) | 2026-09-28 | v8 | AI-assisted receiver / editorial record |

The [version ledger](VERSION_LEDGER.md) retains the repair history, including errors and incomplete checks. Its rc1 release-validation link and all other earlier version references are historical. The final public assembly is recorded in [FINAL_PUBLIC_VALIDATION.md](../release/FINAL_PUBLIC_VALIDATION.md). The earlier [RC2_VALIDATION.md](../release/RC2_VALIDATION.md) is preserved as a historical preparation record for its original input hashes. Reconstruction evidence is indexed in [reproduction/README.md](../reproduction/README.md).

Internal model/session names and skill labels in the evidence are reported descriptions, not independently verified identity, isolation or independence metadata. This index adds context without renaming files, modifying verdicts, inserting banners into old reports or removing failures.
