# Active links, validation routing and CI regression

Local checks completed:

- Current-tree Git-blob gate: 67 unchanged archived files, exactly 16 current TeX/PDF files, 3,507 unchanged lean/ files, all other protected base files unchanged except the bounded 46 navigation/routing edits.
- All changed live Markdown links resolve; root READMEs and four topic pages display the exact eight titles and direct PDF/TeX links. Complete old-to-new path inventory is retained.
- Direct invocation of scripts/verify_ht22_publication.py succeeds after migration. Its original core is unchanged after removing the four-line root resolver.
- scripts/verify_eight_papers.py --historical-checks succeeds. It reconstructs the exact old manuscript paths and old navigation, then runs the unchanged HT22 -> LT22 -> four/three/two-result validator chain. This is in addition to validating the actual current tree and archive against immutable base Git blobs.
- scripts/build_current_papers.py succeeds for all eight manuscripts, three passes each, outside the active/archived trees. Earlier independent builds and full PDF QA are recorded separately.
- All twelve workflow YAML files parse. Git diff whitespace validation uses cr-at-eol for pre-existing CRLF files. Existing formal workflow bodies are restored exactly in the historical hash-checking view.

The new editorial workflow runs current source/archive identity checks, the historical chain and all eight standalone TeX builds. The existing long formal publication workflows first run the same integrity gate; on this byte-identical editorial migration their large formal rebuild jobs are skipped. Workflow dispatch retains the full formal path. This is reuse of prior accepted artifacts after source identity checks, not a fresh kernel replay. No claim is made that skipped jobs recompiled the project.

The legacy root resolver uses a temporary exact historical source view. If an upstream .lake/packages cache is present, only that pinned upstream cache is linked into the view, never pre-existing project objects. The copied verifier cores and formal sources remain checked against original identities. The current archive and current candidates are never rebuilt in place.

Raw local receipts are EVIDENCE/MIGRATION_GATE.log, EVIDENCE/CURRENT_BUILD_REGRESSION.log and EVIDENCE/DIRECT_LEGACY_VALIDATOR.log. GitHub checks, PR and merge state are recorded separately in the publication receipt; local success is not a remote CI success claim.
