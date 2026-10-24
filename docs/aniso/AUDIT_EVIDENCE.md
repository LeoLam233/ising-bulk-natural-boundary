# Audit provenance and available evidence

The following are distinct records. Their reported `EXHAUSTED` outcomes describe completed adversarial investigations, not human peer review or a replacement for the publication gates.

| Record | Reported result and scope | Evidence identity/availability |
|---|---|---|
| Original ANISO mathematical manuscript | Three completed external adversarial mathematical investigations: two Pro and one Codex; all reported `EXHAUSTED` | Historical research manuscript and supplied handoff provenance; distinct from later C001 Lean audits |
| Dot C001 | Three internal independent Lean audits and frozen final source | C001 source authority is the exact inner-ZIP `project/lean/`, with 2,279 Lean/config files |
| Independent Codex C001 mathematical/Lean audit | `EXHAUSTED`; 36 successful build/audit/fresh-replay commands | Expected `ANISO_C001_EVIDENCE.zip`: 428,305,070 bytes; SHA-256 below. The handoff reports it saved in ChatGPT Library; this small handoff does not contain it. Actual archive bytes have not yet been recovered in this publication checkout. |
| Independent Pro C001 Lean audit | Reported `EXHAUSTED`; 18 successful gates for the same 2,279 frozen files | Its distinct 684.4 MB final archive was lost before durable storage. A checkpoint and historical final response survive according to the handoff. No substitute archive is represented as that missing evidence. |
| Current publication verification | Newly executed source/build/strict/closure/controls/fresh-replay gates on the integrated source, then merged commit | Exact run-specific local and Actions logs, source/runtime identities, exit codes, timings and SHA-256 receipts accompany the PR/release. They keep their own execution identity. |

Expected independent Codex evidence SHA-256:

```text
5c1ef7f28e70228cc33376d5fe62e2310e93e38acce438515635561a2f506c6e  ANISO_C001_EVIDENCE.zip
```

## Archive recovery and release policy

The original full Codex archive was not found by name in Downloads, the prior local audit output, or the local Linux search. The prior Windows audit-output directory is empty after a separately recorded cleanup. A surviving Linux `ANISO_C001_VAZKIL2_LINEAGE_EVIDENCE.zip` has a different size and hash and is not the requested Codex archive. The six `ANISO_C001_COMPLETE_PART_*` delivery ZIPs are also different artifacts.

Release assets must state whether the exact 428,305,070-byte Codex archive was recovered. Upload it only after checking the actual size and SHA-256. If unavailable, publish the verifiable source reproducer, manuscripts, source receipts and new execution receipts, and explicitly list the Codex archive as missing. The unavailable distinct Pro archive remains missing in either case. Neither recovery status changes the C001 mathematics.

Large evidence archives, transient logs and `.olean` outputs stay outside Git history. GitHub Release assets and Actions artifacts carry execution evidence; compact source/receipt manifests are sufficient in the source tree. The 30 compiler-generated partial execution helpers are inventoried outside the final theorem closure; no claim of a globally partial-free build is made.
