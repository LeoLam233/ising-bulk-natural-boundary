# Audit provenance and available evidence

The following are distinct records. Their reported `EXHAUSTED` outcomes describe completed adversarial investigations, not human peer review or a replacement for the publication gates.

| Record | Reported result and scope | Evidence identity/availability |
|---|---|---|
| Original ANISO mathematical manuscript | Three completed external adversarial mathematical investigations: two Pro and one Codex; all reported `EXHAUSTED` | Historical research manuscript and supplied handoff provenance; distinct from later C001 Lean audits |
| Dot C001 | Three internal independent Lean audits and frozen final source | C001 source authority is the exact inner-ZIP `project/lean/`, with 2,279 Lean/config files |
| Independent Codex C001 mathematical/Lean audit | `EXHAUSTED`; 36 successful build/audit/fresh-replay commands | `ANISO_C001_EVIDENCE.zip` recovered from ChatGPT Library: exactly 428,305,070 bytes with the required SHA-256. Every payload was read with CRC and SHA-256 verification; all 2,279 source hashes match the handoff. |
| Independent Pro C001 Lean audit | Reported `EXHAUSTED`; 18 successful gates for the same 2,279 frozen files | Its distinct 684.4 MB final archive was lost before durable storage. A checkpoint and historical final response survive according to the handoff. No substitute archive is represented as that missing evidence. |
| Current publication verification | Newly executed source/build/strict/closure/controls/fresh-replay gates on the integrated source, then merged commit | Exact run-specific local and Actions logs, source/runtime identities, exit codes, timings and SHA-256 receipts accompany the PR/release. They keep their own execution identity. |

Verified independent Codex evidence SHA-256:

```text
5c1ef7f28e70228cc33376d5fe62e2310e93e38acce438515635561a2f506c6e  ANISO_C001_EVIDENCE.zip
```

## Archive recovery and release policy

The original full Codex archive was retrieved through ChatGPT Library on 24 October 2026. The [recovery receipt](../../provenance/aniso/INDEPENDENT_CODEX_RECOVERY.json) binds its exact bytes and matches every frozen Lean/configuration source hash. The [complete payload verification receipt](../../provenance/aniso/INDEPENDENT_CODEX_PAYLOAD_VERIFICATION.json) confirms 3,421 manifest payloads plus the manifest itself, all CRCs and payload SHA-256 values, the 36-command execution matrix, and the archived verdict/report identity. The matrix's selected successes are distinct from the preserved interrupted or unsuccessful historical preparation/control attempts elsewhere in the archive.

The verified 428,305,070-byte Codex archive is prepared outside Git for the ANISO Release, with an independently checkable hash manifest and compact receipts. The distinct 684.4 MB Pro archive remains unavailable; its reported 18 gates are not relabeled as the Codex 36 gates. A surviving Linux `ANISO_C001_VAZKIL2_LINEAGE_EVIDENCE.zip` and the six original delivery parts have different identities. Recovery and publication of these records do not modify C001 mathematics.

Large evidence archives, transient logs and `.olean` outputs stay outside Git history. GitHub Release assets and Actions artifacts carry execution evidence; compact source/receipt manifests are sufficient in the source tree. The 30 compiler-generated partial execution helpers are inventoried outside the final theorem closure; no claim of a globally partial-free build is made.
