# Ising v0.2.1 post-audit remediation

This branch starts at immutable audited release `v0.2.0`, commit
`50ec73db799ba8f72dff802b4a6fecdc69b61932`, tree
`2babc765011d98a524c37494724b91ec8c451521`. The authoritative Opus verdict
was `PASS_WITH_NONBLOCKING_ISSUES`. This revision implements the targeted
R1–R7 remediation contract, with the same mathematical theorem content.
It does not publish a release or merge into main.

The verification gate rejects foreign `IsingBulk` and `Audit` namespaces
under dependency build outputs before environment-resolving checks, and
runs the project axiom audit through `lake -f lakefile.toml --no-cache build Audit`.
An unreadable dependency build directory fails closed; readable artifacts
behind an unlistable directory cannot silently escape the scan.
The production payload verifier requires `--expected-id` from its caller
and shares preflight's dependency HEAD, tracked-source and Lake-override checks.
The workflow's `ci/accepted_identity.json` pin is separate from `payload.json`,
but remains part of the same Git commit; no cryptographically external pin
is claimed.

`theorem_tail_with_summability` composes the existing
`actual_upper_tail_summable` and unchanged `theorem_tail`. FIRST now has an
exact public-root application and defining-module check. The narrow E3
control checks its non-Nickel guard, the selected order-2p Nickel point,
and the refutation of a guard-less comparison premise from FIRST.
E1/E2/E3 and positive physical coupling retain their audited scopes.

The focused production-verifier regressions are in
`lean/control_packet/continuation/run_remediation_controls.py`. The existing
toy/manifest controls remain recorded with their original bounded scope;
this revision does not turn them into a generic premise/body framework.
The source-facing off-path wrappers and all 106 off-path modules are preserved.
Ledger status means proved, and does not imply final endpoint reachability.

The manuscript PDF's `0.1-rc4` self-label identifies the frozen analytic
manuscript baseline. It is intentionally retained, separately from the Lean
release version. Neither the frozen manuscript nor the v0.2.0 tag/release
assets are changed by this branch. Internal Lean kernel verification and AI
audit evidence do not imply human peer review.

The first frozen candidate passed its local clean build and fresh kernel
replay. A subsequent targeted regression exposed silent skipping of an
unlistable dependency cache. The scanner was repaired, the candidate was
recommitted, and the final heavy validation was repeated for those corrected
bytes, as required by the contract's genuine-failure repair exception.
Exact candidate identities, before/after regression
logs, final validation results and remote CI status are reported separately
after execution, so historical v0.2.0 receipts are not assigned to new bytes.
Dependencies use the pinned official cache; binary/source correspondence
and the single Lean kernel remain trusted. No Mathlib source rebuild or
second kernel implementation is part of this remediation.
