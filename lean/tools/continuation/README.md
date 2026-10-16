# Current v0.3.0-rc1 verification gate

This Linux/WSL gate binds the exact candidate manuscript snapshot, every production
source, configuration/dependency pins, checking scripts, source map, coverage records
and actual runtime. The old launcher record is byte-preserved under
[history/v0.2.1](../../history/v0.2.1/tools/continuation/README.md).

Preflight is read-only except for an expressly requested new receipt. It checks
root coverage, forbidden constructs, source-map completeness, exact manuscript
blob/hash, nine clean tracked dependency trees and the runtime. It does not build.
Use the tools inside the chosen candidate; mixed-tree external drivers are rejected.

With --execute, final_gate requires a fresh source-only project with .lake/packages
as its only existing Lake entry. It never silently deletes previous build outputs.
It runs the full public-root build, project-wide Audit, 18 exact endpoint
type/origin/axiom checks, seven ordinary Lean controls, the unused-E3 negative
dependency control, and official leanchecker --fresh --verbose IsingBulk.
Every stage binds proof, verification and runtime IDs before and after execution.
Each has exact argv, stdout/stderr, exit status and Linux wait4 resource records.

The dependency namespace scanner rejects foreign IsingBulk/Audit artifacts before
environment-resolving stages, including unreadable caches. Lake uses explicit
-f lakefile.toml, exact binaries and a sanitized environment; local artifact caches
and inherited loader overrides are disabled. Runtime hashes bind the official
Lean implementation, not an independent second kernel. Cached dependency
binary/source correspondence remains trusted.

InternalRegularity traverses compiled types and proof bodies, rejects E3 and
published-transfer helpers in canonical dependencies, and requires the new
internal analytic route. The negative control puts an UNUSED E3 parameter on a
valid NB wrapper; the same traversal must reject it. Resource/import/timeout
failures do not count as successful negative controls.

run_manifest_controls.py and run_remediation_controls.py are separate bounded
verification regressions. The latter must run as an unprivileged Linux user for
its unlistable-cache test. Their generated results are not production imports.
No lake update is required. [Full commands](../../README.md).

Success is reported as CHECK_SEQUENCE_PASSED_NOT_AUDIT_ROUND. It records the
executed sequence, not mathematical source equivalence, human review, exhaustive
priority, or completion of the separately documented repository consistency audit.
