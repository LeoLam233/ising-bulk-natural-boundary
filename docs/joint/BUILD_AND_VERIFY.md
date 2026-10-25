# Execute JOINT and all three regressions

Use Lean 4.34.1 (`5045d0056413266e57c625dcd7c365b10e377c52`) and the unchanged lockfile, including Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`.

```bash
python3 scripts/verify_four_result_publication.py
cd lean
lake -f lakefile.joint.toml exe cache get
cd ..
python3 scripts/prepare_three_proof_checkout.py --output /absolute/new/source-joint
python3 /absolute/new/source-joint/scripts/run_four_result_verification.py --only joint --output /absolute/new/receipts-joint
```

Repeat fresh source preparation and the runner with `--only lt`, `--only ht`, and `--only aniso`, using distinct checkout/output directories. Share only pinned upstream packages. The runner rejects existing candidate objects, records every actual compiler action and verifies that all resulting project objects came from that run's own sources and outputs. `-H` alone is not treated as a cache disablement.

Each phase executes `lake -f CONFIG -R -H build ROOT AUDIT`, a direct `lean -j1 -DwarningAsError=true AUDIT.lean`, a separate `leanchecker --fresh --verbose ROOT`, a type/value/constructor closure, an injected-axiom rejection and a physical-contract type-mismatch rejection. JOINT additionally executes the twelve calibrated frozen controls (two acceptances, ten intended rejections), prints the actual theorem/physical/eleven-field/seven-core structures and runs the publication closure. ANISO retains `AuditAnisotropicClosure.lean` and its three positive control modules. All original LT/HT/ANISO workflows and verifiers remain unchanged.

| Phase | CONFIG | ROOT | AUDIT |
|---|---|---|---|
| JOINT | `lakefile.joint.toml` | `IsingBulkJoint` | `AuditJoint` |
| LT | `lakefile.toml` | `IsingBulk` | `Audit` |
| HT | `lakefile.ht.toml` | `IsingBulkHT` | `AuditHT` |
| ANISO | `lakefile.anisotropic.toml` | `IsingBulkAnisotropic` | `AuditAnisotropic` |

The new [four-result workflow](../../.github/workflows/four-result-publication-acceptance.yml) and reusable [JOINT workflow](../../.github/workflows/joint-lean-acceptance.yml) run these gates on the actual PR merge checkout and merged main. The published compressed receipts include raw commands, identities, stdout/stderr, timings, per-object provenance and summary. `scripts/verify_joint_execution_receipts.py` validates those executable records; rerunning the gates is a separate new execution.
