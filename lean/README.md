# Ising bulk natural boundary: Lean formalization

This source formalizes the pinned manuscript's original form-factor chain and the internally proved absolute higher-even tail in Lean 4. The current Lean/post-audit release is [v0.2.1](https://github.com/LeoLam233/ising-bulk-natural-boundary/releases/tag/v0.2.1), published on 2026-10-07; the frozen analytic manuscript remains `v0.1-rc4`. The physical identification and published fixed-order smoothness interfaces remain explicit E1/E2/E3 premises.

Core declarations:

- `IsingBulk.First.theorem_first`: first-particle singular asymptotic and lower even orders.
- `IsingBulk.Final.theorem_tail_with_summability`: convergence of the exact higher-even derivative-norm sequence for every positive radial parameter, together with the unchanged TAIL little-o bound.
- `IsingBulk.Final.theorem_tail`: the literal infinite sum of norms of every permitted derivative of the higher even form factors is little-o of the first singular scale.
- `IsingBulk.Final.theorem_nb`: no local holomorphic continuation of the constructed exterior normalized bulk series through any unit-circle point, conditional on the explicit published fixed-order interface.
- `IsingBulk.Final.theorem_nb_physical`: physical germ identification and boundary nonextension, conditional on E1, E2, and the same fixed-order interface, with positive coupling.

The reachable axiom union is `propext`, `Classical.choice`, and `Quot.sound`. The formalization does not construct the infinite-volume probability measure or reprove the external physics publications.

## Reproduction and evidence scope

Lean 4.34.1, commit `5045d0056413266e57c625dcd7c365b10e377c52`, and all nine dependency revisions are frozen. There are 1,071 production subtree modules and the public root, totaling 1,072 production `.lean` files.

### Independently audited v0.2.0 baseline

The frozen v0.2.0 release received an independent adversarial Opus audit with verdict `PASS_WITH_NONBLOCKING_ISSUES` and no blocking or load-bearing mathematical defect. Its proof-critical payload ID was `bf9e537fb5a963000ab1a7f1aef969144ba8e3fc7780b5cf1b56cba1c4bf37b2`. Baseline evidence records a clean project build, 9,199 safe declaration/axiom checks, endpoint and positive/negative controls, and full `leanchecker --fresh --verbose IsingBulk` replay. The full acceptance workflow completed for v0.2.0 in run `37481273735`. These receipts and the three internal adversarial rounds are historical v0.2.0 evidence.

### Final v0.2.1 release validation

v0.2.1 completes targeted remediation of the v0.2.0 audit findings, including verification hardening and complete TAIL endpoint packaging. It does not change `IsingBulk.Final.theorem_nb` or `IsingBulk.Final.theorem_nb_physical`. Its final exact-commit validation is separate from the baseline independent audit; no independent re-audit of the entire v0.2.1 tree is claimed.

- Release commit: `de23d9475744fb4625666142d5a03b3d688195e6`
- Release tree: `c4f8dd4e81dba9e88e18dadfdb0778cf3771d1d2`
- Proof payload: `6989420e855e0c3d882ce51e302dbc6579890da81aa0fd866176bab583067715`
- Verification input ID: `99165310d8040d145faecdd2e9bb899f6db576e074049d357621b067b48ad0e2`
- Runtime ID: `6633dc8f4aec1108be34292fdac2f23c944ea00e1519e3e71d9f2b0c36e70780`

The exact v0.2.1 commit passed the clean full build, the project-wide axiom audit of 9,200 safe declarations with union exactly `propext`, `Classical.choice`, `Quot.sound`, all 14 endpoint checks, 13/13 targeted production regressions, 13/13 manifest controls, 6/6 Lean controls, and fresh `leanchecker --fresh --verbose IsingBulk` replay. Exact-commit [full CI run 37518976590](https://github.com/LeoLam233/ising-bulk-natural-boundary/actions/runs/37518976590) and [smoke CI run 37518976672](https://github.com/LeoLam233/ising-bulk-natural-boundary/actions/runs/37518976672) both completed with `SUCCESS`.

### Trust and publication boundaries

The supplied execution records and artifact hashes bind the validation under the documented trusted-operator/runtime/distribution assumptions. Cached dependency binary/source correspondence remains trusted; the build and fresh replay use the same Lean kernel implementation. Callers pass the expected proof ID explicitly to `ci/verify_payload.py`, and the accepted identities are recorded in `ci/accepted_identity.json`; this expected-ID pin is inside the Git commit, not cryptographically external to it.

E1/E2/E3 remain explicit external literature premises. This is still an AI-assisted candidate proof, and no independent human expert validation or peer review is claimed. The manuscript PDF self-label `0.1-rc4` records the frozen analytic baseline separately from the Lean release version. See [the remediation record](../REMEDIATION_v0.2.1.md) for the targeted post-audit scope.

Publication warning: `.github/workflows/release-v0.2.0.yml` and `lean/ci/prepare_release_assets.py` are historical **v0.2.0-specific** publication machinery, not a generic future-release publisher.
