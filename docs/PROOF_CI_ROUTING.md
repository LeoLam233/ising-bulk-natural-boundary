# Scope-aware proof CI (26 October 2026)

The dedicated [LT22 Preferred22 workflow](../.github/workflows/lt22-lean-acceptance.yml) runs on PRs, main pushes and manual dispatch. It binds the frozen 491-entry source/provenance closure, 333 new modules, PDF/TeX and protected four-result bytes; builds the aggregate from zero project objects; checks the actual terminal type, allowed axioms and exact previously audited dependency graph; and runs official `leanchecker --fresh --verbose`. Failure propagates to CI and raw streams plus machine-readable receipts are retained for 90 days.

The older three/four-result automatic filters now exclude both `lean/IsingBulk/Preferred22/**` and `lean/IsingBulk/Preferred22.lean`. All three routes also exclude the navigation-only `lean/README.md`. Their verification jobs and historical algorithms are unchanged. Routing-only edits to those two entry-point workflow files do not automatically request historical heavy replays; use their retained manual dispatch when changing job logic. Historical verifier scripts and reusable implementations remain automatic triggers. Shared Lean sources, any lock/toolchain/configuration change, or original theorem changes still match `lean/**` and invoke the affected original suites as before. LT22 also conservatively matches all Lean formal/configuration changes.

| Changed scope | Automatic acceptance |
|---|---|
| Preferred22 source, its frozen manuscript/identity/probe/runner/workflow | LT22; original four-result preservation inside that gate |
| Original/shared LT, HT or ANISO formal sources or dependency/configuration pins | Existing three/four-result regressions and LT22 |
| Original JOINT-only formal sources | Existing four-result regression and conservative LT22 |
| Reader/navigation-only prose | No heavy proof replay |

Future HT22, ANISO F002 and JOINT F001 routes must have separate namespaces, roots, immutable identities and acceptance workflows. Add exclusions only when their dependency ownership has been established; existing `lean/**` routing remains conservative until then. No future route is claimed complete by reserving this design.

## Policy

The previously published LT, HT, ANISO C001 and JOINT C002 Lean sources remain immutable for a Reader-only documentation change. The complete Reader editions under `paper/{lt,ht,aniso,joint}/reader/` do not change proof objects or their dependencies. Such changes must not trigger source-clean Lean builds or fresh kernel replays.

The active entry points are:

- `three-proof-publication-acceptance.yml`: automatically runs for LT/HT/ANISO or shared Lean source/configuration changes and its verification scripts. JOINT-only files are excluded from this earlier three-result entry.
- `four-result-publication-acceptance.yml`: automatically runs when the published four-result Lean source/configuration or its verification scripts change. Shared or upstream LT/HT/ANISO edits can affect the downstream JOINT proof and therefore still trigger four-result regression.
- `unified-publication-acceptance.yml`: preserved as an **explicitly manual** historical full LT/HT verification entry. It no longer triggers on every PR.
- `aniso-lean-acceptance.yml` and `joint-lean-acceptance.yml`: reusable verification implementations, still callable explicitly; their acceptance algorithms are not altered.

## PSER descendants

Standalone, additive PSER manuscripts and code should live in separately scoped paths, such as `paper/*/pser/`, `lean/PSER/` or `lean/IsingBulk/PSER/`, rather than overwriting frozen non-PSER files. These paths are not automatic triggers for the old full proof suites. New PSER workflows must verify their own Lean endpoints, dependencies, scope and kernel checks.

If a proposed PSER revision changes a shared dependency, a previously published theorem declaration, the Lean toolchain/lockfile, or another source file imported by the frozen results, run the affected historical regressions. File-path filtering is conservative and cannot by itself establish proof-body dependency independence. Treat any new shared location not yet covered by the paths as requiring an explicit CI-routing review.

The `workflow_dispatch` entry remains available for deliberate complete revalidation, including before a major proof-source publication or a change to the validation architecture.

## Boundaries and validation

No mathematical source, Lean source, theorem interface, frozen paper, dependency pin, or verification script is changed in this CI-routing PR. GitHub Actions `pull_request.paths` and `push.paths` use an ordered exclusion list. The negative filters only suppress a run when all changed files fall outside the positive/remaining matched paths.

These edits eliminate unnecessary old Lean build/replay on changes confined to Reader directories and the new isolated PSER paths. They do not assert that an arbitrary future PSER file placement or shared-source edit is isolated. Full Lean validation of actual shared proof changes is intentionally retained.
