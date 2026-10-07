# Continuation source correspondence

Current status, 2026-10-07: the Lean/post-audit release is
[v0.2.1](https://github.com/LeoLam233/ising-bulk-natural-boundary/releases/tag/v0.2.1);
the frozen analytic manuscript remains `v0.1-rc4`.

The independently audited baseline is frozen v0.2.0, commit
`50ec73db799ba8f72dff802b4a6fecdc69b61932`. Its clean build,
project-wide audit of 9,199 safe declarations, endpoint controls and fresh
kernel replay are baseline evidence. The independent adversarial Opus audit
returned `PASS_WITH_NONBLOCKING_ISSUES`, with no blocking or load-bearing
mathematical defect.

v0.2.1 completes targeted remediation of those audit findings, including
verification hardening and complete TAIL endpoint packaging. The original
five-module mathematical assembly is preserved, and
`IsingBulk.Final.theorem_nb` and `IsingBulk.Final.theorem_nb_physical` are
unchanged. The final release identities are:

- Commit: `de23d9475744fb4625666142d5a03b3d688195e6`
- Tree: `c4f8dd4e81dba9e88e18dadfdb0778cf3771d1d2`
- Proof payload: `6989420e855e0c3d882ce51e302dbc6579890da81aa0fd866176bab583067715`

That exact commit passed a clean full build, a project-wide axiom audit of
9,200 safe declarations with union exactly `propext`, `Classical.choice`,
`Quot.sound`, 14/14 endpoints, 13/13 targeted production regressions,
13/13 manifest controls, 6/6 Lean controls, and fresh
`leanchecker --fresh --verbose IsingBulk` replay.
[Full CI run 37518976590](https://github.com/LeoLam233/ising-bulk-natural-boundary/actions/runs/37518976590)
and [smoke CI run 37518976672](https://github.com/LeoLam233/ising-bulk-natural-boundary/actions/runs/37518976672)
both completed with `SUCCESS` for the exact release commit. These final
receipts are separate from baseline audit evidence; no independent re-audit
of the entire v0.2.1 tree is claimed.

E1/E2/E3 remain explicit external literature premises. This is still an
AI-assisted candidate proof; no independent human expert validation or peer
review is claimed. Cached dependency binary/source correspondence remains
trusted, the build and fresh replay use the same Lean kernel implementation,
and the expected-ID pin is inside the Git commit rather than cryptographically
external to it.

## Source identity and preserved scope

The imported formalization baseline is
`88cb554a65eb040050badd47742d343bed82b7f2`. The normative manuscript is the
pinned source at commit `1b4b506c9cb19d5fdbf9f59d89c7a179739d337d`.
`git hash-object source_snapshot/manuscript.tex` returned the required blob
`1c6c0f47e3f1e4d13e59b49c52c18414e9dd3939`.

The exact target remains manuscript `thm:tail`, lines 1919–1950: for every
fixed permitted derivative order, sum the absolute values over all higher
even particle orders before taking the radial little-o limit. The Lean
predicate is `IsingBulk.Final.AbsoluteUpperTailSmall`; its summand is
`norm (iteratedDeriv j (upperFormFactor (2*(n+p+1)))
(radialParameter theta eps))`. The finite ceiling is `(2*p)^2/2-1`.
Neither a complex sum nor a termwise asymptotic replaces this target.

## Historical checkpoint evidence

The imported compact-right checkpoint records 1,066 directly root-imported
production modules, a 4,830-job root build, eight endpoint checks, and 9,125
kernel-safe project declarations with axiom union `propext`,
`Classical.choice`, `Quot.sound`. These are baseline checkpoint figures,
not measured totals for the five-module continuation. Existing checkpoint
receipts and the separately supplied Linux baseline logs remain evidence
for that baseline only. The restored-cache root-import check is likewise
not a new whole-project declaration inventory or final clean candidate gate.

`AUTHORED_DECLARATIONS.tsv` and `DECLARATIONS.tsv` are older FIRST-era
snapshots: respectively 2,185 and 4,102 data rows, with no declaration whose
name begins `IsingBulk.Tail.` or `IsingBulk.Final.`. Preserve their rows and
receipts. They must not be called complete current-project inventories.
The 9,125-declaration audit receipt is distinct from these two TSVs.

## Five-module implementation map

| Module | Exact principal endpoints | Source role and preserved semantics |
|---|---|---|
| `IsingBulk/Tail/CommonAllSectorParameters.lean` | `IsingBulk.Tail.common_all_sector_parameters`; `IsingBulk.Tail.finite_order_common_radius` | Implements the finite common-choice step in the proof of `thm:tail`. One selected geometry, selector, deformation, outer/inner widths, cutoff power and high-order threshold serve every `j <= order`. One positive source-summability radius precedes both epsilon and the current cutoff. |
| `IsingBulk/Tail/ExactSectorNormDomination.lean` | `IsingBulk.Tail.originalKSNorm_le_sectors`; `IsingBulk.Tail.constructed_originalKSNorm_le_sectors` | Attaches the existing exact original/current finite decomposition to the categories from `lem:partition` (manuscript line 957), discharging the finite norm comparison needed after `eq:FKS` (line 736). The norm of each actual current interval integral is retained. All-branch current vanishing is proved for the constructed selector. |
| `IsingBulk/Tail/IntermediateWindowAssembly.lean` | `IsingBulk.Tail.common_intermediateKSNormWindow_radialSeriesSmall`; `IsingBulk.Tail.common_intermediateKSNormWindow_littleO` | Combines the actual all-B, mixed/left and compact-right endpoints from `prop:allB` (line 1458), `prop:mixed` (line 1596), and `prop:compactR` (line 1695). The exact strict intermediate window is contained in the existing weak all-B/right windows; they are not asserted equal. Eventual summability and little-o of the infinite norm sum are both retained. |
| `IsingBulk/Tail/AbsoluteTailAssembly.lean` | `IsingBulk.Tail.common_absoluteUpperTailSmall`; `IsingBulk.Tail.selected_absolute_upper_tail_small`; `IsingBulk.Tail.actual_upper_tail_summable` | Combines the proved full F and large-current series, exact intermediate window, and high-KS tail using `actual_higher_tail_domination`. This implements the literal `thm:tail` target (line 1919). Actual upper-tail summability is separately available at every positive radial parameter. |
| `IsingBulk/Final/UnconditionalNaturalBoundary.lean` | `IsingBulk.Final.theorem_tail`; `IsingBulk.Final.theorem_tail_with_summability`; `IsingBulk.Final.theorem_nb`; `IsingBulk.Final.theorem_nb_physical` | Exposes the exact selected-point tail, packages positive-parameter norm summability in theorem_tail_with_summability, and supplies the unchanged theorem_tail to existing `theorem_conditional`/`theorem_conditional_physical`, corresponding to `thm:conditional` (line 1956) and `thm:nb` (line 1992). Only the TAIL premise is discharged; the published and physical inputs below remain explicit. |

### Common parameter order

Fix the selected arithmetic geometry and finite derivative ceiling first.
Choose eta below the completed/source/mixed/right caps; then alpha; then tau,
including the mixed tau threshold that depends on the chosen alpha. Obtain
the all-B and current-exclusion outer caps, choose one outer width, obtain
the finite-order mixed inner cap, and choose one inner width also satisfying
the compact-right geometric restriction. Choose
`beta=(1/4)/(order+1)`, which satisfies `beta*(j+1)<1/2` for every `j<=order`.
Choose one positive D using the finite-order high-KS endpoint at Q=0.
Finally, finite minima produce a source-summability epsilon radius before
all epsilon/cut variables.

The temporary selected branch data used to obtain caps and the final branch
data have different tau/alpha fields. Only their definitionally identical
theta, thetaB and c0 projections are transferred. No equality of the whole
records is assumed. The final selected-angle transfer uses the existing
`selectedLocalBranchData_theta` theorem.

### Relation to the manuscript's split

The F endpoint attached by this route is the internally proved full
positive-even derivative-norm series, stronger than the finite-window
`prop:F` statement at line 857. The corresponding full large-current series
is also internally proved and implies the role of `prop:largeS` at line
1873. The finite-order common high-KS threshold comes from the existing
endpoint serving `prop:highKS` at line 1894. Thus the source comparison may
use full F/full large-current sums without an additional ultra-high cutoff.
The separately proved source-aligned UltraHigh node is preserved; no new
estimate is installed as a hypothesis and no dummy UltraHigh premise is
introduced.

## External-input boundary

- `theorem_tail` has no E1, E2 or E3 premise. Its selected-point assumptions
  are prime p, p>=11, admissible a,b, a!=b, and the stated finite derivative
  ceiling. Internal stronger endpoints may not use every one of these
  public assumptions, but the public target retains them.
- `theorem_nb` retains the exact `PublishedTWFixedOrderInput` family (E3).
  This is the existing local full-site non-Nickel fixed-even-order bound,
  used through the previously proved lower-order transfer. It is not a
  tail, global analyticity, or natural-boundary certificate.
- `theorem_nb_physical` retains `PhysicalSusceptibilityE1 J chi M`,
  `YangMagnetizationE2 M`, `0<J`, and the same E3 family. The real physical
  germ identification and arbitrary local inverse-temperature-sheet
  boundary predicate are unchanged. No global inverse-temperature branch
  or complex physical continuation is added as an external premise.

Accordingly, “unconditional” in the new wrapper filename means that the
previously open internal TAIL premise has been discharged; it must not be
reported as elimination of E1/E2/E3.

## Historical focused verification (2026-10-06)

The focused observations below preceded the completed v0.2.0 full build and
independent Opus audit recorded above. Their original receipts are preserved
as stage-specific evidence.

| Module | Observed focused result | Evidence |
|---|---|---|
| CommonAllSectorParameters | Compile exit 0; both new theorem axiom queries exit 0 with exactly the core trio | `run_logs/continuation/common_parameters/attempt3.result.json`; `axioms.result.json`; `axioms.stdout.txt` |
| ExactSectorNormDomination | Latest focused compile exit 0; four theorem axiom queries exit 0 with exactly the core trio | `run_logs/continuation/exact_sector_norm/attempt3.measurement.json`; `axioms.measurement.json`; `axioms.stdout.txt` |
| IntermediateWindowAssembly | Latest focused compile exit 0; seven theorem axiom queries exit 0 with exactly the core trio | `run_logs/continuation/intermediate_window/attempt2.result.json`; `axioms2.result.json`; `axioms2.stdout.txt` |
| AbsoluteTailAssembly | Compile and six theorem axiom checks exit 0; warnings-as-errors; exact core trio | `run_logs/continuation/absolute_tail/attempt1.result.json`; `axioms1.result.json`; `axioms1.stdout.txt` |
| UnconditionalNaturalBoundary | Compile and all three final endpoint type/axiom checks exit 0; exact core trio | `run_logs/continuation/final_wrappers/attempt1.result.json`; `axioms.result.json`; `axioms.stdout.txt` |

All five module results above are observed focused checks. No new full-build job count,
build-job count, declaration count, or whole-project axiom total is asserted.

## Proof status and endpoint path

`CLAIM_LEDGER.tsv` records proved source-mapped declarations; it does not
assert that each named wrapper is reachable from the final endpoints.
In particular, `lem:resultant` uses the on-path exponential separation,
resultant nonvanishing and selected-branch infinite-order route; `lem:lie`
uses the core divergence/flux, lieStep and transport machinery. Their
source-facing wrappers are proved off-path. The separate UltraHigh wrappers
are also proved off-path: the on-path `CommonAllSectorParameters.high_tendsto`
and full F/full large-current series subsume their final-tail role.
The auditor's 106 off-path modules remain preserved, including regressions
and alternate/source-facing routes. No theorem is removed or weakened.

The pinned manuscript self-label `0.1-rc4` identifies the analytic baseline.
It is intentionally retained; the Lean release/remediation version is separate.
E1/E2/E3 remain explicit external premises, and the E3 non-Nickel guard is
checked by `control_packet/continuation/fixtures/E3Guard.lean`.
