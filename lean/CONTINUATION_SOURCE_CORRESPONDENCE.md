# Provisional continuation source correspondence

Prepared 2026-10-06 at 11:44 UTC for coordinator review. This document is an
additive source map and update proposal. It does not change the historical
ledgers, assign final candidate status, or constitute an independent audit.
All five modules and final wrappers now have focused compilation and endpoint axiom checks. Final candidate verification and formal audits remain pending.

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
| `IsingBulk/Final/UnconditionalNaturalBoundary.lean` | `IsingBulk.Final.theorem_tail`; `IsingBulk.Final.theorem_nb`; `IsingBulk.Final.theorem_nb_physical` | Exposes the exact selected-point tail and supplies it to existing `theorem_conditional`/`theorem_conditional_physical`, corresponding to `thm:conditional` (line 1956) and `thm:nb` (line 1992). Only the TAIL premise is discharged; the published and physical inputs below remain explicit. |

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

## Validation snapshot: provisional, targeted only

The following observations are based on the named local logs as read at
11:47 UTC; final freeze and source-hash reconciliation remain coordinator
work. They do not establish a whole-project clean candidate or independent
audit.

| Module | Observed focused result | Evidence |
|---|---|---|
| CommonAllSectorParameters | Compile exit 0; both new theorem axiom queries exit 0 with exactly the core trio | `run_logs/continuation/common_parameters/attempt3.result.json`; `axioms.result.json`; `axioms.stdout.txt` |
| ExactSectorNormDomination | Latest focused compile exit 0; four theorem axiom queries exit 0 with exactly the core trio | `run_logs/continuation/exact_sector_norm/attempt3.measurement.json`; `axioms.measurement.json`; `axioms.stdout.txt` |
| IntermediateWindowAssembly | Latest focused compile exit 0; seven theorem axiom queries exit 0 with exactly the core trio | `run_logs/continuation/intermediate_window/attempt2.result.json`; `axioms2.result.json`; `axioms2.stdout.txt` |
| AbsoluteTailAssembly | Compile and six theorem axiom checks exit 0; warnings-as-errors; exact core trio | `run_logs/continuation/absolute_tail/attempt1.result.json`; `axioms1.result.json`; `axioms1.stdout.txt` |
| UnconditionalNaturalBoundary | Compile and all three final endpoint type/axiom checks exit 0; exact core trio | `run_logs/continuation/final_wrappers/attempt1.result.json`; `axioms.result.json`; `axioms.stdout.txt` |

All five module results above are observed focused checks. No new full-build job count,
build-job count, declaration count, or whole-project axiom total is asserted.

## Reviewer notes: exact documentation update map

Apply these proposals only after the required final focused wrapper passes.
They are not edits to the original files.

### CLAIM_LEDGER.tsv

Physical line numbers below refer to the inspected baseline table, including
its header on line 1.

- Line 24, `thm:tail`: replace the old `Tail.SummationGrowth`-only pointer
  with the actual common-choice, sector-domination, intermediate and
  selected-tail endpoints plus `IsingBulk.Final.theorem_tail`. Describe
  the literal higher-even absolute sum and full finite derivative ceiling.
  Remove the now-superseded common-selector/decomposition/little-o blocker
  and old stop-at-compact-right note. Record actual targeted receipts.
  E1/E2/E3 are not inputs to this theorem.
- Line 25, `thm:conditional`: preserve the two conditional theorem
  statements and their explicit hTail parameter; record that separate
  proved wrapper endpoints now supply hTail. Do not rewrite the original
  conditional theorem as though its statement lost a premise. Preserve
  its physical nonvacuity regression and narrow E1/E2/E3 boundaries.
- Line 26, `thm:nb`: replace the pending-assembly pointer with
  `IsingBulk.Final.theorem_nb` and `IsingBulk.Final.theorem_nb_physical`;
  describe the internally discharged TAIL premise and retained E3 or
  E1/E2/E3 inputs. Keep final source/candidate and independent-audit gates
  explicit unless separately completed.
- Lines 12 (`prop:F`), 13 (`lem:partition`), 15 (`lem:originaldisk`),
  21 (`lem:protected`), 22 (`prop:largeS`), 23 (`prop:highKS`): reconcile
  the stale common-selector/final-instantiation remaining-work phrases.
  Do not silently discharge line 15's separate raw-source-clause
  reconciliation or any source/candidate gate merely because the wrapper
  compiles. Preserve each prior mathematical status unless separately
  justified by its own source review.
- Lines 18–20 (`prop:allB`, `prop:mixed`, `prop:compactR`): preserve
  IMPLEMENTED and original receipts; update only superseded downstream
  open-work notes and append the actual new attachment references.
- Line 17 (`prop:micro`): its “allB exterior ... open” note is already
  superseded by the preserved implemented all-B endpoint; reconcile that
  note without changing the microcore proof or its historical gate status.
- Line 14 (`lem:contraction`): any change to its source-wide finite-jet
  attachment note needs its own source-clause review, not merely inference
  from final theorem use.
- Preserve all existing CLOSED and six FIRST CANDIDATE_CLOSED statuses.
  Targeted compilation alone warrants at most an IMPLEMENTED/targeted
  acceptance description for new source nodes, not CANDIDATE_CLOSED or
  AUDITED_CLOSED.

### COVERAGE.md, CORRESPONDENCE.md and GAP_MANIFEST.md

All three inspected files have the same top checkpoint authority block at
lines 1–30. Its current-status sentence is line 9, baseline metrics are
lines 11–19, obsolete stop/open assertions are lines 21–26, and a stage-local
one-agent directive appears at line 30. Add a dated new authority block and
explicitly identify the old block as historical checkpoint evidence. Do
not replace its measured 1066/4830/9125 figures with invented new totals.

The compact-right closure chronology is lines 217–220 and the older
`TAIL_CONTINUATION_CURRENT` block is lines 224–232. Line 229 contains old
open-node claims and an obsolete three-audit workflow. Preserve these as
stage-local history, with the new authority block explicitly superseding
them. The preserved FIRST history begins at line 234; its candidate
statuses and original evidence must remain unchanged.

In COVERAGE.md, the old source-status table at lines 586–619, including
NOT_STARTED tail/final rows at 614–616, is historical branch-era reporting,
not a table to silently rewrite as current. GAP_MANIFEST.md's “Remaining
proof obligations — after branch closure” section begins at line 738 and
is likewise historical. Put the actual remaining current obligations in
the new dated authority block: focused checks still pending, source/freeze
reconciliation and whichever normal candidate gate the coordinator
actually authorizes. No independent-audit completion is implied.

CORRESPONDENCE.md should additionally link the source/endpoint table above,
record the stronger full-F/full-current route and the strict-to-weak window
bridge, and explicitly retain the physical/published input boundaries.

### Separate continuation declaration inventory

Preserve `AUTHORED_DECLARATIONS.tsv` and `DECLARATIONS.tsv` unchanged as the
FIRST-era snapshots described above. A separate continuation source map
may list the 24 authored declarations currently present in the five new
source files, but this source count is not an environment declaration count.
Structure projections, recursors, generated equations and private helpers
must be collected from the actual final loaded environment.

After the final focused wrapper/root checks, create the separate inventory
from actual declaration names, types, defining modules and reachable axiom
lists. Do not assign the endpoint axiom union to every individual entry or
reuse the historical 9,125 count as the candidate inventory. Record actual
source hashes, command/log receipts and the exact scope of the export.
