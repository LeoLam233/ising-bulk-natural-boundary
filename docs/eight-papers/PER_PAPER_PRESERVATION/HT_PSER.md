# HT_PSER: preservation record

Judgment: **PRESERVED**. Public path: `papers/high-temperature/alternative-proof/manuscript.{tex,pdf}`.

This is preservation of the frozen argument under editing. Unchanged proof text is checked by complete line correspondence; changed proof-bearing prose is read in context and adjudicated below. This is not a new independent correctness proof of every frozen estimate.

## Exact version identities

| Version | File | SHA-256 | Git blob | Pages |
|---|---|---|---|---|
| source | `work/authority/SOURCES/AUTHORITATIVE/HT_PSER_HT22_22P.tex` | `5d962d44180f33df66fbad90e2f66a8c95425d3eddc91765abb6953bd3b48c0f` | `6077dfd00713e307ec9500198093857d324b6d11` |  |
| source | `work/authority/SOURCES/AUTHORITATIVE/HT_PSER_HT22_22P.pdf` | `2e0e674c88f3bd5edc3846aa1f62eb2a124ce96c588221b24cc176f2a97a00d9` | `06f375cc4bbf259ba8d9398f20e419a7e60c4525` | 22 |
| pre13 | `work/pre13/ACADEMIC/HT/PSER/manuscript.tex` | `3fdcd2562d66efa0f301879e1e78b57762d15653f59c59c29ba9896357e40081` | `2fdf7cd6ddb09ee0d5e3f844b3b52c6386cd9038` |  |
| pre13 | `work/pre13/ACADEMIC/HT/PSER/manuscript.pdf` | `3a89e17c6bf0125bd5938d0d849449423e12cd8c29e9743b22bf2130da534b6b` | `744435f6680c2e6cff9927c6b6ef11ee9ffbc3e5` | 22 |
| final | `work/final/ACADEMIC/HT/PSER/manuscript.tex` | `3fdcd2562d66efa0f301879e1e78b57762d15653f59c59c29ba9896357e40081` | `2fdf7cd6ddb09ee0d5e3f844b3b52c6386cd9038` |  |
| final | `work/final/ACADEMIC/HT/PSER/manuscript.pdf` | `3a89e17c6bf0125bd5938d0d849449423e12cd8c29e9743b22bf2130da534b6b` | `744435f6680c2e6cff9927c6b6ef11ee9ffbc3e5` | 22 |

## Complete statement and hypothesis map

All statement bodies and their exact source/final quantified hypotheses are in `EVIDENCE/STATEMENTS/HT_PSER.json`; the complete line and reference maps are in `FULL_LINE_CORRESPONDENCE.json` and `REFERENCE_CORRESPONDENCE.csv`.

| Source lines | Final lines | Statement labels | Mathematical disposition |
|---|---|---|---|
| 59–63 | 71–75 | `thm:main ` | Identical after whitespace/labels |
| 134–144 | 150–160 | `prop:angular-bulk;eq:bulk ` | Identical after whitespace/labels |
| 227–241 | 243–257 | `lem:prime-root-family ` | Identical after whitespace/labels |
| 300–311 | 316–327 | `(unlabelled) ` | Identical after whitespace/labels |
| 346–358 | 362–374 | `lem:pf-propagation ` | Identical after whitespace/labels |
| 389–403 | 405–419 | `prop:complete-product;prop:local-determinant-coefficient;eq:odd-border ` | Identical after whitespace/labels |
| 432–444 | 448–460 | `lem:border-minors ` | Identical after whitespace/labels |
| 511–516 | 527–532 | `lem:constrained-homotopy ` | Identical after whitespace/labels |
| 571–578 | 587–594 | `lem:constrained-selected ` | Identical after whitespace/labels |
| 677–688 | 693–704 | `lem:inverse ` | Identical after whitespace/labels |
| 757–785 | 773–801 | `lem:constrained-branch-geometry;eq:constrained-branch-bounds ` | Identical after whitespace/labels |
| 812–832 | 828–848 | `lem:coordinate-scale;eq:v-21;eq:v-22;eq:v-23 ` | Identical after whitespace/labels |
| 1017–1027 | 1032–1042 | `lem:covariance;eq:v-15 ` | Identical after whitespace/labels |
| 1076–1085 | 1091–1100 | `lem:jets;eq:v-14 ` | Identical after whitespace/labels |
| 1185–1197 | 1200–1212 | `lem:oblique-kernel ` | Identical after whitespace/labels |
| 1259–1275 | 1274–1290 | `lem:global-coarea;eq:g-G1 ` | Identical after whitespace/labels |
| 1490–1501 | 1505–1516 | `thm:constrained-tail;eq:logarithmic-absolute-tail ` | Identical after whitespace/labels |
| 1537–1544 | 1552–1559 | `lem:finite-complement ` | Identical after whitespace/labels |
| 1658–1672 | 1672–1686 | `lem:single-period;eq:single-period ` | Identical after whitespace/labels |
| 1691–1698 | 1705–1712 | `thm:single-first ` | Identical after whitespace/labels |

## Physical observable and dependency graph

Real full-site inputs -> exact coefficient normalization/Fubini -> normal convergence -> first nonzero coefficient + finite lower orders + complete differentiated absolute infinite tail -> no cancellation -> actual curve/local obstruction -> density and componentwise closure -> physical analytic-unit transfer. Each route uses its own corresponding nodes.

No completed natural-boundary endpoint of a different proof route is substituted.

### independent-constrained-route

All twenty statement environments and every displayed formula are retained. The signed constrained measures, bordered odd determinant, normal convergence, both upper quadrants, complete logarithmic higher-odd tail, finite complement and exact first coefficient are unchanged. The normalized Haar measure d mu_N was already defined for the eliminated-angle torus; writing it explicitly preserves the (2pi)^(1-N) normalization. Reworded transport paragraphs still use scalar coefficients on the original real constrained measure, smooth real-angle occupancies, and the commuting frame. The displaced mixed pieces remain holomorphic on a disk depending on the fixed order. The replacement scope sentence explicitly includes every constrained mean and every odd tail order N>=N_*+2; no excluded range or new uniformity is introduced.

## All changed passages

The exhaustive ledger records exact removed/added text, both paragraph contexts and classifications. Intermediate Reader changes are included separately, so the pinned Reader route cannot silently substitute another original.

- `HT_PSER:source-final:0001` (source_to_final): source [24, 24] → target [24, 26]; **NONLOADBEARING**; checked dependency node `independent-constrained-route`. Exact text and reason: `MATH_DIFF_LEDGER.json`.
- `HT_PSER:source-final:0003` (source_to_final): source [44, 43] → target [46, 55]; **MATHEMATICALLY_EQUIVALENT**; checked dependency node `independent-constrained-route`. Exact text and reason: `MATH_DIFF_LEDGER.json`.
- `HT_PSER:source-final:0005` (source_to_final): source [90, 89] → target [102, 105]; **NONLOADBEARING**; checked dependency node `independent-constrained-route`. Exact text and reason: `MATH_DIFF_LEDGER.json`.
- `HT_PSER:source-final:0007` (source_to_final): source [187, 187] → target [203, 203]; **MATHEMATICALLY_EQUIVALENT**; checked dependency node `independent-constrained-route`. Exact text and reason: `MATH_DIFF_LEDGER.json`.
- `HT_PSER:source-final:0009` (source_to_final): source [296, 296] → target [312, 312]; **NONLOADBEARING**; checked dependency node `independent-constrained-route`. Exact text and reason: `MATH_DIFF_LEDGER.json`.
- `HT_PSER:source-final:0011` (source_to_final): source [668, 669] → target [684, 685]; **MATHEMATICALLY_EQUIVALENT**; checked dependency node `independent-constrained-route`. Exact text and reason: `MATH_DIFF_LEDGER.json`.
- `HT_PSER:source-final:0013` (source_to_final): source [940, 942] → target [956, 958]; **MATHEMATICALLY_EQUIVALENT**; checked dependency node `independent-constrained-route`. Exact text and reason: `MATH_DIFF_LEDGER.json`.
- `HT_PSER:source-final:0015` (source_to_final): source [955, 957] → target [971, 973]; **MATHEMATICALLY_EQUIVALENT**; checked dependency node `independent-constrained-route`. Exact text and reason: `MATH_DIFF_LEDGER.json`.
- `HT_PSER:source-final:0017` (source_to_final): source [994, 995] → target [1010, 1010]; **MATHEMATICALLY_EQUIVALENT**; checked dependency node `independent-constrained-route`. Exact text and reason: `MATH_DIFF_LEDGER.json`.
- `HT_PSER:source-final:0019` (source_to_final): source [1004, 1004] → target [1019, 1019]; **MATHEMATICALLY_EQUIVALENT**; checked dependency node `independent-constrained-route`. Exact text and reason: `MATH_DIFF_LEDGER.json`.
- `HT_PSER:source-final:0021` (source_to_final): source [1484, 1485] → target [1499, 1500]; **MATHEMATICALLY_EQUIVALENT**; checked dependency node `independent-constrained-route`. Exact text and reason: `MATH_DIFF_LEDGER.json`.
- `HT_PSER:source-final:0023` (source_to_final): source [1557, 1559] → target [1572, 1573]; **MATHEMATICALLY_EQUIVALENT**; checked dependency node `independent-constrained-route`. Exact text and reason: `MATH_DIFF_LEDGER.json`.
- `HT_PSER:source-final:0025` (source_to_final): source [1764, 1763] → target [1778, 1778]; **NONLOADBEARING**; checked dependency node `independent-constrained-route`. Exact text and reason: `MATH_DIFF_LEDGER.json`.

## Thirteen-correction pass

No final-pass TeX correction in this paper; exact pre13/final comparison confirms this.

## Formalization scope

The actual endpoint, expanded fields, physical antecedents and manuscript-only strength are mapped clause by clause in `SIX_PAPER_LEAN_SCOPE_MATRIX.csv`. Exact current declarations and existing compiler type evidence are in `EVIDENCE/LEAN/`. No fresh full clean formal build is claimed.

Remaining mathematical-preservation obligations: none. Archive/live-CI verification is a separate publication gate recorded in `ACTIVE_LINK_AND_CI_REGRESSION.md`.
