# LT_PSER: preservation record

Judgment: **PRESERVED**. Public path: `papers/low-temperature/alternative-proof/manuscript.{tex,pdf}`.

This is preservation of the frozen argument under editing. Unchanged proof text is checked by complete line correspondence; changed proof-bearing prose is read in context and adjudicated below. This is not a new independent correctness proof of every frozen estimate.

## Exact version identities

| Version | File | SHA-256 | Git blob | Pages |
|---|---|---|---|---|
| source | `work/authority/SOURCES/AUTHORITATIVE/LT_PSER_LT22_22P.tex` | `3d2454dacf245d4dd9238ef0331eef5dc9fec846621075cd003aaa5bf506f760` | `f0e907c07a2fc026dd6681bf95ec7e7b07a3a3ce` |  |
| source | `work/authority/SOURCES/AUTHORITATIVE/LT_PSER_LT22_22P.pdf` | `e85da407d281efb0898009368328dcec5bf5161e69e7571464bd15dff5d32bbb` | `c96d3281475d5f33db0a3956979e5773864bf108` | 22 |
| pre13 | `work/pre13/ACADEMIC/LT/PSER/manuscript.tex` | `789386d3556659e900c08d1827e07641568a6894db09a29fd3c1161fea535b01` | `9393d8d492a8d56abd2ae32037c0369c8e701132` |  |
| pre13 | `work/pre13/ACADEMIC/LT/PSER/manuscript.pdf` | `cc1769a9a22505cc77fe1977552e484f5ae1dc0bd4587085265ce13aa770ff7e` | `8045bad0b17c95f845f009c87b0cb3b2c0f3c9d5` | 23 |
| final | `work/final/ACADEMIC/LT/PSER/manuscript.tex` | `98877fbf21eacbe1bd6537b3044139dde5f32adc878e3c3984dfd8a59c6a0730` | `803d7141814525bef69ebb9d0eb190eae6536dcc` |  |
| final | `work/final/ACADEMIC/LT/PSER/manuscript.pdf` | `ad0d0a66d9b8d4ceb36e490bfd591e707a7389b51a44a864b15b599190198c2c` | `be734e875c2d4a92c2dd8b5daf59d378ef72a646` | 23 |

## Complete statement and hypothesis map

All statement bodies and their exact source/final quantified hypotheses are in `EVIDENCE/STATEMENTS/LT_PSER.json`; the complete line and reference maps are in `FULL_LINE_CORRESPONDENCE.json` and `REFERENCE_CORRESPONDENCE.csv`.

| Source lines | Final lines | Statement labels | Mathematical disposition |
|---|---|---|---|
| 73–80 | 95–102 | `thm:main ` | Identical after whitespace/labels |
| 156–170 | 182–196 | `prop:angular-bulk;eq:angular-bulk;eq:bulk ` | Identical after whitespace/labels |
| 255–273 | 281–299 | `lem:prime-root-family ` | Identical after whitespace/labels |
| 319–330 | 345–356 | `(unlabelled) ` | Identical after whitespace/labels |
| 365–377 | 391–403 | `lem:pf-propagation ` | Identical after whitespace/labels |
| 407–418 | 433–444 | `prop:complete-product;prop:local-determinant-coefficient ` | Identical after whitespace/labels |
| 435–460 | 461–486 | `lem:alternating-division ` | Identical after whitespace/labels |
| 511–516 | 537–542 | `lem:constrained-homotopy ` | Identical after whitespace/labels |
| 569–576 | 595–602 | `lem:constrained-selected ` | Identical after whitespace/labels |
| 674–689 | 700–715 | `lem:inverse ` | Identical after whitespace/labels |
| 759–787 | 785–813 | `lem:constrained-branch-geometry;eq:constrained-branch-bounds ` | Identical after whitespace/labels |
| 814–834 | 840–860 | `lem:coordinate-scale;eq:q-21;eq:q-22;eq:q-23 ` | Identical after whitespace/labels |
| 1028–1037 | 1053–1062 | `lem:jets;eq:q-14 ` | Identical after whitespace/labels |
| 1146–1158 | 1171–1183 | `lem:oblique-kernel ` | Identical after whitespace/labels |
| 1215–1231 | 1240–1256 | `lem:global-coarea;eq:g-G1 ` | Identical after whitespace/labels |
| 1434–1445 | 1459–1470 | `thm:constrained-tail;eq:logarithmic-absolute-tail ` | Identical after whitespace/labels |
| 1494–1502 | 1519–1527 | `lem:finite-complement ` | Identical after whitespace/labels |
| 1619–1624 | 1644–1649 | `lem:single-q-bound ` | Identical after whitespace/labels |
| 1659–1680 | 1684–1705 | `lem:single-period;eq:single-period ` | Identical after whitespace/labels |
| 1694–1706 | 1719–1731 | `thm:single-first ` | Identical after whitespace/labels |

## Physical observable and dependency graph

Real full-site inputs -> exact coefficient normalization/Fubini -> normal convergence -> first nonzero coefficient + finite lower orders + complete differentiated absolute infinite tail -> no cancellation -> actual curve/local obstruction -> density and componentwise closure -> physical analytic-unit transfer. Each route uses its own corresponding nodes.

No completed natural-boundary endpoint of a different proof route is substituted.

### independent-coordinate-route

All twenty statement environments and every displayed proof formula are retained. The proof still uses its own equal-angle prime family, four-point determinant propagation, exact constrained homotopy, regular inverse, collective current, oblique coarea and complete logarithmic tail. The removed sentence only listed methods not needed on the left-root piece; the separated product kernel and C^N one-body integration proving that piece remain in place. The one mathematical notation correction is the argument of sin(phi): the square-root normal form gives arg sin(phi) in [-pi/4,0] up to a small enlargement, so arg[-phi_doubleprime] lies in [0,3pi/4] and rotation by -3pi/8 has a uniformly positive real part. This is exactly the sector estimate used by the unchanged equation g-G3, not a claim that a complex sine value is a negative real number. Added historical citations do not enter the proof.

## All changed passages

The exhaustive ledger records exact removed/added text, both paragraph contexts and classifications. Intermediate Reader changes are included separately, so the pinned Reader route cannot silently substitute another original.

- `LT_PSER:source-final:0001` (source_to_final): source [24, 23] → target [24, 26]; **MATHEMATICALLY_EQUIVALENT**; checked dependency node `independent-coordinate-route`. Exact text and reason: `MATH_DIFF_LEDGER.json`.
- `LT_PSER:source-final:0003` (source_to_final): source [25, 25] → target [28, 31]; **NONLOADBEARING**; checked dependency node `independent-coordinate-route`. Exact text and reason: `MATH_DIFF_LEDGER.json`.
- `LT_PSER:source-final:0005` (source_to_final): source [73, 72] → target [79, 94]; **MATHEMATICALLY_EQUIVALENT**; checked dependency node `independent-coordinate-route`. Exact text and reason: `MATH_DIFF_LEDGER.json`.
- `LT_PSER:source-final:0007` (source_to_final): source [111, 110] → target [133, 136]; **NONLOADBEARING**; checked dependency node `independent-coordinate-route`. Exact text and reason: `MATH_DIFF_LEDGER.json`.
- `LT_PSER:source-final:0009` (source_to_final): source [311, 311] → target [337, 337]; **NONLOADBEARING**; checked dependency node `independent-coordinate-route`. Exact text and reason: `MATH_DIFF_LEDGER.json`.
- `LT_PSER:source-final:0011` (source_to_final): source [997, 998] → target [1023, 1023]; **MATHEMATICALLY_EQUIVALENT**; checked dependency node `independent-coordinate-route`. Exact text and reason: `MATH_DIFF_LEDGER.json`.
- `LT_PSER:source-final:0013` (source_to_final): source [1254, 1254] → target [1279, 1279]; **MATHEMATICALLY_EQUIVALENT**; checked dependency node `independent-coordinate-route`. Exact text and reason: `MATH_DIFF_LEDGER.json`.
- `LT_PSER:source-final:0015` (source_to_final): source [1789, 1789] → target [1814, 1815]; **MATHEMATICALLY_EQUIVALENT**; checked dependency node `independent-coordinate-route`. Exact text and reason: `MATH_DIFF_LEDGER.json`.
- `LT_PSER:source-final:0017` (source_to_final): source [1807, 1806] → target [1833, 1854]; **NONLOADBEARING**; checked dependency node `independent-coordinate-route`. Exact text and reason: `MATH_DIFF_LEDGER.json`.
- `LT_PSER:pre13-final:0001` (pre13_to_final): source [1279, 1279] → target [1279, 1279]; **MATHEMATICALLY_EQUIVALENT**; checked dependency node `independent-coordinate-route`. Exact text and reason: `MATH_DIFF_LEDGER.json`.

## Thirteen-correction pass

- **E-P05-01**: The branch normal form gives the angle arg(sin phi) in [-pi/4,0], up to a fixed small enlargement. The positive numerator in -phi_doubleprime/(sin phi)^3 puts -phi_doubleprime in [0,3pi/4]; rotation by -3pi/8 is strictly in a right half-plane. This proves exactly g-G3 with its original uniform constants.

## Formalization scope

The actual endpoint, expanded fields, physical antecedents and manuscript-only strength are mapped clause by clause in `SIX_PAPER_LEAN_SCOPE_MATRIX.csv`. Exact current declarations and existing compiler type evidence are in `EVIDENCE/LEAN/`. No fresh full clean formal build is claimed.

Remaining mathematical-preservation obligations: none. Archive/live-CI verification is a separate publication gate recorded in `ACTIVE_LINK_AND_CI_REGRESSION.md`.
