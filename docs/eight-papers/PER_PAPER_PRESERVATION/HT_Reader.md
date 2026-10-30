# HT_Reader: preservation record

Judgment: **PRESERVED**. Public path: `papers/high-temperature/original-proof/manuscript.{tex,pdf}`.

This is preservation of the frozen argument under editing. Unchanged proof text is checked by complete line correspondence; changed proof-bearing prose is read in context and adjudicated below. This is not a new independent correctness proof of every frozen estimate.

## Exact version identities

| Version | File | SHA-256 | Git blob | Pages |
|---|---|---|---|---|
| source | `work/authority/SOURCES/AUTHORITATIVE/HT_ORIGINAL_33P.tex` | `128739407e585457b38d150bd5a74514d8567b5a936c8b4bc2a5c613b1962c65` | `c57850da756c94ba05637354af22abb561a208f4` |  |
| source | `work/authority/SOURCES/AUTHORITATIVE/HT_ORIGINAL_33P.pdf` | `2eac849878f513b46643d651f76280a7d71048d21aad20a680872af1fc5fc765` | `94e36dba383bd0634ef3f9b621266db3f04e1b41` | 33 |
| reader | `work/repository-current/paper/ht/reader/manuscript.tex` | `1d75fa831b5a214a93bf708c08764cef073392b481163f51ab73bd2a7ac8e473` | `63012a8946378168b326629c9247df3d25200ef6` |  |
| reader | `work/repository-current/paper/ht/reader/manuscript.pdf` | `7c29a84066602b8e86feda0a6c5909a2a28f9aa3a537702a1bdd6a2872b18c88` | `164d2b0d2574e8fae445eb00390ed9c154848429` | 35 |
| pre13 | `work/pre13/ACADEMIC/HT/Reader/manuscript.tex` | `22707bfe987d3eab4e382a49ac51c341a8e02fca6a2c7e4d39ed2928ba14b1bf` | `0c578f21615e7b89e6f860717f5bae47f94f4c9d` |  |
| pre13 | `work/pre13/ACADEMIC/HT/Reader/manuscript.pdf` | `2a97692d17374d7d0a53f97130ec8e6d8f6805b0e427f6df4dd2e0e1996a68e7` | `2a4e15a9df96e695c143c20a41467e6e710fdb4d` | 35 |
| final | `work/final/ACADEMIC/HT/Reader/manuscript.tex` | `21730113b199269a5eb1eb25e48f0202a65b584bb0e9c4184c4ed3cf66be113f` | `c42f04e6ba48235bc2de4a9d49d5993800d90a94` |  |
| final | `work/final/ACADEMIC/HT/Reader/manuscript.pdf` | `9ab769e322d82f086f72cbcf7c205e92062d1c59433ed579450fbe1db6c65729` | `dd2e0a301136ac897b0876153e39b4d916c1b2dd` | 35 |

## Complete statement and hypothesis map

All statement bodies and their exact source/final quantified hypotheses are in `EVIDENCE/STATEMENTS/HT_Reader.json`; the complete line and reference maps are in `FULL_LINE_CORRESPONDENCE.json` and `REFERENCE_CORRESPONDENCE.csv`.

| Source lines | Final lines | Statement labels | Mathematical disposition |
|---|---|---|---|
| 69–73 | 69–73 | `thm:main ` | Identical after whitespace/labels |
| 149–169 | 183–203 | `lem:residue;eq:reduced;eq:pair;eq:onsiteidentity ` | Identical after whitespace/labels |
| 217–229 | 253–265 | `lem:schur ` | Identical after whitespace/labels |
| 272–277 | 314–319 | `thm:prime ` | Identical after whitespace/labels |
| 319–324 | 361–366 | `lem:resultant ` | Identical after whitespace/labels |
| 346–353 | 394–401 | `lem:complement ` | Identical after whitespace/labels |
| 401–421 | 449–469 | `thm:first;eq:amplitudeclosed ` | Identical after whitespace/labels |
| 624–636 | 679–691 | `prop:selector;eq:FKS;eq:current ` | Identical after whitespace/labels |
| 706–708 | 766–768 | `prop:F ` | Identical after whitespace/labels |
| 836–845 | 901–910 | `lem:partition ` | Identical after whitespace/labels |
| 914–936 | 978–1000 | `lem:contraction ` | Identical after whitespace/labels |
| 1101–1112 | 1165–1176 | `lem:originaldisk ` | Identical after whitespace/labels |
| 1192–1226 | 1254–1288 | `lem:branch ` | Identical after whitespace/labels |
| 1277–1290 | 1338–1351 | `prop:micro ` | Identical after whitespace/labels |
| 1334–1340 | 1395–1401 | `prop:allB ` | Identical after whitespace/labels |
| 1469–1475 | 1536–1542 | `prop:mixed ` | Identical after whitespace/labels |
| 1567–1570 | 1632–1635 | `prop:compactR ` | Identical after whitespace/labels |
| 1657–1668 | 1721–1732 | `lem:protected ` | Identical after whitespace/labels |
| 1754–1757 | 1817–1820 | `prop:largeS ` | Identical after whitespace/labels |
| 1774–1777 | 1836–1839 | `prop:highKS ` | Identical after whitespace/labels |
| 1795–1803 | 1863–1871 | `prop:onsitesum ` | Identical after whitespace/labels |
| 1867–1888 | 1935–1956 | `(unlabelled) ` | Statement body retained; notation/caption or post-statement commentary is adjudicated in the diff ledger |
| 1890–1900 | 1958–1968 | `thm:tail ` | Identical after whitespace/labels |
| 1995–2006 | 2071–2082 | `lem:lie ` | Identical after whitespace/labels |
| 2105–2127 | 2181–2203 | `lem:jets;eq:jetexpansion;eq:jetdegree ` | Identical after whitespace/labels |

## Physical observable and dependency graph

Real full-site inputs -> exact coefficient normalization/Fubini -> normal convergence -> first nonzero coefficient + finite lower orders + complete differentiated absolute infinite tail -> no cancellation -> actual curve/local obstruction -> density and componentwise closure -> physical analytic-unit transfer. Each route uses its own corresponding nodes.

No completed natural-boundary endpoint of a different proof route is substituted.

### physical

The full positive-odd series and C_N=f_N+2T_N remain the physical observable, with every lattice site. The fourth-root branch is positive on 0<s<1 and t=1/s. Residue measures and all compact-set differentiated convergence claims are unchanged. New physical/outline prose does not replace the full lattice by the diagonal or omit the origin.

### arithmetic-first

The distinct-angle prime family, both upper quadrants and the negative-real-part endpoint exception are retained. Mean integration precedes the constrained shape limit. The residue multiplier is +2pi; the rational radial primitive applies for k=(p^2-1)/2 divisible by four, for either sign of d. Both ordered charts add with the same phase. Lower derivatives remain bounded through k-2 and logarithmic at k-1.

### signed-selected

T_N^sigma retains both signed product denominators. Negation/conjugation is an identity of auxiliary integrals and does not assert evenness of physical X_H. The weighted deformation includes its current; the selected integral is estimated on its protected disk before Cauchy. The compact roots may leave the unit disk on continued neighborhoods; the complete-pair estimate, rather than a disk Schur assertion, supplies the bound.

### original-tail

The fixed cutoff partition and all branch/compact/current supports are unchanged. Same-group contraction, non-strict cross bounds and uniform named-pair bounds are used with reserved slack. Margins precede slack and sliver width. The original c epsilon disk and occupancy-independent one-body majorant retain their domains. Microcore and equality inclusions are valid for every finite tail order; coarea multiplicity and translated period boxes are charged exactly once.

### mixed-current

All intermediate sectors retain fixed-domain differentiation before absolute coarea and all previous puncture-flux checks. The large-current disk is chosen after tau and before epsilon_0, so the sheet margin persists. Limiting distance from W=-1 is a distance of W-values. High orders use c min(1,N epsilon)>=c epsilon on epsilon<=1; this follows from the elementary bound 1-e^(-a x)>=c_a min(1,x), and does not use the false unbounded-index linear lower bound.

### onsite-tail

The onsite norm series is estimated independently before the infinite tail is assembled. In the physical consistency check, sigma=1 gives exactly the ordinary T_N, so T_N^1 is the same offsite integral. Onsite spin-square gives prefactor times sum f_N=1, then C_N=f_N+2T_N^1 gives the displayed full susceptibility. The absolute full-site tail still holds for every 0<=j<=k and all odd N>p.

### closure-calculus

The full odd infinite series, the first coefficient and every product-rule derivative are retained. The pole-counting recurrence still differentiates the unfactored numerator on a fixed smooth real domain. Overlapping weighted charts use their own fields, preserving each frozen-product identity independently. Shape radius and phase measure are not counted twice. Density and inversion t=1/s yield every unit-circle point.

### constants-citations

The original radial radius constant c_0 and original-disk constant c_O refer to the explicitly defined constants in the proof, distinct from protected-disk c_P. Replacing c_1 by c_O in the dependency table repairs the table referent without changing a chosen radius or quantifier. Bibliography locator cleanup retains the same real physical input; removal of the internal Snapshot self-citation does not import or discard any theorem premise.

## All changed passages

The exhaustive ledger records exact removed/added text, both paragraph contexts and classifications. Intermediate Reader changes are included separately, so the pinned Reader route cannot silently substitute another original.

- `HT_Reader:source-final:0001` (source_to_final): source [36, 36] → target [36, 36]; **NONLOADBEARING**; checked dependency node `physical`. Exact text and reason: `MATH_DIFF_LEDGER.json`.
- `HT_Reader:source-final:0003` (source_to_final): source [38, 39] → target [38, 39]; **NONLOADBEARING**; checked dependency node `physical`. Exact text and reason: `MATH_DIFF_LEDGER.json`.
- `HT_Reader:source-final:0005` (source_to_final): source [43, 53] → target [43, 53]; **MATHEMATICALLY_EQUIVALENT**; checked dependency node `physical`. Exact text and reason: `MATH_DIFF_LEDGER.json`.
- `HT_Reader:source-final:0007` (source_to_final): source [90, 90] → target [90, 100]; **MATHEMATICALLY_EQUIVALENT**; checked dependency node `physical`. Exact text and reason: `MATH_DIFF_LEDGER.json`.
- `HT_Reader:source-final:0009` (source_to_final): source [94, 101] → target [104, 127]; **NONLOADBEARING**; checked dependency node `physical`. Exact text and reason: `MATH_DIFF_LEDGER.json`.
- `HT_Reader:source-final:0011` (source_to_final): source [106, 105] → target [132, 138]; **MATHEMATICALLY_EQUIVALENT**; checked dependency node `physical`. Exact text and reason: `MATH_DIFF_LEDGER.json`.
- `HT_Reader:source-final:0013` (source_to_final): source [132, 133] → target [165, 167]; **MATHEMATICALLY_EQUIVALENT**; checked dependency node `physical`. Exact text and reason: `MATH_DIFF_LEDGER.json`.
- `HT_Reader:source-final:0015` (source_to_final): source [170, 169] → target [204, 205]; **MATHEMATICALLY_EQUIVALENT**; checked dependency node `physical`. Exact text and reason: `MATH_DIFF_LEDGER.json`.
- `HT_Reader:source-final:0017` (source_to_final): source [171, 171] → target [207, 207]; **MATHEMATICALLY_EQUIVALENT**; checked dependency node `physical`. Exact text and reason: `MATH_DIFF_LEDGER.json`.
- `HT_Reader:source-final:0019` (source_to_final): source [183, 183] → target [219, 219]; **MATHEMATICALLY_EQUIVALENT**; checked dependency node `physical`. Exact text and reason: `MATH_DIFF_LEDGER.json`.
- `HT_Reader:source-final:0021` (source_to_final): source [231, 231] → target [267, 267]; **MATHEMATICALLY_EQUIVALENT**; checked dependency node `physical`. Exact text and reason: `MATH_DIFF_LEDGER.json`.
- `HT_Reader:source-final:0023` (source_to_final): source [240, 240] → target [276, 276]; **MATHEMATICALLY_EQUIVALENT**; checked dependency node `physical`. Exact text and reason: `MATH_DIFF_LEDGER.json`.
- `HT_Reader:source-final:0025` (source_to_final): source [259, 258] → target [295, 300]; **MATHEMATICALLY_EQUIVALENT**; checked dependency node `arithmetic-first`. Exact text and reason: `MATH_DIFF_LEDGER.json`.
- `HT_Reader:source-final:0027` (source_to_final): source [279, 279] → target [321, 321]; **MATHEMATICALLY_EQUIVALENT**; checked dependency node `arithmetic-first`. Exact text and reason: `MATH_DIFF_LEDGER.json`.
- `HT_Reader:source-final:0029` (source_to_final): source [294, 294] → target [336, 336]; **MATHEMATICALLY_EQUIVALENT**; checked dependency node `arithmetic-first`. Exact text and reason: `MATH_DIFF_LEDGER.json`.
- `HT_Reader:source-final:0031` (source_to_final): source [303, 303] → target [345, 345]; **MATHEMATICALLY_EQUIVALENT**; checked dependency node `arithmetic-first`. Exact text and reason: `MATH_DIFF_LEDGER.json`.
- `HT_Reader:source-final:0033` (source_to_final): source [338, 337] → target [380, 385]; **MATHEMATICALLY_EQUIVALENT**; checked dependency node `arithmetic-first`. Exact text and reason: `MATH_DIFF_LEDGER.json`.
- `HT_Reader:source-final:0035` (source_to_final): source [380, 381] → target [428, 429]; **MATHEMATICALLY_EQUIVALENT**; checked dependency node `arithmetic-first`. Exact text and reason: `MATH_DIFF_LEDGER.json`.
- `HT_Reader:source-final:0037` (source_to_final): source [423, 424] → target [471, 471]; **MATHEMATICALLY_EQUIVALENT**; checked dependency node `arithmetic-first`. Exact text and reason: `MATH_DIFF_LEDGER.json`.
- `HT_Reader:source-final:0039` (source_to_final): source [435, 435] → target [482, 482]; **MATHEMATICALLY_EQUIVALENT**; checked dependency node `arithmetic-first`. Exact text and reason: `MATH_DIFF_LEDGER.json`.
- `HT_Reader:source-final:0041` (source_to_final): source [456, 456] → target [503, 503]; **MATHEMATICALLY_EQUIVALENT**; checked dependency node `arithmetic-first`. Exact text and reason: `MATH_DIFF_LEDGER.json`.
- `HT_Reader:source-final:0043` (source_to_final): source [499, 500] → target [546, 547]; **MATHEMATICALLY_EQUIVALENT**; checked dependency node `arithmetic-first`. Exact text and reason: `MATH_DIFF_LEDGER.json`.
- `HT_Reader:source-final:0045` (source_to_final): source [502, 502] → target [549, 549]; **MATHEMATICALLY_EQUIVALENT**; checked dependency node `arithmetic-first`. Exact text and reason: `MATH_DIFF_LEDGER.json`.
- `HT_Reader:source-final:0047` (source_to_final): source [517, 518] → target [564, 565]; **MATHEMATICALLY_EQUIVALENT**; checked dependency node `arithmetic-first`. Exact text and reason: `MATH_DIFF_LEDGER.json`.
- `HT_Reader:source-final:0049` (source_to_final): source [548, 547] → target [595, 599]; **MATHEMATICALLY_EQUIVALENT**; checked dependency node `signed-selected`. Exact text and reason: `MATH_DIFF_LEDGER.json`.
- `HT_Reader:source-final:0051` (source_to_final): source [564, 566] → target [616, 617]; **MATHEMATICALLY_EQUIVALENT**; checked dependency node `signed-selected`. Exact text and reason: `MATH_DIFF_LEDGER.json`.
- `HT_Reader:source-final:0053` (source_to_final): source [582, 581] → target [633, 637]; **MATHEMATICALLY_EQUIVALENT**; checked dependency node `signed-selected`. Exact text and reason: `MATH_DIFF_LEDGER.json`.
- `HT_Reader:source-final:0055` (source_to_final): source [623, 623] → target [679, 678]; **NONLOADBEARING**; checked dependency node `signed-selected`. Exact text and reason: `MATH_DIFF_LEDGER.json`.
- `HT_Reader:source-final:0057` (source_to_final): source [667, 669] → target [722, 724]; **MATHEMATICALLY_EQUIVALENT**; checked dependency node `signed-selected`. Exact text and reason: `MATH_DIFF_LEDGER.json`.
- `HT_Reader:source-final:0059` (source_to_final): source [705, 705] → target [760, 765]; **MATHEMATICALLY_EQUIVALENT**; checked dependency node `signed-selected`. Exact text and reason: `MATH_DIFF_LEDGER.json`.
- `HT_Reader:source-final:0061` (source_to_final): source [710, 710] → target [770, 770]; **MATHEMATICALLY_EQUIVALENT**; checked dependency node `signed-selected`. Exact text and reason: `MATH_DIFF_LEDGER.json`.
- `HT_Reader:source-final:0063` (source_to_final): source [731, 731] → target [791, 791]; **MATHEMATICALLY_EQUIVALENT**; checked dependency node `signed-selected`. Exact text and reason: `MATH_DIFF_LEDGER.json`.
- `HT_Reader:source-final:0065` (source_to_final): source [765, 766] → target [825, 826]; **MATHEMATICALLY_EQUIVALENT**; checked dependency node `signed-selected`. Exact text and reason: `MATH_DIFF_LEDGER.json`.
- `HT_Reader:source-final:0067` (source_to_final): source [793, 793] → target [853, 853]; **MATHEMATICALLY_EQUIVALENT**; checked dependency node `signed-selected`. Exact text and reason: `MATH_DIFF_LEDGER.json`.
- `HT_Reader:source-final:0069` (source_to_final): source [834, 835] → target [894, 900]; **MATHEMATICALLY_EQUIVALENT**; checked dependency node `original-tail`. Exact text and reason: `MATH_DIFF_LEDGER.json`.
- `HT_Reader:source-final:0071` (source_to_final): source [913, 913] → target [978, 977]; **NONLOADBEARING**; checked dependency node `original-tail`. Exact text and reason: `MATH_DIFF_LEDGER.json`.
- `HT_Reader:source-final:0073` (source_to_final): source [938, 938] → target [1002, 1002]; **NONLOADBEARING**; checked dependency node `original-tail`. Exact text and reason: `MATH_DIFF_LEDGER.json`.
- `HT_Reader:source-final:0075` (source_to_final): source [983, 983] → target [1047, 1047]; **MATHEMATICALLY_EQUIVALENT**; checked dependency node `original-tail`. Exact text and reason: `MATH_DIFF_LEDGER.json`.
- `HT_Reader:source-final:0077` (source_to_final): source [1014, 1014] → target [1078, 1078]; **MATHEMATICALLY_EQUIVALENT**; checked dependency node `original-tail`. Exact text and reason: `MATH_DIFF_LEDGER.json`.
- `HT_Reader:source-final:0079` (source_to_final): source [1025, 1025] → target [1089, 1089]; **MATHEMATICALLY_EQUIVALENT**; checked dependency node `original-tail`. Exact text and reason: `MATH_DIFF_LEDGER.json`.
- `HT_Reader:source-final:0081` (source_to_final): source [1027, 1027] → target [1091, 1091]; **MATHEMATICALLY_EQUIVALENT**; checked dependency node `original-tail`. Exact text and reason: `MATH_DIFF_LEDGER.json`.
- `HT_Reader:source-final:0083` (source_to_final): source [1074, 1075] → target [1138, 1139]; **MATHEMATICALLY_EQUIVALENT**; checked dependency node `original-tail`. Exact text and reason: `MATH_DIFF_LEDGER.json`.
- `HT_Reader:source-final:0085` (source_to_final): source [1114, 1114] → target [1178, 1178]; **MATHEMATICALLY_EQUIVALENT**; checked dependency node `original-tail`. Exact text and reason: `MATH_DIFF_LEDGER.json`.
- `HT_Reader:source-final:0087` (source_to_final): source [1123, 1123] → target [1187, 1187]; **MATHEMATICALLY_EQUIVALENT**; checked dependency node `original-tail`. Exact text and reason: `MATH_DIFF_LEDGER.json`.
- `HT_Reader:source-final:0089` (source_to_final): source [1168, 1168] → target [1232, 1232]; **MATHEMATICALLY_EQUIVALENT**; checked dependency node `original-tail`. Exact text and reason: `MATH_DIFF_LEDGER.json`.
- `HT_Reader:source-final:0091` (source_to_final): source [1184, 1188] → target [1248, 1251]; **MATHEMATICALLY_EQUIVALENT**; checked dependency node `original-tail`. Exact text and reason: `MATH_DIFF_LEDGER.json`.
- `HT_Reader:source-final:0093` (source_to_final): source [1191, 1191] → target [1254, 1253]; **NONLOADBEARING**; checked dependency node `original-tail`. Exact text and reason: `MATH_DIFF_LEDGER.json`.
- `HT_Reader:source-final:0095` (source_to_final): source [1276, 1276] → target [1338, 1337]; **NONLOADBEARING**; checked dependency node `original-tail`. Exact text and reason: `MATH_DIFF_LEDGER.json`.
- `HT_Reader:source-final:0097` (source_to_final): source [1292, 1292] → target [1353, 1354]; **MATHEMATICALLY_EQUIVALENT**; checked dependency node `original-tail`. Exact text and reason: `MATH_DIFF_LEDGER.json`.
- `HT_Reader:source-final:0099` (source_to_final): source [1333, 1333] → target [1395, 1394]; **NONLOADBEARING**; checked dependency node `original-tail`. Exact text and reason: `MATH_DIFF_LEDGER.json`.
- `HT_Reader:source-final:0101` (source_to_final): source [1342, 1342] → target [1403, 1403]; **MATHEMATICALLY_EQUIVALENT**; checked dependency node `original-tail`. Exact text and reason: `MATH_DIFF_LEDGER.json`.
- `HT_Reader:source-final:0103` (source_to_final): source [1356, 1357] → target [1417, 1418]; **MATHEMATICALLY_EQUIVALENT**; checked dependency node `original-tail`. Exact text and reason: `MATH_DIFF_LEDGER.json`.
- `HT_Reader:source-final:0105` (source_to_final): source [1359, 1359] → target [1420, 1420]; **MATHEMATICALLY_EQUIVALENT**; checked dependency node `original-tail`. Exact text and reason: `MATH_DIFF_LEDGER.json`.
- `HT_Reader:source-final:0107` (source_to_final): source [1404, 1404] → target [1465, 1465]; **MATHEMATICALLY_EQUIVALENT**; checked dependency node `original-tail`. Exact text and reason: `MATH_DIFF_LEDGER.json`.
- `HT_Reader:source-final:0109` (source_to_final): source [1447, 1448] → target [1508, 1510]; **MATHEMATICALLY_EQUIVALENT**; checked dependency node `original-tail`. Exact text and reason: `MATH_DIFF_LEDGER.json`.
- `HT_Reader:source-final:0111` (source_to_final): source [1468, 1468] → target [1530, 1535]; **MATHEMATICALLY_EQUIVALENT**; checked dependency node `mixed-current`. Exact text and reason: `MATH_DIFF_LEDGER.json`.
- `HT_Reader:source-final:0113` (source_to_final): source [1477, 1477] → target [1544, 1544]; **MATHEMATICALLY_EQUIVALENT**; checked dependency node `mixed-current`. Exact text and reason: `MATH_DIFF_LEDGER.json`.
- `HT_Reader:source-final:0115` (source_to_final): source [1533, 1533] → target [1600, 1600]; **MATHEMATICALLY_EQUIVALENT**; checked dependency node `mixed-current`. Exact text and reason: `MATH_DIFF_LEDGER.json`.
- `HT_Reader:source-final:0117` (source_to_final): source [1565, 1566] → target [1632, 1631]; **NONLOADBEARING**; checked dependency node `mixed-current`. Exact text and reason: `MATH_DIFF_LEDGER.json`.
- `HT_Reader:source-final:0119` (source_to_final): source [1572, 1572] → target [1637, 1637]; **MATHEMATICALLY_EQUIVALENT**; checked dependency node `mixed-current`. Exact text and reason: `MATH_DIFF_LEDGER.json`.
- `HT_Reader:source-final:0121` (source_to_final): source [1612, 1612] → target [1677, 1677]; **MATHEMATICALLY_EQUIVALENT**; checked dependency node `mixed-current`. Exact text and reason: `MATH_DIFF_LEDGER.json`.
- `HT_Reader:source-final:0123` (source_to_final): source [1645, 1646] → target [1710, 1711]; **MATHEMATICALLY_EQUIVALENT**; checked dependency node `mixed-current`. Exact text and reason: `MATH_DIFF_LEDGER.json`.
- `HT_Reader:source-final:0125` (source_to_final): source [1656, 1656] → target [1721, 1720]; **NONLOADBEARING**; checked dependency node `mixed-current`. Exact text and reason: `MATH_DIFF_LEDGER.json`.
- `HT_Reader:source-final:0127` (source_to_final): source [1670, 1670] → target [1734, 1734]; **MATHEMATICALLY_EQUIVALENT**; checked dependency node `mixed-current`. Exact text and reason: `MATH_DIFF_LEDGER.json`.
- `HT_Reader:source-final:0129` (source_to_final): source [1696, 1697] → target [1760, 1760]; **MATHEMATICALLY_EQUIVALENT**; checked dependency node `mixed-current`. Exact text and reason: `MATH_DIFF_LEDGER.json`.
- `HT_Reader:source-final:0131` (source_to_final): source [1718, 1718] → target [1781, 1781]; **MATHEMATICALLY_EQUIVALENT**; checked dependency node `mixed-current`. Exact text and reason: `MATH_DIFF_LEDGER.json`.
- `HT_Reader:source-final:0133` (source_to_final): source [1722, 1722] → target [1785, 1785]; **MATHEMATICALLY_EQUIVALENT**; checked dependency node `mixed-current`. Exact text and reason: `MATH_DIFF_LEDGER.json`.
- `HT_Reader:source-final:0135` (source_to_final): source [1733, 1735] → target [1796, 1798]; **MATHEMATICALLY_EQUIVALENT**; checked dependency node `mixed-current`. Exact text and reason: `MATH_DIFF_LEDGER.json`.
- `HT_Reader:source-final:0137` (source_to_final): source [1773, 1773] → target [1836, 1835]; **NONLOADBEARING**; checked dependency node `mixed-current`. Exact text and reason: `MATH_DIFF_LEDGER.json`.
- `HT_Reader:source-final:0139` (source_to_final): source [1786, 1787] → target [1848, 1849]; **MATHEMATICALLY_EQUIVALENT**; checked dependency node `mixed-current`. Exact text and reason: `MATH_DIFF_LEDGER.json`.
- `HT_Reader:source-final:0141` (source_to_final): source [1794, 1793] → target [1856, 1861]; **MATHEMATICALLY_EQUIVALENT**; checked dependency node `onsite-tail`. Exact text and reason: `MATH_DIFF_LEDGER.json`.
- `HT_Reader:source-final:0143` (source_to_final): source [1863, 1864] → target [1931, 1932]; **MATHEMATICALLY_EQUIVALENT**; checked dependency node `onsite-tail`. Exact text and reason: `MATH_DIFF_LEDGER.json`.
- `HT_Reader:source-final:0145` (source_to_final): source [1881, 1881] → target [1949, 1949]; **MATHEMATICALLY_EQUIVALENT**; checked dependency node `onsite-tail`. Exact text and reason: `MATH_DIFF_LEDGER.json`.
- `HT_Reader:source-final:0147` (source_to_final): source [1886, 1887] → target [1954, 1955]; **MATHEMATICALLY_EQUIVALENT**; checked dependency node `onsite-tail`. Exact text and reason: `MATH_DIFF_LEDGER.json`.
- `HT_Reader:source-final:0149` (source_to_final): source [1902, 1902] → target [1970, 1970]; **MATHEMATICALLY_EQUIVALENT**; checked dependency node `onsite-tail`. Exact text and reason: `MATH_DIFF_LEDGER.json`.
- `HT_Reader:source-final:0151` (source_to_final): source [1907, 1907] → target [1975, 1975]; **MATHEMATICALLY_EQUIVALENT**; checked dependency node `onsite-tail`. Exact text and reason: `MATH_DIFF_LEDGER.json`.
- `HT_Reader:source-final:0153` (source_to_final): source [1923, 1923] → target [1991, 1991]; **MATHEMATICALLY_EQUIVALENT**; checked dependency node `onsite-tail`. Exact text and reason: `MATH_DIFF_LEDGER.json`.
- `HT_Reader:source-final:0155` (source_to_final): source [1940, 1939] → target [2008, 2012]; **MATHEMATICALLY_EQUIVALENT**; checked dependency node `closure-calculus`. Exact text and reason: `MATH_DIFF_LEDGER.json`.
- `HT_Reader:source-final:0157` (source_to_final): source [1990, 1992] → target [2063, 2068]; **MATHEMATICALLY_EQUIVALENT**; checked dependency node `closure-calculus`. Exact text and reason: `MATH_DIFF_LEDGER.json`.
- `HT_Reader:source-final:0159` (source_to_final): source [2026, 2029] → target [2102, 2105]; **MATHEMATICALLY_EQUIVALENT**; checked dependency node `closure-calculus`. Exact text and reason: `MATH_DIFF_LEDGER.json`.
- `HT_Reader:source-final:0161` (source_to_final): source [2161, 2164] → target [2237, 2240]; **MATHEMATICALLY_EQUIVALENT**; checked dependency node `closure-calculus`. Exact text and reason: `MATH_DIFF_LEDGER.json`.
- `HT_Reader:source-final:0163` (source_to_final): source [2204, 2205] → target [2280, 2281]; **MATHEMATICALLY_EQUIVALENT**; checked dependency node `closure-calculus`. Exact text and reason: `MATH_DIFF_LEDGER.json`.
- `HT_Reader:source-final:0165` (source_to_final): source [2246, 2246] → target [2322, 2322]; **NONLOADBEARING**; checked dependency node `closure-calculus`. Exact text and reason: `MATH_DIFF_LEDGER.json`.
- `HT_Reader:source-final:0167` (source_to_final): source [2324, 2328] → target [2400, 2404]; **MATHEMATICALLY_EQUIVALENT**; checked dependency node `closure-calculus`. Exact text and reason: `MATH_DIFF_LEDGER.json`.
- `HT_Reader:source-final:0169` (source_to_final): source [2334, 2336] → target [2410, 2413]; **MATHEMATICALLY_EQUIVALENT**; checked dependency node `constants-citations`. Exact text and reason: `MATH_DIFF_LEDGER.json`.
- `HT_Reader:source-final:0171` (source_to_final): source [2416, 2416] → target [2493, 2493]; **MATHEMATICALLY_EQUIVALENT**; checked dependency node `constants-citations`. Exact text and reason: `MATH_DIFF_LEDGER.json`.
- `HT_Reader:source-final:0173` (source_to_final): source [2465, 2464] → target [2542, 2542]; **NONLOADBEARING**; checked dependency node `constants-citations`. Exact text and reason: `MATH_DIFF_LEDGER.json`.
- `HT_Reader:source-final:0175` (source_to_final): source [2472, 2474] → target [2550, 2550]; **MATHEMATICALLY_EQUIVALENT**; checked dependency node `constants-citations`. Exact text and reason: `MATH_DIFF_LEDGER.json`.
- `HT_Reader:source-final:0177` (source_to_final): source [2480, 2481] → target [2556, 2557]; **MATHEMATICALLY_EQUIVALENT**; checked dependency node `constants-citations`. Exact text and reason: `MATH_DIFF_LEDGER.json`.
- `HT_Reader:source-final:0179` (source_to_final): source [2488, 2490] → target [2564, 2564]; **MATHEMATICALLY_EQUIVALENT**; checked dependency node `constants-citations`. Exact text and reason: `MATH_DIFF_LEDGER.json`.
- `HT_Reader:source-final:0181` (source_to_final): source [2492, 2500] → target [2566, 2565]; **NONLOADBEARING**; checked dependency node `constants-citations`. Exact text and reason: `MATH_DIFF_LEDGER.json`.
- `HT_Reader:pre13-final:0001` (pre13_to_final): source [1760, 1761] → target [1760, 1760]; **MATHEMATICALLY_EQUIVALENT**; checked dependency node `mixed-current`. Exact text and reason: `MATH_DIFF_LEDGER.json`.
- `HT_Reader:pre13-final:0003` (pre13_to_final): source [1950, 1950] → target [1949, 1949]; **MATHEMATICALLY_EQUIVALENT**; checked dependency node `onsite-tail`. Exact text and reason: `MATH_DIFF_LEDGER.json`.
- `HT_Reader:pre13-final:0005` (pre13_to_final): source [2494, 2494] → target [2493, 2493]; **MATHEMATICALLY_EQUIVALENT**; checked dependency node `constants-citations`. Exact text and reason: `MATH_DIFF_LEDGER.json`.
- `HT_Reader:source-reader:0001` (source_to_reader): source [36, 36] → target [36, 36]; **NONLOADBEARING**; checked dependency node `physical`. Exact text and reason: `MATH_DIFF_LEDGER.json`.
- `HT_Reader:source-reader:0003` (source_to_reader): source [38, 39] → target [38, 39]; **NONLOADBEARING**; checked dependency node `physical`. Exact text and reason: `MATH_DIFF_LEDGER.json`.
- `HT_Reader:source-reader:0005` (source_to_reader): source [43, 53] → target [43, 55]; **MATHEMATICALLY_EQUIVALENT**; checked dependency node `physical`. Exact text and reason: `MATH_DIFF_LEDGER.json`.
- `HT_Reader:source-reader:0007` (source_to_reader): source [94, 101] → target [96, 124]; **MATHEMATICALLY_EQUIVALENT**; checked dependency node `physical`. Exact text and reason: `MATH_DIFF_LEDGER.json`.
- `HT_Reader:source-reader:0009` (source_to_reader): source [106, 105] → target [129, 135]; **MATHEMATICALLY_EQUIVALENT**; checked dependency node `physical`. Exact text and reason: `MATH_DIFF_LEDGER.json`.
- `HT_Reader:source-reader:0011` (source_to_reader): source [132, 133] → target [162, 164]; **MATHEMATICALLY_EQUIVALENT**; checked dependency node `physical`. Exact text and reason: `MATH_DIFF_LEDGER.json`.
- `HT_Reader:source-reader:0013` (source_to_reader): source [170, 169] → target [201, 202]; **MATHEMATICALLY_EQUIVALENT**; checked dependency node `physical`. Exact text and reason: `MATH_DIFF_LEDGER.json`.
- `HT_Reader:source-reader:0015` (source_to_reader): source [171, 171] → target [204, 204]; **MATHEMATICALLY_EQUIVALENT**; checked dependency node `physical`. Exact text and reason: `MATH_DIFF_LEDGER.json`.
- `HT_Reader:source-reader:0017` (source_to_reader): source [183, 183] → target [216, 216]; **MATHEMATICALLY_EQUIVALENT**; checked dependency node `physical`. Exact text and reason: `MATH_DIFF_LEDGER.json`.
- `HT_Reader:source-reader:0019` (source_to_reader): source [231, 231] → target [264, 264]; **MATHEMATICALLY_EQUIVALENT**; checked dependency node `physical`. Exact text and reason: `MATH_DIFF_LEDGER.json`.
- `HT_Reader:source-reader:0021` (source_to_reader): source [240, 240] → target [273, 273]; **MATHEMATICALLY_EQUIVALENT**; checked dependency node `physical`. Exact text and reason: `MATH_DIFF_LEDGER.json`.
- `HT_Reader:source-reader:0023` (source_to_reader): source [259, 258] → target [292, 297]; **MATHEMATICALLY_EQUIVALENT**; checked dependency node `arithmetic-first`. Exact text and reason: `MATH_DIFF_LEDGER.json`.
- `HT_Reader:source-reader:0025` (source_to_reader): source [279, 279] → target [318, 318]; **MATHEMATICALLY_EQUIVALENT**; checked dependency node `arithmetic-first`. Exact text and reason: `MATH_DIFF_LEDGER.json`.
- `HT_Reader:source-reader:0027` (source_to_reader): source [294, 294] → target [333, 333]; **MATHEMATICALLY_EQUIVALENT**; checked dependency node `arithmetic-first`. Exact text and reason: `MATH_DIFF_LEDGER.json`.
- `HT_Reader:source-reader:0029` (source_to_reader): source [303, 303] → target [342, 342]; **MATHEMATICALLY_EQUIVALENT**; checked dependency node `arithmetic-first`. Exact text and reason: `MATH_DIFF_LEDGER.json`.
- `HT_Reader:source-reader:0031` (source_to_reader): source [338, 337] → target [377, 382]; **MATHEMATICALLY_EQUIVALENT**; checked dependency node `arithmetic-first`. Exact text and reason: `MATH_DIFF_LEDGER.json`.
- `HT_Reader:source-reader:0033` (source_to_reader): source [423, 424] → target [468, 468]; **MATHEMATICALLY_EQUIVALENT**; checked dependency node `arithmetic-first`. Exact text and reason: `MATH_DIFF_LEDGER.json`.
- `HT_Reader:source-reader:0035` (source_to_reader): source [435, 435] → target [479, 479]; **MATHEMATICALLY_EQUIVALENT**; checked dependency node `arithmetic-first`. Exact text and reason: `MATH_DIFF_LEDGER.json`.
- `HT_Reader:source-reader:0037` (source_to_reader): source [456, 456] → target [500, 500]; **MATHEMATICALLY_EQUIVALENT**; checked dependency node `arithmetic-first`. Exact text and reason: `MATH_DIFF_LEDGER.json`.
- `HT_Reader:source-reader:0039` (source_to_reader): source [502, 502] → target [546, 546]; **MATHEMATICALLY_EQUIVALENT**; checked dependency node `arithmetic-first`. Exact text and reason: `MATH_DIFF_LEDGER.json`.
- `HT_Reader:source-reader:0041` (source_to_reader): source [548, 547] → target [592, 596]; **MATHEMATICALLY_EQUIVALENT**; checked dependency node `signed-selected`. Exact text and reason: `MATH_DIFF_LEDGER.json`.
- `HT_Reader:source-reader:0043` (source_to_reader): source [564, 566] → target [613, 614]; **MATHEMATICALLY_EQUIVALENT**; checked dependency node `signed-selected`. Exact text and reason: `MATH_DIFF_LEDGER.json`.
- `HT_Reader:source-reader:0045` (source_to_reader): source [582, 581] → target [630, 634]; **MATHEMATICALLY_EQUIVALENT**; checked dependency node `signed-selected`. Exact text and reason: `MATH_DIFF_LEDGER.json`.
- `HT_Reader:source-reader:0047` (source_to_reader): source [623, 623] → target [676, 675]; **NONLOADBEARING**; checked dependency node `signed-selected`. Exact text and reason: `MATH_DIFF_LEDGER.json`.
- `HT_Reader:source-reader:0049` (source_to_reader): source [667, 669] → target [719, 721]; **MATHEMATICALLY_EQUIVALENT**; checked dependency node `signed-selected`. Exact text and reason: `MATH_DIFF_LEDGER.json`.
- `HT_Reader:source-reader:0051` (source_to_reader): source [705, 705] → target [757, 762]; **MATHEMATICALLY_EQUIVALENT**; checked dependency node `signed-selected`. Exact text and reason: `MATH_DIFF_LEDGER.json`.
- `HT_Reader:source-reader:0053` (source_to_reader): source [710, 710] → target [767, 767]; **MATHEMATICALLY_EQUIVALENT**; checked dependency node `signed-selected`. Exact text and reason: `MATH_DIFF_LEDGER.json`.
- `HT_Reader:source-reader:0055` (source_to_reader): source [731, 731] → target [788, 788]; **MATHEMATICALLY_EQUIVALENT**; checked dependency node `signed-selected`. Exact text and reason: `MATH_DIFF_LEDGER.json`.
- `HT_Reader:source-reader:0057` (source_to_reader): source [793, 793] → target [850, 850]; **MATHEMATICALLY_EQUIVALENT**; checked dependency node `signed-selected`. Exact text and reason: `MATH_DIFF_LEDGER.json`.
- `HT_Reader:source-reader:0059` (source_to_reader): source [834, 835] → target [891, 897]; **MATHEMATICALLY_EQUIVALENT**; checked dependency node `original-tail`. Exact text and reason: `MATH_DIFF_LEDGER.json`.
- `HT_Reader:source-reader:0061` (source_to_reader): source [913, 913] → target [975, 974]; **NONLOADBEARING**; checked dependency node `original-tail`. Exact text and reason: `MATH_DIFF_LEDGER.json`.
- `HT_Reader:source-reader:0063` (source_to_reader): source [938, 938] → target [999, 999]; **NONLOADBEARING**; checked dependency node `original-tail`. Exact text and reason: `MATH_DIFF_LEDGER.json`.
- `HT_Reader:source-reader:0065` (source_to_reader): source [983, 983] → target [1044, 1044]; **MATHEMATICALLY_EQUIVALENT**; checked dependency node `original-tail`. Exact text and reason: `MATH_DIFF_LEDGER.json`.
- `HT_Reader:source-reader:0067` (source_to_reader): source [1027, 1027] → target [1088, 1088]; **MATHEMATICALLY_EQUIVALENT**; checked dependency node `original-tail`. Exact text and reason: `MATH_DIFF_LEDGER.json`.
- `HT_Reader:source-reader:0069` (source_to_reader): source [1074, 1075] → target [1135, 1136]; **MATHEMATICALLY_EQUIVALENT**; checked dependency node `original-tail`. Exact text and reason: `MATH_DIFF_LEDGER.json`.
- `HT_Reader:source-reader:0071` (source_to_reader): source [1114, 1114] → target [1175, 1175]; **MATHEMATICALLY_EQUIVALENT**; checked dependency node `original-tail`. Exact text and reason: `MATH_DIFF_LEDGER.json`.
- `HT_Reader:source-reader:0073` (source_to_reader): source [1123, 1123] → target [1184, 1184]; **MATHEMATICALLY_EQUIVALENT**; checked dependency node `original-tail`. Exact text and reason: `MATH_DIFF_LEDGER.json`.
- `HT_Reader:source-reader:0075` (source_to_reader): source [1168, 1168] → target [1229, 1229]; **MATHEMATICALLY_EQUIVALENT**; checked dependency node `original-tail`. Exact text and reason: `MATH_DIFF_LEDGER.json`.
- `HT_Reader:source-reader:0077` (source_to_reader): source [1184, 1188] → target [1245, 1248]; **MATHEMATICALLY_EQUIVALENT**; checked dependency node `original-tail`. Exact text and reason: `MATH_DIFF_LEDGER.json`.
- `HT_Reader:source-reader:0079` (source_to_reader): source [1191, 1191] → target [1251, 1250]; **NONLOADBEARING**; checked dependency node `original-tail`. Exact text and reason: `MATH_DIFF_LEDGER.json`.
- `HT_Reader:source-reader:0081` (source_to_reader): source [1276, 1276] → target [1335, 1334]; **NONLOADBEARING**; checked dependency node `original-tail`. Exact text and reason: `MATH_DIFF_LEDGER.json`.
- `HT_Reader:source-reader:0083` (source_to_reader): source [1292, 1292] → target [1350, 1351]; **MATHEMATICALLY_EQUIVALENT**; checked dependency node `original-tail`. Exact text and reason: `MATH_DIFF_LEDGER.json`.
- `HT_Reader:source-reader:0085` (source_to_reader): source [1333, 1333] → target [1392, 1391]; **NONLOADBEARING**; checked dependency node `original-tail`. Exact text and reason: `MATH_DIFF_LEDGER.json`.
- `HT_Reader:source-reader:0087` (source_to_reader): source [1342, 1342] → target [1400, 1400]; **MATHEMATICALLY_EQUIVALENT**; checked dependency node `original-tail`. Exact text and reason: `MATH_DIFF_LEDGER.json`.
- `HT_Reader:source-reader:0089` (source_to_reader): source [1356, 1357] → target [1414, 1415]; **MATHEMATICALLY_EQUIVALENT**; checked dependency node `original-tail`. Exact text and reason: `MATH_DIFF_LEDGER.json`.
- `HT_Reader:source-reader:0091` (source_to_reader): source [1359, 1359] → target [1417, 1417]; **MATHEMATICALLY_EQUIVALENT**; checked dependency node `original-tail`. Exact text and reason: `MATH_DIFF_LEDGER.json`.
- `HT_Reader:source-reader:0093` (source_to_reader): source [1404, 1404] → target [1462, 1462]; **MATHEMATICALLY_EQUIVALENT**; checked dependency node `original-tail`. Exact text and reason: `MATH_DIFF_LEDGER.json`.
- `HT_Reader:source-reader:0095` (source_to_reader): source [1447, 1448] → target [1505, 1507]; **MATHEMATICALLY_EQUIVALENT**; checked dependency node `original-tail`. Exact text and reason: `MATH_DIFF_LEDGER.json`.
- `HT_Reader:source-reader:0097` (source_to_reader): source [1468, 1468] → target [1527, 1532]; **MATHEMATICALLY_EQUIVALENT**; checked dependency node `mixed-current`. Exact text and reason: `MATH_DIFF_LEDGER.json`.
- `HT_Reader:source-reader:0099` (source_to_reader): source [1477, 1477] → target [1541, 1541]; **MATHEMATICALLY_EQUIVALENT**; checked dependency node `mixed-current`. Exact text and reason: `MATH_DIFF_LEDGER.json`.
- `HT_Reader:source-reader:0101` (source_to_reader): source [1533, 1533] → target [1597, 1597]; **MATHEMATICALLY_EQUIVALENT**; checked dependency node `mixed-current`. Exact text and reason: `MATH_DIFF_LEDGER.json`.
- `HT_Reader:source-reader:0103` (source_to_reader): source [1565, 1566] → target [1629, 1628]; **NONLOADBEARING**; checked dependency node `mixed-current`. Exact text and reason: `MATH_DIFF_LEDGER.json`.
- `HT_Reader:source-reader:0105` (source_to_reader): source [1572, 1572] → target [1634, 1634]; **MATHEMATICALLY_EQUIVALENT**; checked dependency node `mixed-current`. Exact text and reason: `MATH_DIFF_LEDGER.json`.
- `HT_Reader:source-reader:0107` (source_to_reader): source [1612, 1612] → target [1674, 1674]; **MATHEMATICALLY_EQUIVALENT**; checked dependency node `mixed-current`. Exact text and reason: `MATH_DIFF_LEDGER.json`.
- `HT_Reader:source-reader:0109` (source_to_reader): source [1645, 1646] → target [1707, 1708]; **MATHEMATICALLY_EQUIVALENT**; checked dependency node `mixed-current`. Exact text and reason: `MATH_DIFF_LEDGER.json`.
- `HT_Reader:source-reader:0111` (source_to_reader): source [1656, 1656] → target [1718, 1717]; **NONLOADBEARING**; checked dependency node `mixed-current`. Exact text and reason: `MATH_DIFF_LEDGER.json`.
- `HT_Reader:source-reader:0113` (source_to_reader): source [1670, 1670] → target [1731, 1731]; **MATHEMATICALLY_EQUIVALENT**; checked dependency node `mixed-current`. Exact text and reason: `MATH_DIFF_LEDGER.json`.
- `HT_Reader:source-reader:0115` (source_to_reader): source [1722, 1722] → target [1783, 1783]; **MATHEMATICALLY_EQUIVALENT**; checked dependency node `mixed-current`. Exact text and reason: `MATH_DIFF_LEDGER.json`.
- `HT_Reader:source-reader:0117` (source_to_reader): source [1733, 1735] → target [1794, 1796]; **MATHEMATICALLY_EQUIVALENT**; checked dependency node `mixed-current`. Exact text and reason: `MATH_DIFF_LEDGER.json`.
- `HT_Reader:source-reader:0119` (source_to_reader): source [1773, 1773] → target [1834, 1833]; **NONLOADBEARING**; checked dependency node `mixed-current`. Exact text and reason: `MATH_DIFF_LEDGER.json`.
- `HT_Reader:source-reader:0121` (source_to_reader): source [1794, 1793] → target [1854, 1859]; **MATHEMATICALLY_EQUIVALENT**; checked dependency node `onsite-tail`. Exact text and reason: `MATH_DIFF_LEDGER.json`.
- `HT_Reader:source-reader:0123` (source_to_reader): source [1863, 1864] → target [1929, 1930]; **MATHEMATICALLY_EQUIVALENT**; checked dependency node `onsite-tail`. Exact text and reason: `MATH_DIFF_LEDGER.json`.
- `HT_Reader:source-reader:0125` (source_to_reader): source [1886, 1887] → target [1952, 1953]; **MATHEMATICALLY_EQUIVALENT**; checked dependency node `onsite-tail`. Exact text and reason: `MATH_DIFF_LEDGER.json`.
- `HT_Reader:source-reader:0127` (source_to_reader): source [1902, 1902] → target [1968, 1968]; **MATHEMATICALLY_EQUIVALENT**; checked dependency node `onsite-tail`. Exact text and reason: `MATH_DIFF_LEDGER.json`.
- `HT_Reader:source-reader:0129` (source_to_reader): source [1907, 1907] → target [1973, 1973]; **MATHEMATICALLY_EQUIVALENT**; checked dependency node `onsite-tail`. Exact text and reason: `MATH_DIFF_LEDGER.json`.
- `HT_Reader:source-reader:0131` (source_to_reader): source [1923, 1923] → target [1989, 1989]; **MATHEMATICALLY_EQUIVALENT**; checked dependency node `onsite-tail`. Exact text and reason: `MATH_DIFF_LEDGER.json`.
- `HT_Reader:source-reader:0133` (source_to_reader): source [1940, 1939] → target [2006, 2010]; **MATHEMATICALLY_EQUIVALENT**; checked dependency node `closure-calculus`. Exact text and reason: `MATH_DIFF_LEDGER.json`.
- `HT_Reader:source-reader:0135` (source_to_reader): source [1990, 1992] → target [2061, 2066]; **MATHEMATICALLY_EQUIVALENT**; checked dependency node `closure-calculus`. Exact text and reason: `MATH_DIFF_LEDGER.json`.
- `HT_Reader:source-reader:0137` (source_to_reader): source [2026, 2029] → target [2100, 2103]; **MATHEMATICALLY_EQUIVALENT**; checked dependency node `closure-calculus`. Exact text and reason: `MATH_DIFF_LEDGER.json`.
- `HT_Reader:source-reader:0139` (source_to_reader): source [2161, 2164] → target [2235, 2238]; **MATHEMATICALLY_EQUIVALENT**; checked dependency node `closure-calculus`. Exact text and reason: `MATH_DIFF_LEDGER.json`.
- `HT_Reader:source-reader:0141` (source_to_reader): source [2204, 2205] → target [2278, 2279]; **MATHEMATICALLY_EQUIVALENT**; checked dependency node `closure-calculus`. Exact text and reason: `MATH_DIFF_LEDGER.json`.
- `HT_Reader:source-reader:0143` (source_to_reader): source [2246, 2246] → target [2320, 2320]; **NONLOADBEARING**; checked dependency node `closure-calculus`. Exact text and reason: `MATH_DIFF_LEDGER.json`.
- `HT_Reader:source-reader:0145` (source_to_reader): source [2324, 2328] → target [2398, 2402]; **MATHEMATICALLY_EQUIVALENT**; checked dependency node `closure-calculus`. Exact text and reason: `MATH_DIFF_LEDGER.json`.
- `HT_Reader:source-reader:0147` (source_to_reader): source [2334, 2336] → target [2408, 2411]; **MATHEMATICALLY_EQUIVALENT**; checked dependency node `constants-citations`. Exact text and reason: `MATH_DIFF_LEDGER.json`.
- `HT_Reader:reader-final:0001` (reader_to_final): source [39, 39] → target [39, 39]; **NONLOADBEARING**; checked dependency node `physical`. Exact text and reason: `MATH_DIFF_LEDGER.json`.
- `HT_Reader:reader-final:0003` (reader_to_final): source [53, 55] → target [53, 53]; **MATHEMATICALLY_EQUIVALENT**; checked dependency node `physical`. Exact text and reason: `MATH_DIFF_LEDGER.json`.
- `HT_Reader:reader-final:0005` (reader_to_final): source [92, 92] → target [90, 100]; **MATHEMATICALLY_EQUIVALENT**; checked dependency node `physical`. Exact text and reason: `MATH_DIFF_LEDGER.json`.
- `HT_Reader:reader-final:0007` (reader_to_final): source [96, 104] → target [104, 109]; **MATHEMATICALLY_EQUIVALENT**; checked dependency node `physical`. Exact text and reason: `MATH_DIFF_LEDGER.json`.
- `HT_Reader:reader-final:0009` (reader_to_final): source [106, 106] → target [111, 111]; **NONLOADBEARING**; checked dependency node `physical`. Exact text and reason: `MATH_DIFF_LEDGER.json`.
- `HT_Reader:reader-final:0011` (reader_to_final): source [120, 124] → target [125, 127]; **NONLOADBEARING**; checked dependency node `physical`. Exact text and reason: `MATH_DIFF_LEDGER.json`.
- `HT_Reader:reader-final:0013` (reader_to_final): source [425, 426] → target [428, 429]; **MATHEMATICALLY_EQUIVALENT**; checked dependency node `arithmetic-first`. Exact text and reason: `MATH_DIFF_LEDGER.json`.
- `HT_Reader:reader-final:0015` (reader_to_final): source [543, 544] → target [546, 547]; **MATHEMATICALLY_EQUIVALENT**; checked dependency node `arithmetic-first`. Exact text and reason: `MATH_DIFF_LEDGER.json`.
- `HT_Reader:reader-final:0017` (reader_to_final): source [561, 562] → target [564, 565]; **MATHEMATICALLY_EQUIVALENT**; checked dependency node `arithmetic-first`. Exact text and reason: `MATH_DIFF_LEDGER.json`.
- `HT_Reader:reader-final:0019` (reader_to_final): source [822, 823] → target [825, 826]; **MATHEMATICALLY_EQUIVALENT**; checked dependency node `signed-selected`. Exact text and reason: `MATH_DIFF_LEDGER.json`.
- `HT_Reader:reader-final:0021` (reader_to_final): source [1075, 1075] → target [1078, 1078]; **MATHEMATICALLY_EQUIVALENT**; checked dependency node `original-tail`. Exact text and reason: `MATH_DIFF_LEDGER.json`.
- `HT_Reader:reader-final:0023` (reader_to_final): source [1086, 1086] → target [1089, 1089]; **MATHEMATICALLY_EQUIVALENT**; checked dependency node `original-tail`. Exact text and reason: `MATH_DIFF_LEDGER.json`.
- `HT_Reader:reader-final:0025` (reader_to_final): source [1757, 1758] → target [1760, 1760]; **MATHEMATICALLY_EQUIVALENT**; checked dependency node `mixed-current`. Exact text and reason: `MATH_DIFF_LEDGER.json`.
- `HT_Reader:reader-final:0027` (reader_to_final): source [1779, 1779] → target [1781, 1781]; **MATHEMATICALLY_EQUIVALENT**; checked dependency node `mixed-current`. Exact text and reason: `MATH_DIFF_LEDGER.json`.
- `HT_Reader:reader-final:0029` (reader_to_final): source [1846, 1847] → target [1848, 1849]; **MATHEMATICALLY_EQUIVALENT**; checked dependency node `mixed-current`. Exact text and reason: `MATH_DIFF_LEDGER.json`.
- `HT_Reader:reader-final:0031` (reader_to_final): source [1947, 1947] → target [1949, 1949]; **MATHEMATICALLY_EQUIVALENT**; checked dependency node `onsite-tail`. Exact text and reason: `MATH_DIFF_LEDGER.json`.
- `HT_Reader:reader-final:0033` (reader_to_final): source [2491, 2491] → target [2493, 2493]; **MATHEMATICALLY_EQUIVALENT**; checked dependency node `constants-citations`. Exact text and reason: `MATH_DIFF_LEDGER.json`.
- `HT_Reader:reader-final:0035` (reader_to_final): source [2540, 2539] → target [2542, 2542]; **NONLOADBEARING**; checked dependency node `constants-citations`. Exact text and reason: `MATH_DIFF_LEDGER.json`.
- `HT_Reader:reader-final:0037` (reader_to_final): source [2547, 2549] → target [2550, 2550]; **MATHEMATICALLY_EQUIVALENT**; checked dependency node `constants-citations`. Exact text and reason: `MATH_DIFF_LEDGER.json`.
- `HT_Reader:reader-final:0039` (reader_to_final): source [2555, 2556] → target [2556, 2557]; **MATHEMATICALLY_EQUIVALENT**; checked dependency node `constants-citations`. Exact text and reason: `MATH_DIFF_LEDGER.json`.
- `HT_Reader:reader-final:0041` (reader_to_final): source [2563, 2565] → target [2564, 2564]; **MATHEMATICALLY_EQUIVALENT**; checked dependency node `constants-citations`. Exact text and reason: `MATH_DIFF_LEDGER.json`.
- `HT_Reader:reader-final:0043` (reader_to_final): source [2567, 2575] → target [2566, 2565]; **NONLOADBEARING**; checked dependency node `constants-citations`. Exact text and reason: `MATH_DIFF_LEDGER.json`.

## Thirteen-correction pass

- **E-P02-01**: Setting sigma=1 in the displayed definition of T_N^sigma gives exactly the original unsigned offsite T_N. Combine C_N=f_N+2T_N and Q_H sum f_N=1 to obtain X_H(1/t)=1+2Q_H sum T_N^1. The negative-family signed estimates remain separate.
- **E-P02-02**: The dispersion coordinate is W and the excluded branch value is W=-1. The limiting W-set has the displayed S_* separation; the quadratic roots z live in another plane. The noun now identifies the quantity actually used in the following distance inequality, without changing its bound.
- **E-P02-03**: The original-disk constant is explicitly named c_O in the proof and the protected-current constant c_P is distinct. The table now points to c_O; no disk radius or order of choices changes.

## Formalization scope

The actual endpoint, expanded fields, physical antecedents and manuscript-only strength are mapped clause by clause in `SIX_PAPER_LEAN_SCOPE_MATRIX.csv`. Exact current declarations and existing compiler type evidence are in `EVIDENCE/LEAN/`. No fresh full clean formal build is claimed.

Remaining mathematical-preservation obligations: none. Archive/live-CI verification is a separate publication gate recorded in `ACTIVE_LINK_AND_CI_REGRESSION.md`.
