# ANISO_PSER: preservation record

Judgment: **PRESERVED**. Public path: `papers/fixed-ratio-anisotropy/alternative-proof/manuscript.{tex,pdf}`.

This is preservation of the frozen argument under editing. Unchanged proof text is checked by complete line correspondence; changed proof-bearing prose is read in context and adjudicated below. This is not a new independent correctness proof of every frozen estimate.

## Exact version identities

| Version | File | SHA-256 | Git blob | Pages |
|---|---|---|---|---|
| source | `work/authority/SOURCES/AUTHORITATIVE/ANISO_PSER_F002_52P.tex` | `7c0fc588a688869d0c95698ec67b989bf644f3bd0cb9ca1c7eb8624d3976c977` | `7532c69c2b8d9233e8e91003d128b2d816235255` |  |
| source | `work/authority/SOURCES/AUTHORITATIVE/ANISO_PSER_F002_52P.pdf` | `b82149625b7c2223c743b8e7482f4818543a760b46decd845acdf217d7a2376c` | `43d03991cb1f2fe1f523b148ad99bcfb6cb6d494` | 52 |
| pre13 | `work/pre13/ACADEMIC/ANISO/PSER/manuscript.tex` | `b0d649cdfa3c20927fdfda2984b520d807db2992bc00de3c9a405389a185b725` | `2ba8f0d4573abeed44b2e6fb8d750ed22f57bef9` |  |
| pre13 | `work/pre13/ACADEMIC/ANISO/PSER/manuscript.pdf` | `e028452c85de97b8bc9f5794b7fe908cb7be6eede16e27facd1758583222dea6` | `64f75a4660f1821d79779778cf77476590c8b92d` | 53 |
| final | `work/final/ACADEMIC/ANISO/PSER/manuscript.tex` | `c92c1a226e74d6f7424151b87b4e4b93bef52529d9344e494b417f0aee1c39a4` | `d13894810e8ca07e460e7e49820ea201bad94dcf` |  |
| final | `work/final/ACADEMIC/ANISO/PSER/manuscript.pdf` | `0855cd0083c9b0e400f17d6763e94a5121299779561ae37ad0e50e95f2fda862` | `aa815130e19ea063b949260b33d2458f4c392909` | 53 |

## Complete statement and hypothesis map

All statement bodies and their exact source/final quantified hypotheses are in `EVIDENCE/STATEMENTS/ANISO_PSER.json`; the complete line and reference maps are in `FULL_LINE_CORRESPONDENCE.json` and `REFERENCE_CORRESPONDENCE.csv`.

| Source lines | Final lines | Statement labels | Mathematical disposition |
|---|---|---|---|
| 97–108 | 131–142 | `thm:aniso ` | Identical after whitespace/labels |
| 486–492 | 520–526 | `lem:endpoint-sandwich;eq:endpoint-sandwich ` | Identical after whitespace/labels |
| 551–557 | 585–591 | `thm:components ` | Identical after whitespace/labels |
| 606–608 | 640–642 | `lem:profile-discrete ` | Identical after whitespace/labels |
| 688–696 | 720–728 | `prop:regular_dense ` | Identical after whitespace/labels |
| 737–748 | 769–780 | `lem:canonicalroot ` | Identical after whitespace/labels |
| 848–856 | 880–888 | `lem:matching ` | Identical after whitespace/labels |
| 1237–1244 | 1268–1275 | `lem:rc-density;eq:rc-density-log ` | Identical after whitespace/labels |
| 1271–1279 | 1302–1310 | `lem:rc-angular;eq:rc-angular-moment ` | Identical after whitespace/labels |
| 1433–1454 | 1465–1486 | `prop:negative-real-cycle-coefficients;eq:rc-one-winding-model;eq:rc-two-winding-model;eq:rc-model ` | Identical after whitespace/labels |
| 1645–1662 | 1676–1693 | `lem:jets_boundary_derivatives;eq:jets_small_disk;eq:jets_boundary_coefficients ` | Identical after whitespace/labels |
| 1756–1772 | 1787–1803 | `lem:jets_remainder;eq:jets_remainder_bound;eq:jets_exact_residue_coefficient ` | Identical after whitespace/labels |
| 1859–1878 | 1890–1909 | `lem:jets_windings_large_n;eq:jets_winding_bound;eq:jets_large_n_bound ` | Identical after whitespace/labels |
| 1969–1989 | 2001–2021 | `lem:jets_discrete_concavity;eq:jets_second_difference;eq:jets_crossing_expansion;eq:jets_middle_window ` | Identical after whitespace/labels |
| 2211–2225 | 2243–2257 | `thm:jets_negative_edge ` | Identical after whitespace/labels |
| 2492–2509 | 2509–2526 | `lem:iso-prime-family;eq:iso-Nickel ` | Identical after whitespace/labels |
| 2624–2635 | 2641–2652 | `thm:iso-tail;eq:iso-complete-tail ` | Identical after whitespace/labels |
| 2800–2808 | 2817–2825 | `lem:iso-inverse ` | Identical after whitespace/labels |
| 2866–2879 | 2883–2896 | `lem:iso-cell-gaussian ` | Identical after whitespace/labels |
| 3078–3091 | 3092–3105 | `lem:iso-covariance-jets;eq:iso-covariance-lower;eq:iso-field-jets ` | Identical after whitespace/labels |
| 3223–3236 | 3237–3250 | `lem:iso-coarea;eq:iso-shell-coarea ` | Identical after whitespace/labels |
| 3374–3384 | 3387–3397 | `prop:iso-finite-transport ` | Identical after whitespace/labels |
| 3405–3415 | 3418–3428 | `lem:iso-finite-complement ` | Identical after whitespace/labels |
| 3580–3606 | 3593–3619 | `lem:iso-period;eq:iso-period;eq:iso-odd-period ` | Identical after whitespace/labels |
| 3639–3663 | 3652–3676 | `thm:iso-first-coefficient;eq:iso-first-S;eq:iso-first-t;eq:iso-first-constants ` | Identical after whitespace/labels |
| 3713–3720 | 3726–3733 | `thm:iso-internal-boundary ` | Statement body retained; notation/caption or post-statement commentary is adjudicated in the diff ledger |
| 3835–3841 | 3848–3854 | `cor:alllambda ` | Identical after whitespace/labels |

## Physical observable and dependency graph

Real full-site inputs -> exact coefficient normalization/Fubini -> normal convergence -> first nonzero coefficient + finite lower orders + complete differentiated absolute infinite tail -> no cancellation -> actual curve/local obstruction -> density and componentwise closure -> physical analytic-unit transfer. Each route uses its own corresponding nodes.

No completed natural-boundary endpoint of a different proof route is substituted.

### real-cycle-route

The exact physical definitions and every main hypothesis are unchanged. Endpoint incidence and analytic profile differences replace no frozen argument: they are the same distinct frozen F002 route. The negative-odd analysis retains its real-plane pole estimate, complete residue, angular exponential moment, positive-majorant comparison on the same real cycle, exact complex beta period, two first windings, integer selection and all-index/winding remainder bounds. Removed negative descriptions only state which alternative methods are unnecessary; the actual estimates and their domain restrictions remain. The full spectral interior is still distinguished from the physical frontiers.

### isotropic-coefficient-name

At B=1, C=s+s^-1 and W=C-cos(q); the interior transfer root, independent-angle normalized measure, full pair product and every particle order agree term by term with the isotropic coefficient. Thus the formerly external notation C_N^iso(1/s) equals the manuscript-own C_N(s) on 0<s<1. The prefactor (1-s^4)^(1/4)/s and the connected LT onsite term are unchanged. Replacing that alias removes a workflow self-citation, not an external natural-boundary premise.

### internal-isotropic-transport

The internal lambda=1 proof remains complete in Section 7: signed constrained homotopy before weights, Schur matchings, retained collision factors, regular inverse, phase-preserving current, its joint jets, flux limits, all means/diameters, finite complements and first periods. At a branch theta_b=+/-b, the normal form is a statement about W-1 in the real angular variable theta-theta_b. Its imaginary margin controls the near region and its nonzero linear real part controls the complement, yielding the same integrable distance^(-1/2) majorant. This correction does not refer to the later inverse coordinate u. The unchanged full even/odd tail and covering proof establish lambda=1 internally. The distinct F002 Lean status remains PARTIAL.

## All changed passages

The exhaustive ledger records exact removed/added text, both paragraph contexts and classifications. Intermediate Reader changes are included separately, so the pinned Reader route cannot silently substitute another original.

- `ANISO_PSER:source-final:0001` (source_to_final): source [6, 5] → target [6, 6]; **NONLOADBEARING**; checked dependency node `real-cycle-route`. Exact text and reason: `MATH_DIFF_LEDGER.json`.
- `ANISO_PSER:source-final:0003` (source_to_final): source [34, 37] → target [35, 38]; **NONLOADBEARING**; checked dependency node `real-cycle-route`. Exact text and reason: `MATH_DIFF_LEDGER.json`.
- `ANISO_PSER:source-final:0005` (source_to_final): source [60, 61] → target [61, 62]; **MATHEMATICALLY_EQUIVALENT**; checked dependency node `real-cycle-route`. Exact text and reason: `MATH_DIFF_LEDGER.json`.
- `ANISO_PSER:source-final:0007` (source_to_final): source [63, 62] → target [64, 96]; **NONLOADBEARING**; checked dependency node `real-cycle-route`. Exact text and reason: `MATH_DIFF_LEDGER.json`.
- `ANISO_PSER:source-final:0009` (source_to_final): source [216, 217] → target [250, 252]; **MATHEMATICALLY_EQUIVALENT**; checked dependency node `real-cycle-route`. Exact text and reason: `MATH_DIFF_LEDGER.json`.
- `ANISO_PSER:source-final:0011` (source_to_final): source [248, 249] → target [283, 283]; **MATHEMATICALLY_EQUIVALENT**; checked dependency node `real-cycle-route`. Exact text and reason: `MATH_DIFF_LEDGER.json`.
- `ANISO_PSER:source-final:0013` (source_to_final): source [628, 629] → target [662, 662]; **MATHEMATICALLY_EQUIVALENT**; checked dependency node `real-cycle-route`. Exact text and reason: `MATH_DIFF_LEDGER.json`.
- `ANISO_PSER:source-final:0015` (source_to_final): source [638, 639] → target [671, 671]; **MATHEMATICALLY_EQUIVALENT**; checked dependency node `real-cycle-route`. Exact text and reason: `MATH_DIFF_LEDGER.json`.
- `ANISO_PSER:source-final:0017` (source_to_final): source [960, 961] → target [992, 993]; **MATHEMATICALLY_EQUIVALENT**; checked dependency node `real-cycle-route`. Exact text and reason: `MATH_DIFF_LEDGER.json`.
- `ANISO_PSER:source-final:0019` (source_to_final): source [1013, 1015] → target [1045, 1047]; **MATHEMATICALLY_EQUIVALENT**; checked dependency node `real-cycle-route`. Exact text and reason: `MATH_DIFF_LEDGER.json`.
- `ANISO_PSER:source-final:0021` (source_to_final): source [1206, 1206] → target [1238, 1237]; **MATHEMATICALLY_EQUIVALENT**; checked dependency node `real-cycle-route`. Exact text and reason: `MATH_DIFF_LEDGER.json`.
- `ANISO_PSER:source-final:0023` (source_to_final): source [1420, 1421] → target [1451, 1453]; **MATHEMATICALLY_EQUIVALENT**; checked dependency node `real-cycle-route`. Exact text and reason: `MATH_DIFF_LEDGER.json`.
- `ANISO_PSER:source-final:0025` (source_to_final): source [1574, 1576] → target [1606, 1607]; **MATHEMATICALLY_EQUIVALENT**; checked dependency node `real-cycle-route`. Exact text and reason: `MATH_DIFF_LEDGER.json`.
- `ANISO_PSER:source-final:0027` (source_to_final): source [1939, 1939] → target [1970, 1971]; **MATHEMATICALLY_EQUIVALENT**; checked dependency node `real-cycle-route`. Exact text and reason: `MATH_DIFF_LEDGER.json`.
- `ANISO_PSER:source-final:0029` (source_to_final): source [2293, 2298] → target [2325, 2328]; **MATHEMATICALLY_EQUIVALENT**; checked dependency node `real-cycle-route`. Exact text and reason: `MATH_DIFF_LEDGER.json`.
- `ANISO_PSER:source-final:0031` (source_to_final): source [2330, 2330] → target [2360, 2360]; **MATHEMATICALLY_EQUIVALENT**; checked dependency node `isotropic-coefficient-name`. Exact text and reason: `MATH_DIFF_LEDGER.json`.
- `ANISO_PSER:source-final:0033` (source_to_final): source [2342, 2345] → target [2372, 2374]; **MATHEMATICALLY_EQUIVALENT**; checked dependency node `isotropic-coefficient-name`. Exact text and reason: `MATH_DIFF_LEDGER.json`.
- `ANISO_PSER:source-final:0035` (source_to_final): source [2348, 2348] → target [2377, 2377]; **MATHEMATICALLY_EQUIVALENT**; checked dependency node `isotropic-coefficient-name`. Exact text and reason: `MATH_DIFF_LEDGER.json`.
- `ANISO_PSER:source-final:0037` (source_to_final): source [2350, 2350] → target [2379, 2378]; **MATHEMATICALLY_EQUIVALENT**; checked dependency node `isotropic-coefficient-name`. Exact text and reason: `MATH_DIFF_LEDGER.json`.
- `ANISO_PSER:source-final:0039` (source_to_final): source [2356, 2359] → target [2384, 2386]; **MATHEMATICALLY_EQUIVALENT**; checked dependency node `isotropic-coefficient-name`. Exact text and reason: `MATH_DIFF_LEDGER.json`.
- `ANISO_PSER:source-final:0041` (source_to_final): source [2361, 2371] → target [2388, 2389]; **MATHEMATICALLY_EQUIVALENT**; checked dependency node `isotropic-coefficient-name`. Exact text and reason: `MATH_DIFF_LEDGER.json`.
- `ANISO_PSER:source-final:0043` (source_to_final): source [2441, 2441] → target [2459, 2458]; **MATHEMATICALLY_EQUIVALENT**; checked dependency node `internal-isotropic-transport`. Exact text and reason: `MATH_DIFF_LEDGER.json`.
- `ANISO_PSER:source-final:0045` (source_to_final): source [2661, 2661] → target [2678, 2678]; **MATHEMATICALLY_EQUIVALENT**; checked dependency node `internal-isotropic-transport`. Exact text and reason: `MATH_DIFF_LEDGER.json`.
- `ANISO_PSER:source-final:0047` (source_to_final): source [2710, 2710] → target [2727, 2727]; **MATHEMATICALLY_EQUIVALENT**; checked dependency node `internal-isotropic-transport`. Exact text and reason: `MATH_DIFF_LEDGER.json`.
- `ANISO_PSER:source-final:0049` (source_to_final): source [2766, 2767] → target [2783, 2785]; **MATHEMATICALLY_EQUIVALENT**; checked dependency node `internal-isotropic-transport`. Exact text and reason: `MATH_DIFF_LEDGER.json`.
- `ANISO_PSER:source-final:0051` (source_to_final): source [2783, 2783] → target [2801, 2801]; **MATHEMATICALLY_EQUIVALENT**; checked dependency node `internal-isotropic-transport`. Exact text and reason: `MATH_DIFF_LEDGER.json`.
- `ANISO_PSER:source-final:0053` (source_to_final): source [2793, 2794] → target [2811, 2811]; **MATHEMATICALLY_EQUIVALENT**; checked dependency node `internal-isotropic-transport`. Exact text and reason: `MATH_DIFF_LEDGER.json`.
- `ANISO_PSER:source-final:0055` (source_to_final): source [3051, 3053] → target [3068, 3067]; **NONLOADBEARING**; checked dependency node `internal-isotropic-transport`. Exact text and reason: `MATH_DIFF_LEDGER.json`.
- `ANISO_PSER:source-final:0057` (source_to_final): source [3177, 3177] → target [3191, 3191]; **MATHEMATICALLY_EQUIVALENT**; checked dependency node `internal-isotropic-transport`. Exact text and reason: `MATH_DIFF_LEDGER.json`.
- `ANISO_PSER:source-final:0059` (source_to_final): source [3361, 3363] → target [3375, 3376]; **MATHEMATICALLY_EQUIVALENT**; checked dependency node `internal-isotropic-transport`. Exact text and reason: `MATH_DIFF_LEDGER.json`.
- `ANISO_PSER:source-final:0061` (source_to_final): source [3628, 3628] → target [3641, 3641]; **MATHEMATICALLY_EQUIVALENT**; checked dependency node `internal-isotropic-transport`. Exact text and reason: `MATH_DIFF_LEDGER.json`.
- `ANISO_PSER:source-final:0063` (source_to_final): source [3713, 3713] → target [3726, 3726]; **MATHEMATICALLY_EQUIVALENT**; checked dependency node `internal-isotropic-transport`. Exact text and reason: `MATH_DIFF_LEDGER.json`.
- `ANISO_PSER:source-final:0065` (source_to_final): source [3829, 3829] → target [3842, 3842]; **MATHEMATICALLY_EQUIVALENT**; checked dependency node `internal-isotropic-transport`. Exact text and reason: `MATH_DIFF_LEDGER.json`.
- `ANISO_PSER:source-final:0067` (source_to_final): source [3843, 3842] → target [3856, 3856]; **NONLOADBEARING**; checked dependency node `internal-isotropic-transport`. Exact text and reason: `MATH_DIFF_LEDGER.json`.
- `ANISO_PSER:source-final:0069` (source_to_final): source [3844, 3849] → target [3858, 3868]; **NONLOADBEARING**; checked dependency node `internal-isotropic-transport`. Exact text and reason: `MATH_DIFF_LEDGER.json`.
- `ANISO_PSER:source-final:0071` (source_to_final): source [3852, 3853] → target [3871, 3874]; **MATHEMATICALLY_EQUIVALENT**; checked dependency node `internal-isotropic-transport`. Exact text and reason: `MATH_DIFF_LEDGER.json`.
- `ANISO_PSER:source-final:0073` (source_to_final): source [3856, 3876] → target [3877, 3892]; **NONLOADBEARING**; checked dependency node `internal-isotropic-transport`. Exact text and reason: `MATH_DIFF_LEDGER.json`.
- `ANISO_PSER:pre13-final:0001` (pre13_to_final): source [2783, 2784] → target [2783, 2785]; **MATHEMATICALLY_EQUIVALENT**; checked dependency node `internal-isotropic-transport`. Exact text and reason: `MATH_DIFF_LEDGER.json`.

## Thirteen-correction pass

- **E-P07-01**: At theta_b=+/-b, W-1 has a nonzero linear real angular term and the displaced imaginary margin. Near |theta-theta_b|<=C(epsilon+|h|) use that margin; outside use the linear term. Since W+1 is separated, the inverse one-body factor has the same integrable angular distance^(-1/2) majorant. The later inverse coordinate is not used here.

## Formalization scope

**PARTIAL**. The complete independent fixed-ratio real-cycle target, including its own isotropic closure, is not established by a completed separate Lean endpoint in the supplied repository. No F002 source tree is present; no exact missing partial lemma is invented.

Remaining mathematical-preservation obligations: none. Archive/live-CI verification is a separate publication gate recorded in `ACTIVE_LINK_AND_CI_REGRESSION.md`.
