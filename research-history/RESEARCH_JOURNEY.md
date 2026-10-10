# How the initial Ising proof prototype emerged

**Evidence scope:** This account covers only the saved v1–v38 materials from one original Codex session. Its source is the [verbatim reconstructed retrospective](original-session/ising_project_complete_history_2026-10-10.md); it must not be confused with subsequent audits, repairs or Lean formalization.

## Central target

The original target was the natural boundary of the **full** zero-field isotropic square-lattice bulk susceptibility continued from the exterior low-temperature germ. Nickel singularities of fixed even-particle form factors alone do not establish singularities for their infinite sum: cancellation or nonuniform limits could defeat the inference.

At a dense family of chosen boundary points, the proposed proof strategy sought a nonzero first singular derivative and control of **every higher even order**, including the lower derivatives needed for the physical prefactor. The prototype's claims were a leading term of scale `epsilon^(-1/2)` and an entire tail of `o(epsilon^(-1/2))`. These remain historical **candidate** statements.

## Nine route families, not nine model calls

| Route | Approach in the initial session | What happened |
|---|---|---|
| R1 | First four-particle Nickel singularity at `s=exp(i*pi/3)` | Local exponent `13/2` and seventh derivative gave a useful test; one point and one form factor could not establish the full sum or a dense natural boundary. |
| R2 | Transfer diagonal-susceptibility proof pattern | Retained first-carrier/controlled-tail logic, but bulk extra variables, inverse branches and global product denominators prevented direct transfer. |
| R3 | Suppress higher terms using Nickel-amplitude asymptotics | A fixed channel showed formal `exp(-c N^2)` decay, yet near-critical prime channels grew; fixed-N asymptotics lacked a uniform neighborhood. |
| R4 | Build dense prime-angle families with unique first order | First family had degenerate endpoint/branch and amplitude issues. A second, two-nonzero-angle family appeared early and later became the preferred carrier. |
| R5 | Positivity, coefficient and spectral reasoning | Real-axis positivity did not control cancellation of complex singular coefficients; no independent spectral certificate. |
| R6 | Pfaffian, exact x-residues, contour deformations, Stokes currents, Lie/coarea bounds | Reduced the very-high tail but repeatedly exposed missing connector, cutoff-jet, complex-disk and N-dependent estimates. Ultimately combined with R4 as the candidate framework. |
| R7 | Direct Pólya–Carlson arithmetic shortcut | Needed coefficient integrality and the desired unit radius together; the attempted change of variable did not provide both. The **direct** approach was abandoned, not all arithmetic methods. |
| R8 | Auxiliary particle-weight `lambda` | Generic parameter noncancellation could fail exactly at physical `lambda=1`; no zero-exclusion argument. |
| R9 | Finite-cylinder limit | Had to remove a zero-particle tunneling term; exterior convergence alone would not preserve branch jumps at the boundary. |

The route classifications are the project's own finite ledger; they are not exhaustive classifications of all possible mathematical methods.

## How the attack changed

1. **Low-order point and amplitude heuristic (v1):** The four-particle test located a strong derivative singularity. Large-order amplitude decay could not be upgraded to a summable bound, and counterchannels invalidated a universal decay heuristic.
2. **Exact integral structure (v1–v2):** Schur Pfaffian structure and x-contour residues exposed a squared Vandermonde factor, removed apparent pair poles, and drove the very-high-order threshold from powers of `epsilon^(-1)` to `N >= C log^2(1/epsilon)` via weighted two-variable integrals.
3. **Mixed branches and legal contours (v2–v10):** Lower and upper inverse branches required different deformations. A good final contour estimate was not the original integral: crossed poles, smooth cutoffs, Jacobians and Stokes connectors all needed explicit treatment.
4. **Phase transport and differentiated estimates (v11–v25):** Uniformizing the branch coordinates eliminated artificial square-root singular factors. A two-phase Lie transport sought to freeze both `Y` and `Z`, turning temperature derivatives into geometric/pair-distance costs. Several shortcuts were explicitly withdrawn, including a max-radius derivative bound and a nonholomorphic pair selection.
5. **First-carrier and normalization crisis (v18–v28):** A nonzero Gaussian model period did not establish the physical cycle coefficient. The archive also preserved unresolved comparisons between Fredholm-normalized, whole-particle and ODE amplitude conventions. A high-tail coarea estimate failed at the **first** singular index.
6. **Second prime family activated (v29–v31):** Earlier two-nonzero-angle arithmetic made the first critical charts compact and nondegenerate. The inverse-branch phase became an algebraic non-root-of-unity; a resultant gave an exponential, N-dependent nonresonance gap. This allowed an exponentially small microcore, and actual mean-angle Y-residues produced a nonzero **physical-carrier candidate**.
7. **Four windows and final kill checks (v31–v38):** Low, intermediate, very-high particle orders, plus selected/connector subregions, were assigned different estimates. Fresh checks uncovered endpoint equality, root-radius, Stokes orientation, `exp(C N^3)` constants and all-jets issues. The archived outcome was `PROVISIONAL CENTRAL CLOSURE`, not expert-verified resolution.

## What made the route viable *as a candidate*

The decisive change was **compatibility**, not a single miraculous estimate: R6's accumulated contour and differentiated-tail tools became compatible with R4's second prime family. That family simultaneously offered a nondegenerate first-carrier calculation and a non-root-of-unity inverse-branch phase for the difficult higher-order region. Different order windows permitted different bounds; the tail only had to be little-o of the first divergent scale, not uniformly bounded.

## Later history is separate

The first-session prototype **did not end the project**. Later hostile AI audits, repair cycles, W1/W2 mathematical changes and Lean verification are indexed in the [history entrypoint](README.md) and [crosswalk](ORIGINAL_TO_LEAN_CROSSWALK.md). This initial-session narrative must never be used to claim that the final candidate, its current formalization, or all repairs existed in v38.
