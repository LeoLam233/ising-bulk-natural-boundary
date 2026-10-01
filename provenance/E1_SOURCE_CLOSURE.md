# E1 source closure for the local rc4 candidate

**Scope:** source and normalization integration, 1 October 2026, above W2 candidate `fc0f82d127081cc372b84ebcfac48da9f5ccd79f`. Version remains `0.1-rc4-unreleased`. The full natural-boundary theorem remains an AI-assisted candidate without independent human, peer or proof-assistant certification.

## Primary sources and state

- [Palmer–Tracy 1981](https://doi.org/10.1016/0196-8858(81)90010-5): Cor. 2.0 p. 351; Thm 4.1 p. 361; Thm 5.0 p. 374 and proof pp. 375–378. [Author-hosted journal scan](https://www.math.ucdavis.edu/~tracy/selectedPapers/1980s/CV18.pdf), SHA-256 `c21b46c7e22f7355bdb7a41bb6e0d2dad983117e74eb18d2b18ce79ad40bf354`.
- [Tracy–Widom 2014, published journal version](https://doi.org/10.1007/s10955-014-1061-4): Eq. (3) and its coefficient pp. 1126–1127; Appendix 1 (7)–(8), pp. 1132–1133. [Author-hosted Springer-typeset PDF](https://www.math.ucdavis.edu/~tracy/selectedPapers/2010s/CV100.pdf), SHA-256 `3d04abde8c11c7c40c12390c23244a0c2974bc59ac425b877269ad7afd6412f9`.

Both PDFs were retrieved independently and their decisive equations read from rendered pages. The source correlation theorem is used for real `s>1` in the infinite-volume + state, obtained with + boundary conditions. Global spin flip gives the same two-point function and subtraction `M^2` in the - state. No positive-field-limit identification is invoked. This is the verified Stage-A wording repair.

## Determinant and normalization

PT Thm 4.1 is squared. The two-point reduction on p. 375 gives `det_2(I+G)=det_2(I+g)^2`; the unsquared series is in Thm 5.0 and p. 376. The smooth weighted two-point kernel is trace class and has zero diagonal, so `det_2(I+g)=det(I+g)`. Reflection makes its determinant real. Continuity, the Griffiths lower bound used on PT p. 359, and its limit 1 as `s` tends to infinity select the positive square root. The symmetric PT kernel and row-weighted TW kernel are similar by a bounded invertible multiplication at each fixed lattice separation. These facts fix the unsquared prefactor `M^2`.

At particle number `N`, the angular measures give `N` copies of `dx/(2pi i x)`. Each auxiliary residue adds `dy/(2pi i)`, and the Fredholm factorial stays `1/N!`. With `z=exp(-gamma)`, `yD=-(y-z)(y-z^-1)/2`; the residue of `1/(yD)` is `2z/(1-z^2)=1/sinh(gamma)`. For nonnegative lattice row, zero introduces no pole. All contours are positive. Thus the prefactor is `(2pi i)^(-2N)/N!`, exactly the journal's coefficient normalization. Two denominator sign changes per pair cancel. The `(2pi)^(-N)` in journal (8) belongs to the bare integral in (7), and is consistent for even `N`.

For fixed real `s>1`, a small common angle strip retains `Re gamma>=c>0` and a bounded canceled kernel. Shifting all angles by the sign of the first lattice coordinate, then using Hadamard, bounds the coefficient at `(a,b)` by `N^(N/2) C^N/N! exp[-N(eta|a|+c|b|)]`. This is summable in sites and even `N>=2`; the determinant integrand is periodic because each half-angle sign changes a row and column together. It justifies the physical real-axis lattice/Fredholm interchange. It supplies no uniform estimate near the complex boundary.

## Published full-site coefficient

Define `I_N[q]` by the pair factors and normalized measure of manuscript `eq:double`, with its global rational factor replaced by `q(X,Y)`. Then

```
C_N^std := chi_PUB^(N) = I_N[(1+X^-1)(1+Y^-1)/((1-X)(1-Y))],
f00^(N) = I_N[1/(XY)],
T_N = I_N[(X^-1+Y^-1)/((1-X)(1-Y))].
```

The exact identity

```
(1+X^-1)(1+Y^-1)/((1-X)(1-Y))
 = 1/(XY) + 2(X^-1+Y^-1)/((1-X)(1-Y))
```

proves `C_N^std=f00^(N)+2T_N` for every fixed even `N`. Independently, multiplying the one-coordinate lattice multiplicities `(1+X)/(1-X)` and `(1+Y)/(1-Y)` and subtracting the origin gives `2(X+Y)/((1-X)(1-Y))`. The measure contributes `1/(XY)`, giving the same offsite numerator and factor 2.

The physical origin is `sigma^2=1`. It yields `1-M^2` directly in `eq:bulk`. The fixed-N relation requires no sum over `N`. Applying TW's stated correlation representation at the origin implies `M^2 det(I+g00)=1`; no finite onsite computation is used as an all-orders proof. Reconciliation introduces no new theorem obligation for the candidate. **Neither `eq:double` nor `eq:bulk` changes.**

## arXiv v1 history only

[arXiv:1403.3966v1](https://arxiv.org/pdf/1403.3966v1), dated 16 March 2014, has SHA-256 `ca8d2592602e7e33d0dc762960304990b08758dbabb6950e7a564dcaac218abf`. Its p. 3 prints an offsite numerator with `(2pi i)^(-N)/N!`, unlike the journal's full-site numerator and `(2pi i)^(-2N)/N!`. With ordinary contour measures the v1 coefficient equals `(2pi i)^N T_N`, while its Appendix A gives the normalized offsite value. This discrepancy is **v1-only**; it is absent from the published formula. No publisher erratum is asserted. Proof exposition now cites the published formulas.

## Integration boundary

The supplied Stage-A and Stage-B reports, states, freezes and proposed repairs were checked as untrusted evidence. Hashes establish their identity only. Independent source reading and exact algebra establish the E1 interface; no earlier W1/W2 verdict is a premise. Finite diagnostics and successful builds remain engineering evidence.

E1 closure covers the stated source/state/normalization interface. Exterior holomorphy of the infinite sum, onsite smoothness at selected boundary points, first-amplitude gluing, W1/W2 estimates and noncancellation remain the manuscript's internal proof obligations. Novelty, the whole theorem and independent certification were outside this pass.

Historical `audits/`, `reproduction/`, rc1–rc3 records and frozen [W1](W1_REPAIR_AUDIT.md)/[W2](W2_REPAIR_AUDIT.md) provenance retain their bytes and original verdict scopes. Their historical E1-pending statements describe earlier inputs. Aggregate [current status](../release/STATUS.json) records the integrated E1 state. Nothing in this integration authorizes publication.
