# Real physical interface

This section gives the complete external entry contract for `IsingBulk.Anisotropic.full_uniform_field_conclusion`. Fix `Jx = J > 0`, `Jy = lam*J` with finite `lam > 0`, real `x = 2βJ > 0`, and `p = sinh x sinh(lam*x)`. The HT real interval has `p < 1`; the LT interval has `p > 1`. `corrH x v` and `corrL x v` represent two-spin correlations at every displacement `v ∈ ℤ × ℤ` in the unique HT state and LT plus state, respectively. The minus state has the same even correlations, but the uniform-field LT endpoint selects the positive plus mean.

## Physical interface: exact inputs and interpretation

### `PublishedRealSpinFormFactors lam corrH corrL`

[The frozen structure](../../lean/IsingBulk/Anisotropic/FormFactors/PublishedRealInput.lean) supplies four fields, each quantified over **every** positive real `x` on its phase side:

| Field | Exact content |
|---|---|
| `high_onsite` | `corrH x (0,0) = 1` for `p < 1` |
| `low_onsite` | `corrL x (0,0) = 1` for `p > 1` |
| `high_spin` | At every lattice site, `(corrH x v : ℂ) = (aH : ℂ) * ∑' n, latticeCoefficient (2*n+1) b c v` |
| `low_spin` | At every lattice site, `(corrL x v : ℂ) = (M² : ℂ) * (1 + ∑' n, latticeCoefficient (2*n+2) b c v)` |

Here `b = sinh(lam*x)/sinh x`, `c = cosh x*cosh(lam*x)/sinh x`, `aH = (1-p²)^(1/4)/sqrt p`, and `M² = (1-p⁻²)^(1/4)` are the exact real definitions. `latticeCoefficient` is the literal real-angular coefficient defined in the imported source. The source cites Bugrij–Lisovyy, arXiv:0708.3643, equations (21)–(25), (30)–(39), and Iorgov–Lisovyy, arXiv:1012.2856, Theorem 6.1 and Remark 6.2; the manuscript fixes normalization in (1.6)–(1.8).

This interface identifies real zero-field spin form factors at fixed separation, with onsite normalization. Full-site summability, exchanges of infinite sums, complex contour identities, normal convergence and boundary estimates are subsequently established by the ANISO proof. The LT covariance is `corrL x v - M²` **inside the whole-lattice sum**.

### `PublishedRealGibbsFields J lam corrH corrL mH mL`

[The second structure](../../lean/IsingBulk/Anisotropic/PhysicalField/PublishedRealGibbs.lean) provides real field-dependent means `mH x h`, `mL x h` under the energy-field convention `-h ∑ σ`, with `β = x/(2J)`:

| Field | Exact content |
|---|---|
| `high` | For every HT `x`, a nonempty `GibbsFieldConditions β (corrH x) (mH x)` |
| `low` | For every LT `x`, a nonempty `GibbsFieldConditions β (fun v => corrL x v - M²) (mL x)` |
| `high_spin_flip` | For every HT `x` and every real field `h`, `mH x (-h) = -mH x h` |
| `low_zero_square` | At every LT `x`, `(mL x 0)^2 = M²` |
| `low_plus_positive` | At every LT `x`, `0 < mL x 0` |

The witnesses to `high` and `low` carry all ten fields of [GibbsFieldConditions](../../lean/IsingBulk/Anisotropic/PhysicalField/GibbsFieldConditions.lean). For covariance `c` and mean `m`, they are:

1. `enumeration : ℕ ≃ ℤ × ℤ`, an enumeration of the **whole** lattice.
2. `localLaw n : FiniteSpinLaw n`, a finite spin marginal for every `n`.
3. `volumeLaw n : FiniteSpinLaw n`, a finite-volume law for every `n`.
4. `local_center`: every local law's center mean equals `m 0`.
5. `local_covariance`: its covariance at each enumerated coordinate equals `c (enumeration i.val)`.
6. `field_monotonicity`: for every `n` and `h > 0`, the local-law magnetization at `β,h` is at most `m h`.
7. `covariance_nonnegative`: `0 ≤ c v` at every site.
8. `pinned_covariance`: each volume-law site covariance is at most the corresponding `c`.
9. `ghs_concavity`: each volume-law magnetization is concave on `h ≥ 0`.
10. `thermodynamic_limit`: for every `h ≥ 0`, volume-law magnetizations tend to `m h` as `n → ∞`.

[FiniteSpinLaw](../../lean/IsingBulk/Anisotropic/PhysicalField/FiniteSpinLaw.lean) is an explicitly nonnegative normalized weight on `Fin (n+1) → Bool`, with spin values ±1. Coordinate zero is the observed spin; the other coordinates encode finitely perturbed sites. Its magnetization is the normalized exponential tilt by `β*h*∑ σ`; its zero-field derivative is proved to be `β` times the finite covariance sum. Repeated physical sites can be represented by equal coordinates on the support.

Attaching these finite laws and inequalities to the physical Gibbs states is part of the external physical identification. The formal structure states the displayed finite-law and limit properties; it does not construct an infinite-volume DLR measure or derive those physical properties from the lattice Hamiltonian. The frozen source cites Camia–Garban–Newman, arXiv:1205.6612v4, Theorem 1.5 and Corollary 1.6, and Friedli–Velenik, Chapter 3, for the intended Gibbs/GHS/monotonicity input. The zero-field spin interface alone does not supply the Gibbs-field witnesses.

### Conclusions derived from those inputs

The internal finite-law calculus and thermodynamic squeeze, using the internally proved summability, yield

```lean
HasDerivAt (mH x) (highEnergyFieldResponse J corrH x) 0
HasDerivWithinAt (mL x) (lowEnergyFieldResponse J lam corrL x) (Set.Ioi 0) 0
```

The first is bilateral: the proof upgrades the right derivative with `high_spin_flip`, also obtaining `mH x 0 = 0`. The second is the right-sided plus-phase derivative. The response values are exactly `β * ∑' v, corrH x v` and `β * ∑' v, (corrL x v - M²)`. Neither a field derivative nor susceptibility summability, complex analyticity, natural boundary or dominance estimate is a field of the two external structures.
