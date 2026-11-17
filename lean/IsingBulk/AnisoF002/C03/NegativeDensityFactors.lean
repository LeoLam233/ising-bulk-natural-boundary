import IsingBulk.AnisoF002.C03.NegativeActualUniformPole
import IsingBulk.AnisoF002.C03.IsotropicTrigonometricSecants
import IsingBulk.AnisoF002.RegularTail.PhysicalFactors

/-!
# Complete negative-winding numerator and its filled collision quotient

These are the literal factors of frozen F002 (4.10)--(4.12), retaining the
square-root power, factorial and independent-angle measure normalization.
The quotient is constructed without division by the Vandermonde.  Thus
every partial or total angle coincidence is covered by the same formula.
The full physical coefficient integral and the uniform logarithmic error
are not assumed by these finite identities.
-/

namespace IsingBulk.AnisoF002.NegativeHT
noncomputable section
open IsingBulk.AnisoF002.Isotropic IsingBulk.AnisoF002.RegularTail Set Filter
open scoped Topology BigOperators

def windingNormalization (n : ℕ) : ℂ :=
  (n.factorial : ℂ) * (2 * (Real.pi : ℂ)) ^ (n - 1)

theorem windingNormalization_ne_zero (n : ℕ) : windingNormalization n ≠ 0 := by
  exact mul_ne_zero (by exact_mod_cast Nat.factorial_ne_zero n)
    (pow_ne_zero _ (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)))

def complexVandermondeSquared (n : ℕ) (v : Fin n → ℂ) : ℂ :=
  ∏ ij ∈ indexPairs n, (v ij.1 - v ij.2) ^ 2

def completeNegativeNumerator (n : ℕ) (b : ℂ → ℂ) (g : ℂ × ℂ → ℂ) (d t : ℂ)
    (v : Fin n → ℂ) : ℂ :=
  b t ^ (n ^ 2) / windingNormalization n *
    (∏ i, 1 / Complex.sinh (g (t, d + v i))) *
    ∏ ij ∈ indexPairs n,
      (Complex.sin ((v ij.1 - v ij.2) / 2) /
        Complex.sinh ((g (t, d + v ij.1) + g (t, d + v ij.2)) / 2)) ^ 2

def filledNegativeNumerator (n : ℕ) (b : ℂ → ℂ) (g : ℂ × ℂ → ℂ) (d t : ℂ)
    (v : Fin n → ℂ) : ℂ :=
  b t ^ (n ^ 2) / windingNormalization n *
    (∏ i, 1 / Complex.sinh (g (t, d + v i))) *
    ∏ ij ∈ indexPairs n,
      (complexSinc ((v ij.1 - v ij.2) / 2) /
        (2 * Complex.sinh ((g (t, d + v ij.1) + g (t, d + v ij.2)) / 2))) ^ 2

theorem negative_pair_filled_identity (a b γ η : ℂ) :
    (Complex.sin ((a - b) / 2) / Complex.sinh ((γ + η) / 2)) ^ 2 =
      (a - b) ^ 2 * (complexSinc ((a - b) / 2) /
        (2 * Complex.sinh ((γ + η) / 2))) ^ 2 := by
  have hs := complexSinc_mul ((a - b) / 2)
  have he : Complex.sin ((a - b) / 2) = (a - b) * complexSinc ((a - b) / 2) / 2 := by
    linear_combination -hs
  rw [he]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

theorem completeNegativeNumerator_factorization (n : ℕ) (b : ℂ → ℂ)
    (g : ℂ × ℂ → ℂ) (d t : ℂ) (v : Fin n → ℂ) :
    completeNegativeNumerator n b g d t v =
      complexVandermondeSquared n v * filledNegativeNumerator n b g d t v := by
  unfold completeNegativeNumerator filledNegativeNumerator complexVandermondeSquared
  simp_rw [negative_pair_filled_identity]
  rw [Finset.prod_mul_distrib]
  ring

def phaseTemperatureSum (n : ℕ) (g : ℂ × ℂ → ℂ) (d t : ℂ)
    (v : Fin n → ℂ) : ℂ :=
  ∑ i, fderiv ℂ g (t, d + v i) (1, 0)

def completeNegativeDensity (n : ℕ) (b : ℂ → ℂ) (g : ℂ × ℂ → ℂ)
    (d : ℂ) (T : (Fin n → ℂ) → ℂ) (v : Fin n → ℂ) : ℂ :=
  -(2 * completeNegativeNumerator n b g d (T v) v) /
    phaseTemperatureSum n g d (T v) v

def filledNegativeDensity (n : ℕ) (b : ℂ → ℂ) (g : ℂ × ℂ → ℂ)
    (d : ℂ) (T : (Fin n → ℂ) → ℂ) (v : Fin n → ℂ) : ℂ :=
  -(2 * filledNegativeNumerator n b g d (T v) v) /
    phaseTemperatureSum n g d (T v) v

theorem completeNegativeDensity_factorization (n : ℕ) (b : ℂ → ℂ)
    (g : ℂ × ℂ → ℂ) (d : ℂ) (T : (Fin n → ℂ) → ℂ) (v : Fin n → ℂ) :
    completeNegativeDensity n b g d T v =
      complexVandermondeSquared n v * filledNegativeDensity n b g d T v := by
  unfold completeNegativeDensity filledNegativeDensity
  rw [completeNegativeNumerator_factorization]
  ring

theorem phaseTemperatureSum_hasDerivAt (n : ℕ) (g : ℂ × ℂ → ℂ) (d t : ℂ)
    (v : Fin n → ℂ) (hg : ∀ i, DifferentiableAt ℂ g (t, d + v i)) :
    HasDerivAt (fun t => ∑ i, g (t, d + v i)) (phaseTemperatureSum n g d t v) t := by
  apply HasDerivAt.fun_sum
  intro i _
  exact (hg i).hasFDerivAt.comp_hasDerivAt t
    ((hasDerivAt_id t).prodMk (hasDerivAt_const t (d + v i)))

theorem phaseTemperatureSum_ne_zero_of_average {n : ℕ} {g : ℂ × ℂ → ℂ}
    {γ d t : ℂ} {v : Fin n → ℂ}
    (hg : ∀ i, DifferentiableAt ℂ g (t, d + v i))
    (hD : deriv (centeredPhaseAverage n g γ d v) t ≠ 0) :
    phaseTemperatureSum n g d t v ≠ 0 := by
  rw [(centeredPhaseAverage_hasDerivAt n g γ d v t hg).deriv] at hD
  exact (div_ne_zero_iff.mp hD).1

theorem filledNegativeNumerator_center (n : ℕ) (b : ℂ → ℂ) (g : ℂ × ℂ → ℂ)
    (d τ γ : ℂ) (hcenter : g (τ, d) = γ) :
    filledNegativeNumerator n b g d τ 0 =
      b τ ^ (n ^ 2) / windingNormalization n *
        (1 / Complex.sinh γ) ^ n * (1 / (2 * Complex.sinh γ)) ^ (2 * n.choose 2) := by
  simp only [filledNegativeNumerator, Pi.zero_apply, add_zero, hcenter,
    sub_self, zero_div, complexSinc_zero,
    show (γ + γ) / 2 = γ by ring, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, card_indexPairs, ← pow_mul]

theorem filledNegativeNumerator_center_ne_zero (n : ℕ) (b : ℂ → ℂ)
    (g : ℂ × ℂ → ℂ) (d τ γ : ℂ) (hcenter : g (τ, d) = γ)
    (hb : b τ ≠ 0) (hγ : Complex.sinh γ ≠ 0) :
    filledNegativeNumerator n b g d τ 0 ≠ 0 := by
  rw [filledNegativeNumerator_center n b g d τ γ hcenter]
  exact mul_ne_zero (mul_ne_zero (div_ne_zero (pow_ne_zero _ hb) (windingNormalization_ne_zero n))
    (pow_ne_zero _ (one_div_ne_zero hγ)))
    (pow_ne_zero _ (one_div_ne_zero (mul_ne_zero (by norm_num) hγ)))

end
end IsingBulk.AnisoF002.NegativeHT
