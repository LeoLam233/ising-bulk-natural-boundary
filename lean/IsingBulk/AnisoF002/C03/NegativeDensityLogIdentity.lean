import IsingBulk.AnisoF002.C03.NegativeDensityAnalytic
import IsingBulk.AnisoF002.C03.NegativeAnalyticLogs

/-!
# Exact logarithm of the complete filled residue density

All powers, one-body factors, pair factors and the phase derivative are
present.  The factorization is algebraic on the filled formula, so it
continues to hold at every partial or total angle coincidence.
-/

namespace IsingBulk.AnisoF002.NegativeHT
noncomputable section
open IsingBulk.AnisoF002.Isotropic Set Filter
open scoped Topology BigOperators

def completeNumeratorLog (n : ℕ) (lb : ℂ) (h : Fin n → ℂ)
    (p : Fin n × Fin n → ℂ) : ℂ :=
  ((n ^ 2 : ℕ) : ℂ) * lb - ∑ i, h i + ∑ ij ∈ indexPairs n, 2 * p ij

theorem inverse_factor_from_log (a a₀ l : ℂ) (ha : a = a₀ * Complex.exp l) :
    1 / a = (1 / a₀) * Complex.exp (-l) := by
  rw [ha, Complex.exp_neg]
  simp only [one_div, mul_inv_rev]
  ring

theorem filled_pair_from_logs (s h h₀ ls lh : ℂ)
    (hs : s = Complex.exp ls) (hh : h = h₀ * Complex.exp lh) :
    (s / (2 * h)) ^ 2 = (1 / (2 * h₀)) ^ 2 * Complex.exp (2 * (ls - lh)) := by
  rw [hs, hh, show (2 : ℂ) = ((2 : ℕ) : ℂ) from rfl,
    Complex.exp_nat_mul, Complex.exp_sub]
  simp only [div_eq_mul_inv, mul_inv_rev, one_mul]
  ring

theorem filledNegativeNumerator_eq_center_exp {n : ℕ} {b : ℂ → ℂ}
    {g : ℂ × ℂ → ℂ} {d τ t γ lb : ℂ} {v : Fin n → ℂ}
    (h : Fin n → ℂ) (s p : Fin n × Fin n → ℂ)
    (hcenter : g (τ, d) = γ)
    (hb : b t = b τ * Complex.exp lb)
    (hone : ∀ i, Complex.sinh (g (t, d + v i)) = Complex.sinh γ * Complex.exp (h i))
    (hsine : ∀ ij ∈ indexPairs n, complexSinc ((v ij.1 - v ij.2) / 2) = Complex.exp (s ij))
    (hpair : ∀ ij ∈ indexPairs n,
      Complex.sinh ((g (t, d + v ij.1) + g (t, d + v ij.2)) / 2) =
        Complex.sinh γ * Complex.exp (p ij)) :
    filledNegativeNumerator n b g d t v =
      filledNegativeNumerator n b g d τ 0 *
        Complex.exp (completeNumeratorLog n lb h (fun ij => s ij - p ij)) := by
  have ho : (∏ i, 1 / Complex.sinh (g (t, d + v i))) =
      (1 / Complex.sinh γ) ^ n * Complex.exp (-(∑ i, h i)) := by
    simp_rw [inverse_factor_from_log _ _ _ (hone _)]
    rw [Finset.prod_mul_distrib]
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    congr 1
    rw [← Complex.exp_sum, Finset.sum_neg_distrib]
  have hp : (∏ ij ∈ indexPairs n,
      (complexSinc ((v ij.1 - v ij.2) / 2) /
        (2 * Complex.sinh ((g (t, d + v ij.1) + g (t, d + v ij.2)) / 2))) ^ 2) =
      (1 / (2 * Complex.sinh γ)) ^ (2 * n.choose 2) *
        Complex.exp (∑ ij ∈ indexPairs n, 2 * (s ij - p ij)) := by
    calc
      _ = ∏ ij ∈ indexPairs n, (1 / (2 * Complex.sinh γ)) ^ 2 *
          Complex.exp (2 * (s ij - p ij)) := by
        apply Finset.prod_congr rfl
        intro ij hij
        exact filled_pair_from_logs _ _ _ _ _ (hsine ij hij) (hpair ij hij)
      _ = _ := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, card_indexPairs,
          ← pow_mul, ← Complex.exp_sum]
  rw [filledNegativeNumerator, hb, mul_pow, ho, hp,
    filledNegativeNumerator_center n b g d τ γ hcenter]
  unfold completeNumeratorLog
  rw [Complex.exp_add, Complex.exp_sub, Complex.exp_nat_mul, Complex.exp_neg]
  ring

theorem filledNegativeDensityAt_eq_center_exp {n : ℕ} {b : ℂ → ℂ}
    {g : ℂ × ℂ → ℂ} {d τ t ln ld : ℂ} {v : Fin n → ℂ}
    (hnum : filledNegativeNumerator n b g d t v =
      filledNegativeNumerator n b g d τ 0 * Complex.exp ln)
    (hden : phaseTemperatureSum n g d t v =
      phaseTemperatureSum n g d τ 0 * Complex.exp ld) :
    filledNegativeDensityAt n b g d t v =
      filledNegativeDensityAt n b g d τ 0 * Complex.exp (ln - ld) := by
  unfold filledNegativeDensityAt
  rw [hnum, hden, Complex.exp_sub]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

theorem complete_density_eq_vandermonde_center_exp {n : ℕ} {b : ℂ → ℂ}
    {g : ℂ × ℂ → ℂ} {d τ t l : ℂ} {v : Fin n → ℂ}
    (hfill : filledNegativeDensityAt n b g d t v =
      filledNegativeDensityAt n b g d τ 0 * Complex.exp l) :
    -(2 * completeNegativeNumerator n b g d t v) / phaseTemperatureSum n g d t v =
      filledNegativeDensityAt n b g d τ 0 * complexVandermondeSquared n v * Complex.exp l := by
  have hf : -(2 * completeNegativeNumerator n b g d t v) / phaseTemperatureSum n g d t v =
      complexVandermondeSquared n v * filledNegativeDensityAt n b g d t v := by
    rw [completeNegativeNumerator_factorization]
    unfold filledNegativeDensityAt
    ring
  rw [hf, hfill]
  ring

end
end IsingBulk.AnisoF002.NegativeHT
