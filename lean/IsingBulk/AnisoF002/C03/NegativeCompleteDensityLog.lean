import IsingBulk.AnisoF002.C03.NegativeDerivativeAverage

/-!
# The actual complete filled-density logarithm

This is one explicit logarithm for the full finite residue density,
including its temperature-derivative denominator.  Its analyticity is
proved through the collision divisors by composition with the filled
sinc factors, never by division by a Vandermonde.
-/

namespace IsingBulk.AnisoF002.NegativeHT
noncomputable section
open IsingBulk.AnisoF002.Isotropic Set Filter
open scoped Topology BigOperators

def fullDensityLog (n : ℕ) (g : ℂ × ℂ → ℂ) (Lb Lh Ls Ld : ℂ → ℂ)
    (d τ t : ℂ) (v : Fin n → ℂ) : ℂ :=
  completeNumeratorLog n (Lb t - Lb τ) (fun i => Lh (g (t, d + v i)))
    (fun ij => Ls ((v ij.1 - v ij.2) / 2) -
      Lh ((g (t, d + v ij.1) + g (t, d + v ij.2)) / 2)) -
    Ld (phaseTemperatureSum n g d t v / ((n : ℂ) * phaseTemperatureDerivative g (τ, d)))

theorem phaseTemperatureSum_center (n : ℕ) (g : ℂ × ℂ → ℂ) (d τ : ℂ) :
    phaseTemperatureSum n g d τ 0 = (n : ℂ) * phaseTemperatureDerivative g (τ, d) := by
  simp only [phaseTemperatureSum, phaseTemperatureDerivative, Pi.zero_apply, add_zero,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

theorem fullDensityLog_factorization {n : ℕ} {b : ℂ → ℂ} {g : ℂ × ℂ → ℂ}
    {Lb Lh Ls Ld : ℂ → ℂ} {d τ t γ : ℂ} {v : Fin n → ℂ}
    (hcenter : g (τ, d) = γ)
    (hb : b t = b τ * Complex.exp (Lb t - Lb τ))
    (hone : ∀ i, Complex.sinh (g (t, d + v i)) = Complex.sinh γ * Complex.exp (Lh (g (t, d + v i))))
    (hsine : ∀ ij ∈ indexPairs n,
      complexSinc ((v ij.1 - v ij.2) / 2) = Complex.exp (Ls ((v ij.1 - v ij.2) / 2)))
    (hpair : ∀ ij ∈ indexPairs n,
      Complex.sinh ((g (t, d + v ij.1) + g (t, d + v ij.2)) / 2) =
        Complex.sinh γ * Complex.exp (Lh ((g (t, d + v ij.1) + g (t, d + v ij.2)) / 2)))
    (hden0 : (n : ℂ) * phaseTemperatureDerivative g (τ, d) ≠ 0)
    (hden : Complex.exp (Ld (phaseTemperatureSum n g d t v /
        ((n : ℂ) * phaseTemperatureDerivative g (τ, d)))) =
      phaseTemperatureSum n g d t v / ((n : ℂ) * phaseTemperatureDerivative g (τ, d))) :
    filledNegativeDensityAt n b g d t v =
      filledNegativeDensityAt n b g d τ 0 * Complex.exp (fullDensityLog n g Lb Lh Ls Ld d τ t v) := by
  have hn := filledNegativeNumerator_eq_center_exp
    (fun i => Lh (g (t, d + v i))) (fun ij => Ls ((v ij.1 - v ij.2) / 2))
    (fun ij => Lh ((g (t, d + v ij.1) + g (t, d + v ij.2)) / 2))
    hcenter hb hone hsine hpair
  have hd : phaseTemperatureSum n g d t v = phaseTemperatureSum n g d τ 0 *
      Complex.exp (Ld (phaseTemperatureSum n g d t v /
        ((n : ℂ) * phaseTemperatureDerivative g (τ, d)))) := by
    rw [phaseTemperatureSum_center, hden]
    exact (mul_div_cancel₀ _ hden0).symm
  exact filledNegativeDensityAt_eq_center_exp hn hd

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem fullDensityLog_analyticAt_comp {n : ℕ} {g : ℂ × ℂ → ℂ}
    {Lb Lh Ls Ld : ℂ → ℂ} {d τ : ℂ} {T : E → ℂ} {v : E → Fin n → ℂ} {x : E}
    (hT : AnalyticAt ℂ T x) (hv : ∀ i, AnalyticAt ℂ (fun y => v y i) x)
    (hg : ∀ i, AnalyticAt ℂ g (T x, d + v x i))
    (hb : AnalyticAt ℂ Lb (T x))
    (hh : ∀ i, AnalyticAt ℂ Lh (g (T x, d + v x i)))
    (hs : ∀ ij ∈ indexPairs n, AnalyticAt ℂ Ls ((v x ij.1 - v x ij.2) / 2))
    (hp : ∀ ij ∈ indexPairs n,
      AnalyticAt ℂ Lh ((g (T x, d + v x ij.1) + g (T x, d + v x ij.2)) / 2))
    (hd : AnalyticAt ℂ Ld (phaseTemperatureSum n g d (T x) (v x) /
      ((n : ℂ) * phaseTemperatureDerivative g (τ, d)))) :
    AnalyticAt ℂ (fun y => fullDensityLog n g Lb Lh Ls Ld d τ (T y) (v y)) x := by
  have hγ (i : Fin n) : AnalyticAt ℂ (fun y => g (T y, d + v y i)) x :=
    (hg i).comp_of_eq (hT.prod (analyticAt_const.add (hv i))) rfl
  have hone : AnalyticAt ℂ (fun y => ∑ i, Lh (g (T y, d + v y i))) x := by
    apply Finset.analyticAt_fun_sum
    intro i _
    exact (hh i).comp_of_eq (hγ i) rfl
  have hpair : AnalyticAt ℂ (fun y => ∑ ij ∈ indexPairs n, 2 *
      (Ls ((v y ij.1 - v y ij.2) / 2) -
        Lh ((g (T y, d + v y ij.1) + g (T y, d + v y ij.2)) / 2))) x := by
    apply Finset.analyticAt_fun_sum
    intro ij hij
    exact analyticAt_const.mul
      (((hs ij hij).comp_of_eq (((hv ij.1).sub (hv ij.2)).div_const (c := 2)) rfl).sub
        ((hp ij hij).comp_of_eq (((hγ ij.1).add (hγ ij.2)).div_const (c := 2)) rfl))
  exact (((analyticAt_const.mul ((hb.comp hT).sub analyticAt_const)).sub hone).add hpair).sub
    (hd.comp_of_eq ((phaseTemperatureSum_analyticAt_comp hT hv hg).div_const
      (c := (n : ℂ) * phaseTemperatureDerivative g (τ, d))) rfl)

end
end IsingBulk.AnisoF002.NegativeHT
