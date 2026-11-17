import IsingBulk.AnisoF002.C03.RegularModelCorrections

/-!
# Pointwise bounds for the genuine analytic model corrections

These are constructed from the actual B(tau), curvature and normalized
sinc logarithms.  Both constants and the reciprocal-particle threshold
are chosen before the particle number or derivative order.
-/

namespace IsingBulk.AnisoF002.NegativeHT
noncomputable section
open Set
open scoped Topology

theorem actual_model_correction_values {B : ℂ → ℂ} (hB : AnalyticAt ℂ B 0)
    (hslit : B 0 ∈ Complex.slitPlane) (c s : ℝ) :
    ∃ C R : ℝ, 0 < C ∧ 0 < R ∧ ∀ n : ℕ, Odd n → R ≤ (n : ℝ) →
      |actualModelRemainder B c s n| ≤ C * (n : ℝ) ^ 2 ∧
        |actualTemperatureCorrection n| ≤ C / (n : ℝ) ^ 2 := by
  obtain ⟨q₂, q₁, q₀, U, hU, _, hrepr⟩ := actualModelRemainder_analytic_form hB hslit c s
  let E := analyticSquareFill inverseParticleLogTemperature
  have hE : AnalyticAt ℂ E 0 := analyticSquareFill_analytic inverseParticleLogTemperature_analytic
  have he (z : ℂ) : inverseParticleLogTemperature z = z ^ 2 * E z := by
    simpa only [inverseParticleLogTemperature_zero, zero_add] using
      analyticSquareFill_identity
        (analytic_even_deriv_zero inverseParticleLogTemperature_analytic inverseParticleLogTemperature_even) z
  obtain ⟨rU, MU, hrU, hMU, _, hUb⟩ := exists_analytic_model_disk hU
  obtain ⟨rE, ME, hrE, hME, _, hEb⟩ := exists_analytic_model_disk hE
  let r := min rU rE
  let M := MU + ME
  let C := 1 + |q₂| + |q₁| + |q₀| + M
  let R := max 1 (1 / r)
  have hr : 0 < r := lt_min hrU hrE
  have hM : 0 < M := add_pos hMU hME
  have hC : 0 < C := by dsimp [C]; positivity
  have hR : 0 < R := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have hUM (z : ℂ) (hz : z ∈ Metric.closedBall (0 : ℂ) r) : ‖U z‖ ≤ M :=
    (hUb z (Metric.closedBall_subset_closedBall (min_le_left _ _) hz)).trans (le_add_of_nonneg_right hME.le)
  have hEM (z : ℂ) (hz : z ∈ Metric.closedBall (0 : ℂ) r) : ‖E z‖ ≤ M :=
    (hEb z (Metric.closedBall_subset_closedBall (min_le_right _ _) hz)).trans (le_add_of_nonneg_left hMU.le)
  refine ⟨C, R, hC, hR, ?_⟩
  intro n hn hlarge
  have hn1 : 1 ≤ (n : ℝ) := (le_max_left _ _).trans hlarge
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn.pos
  have hn2 : 1 ≤ (n : ℝ) ^ 2 := by nlinarith
  have hnn2 : (n : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
  have hnorm : ‖(n : ℂ)⁻¹‖ = 1 / (n : ℝ) := by
    have hc : (n : ℂ) = ((n : ℝ) : ℂ) := by norm_cast
    rw [hc, norm_inv, Complex.norm_real, Real.norm_of_nonneg hnR.le, one_div]
  have hnr : 1 / (n : ℝ) ≤ r := by
    have hh : 1 / r ≤ (n : ℝ) := (le_max_right _ _).trans hlarge
    apply (div_le_iff₀ hnR).mpr
    have hh' := (div_le_iff₀ hr).mp hh
    nlinarith
  have hin : (n : ℂ)⁻¹ ∈ Metric.closedBall (0 : ℂ) r := by
    rw [Metric.mem_closedBall, dist_zero_right, hnorm]
    exact hnr
  have hUr : |(U (n : ℂ)⁻¹).re| ≤ M := (Complex.abs_re_le_norm _).trans (hUM _ hin)
  have hCM : M ≤ C := by dsimp [C]; nlinarith [abs_nonneg q₂, abs_nonneg q₁, abs_nonneg q₀]
  constructor
  · rw [hrepr n hn]
    calc
      _ ≤ |q₂ * (n : ℝ) ^ 2 + q₁ * n + q₀| + |(U (n : ℂ)⁻¹).re| := abs_add_le _ _
      _ ≤ (|q₂ * (n : ℝ) ^ 2 + q₁ * n| + |q₀|) + M := add_le_add (abs_add_le _ _) hUr
      _ ≤ ((|q₂ * (n : ℝ) ^ 2| + |q₁ * n|) + |q₀|) + M :=
        add_le_add (add_le_add (abs_add_le _ _) le_rfl) le_rfl
      _ = |q₂| * (n : ℝ) ^ 2 + |q₁| * n + |q₀| + M := by
        rw [abs_mul, abs_mul, abs_of_nonneg (sq_nonneg (n : ℝ)), abs_of_nonneg hnR.le]
      _ ≤ |q₂| * (n : ℝ) ^ 2 + |q₁| * (n : ℝ) ^ 2 + |q₀| * (n : ℝ) ^ 2 + M * (n : ℝ) ^ 2 := by
        exact add_le_add (add_le_add (add_le_add le_rfl (mul_le_mul_of_nonneg_left hnn2 (abs_nonneg _)))
          (le_mul_of_one_le_right (abs_nonneg _) hn2)) (le_mul_of_one_le_right hM.le hn2)
      _ ≤ C * (n : ℝ) ^ 2 := by dsimp [C]; nlinarith [sq_nonneg (n : ℝ)]
  · rw [actualTemperatureCorrection, he]
    calc
      _ ≤ ‖(n : ℂ)⁻¹ ^ 2 * E (n : ℂ)⁻¹‖ := Complex.abs_re_le_norm _
      _ = ‖(n : ℂ)⁻¹‖ ^ 2 * ‖E (n : ℂ)⁻¹‖ := by rw [norm_mul, norm_pow]
      _ ≤ (1 / (n : ℝ)) ^ 2 * M := by
        rw [hnorm]
        exact mul_le_mul_of_nonneg_left (hEM _ hin) (sq_nonneg _)
      _ = M / (n : ℝ) ^ 2 := by ring
      _ ≤ C / (n : ℝ) ^ 2 := div_le_div_of_nonneg_right hCM (sq_nonneg _)

end
end IsingBulk.AnisoF002.NegativeHT
