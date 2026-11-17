import IsingBulk.AnisoF002.C03.RegularFirstObstruction
import IsingBulk.AnisoF002.C03.NegativeHalfIntegerPeriod

/-! # Nonzero first period and complete-series obstruction for even particles -/

namespace IsingBulk.AnisoF002.RegularTail.C03
noncomputable section
open Set Filter MeasureTheory IsingBulk.Anisotropic IsingBulk.AnisoF002.NegativeHT.Angular
open scoped Topology

theorem regularFirstAmplitude_even_ne_zero {b : ℝ} {a : ℂ → ℂ}
    (hb : |b| < 1) (ha : 0 < (a 0).im) {n : ℕ} (hn : Even (n + 1)) :
    regularFirstAmplitude b a n (evenTopOrder (n + 1)) ≠ 0 := by
  have hn0 : 0 < n := by obtain ⟨k, hk⟩ := hn; omega
  have hrad : radialPower n = 2 * evenTopOrder (n + 1) := by
    have h := even_first_scaling_degree hn
    unfold radialPower
    omega
  rw [regularFirstAmplitude_eq_period]
  apply mul_ne_zero (mul_ne_zero (regularCoefficientNormalization_ne_zero _)
    (regularLeadingConstant_ne_zero hb ha _ _))
  exact quadraticPeriod_half_integer_ne_zero hn0 hrad
    (by positivity) (by rw [regularRadialCoefficient_re]; exact half_pos ha)

namespace RegularEdgeCompleteControl

theorem rational_even_series_no_analytic_inward_germ {r p : ℕ}
    (hr : 0 < r) (hrp : 2 * r < p) (hcop : r.Coprime p) (hp : Odd p)
    {a : ℂ → ℂ} (d : RegularEdgeCompleteControl (Real.cos (regularRationalAngle r p)) a)
    (ha : 0 < (a 0).im) :
    ¬ ∃ g : ℂ → ℂ, AnalyticAt ℂ g 0 ∧
      ∀ᶠ eps : ℝ in 𝓝[>] (0 : ℝ),
        edgeParticleTail (affineEdgeCenter (Real.cos (regularRationalAngle r p))) a 1
          =ᶠ[𝓝 ((eps : ℂ) * Complex.I)] g := by
  have hp0 : 2 * p - 1 + 1 = 2 * p := by omega
  have hA := regularFirstAmplitude_even_ne_zero (n := 2 * p - 1)
    (regularRational_cos_abs_lt_one hr hrp) ha (by rw [hp0]; exact ⟨p, by omega⟩)
  rw [hp0] at hA
  apply no_analytic_inward_germ_of_scaled_limit (by norm_num : 0 < 1) hA
  simpa only [pow_one] using d.rational_even_series_first_limit hr hrp hcop hp ha

theorem rational_even_series_no_upper_extension {r p : ℕ}
    (hr : 0 < r) (hrp : 2 * r < p) (hcop : r.Coprime p) (hp : Odd p)
    {a : ℂ → ℂ} (d : RegularEdgeCompleteControl (Real.cos (regularRationalAngle r p)) a)
    (ha : 0 < (a 0).im) :
    ¬ HasDomainExtension {u : ℂ | 0 < u.im}
      (edgeParticleTail (affineEdgeCenter (Real.cos (regularRationalAngle r p))) a 1) 0 := by
  have hp0 : 2 * p - 1 + 1 = 2 * p := by omega
  have hA := regularFirstAmplitude_even_ne_zero (n := 2 * p - 1)
    (regularRational_cos_abs_lt_one hr hrp) ha (by rw [hp0]; exact ⟨p, by omega⟩)
  rw [hp0] at hA
  apply no_upper_domain_extension_of_scaled_limit (by norm_num : 0 < 1) hA
  simpa only [pow_one] using d.rational_even_series_first_limit hr hrp hcop hp ha

end RegularEdgeCompleteControl
end
end IsingBulk.AnisoF002.RegularTail.C03
