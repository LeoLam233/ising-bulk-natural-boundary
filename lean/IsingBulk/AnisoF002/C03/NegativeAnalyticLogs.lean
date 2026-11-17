import IsingBulk.AnisoF002.C03.NegativeDensityFactors
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

/-!
# Fixed scalar analytic logarithms for the complete residue density

Every logarithm is taken only after normalization by a nonzero center
value.  The construction supplies one neighborhood and Lipschitz constant.
The sine divided difference has a quadratic logarithmic bound, including
the collision point, rather than a singular quotient convention.
-/

namespace IsingBulk.AnisoF002.NegativeHT
noncomputable section
open IsingBulk.AnisoF002.Isotropic Set Filter
open scoped Topology

theorem analytic_scalar_lipschitz_ball {f : ℂ → ℂ} {x : ℂ} (hf : AnalyticAt ℂ f x) :
    ∃ r K : ℝ, 0 < r ∧ 0 < K ∧ AnalyticOnNhd ℂ f (Metric.ball x r) ∧
      ∀ y ∈ Metric.ball x r, ∀ z ∈ Metric.ball x r,
        ‖f z - f y‖ ≤ K * ‖z - y‖ := by
  let K : ℝ := ‖deriv f x‖ + 1
  have hK : 0 < K := by dsimp [K]; positivity
  have hb : ∀ᶠ y in 𝓝 x, ‖deriv f y‖ < K :=
    hf.deriv.continuousAt.norm.eventually (Iio_mem_nhds (by dsimp [K]; linarith))
  obtain ⟨r, hr, hh⟩ := Metric.eventually_nhds_iff.mp (hf.eventually_analyticAt.and hb)
  have ha (y : ℂ) (hy : y ∈ Metric.ball x r) : AnalyticAt ℂ f y :=
    (hh (Metric.mem_ball.mp hy)).1
  refine ⟨r, K, hr, hK, ha, ?_⟩
  intro y hy z hz
  exact (convex_ball x r).norm_image_sub_le_of_norm_deriv_le
    (fun a ha' => (ha a ha').differentiableAt)
    (fun a ha' => (hh (Metric.mem_ball.mp ha')).2.le) hy hz

theorem exists_normalized_local_log {f : ℂ → ℂ} {x : ℂ}
    (hf : AnalyticAt ℂ f x) (hf0 : f x ≠ 0) :
    ∃ L : ℂ → ℂ, ∃ r K : ℝ, 0 < r ∧ 0 < K ∧ L x = 0 ∧
      AnalyticOnNhd ℂ L (Metric.ball x r) ∧
      (∀ y ∈ Metric.ball x r, f y ≠ 0 ∧ Complex.exp (L y) = f y / f x) ∧
      ∀ y ∈ Metric.ball x r, ∀ z ∈ Metric.ball x r,
        ‖L z - L y‖ ≤ K * ‖z - y‖ := by
  let L : ℂ → ℂ := fun y => Complex.log (f y / f x)
  have hx : f x / f x ∈ Complex.slitPlane := by simp only [div_self hf0]; exact Complex.one_mem_slitPlane
  have hLa : AnalyticAt ℂ L x := hf.div_const.clog hx
  have hL0 : L x = 0 := by simp only [L, div_self hf0, Complex.log_one]
  obtain ⟨r, K, hr, hK, hL, hLip⟩ := analytic_scalar_lipschitz_ball hLa
  have hne : ∀ᶠ y in 𝓝 x, f y ≠ 0 := hf.continuousAt.eventually_ne hf0
  obtain ⟨s, hs, hsn⟩ := Metric.eventually_nhds_iff.mp hne
  let R : ℝ := min r s
  have hR : 0 < R := lt_min hr hs
  have hRr : Metric.ball x R ⊆ Metric.ball x r := Metric.ball_subset_ball (min_le_left _ _)
  have hRs : Metric.ball x R ⊆ Metric.ball x s := Metric.ball_subset_ball (min_le_right _ _)
  refine ⟨L, R, K, hR, hK, hL0, hL.mono hRr, ?_, ?_⟩
  · intro y hy
    have hfy := hsn (Metric.mem_ball.mp (hRs hy))
    exact ⟨hfy, Complex.exp_log (div_ne_zero hfy hf0)⟩
  · intro y hy z hz
    exact hLip y (hRr hy) z (hRr hz)

theorem analytic_scalar_quadratic_of_deriv_zero {f : ℂ → ℂ} {x : ℂ}
    (hf : AnalyticAt ℂ f x) (hdf : deriv f x = 0) :
    ∃ r K : ℝ, 0 < r ∧ 0 < K ∧ AnalyticOnNhd ℂ f (Metric.ball x r) ∧
      ∀ z ∈ Metric.ball x r, ‖f z - f x‖ ≤ K * ‖z - x‖ ^ 2 := by
  obtain ⟨r, K, hr, hK, _, hLip⟩ := analytic_scalar_lipschitz_ball hf.deriv
  obtain ⟨s, hs, hsa⟩ := Metric.eventually_nhds_iff.mp hf.eventually_analyticAt
  let R : ℝ := min r s
  have hR : 0 < R := lt_min hr hs
  have hRr : Metric.ball x R ⊆ Metric.ball x r := Metric.ball_subset_ball (min_le_left _ _)
  have hRs : Metric.ball x R ⊆ Metric.ball x s := Metric.ball_subset_ball (min_le_right _ _)
  have hfa : AnalyticOnNhd ℂ f (Metric.ball x R) := fun y hy => hsa (Metric.mem_ball.mp (hRs hy))
  refine ⟨R, K, hR, hK, hfa, ?_⟩
  intro z hz
  have hx : x ∈ Metric.ball x R := Metric.mem_ball_self hR
  have hseg : segment ℝ x z ⊆ Metric.ball x R := (convex_ball x R).segment_subset hx hz
  have hb (y : ℂ) (hy : y ∈ segment ℝ x z) : ‖deriv f y‖ ≤ K * ‖z - x‖ := by
    have hh := hLip x (hRr hx) y (hRr (hseg hy))
    rw [hdf, sub_zero] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left (norm_sub_le_of_mem_segment hy) hK.le)
  have he := (convex_segment x z).norm_image_sub_le_of_norm_deriv_le
    (fun y hy => (hfa y (hseg hy)).differentiableAt) hb
    (left_mem_segment ℝ x z) (right_mem_segment ℝ x z)
  simpa only [pow_two, mul_assoc] using he

theorem deriv_zero_of_even {f : ℂ → ℂ} (hf : DifferentiableAt ℂ f 0)
    (heven : ∀ z : ℂ, f (-z) = f z) : deriv f 0 = 0 := by
  have hneg : HasDerivAt (fun z : ℂ => f (-z)) (-deriv f 0) 0 := by
    have hf' : HasDerivAt f (deriv f 0) (-(0 : ℂ)) := by simpa using hf.hasDerivAt
    simpa only [Function.comp_def, neg_one_smul] using
      hf'.scomp (0 : ℂ) (hasDerivAt_neg (0 : ℂ))
  have hsame : HasDerivAt (fun z : ℂ => f (-z)) (deriv f 0) 0 := by
    simpa only [heven] using hf.hasDerivAt
  have hh := hneg.unique hsame
  linear_combination -hh / 2

theorem complexSinc_even (z : ℂ) : complexSinc (-z) = complexSinc z := by
  by_cases hz : z = 0
  · simp [hz]
  · apply mul_left_cancel₀ (neg_ne_zero.mpr hz)
    rw [complexSinc_mul, neg_mul, complexSinc_mul, Complex.sin_neg]

theorem exists_quadratic_sinc_log :
    ∃ L : ℂ → ℂ, ∃ r K : ℝ, 0 < r ∧ 0 < K ∧ L 0 = 0 ∧
      AnalyticOnNhd ℂ L (Metric.ball 0 r) ∧
      (∀ z ∈ Metric.ball 0 r, complexSinc z ≠ 0 ∧ Complex.exp (L z) = complexSinc z) ∧
      ∀ z ∈ Metric.ball 0 r, ‖L z‖ ≤ K * ‖z‖ ^ 2 := by
  let L : ℂ → ℂ := fun z => Complex.log (complexSinc z)
  have hL : AnalyticAt ℂ L 0 := (complexSinc_analyticAt 0).clog
    (by simpa only [complexSinc_zero] using Complex.one_mem_slitPlane)
  have hL0 : L 0 = 0 := by simp only [L, complexSinc_zero, Complex.log_one]
  have hd : deriv L 0 = 0 := deriv_zero_of_even hL.differentiableAt
    (fun z => by simp only [L, complexSinc_even])
  obtain ⟨r, K, hr, hK, hLa, hquad⟩ := analytic_scalar_quadratic_of_deriv_zero hL hd
  have hne : ∀ᶠ z in 𝓝 (0 : ℂ), complexSinc z ≠ 0 :=
    (complexSinc_analyticAt 0).continuousAt.eventually_ne (by simp)
  obtain ⟨s, hs, hsn⟩ := Metric.eventually_nhds_iff.mp hne
  let R : ℝ := min r s
  have hR : 0 < R := lt_min hr hs
  have hRr : Metric.ball (0 : ℂ) R ⊆ Metric.ball 0 r := Metric.ball_subset_ball (min_le_left _ _)
  have hRs : Metric.ball (0 : ℂ) R ⊆ Metric.ball 0 s := Metric.ball_subset_ball (min_le_right _ _)
  refine ⟨L, R, K, hR, hK, hL0, hLa.mono hRr, ?_, ?_⟩
  · intro z hz
    have hn := hsn (Metric.mem_ball.mp (hRs hz))
    exact ⟨hn, Complex.exp_log hn⟩
  · intro z hz
    simpa only [hL0, sub_zero] using hquad z (hRr hz)

end
end IsingBulk.AnisoF002.NegativeHT
