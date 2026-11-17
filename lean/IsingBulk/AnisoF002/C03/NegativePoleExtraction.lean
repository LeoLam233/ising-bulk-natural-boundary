import IsingBulk.AnisoF002.C03.NegativePoleFactor
import IsingBulk.AnisoF002.C03.RegularEdgeSiteKernel

/-!
# Exact pole extraction from the full physical site factor

Both divided differences are filled at their centers.  The first one
factors the normalized phase; the second factors the actual exponential
denominator.  The resulting holomorphic numerator gives the exact residue
and an ordinary analytic remainder, retaining the entire numerator H.
-/

namespace IsingBulk.AnisoF002.NegativeHT
noncomputable section
open Set Filter IsingBulk.AnisoF002.RegularTail.C03
open scoped Topology

theorem exponential_dslope_entire : AnalyticOnNhd ℂ (dslope Complex.exp 0) Set.univ := by
  apply (Complex.analyticOnNhd_iff_differentiableOn isOpen_univ).mpr
  exact (Complex.differentiableOn_dslope (by simp)).mpr Complex.differentiable_exp.differentiableOn

theorem exists_exponential_dslope_control :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ w ∈ Metric.closedBall (0 : ℂ) ρ,
      ‖dslope Complex.exp 0 w - 1‖ ≤ 1 / 2 ∧
      1 / 2 ≤ ‖dslope Complex.exp 0 w‖ ∧
      dslope Complex.exp 0 w ≠ 0 ∧ ‖Complex.exp w‖ ≤ 2 := by
  have he : Tendsto (dslope Complex.exp 0) (𝓝 0) (𝓝 1) := by
    simpa only [dslope_same, Complex.deriv_exp, Complex.exp_zero] using
      (exponential_dslope_entire 0 (mem_univ _)).continuousAt.tendsto
  have hx : Tendsto Complex.exp (𝓝 0) (𝓝 1) := by
    simpa only [Complex.exp_zero] using Complex.continuous_exp.continuousAt.tendsto (x := 0)
  have hnear : ∀ᶠ w : ℂ in 𝓝 0,
      ‖dslope Complex.exp 0 w - 1‖ < 1 / 2 ∧ ‖Complex.exp w - 1‖ < 1 := by
    filter_upwards [he.eventually (Metric.ball_mem_nhds (1 : ℂ) (by norm_num : (0 : ℝ) < 1 / 2)),
      hx.eventually (Metric.ball_mem_nhds (1 : ℂ) zero_lt_one)] with w hw hew
    simpa only [Metric.mem_ball, dist_eq_norm] using And.intro hw hew
  obtain ⟨ρ, hρ, hball⟩ := Metric.eventually_nhds_iff.mp hnear
  refine ⟨ρ / 2, half_pos hρ, ?_⟩
  intro w hw
  have h := hball ((Metric.mem_closedBall.mp hw).trans_lt (half_lt_self hρ))
  have hlow : 1 / 2 ≤ ‖dslope Complex.exp 0 w‖ := by
    have hh := norm_sub_le_norm_sub_add_norm_sub (1 : ℂ) (dslope Complex.exp 0 w) 0
    simp only [sub_zero, norm_one, norm_sub_rev (1 : ℂ)] at hh
    linarith [h.1]
  refine ⟨h.1.le, hlow, norm_pos_iff.mp (by linarith), ?_⟩
  have hh := norm_sub_le_norm_sub_add_norm_sub (Complex.exp w) 1 0
  simp only [sub_zero, norm_one] at hh
  linarith [h.2]

def filledPoleNumerator (H F : ℂ → ℂ) (n : ℕ) (T t : ℂ) : ℂ :=
  H t * (1 + Complex.exp (-((n : ℂ) * F t))) /
    ((n : ℂ) * dslope F T t * dslope Complex.exp 0 (-((n : ℂ) * F t)))

theorem filledPoleNumerator_center (H F : ℂ → ℂ) (n : ℕ) (T : ℂ)
    (hzero : F T = 0) :
    filledPoleNumerator H F n T T = 2 * H T / ((n : ℂ) * deriv F T) := by
  simp only [filledPoleNumerator, hzero, mul_zero, neg_zero, Complex.exp_zero,
    dslope_same, Complex.deriv_exp, mul_one]
  ring

theorem full_site_factor_eq_filled_quotient (H F : ℂ → ℂ) (n : ℕ) (Γ T t : ℂ)
    (hzero : F T = 0) (hres : Complex.exp (-Γ) = 1) :
    H t * phaseSiteFactor (Γ + (n : ℂ) * F t) = filledPoleNumerator H F n T t / (t - T) := by
  have hF : F t = (t - T) * dslope F T t := by
    simpa only [hzero, sub_zero, smul_eq_mul] using (sub_smul_dslope F T t).symm
  have he := sub_smul_dslope Complex.exp 0 (-((n : ℂ) * F t))
  simp only [sub_zero, Complex.exp_zero, smul_eq_mul] at he
  have hd : 1 - Complex.exp (-((n : ℂ) * F t)) =
      ((n : ℂ) * dslope F T t * dslope Complex.exp 0 (-((n : ℂ) * F t))) * (t - T) := by
    rw [hF] at he ⊢
    linear_combination he
  unfold phaseSiteFactor filledPoleNumerator
  rw [neg_add, Complex.exp_add, hres, one_mul, hd, div_div, ← mul_div_assoc]

theorem full_site_factor_exact_pole_remainder (H F : ℂ → ℂ) (n : ℕ) (Γ T t : ℂ)
    (hzero : F T = 0) (hres : Complex.exp (-Γ) = 1) (ht : t ≠ T) :
    H t * phaseSiteFactor (Γ + (n : ℂ) * F t) =
      (2 * H T / ((n : ℂ) * deriv F T)) / (t - T) +
        dslope (filledPoleNumerator H F n T) T t := by
  rw [full_site_factor_eq_filled_quotient H F n Γ T t hzero hres,
    ← filledPoleNumerator_center H F n T hzero]
  have he := sub_smul_dslope (filledPoleNumerator H F n T) T t
  simp only [smul_eq_mul] at he
  field_simp [sub_ne_zero.mpr ht]
  linear_combination -he

theorem analytic_remainder_uniform_bound {K : ℂ → ℂ} {T : ℂ} {R M : ℝ}
    (hR : 0 < R) (hK : AnalyticOnNhd ℂ K (Metric.ball (0 : ℂ) R))
    (hM : ∀ t ∈ Metric.ball (0 : ℂ) R, ‖K t‖ ≤ M)
    (hT : ‖T‖ ≤ R / 4) :
    AnalyticOnNhd ℂ (dslope K T) (Metric.ball (0 : ℂ) R) ∧
      ∀ t ∈ Metric.ball (0 : ℂ) (R / 4), ‖dslope K T t‖ ≤ 4 * M / R := by
  have hTin : T ∈ Metric.ball (0 : ℂ) R := by
    rw [Metric.mem_ball, dist_zero_right]
    linarith
  have hsub : Metric.ball T (R / 2) ⊆ Metric.ball (0 : ℂ) R := by
    intro u hu
    have htri := norm_add_le (u - T) T
    rw [sub_add_cancel] at htri
    have hun : ‖u - T‖ < R / 2 := by simpa only [Metric.mem_ball, dist_eq_norm] using hu
    rw [Metric.mem_ball, dist_zero_right]
    linarith
  refine ⟨analyticOnNhd_dslope_ball hK hTin, ?_⟩
  intro t ht
  have htT : t ∈ Metric.ball T (R / 2) := by
    have htn : ‖t‖ < R / 4 := by simpa only [Metric.mem_ball, dist_zero_right] using ht
    have htri := norm_sub_le t T
    rw [Metric.mem_ball, dist_eq_norm]
    linarith
  have hmaps : MapsTo K (Metric.ball T (R / 2)) (Metric.closedBall (K T) (2 * M)) := by
    intro u hu
    rw [Metric.mem_closedBall, dist_eq_norm]
    exact (norm_sub_le (K u) (K T)).trans (by linarith [hM u (hsub hu), hM T hTin])
  have hh := Complex.norm_dslope_le_div_of_mapsTo_ball
    (hK.differentiableOn.mono hsub) hmaps htT
  convert hh using 1
  ring

end
end IsingBulk.AnisoF002.NegativeHT
