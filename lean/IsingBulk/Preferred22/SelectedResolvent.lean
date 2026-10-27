import IsingBulk.Preferred22.SelectedAttenuation
import IsingBulk.Preferred22.IntegratedCoarea

/-! The literal complete product resolvent on the selected population costs
only C*N for each fixed positive deformation strength. -/
namespace IsingBulk.Preferred22
noncomputable section

lemma preferred_resolvent_of_attenuation {z : ℂ} {x : ℝ} (hx : 0<x) (hx1 : x≤1)
    (hz : ‖z‖≤Real.exp (-x)) : ‖(1+z)/(1-z)‖≤2*Real.exp 1/x := by
  have he := Real.add_one_le_exp x
  have hm := mul_le_mul_of_nonneg_right he (Real.exp_pos (-x)).le
  rw [← Real.exp_add,add_neg_cancel,Real.exp_zero] at hm
  have hex : Real.exp (-1)≤Real.exp (-x) := Real.exp_le_exp.mpr (by linarith)
  have hd := norm_sub_norm_le (1:ℂ) z
  simp only [norm_one] at hd
  have hb : x*Real.exp (-1)≤‖1-z‖ := by
    nlinarith [mul_le_mul_of_nonneg_left hex hx.le]
  rw [Real.exp_neg,← div_eq_mul_inv] at hb
  have hb' := (div_le_iff₀ (Real.exp_pos 1)).mp hb
  have hden : 0<‖1-z‖ := by nlinarith [norm_nonneg (1-z)]
  have hz1 : ‖z‖≤1 := hz.trans (Real.exp_le_one_iff.mpr (by linarith))
  rw [norm_div]
  apply (div_le_div_iff₀ hden hx).mpr
  have hn := norm_add_le (1:ℂ) z
  simp only [norm_one] at hn
  nlinarith [mul_le_mul_of_nonneg_right hn hx.le]

/-- Exact source product-kernel bound on the genuine selected support.
The constant is independent of N, epsilon, tau and every angle. -/
theorem preferred_selected_physical_product_bound (d : PreferredBranchData)
    {cap : ℝ} (hcap : 0<cap) :
    ∃ C : ℝ,0<C ∧ ∀ N : ℕ,0<N → ∀ ε τ : ℝ,
      0<ε → ε≤1 → 0<τ → τ≤1 → ∀ θ : Fin N → ℝ,
      preferredFullPopulationWeight preferredPopulationCutoff
        (cappedCanonicalPreferredBump d cap hcap).p
        (cappedCanonicalPreferredBump d cap hcap).m θ≠0 →
      ‖(1+preferredActualZ d (cappedCanonicalPreferredBump d cap hcap) ε τ θ)/
        (1-preferredActualZ d (cappedCanonicalPreferredBump d cap hcap) ε τ θ)‖≤C*(N:ℝ)/τ := by
  obtain ⟨c₀,hc₀,hgap⟩ := preferred_selected_attenuation_gap d hcap
  let c := min 1 c₀
  have hc : 0<c := lt_min zero_lt_one hc₀
  have hc1 : c≤1 := min_le_left _ _
  have hcc : c≤c₀ := min_le_right _ _
  refine ⟨2*Real.exp 1/c,by positivity,?_⟩
  intro N hN ε τ hε hε1 hτ hτ1 θ hw
  let B := cappedCanonicalPreferredBump d cap hcap
  let x := c*τ/(N:ℝ)
  have hNr : (0:ℝ)<N := by exact_mod_cast hN
  have hN1 : (1:ℝ)≤N := by exact_mod_cast hN
  have hx : 0<x := by dsimp only [x]; positivity
  have hx1 : x≤1 := by
    apply (div_le_one₀ hNr).mpr
    nlinarith [mul_le_mul hc1 hτ1 hτ.le (by norm_num : (0:ℝ)≤1)]
  have hphase : x≤ -(preferredTotalPhase d ε τ B.p B.m θ).im := by
    have hb := hgap N hN ε τ hε hε1 hτ.le hτ1 θ hw
    exact (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hcc hτ.le) hNr.le).trans hb
  have hz : ‖preferredActualZ d B ε τ θ‖≤Real.exp (-x) := by
    rw [preferredActualZ_eq_exp d B hε hτ.le θ,Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    simp only [Complex.mul_re,Complex.neg_re,Complex.neg_im,Complex.I_re,
      Complex.I_im,neg_zero,zero_mul,neg_neg,zero_sub,neg_one_mul]
    linarith
  calc
    _ ≤ 2*Real.exp 1/x := preferred_resolvent_of_attenuation hx hx1 hz
    _ = (2*Real.exp 1/c)*(N:ℝ)/τ := by
      dsimp only [x]
      field_simp

end
end IsingBulk.Preferred22
