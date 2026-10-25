import IsingBulk.Joint.Negative.FamilyDensityLog
import IsingBulk.Joint.Negative.FamilyHessianBounds
import IsingBulk.Anisotropic.NegativeDominance.CompleteCoefficientRadius

namespace IsingBulk.Joint.Negative
noncomputable section
open Set Filter Metric IsingBulk.Anisotropic.NegativeNormalForm
open IsingBulk.Anisotropic.NegativeDominance
open scoped Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
set_option maxHeartbeats 1500000

theorem compact_family_hessian_sequence (B : ℂ × E → ℂ) (phi : ℝ)
    {K : Set E} (hK : IsCompact K) (hB : ∀ eta ∈ K, AnalyticAt ℂ B (0,eta)) :
    ∃ C : ℝ, 0<C ∧ ∀ᶠ n : ℕ in atTop, ∀ eta ∈ K,
      ‖hessianFactor (B (tau n,eta)) (Real.cos phi) (Real.sin phi) n-1‖≤C/(n:ℝ)^2 ∧
      ‖hessianFactor (B (tau n,eta)) (Real.cos phi) (Real.sin phi) n-1‖<1/2 := by
  obtain ⟨r,L,hr,hL,hbound⟩ := compact_family_hessian_quadratic B phi hK hB
  refine ⟨L*Real.pi^2,by positivity,?_⟩
  have hnear := winding_angle_complex_tendsto_zero.eventually (ball_mem_nhds (0:ℂ) hr)
  filter_upwards [hnear] with n hn
  intro eta heta
  have hh := hbound eta heta ((Real.pi/(n:ℝ):ℝ):ℂ) (by simpa using hn)
  rw [centralHessian_at_winding] at hh
  exact ⟨by simpa only [familyMember,Complex.norm_real,Real.norm_eq_abs,sq_abs,div_pow,mul_div_assoc] using hh.1,hh.2⟩

theorem compact_family_B_log_norm_bound (B : ℂ × E → ℂ)
    {K : Set E} (hK : IsCompact K) (hB : ∀ eta ∈ K, AnalyticAt ℂ B (0,eta))
    (hB0 : ∀ eta ∈ K, B (0,eta)≠0) :
    ∃ C : ℝ, 0<C ∧ ∀ᶠ n : ℕ in atTop, ∀ eta ∈ K,
      |Real.log ‖B (tau n,eta)‖-Real.log ‖B (0,eta)‖|≤C/(n:ℝ)^2 := by
  obtain ⟨r,L,hr,hL,hlog⟩ := compact_family_parameter_log_control B hK hB hB0
  obtain ⟨s,hs,hnonzero⟩ := compact_family_parameter_nonzero B hK hB hB0
  have hnear := tau_complex_tendsto_zero.eventually (ball_mem_nhds (0:ℂ) (lt_min hr hs))
  refine ⟨L*Real.pi^2/2,by positivity,?_⟩
  filter_upwards [hnear,eventually_ge_atTop (1:ℕ)] with n hn hnp
  intro eta heta
  have htn : ‖(tau n:ℂ)‖<min r s := by simpa using hn
  have hnB := (hnonzero eta heta (tau n) (htn.trans_le (min_le_right _ _))).2
  have hb := (hlog eta heta (tau n) 0 (htn.trans_le (min_le_left _ _)) (by simpa using hr)).2.2
  have hreal : Real.log ‖B (tau n,eta)‖-Real.log ‖B (0,eta)‖=
      (Complex.log (B (tau n,eta)/B (0,eta))).re := by
    rw [Complex.log_re,norm_div,Real.log_div (norm_ne_zero_iff.mpr hnB) (norm_ne_zero_iff.mpr (hB0 eta heta))]
  rw [hreal]
  apply (Complex.abs_re_le_norm _).trans (hb.trans _)
  have htp := tau_pos n (by omega)
  rw [sub_zero,Complex.norm_real,Real.norm_eq_abs,abs_of_pos htp]
  exact (mul_le_mul_of_nonneg_left (tau_bounds n (by omega)).2 hL.le).trans_eq (by ring)

theorem compact_family_modelAnalyticError_bound (B : ℂ × E → ℂ) (phi : ℝ)
    {K : Set E} (hK : IsCompact K) (hB : ∀ eta ∈ K, AnalyticAt ℂ B (0,eta))
    (hB0 : ∀ eta ∈ K, B (0,eta)≠0) :
    ∃ C : ℝ, 0<C ∧ ∀ᶠ n : ℕ in atTop, ∀ eta ∈ K, Odd n →
      |modelAnalyticError (B (0,eta)) (B (tau n,eta))
        (hessianFactor (B (tau n,eta)) (Real.cos phi) (Real.sin phi) n) n|≤C := by
  obtain ⟨CB,hCB,hb⟩ := compact_family_B_log_norm_bound B hK hB hB0
  obtain ⟨CH,hCH,hh⟩ := compact_family_hessian_sequence B phi hK hB
  refine ⟨CB+2*CH+Real.pi^2/10,by positivity,?_⟩
  filter_upwards [hb,hh,eventually_ge_atTop (2:ℕ)] with n hBn hHn hn
  intro eta heta ho
  have hH := hHn eta heta
  have hhalf : (1:ℝ)/2≤‖hessianFactor (B (tau n,eta)) (Real.cos phi) (Real.sin phi) n‖ := by
    have h := norm_sub_norm_le (1:ℂ) (hessianFactor (B (tau n,eta)) (Real.cos phi) (Real.sin phi) n)
    rw [norm_one,norm_sub_rev] at h
    linarith
  have hlog : |Real.log ‖hessianFactor (B (tau n,eta)) (Real.cos phi) (Real.sin phi) n‖|≤
      (2*CH)/(n:ℝ)^2 := by
    have h := abs_log_le_two_mul_abs_sub_one hhalf
    have ha := abs_norm_sub_norm_le (hessianFactor (B (tau n,eta)) (Real.cos phi) (Real.sin phi) n) (1:ℂ)
    rw [norm_one] at ha
    exact h.trans ((mul_le_mul_of_nonneg_left (ha.trans hH.1) (by norm_num)).trans_eq (by ring))
  apply modelAnalyticError_bound _ _ _ n (by omega) ho CB (2*CH) (Real.pi^2/10) (hBn eta heta) hlog
  have ht := log_tau_error_bounds n hn
  rw [abs_of_nonneg ht.1]
  convert ht.2 using 1
  ring

theorem compact_family_model_constants_bound (B : ℂ × E → ℂ) (phi : ℝ)
    {K : Set E} (hK : IsCompact K) (hB : ∀ eta ∈ K, AnalyticAt ℂ B (0,eta))
    (hB0 : ∀ eta ∈ K, B (0,eta)≠0) :
    ∃ M : ℝ, 0<M ∧ ∀ eta ∈ K,
      |modelQuadraticConstant (B (0,eta)) (Real.sin phi)|≤M ∧
      |modelAdditiveConstant (B (0,eta))|≤M := by
  have hc : ContinuousOn (fun eta =>
      (modelQuadraticConstant (B (0,eta)) (Real.sin phi),modelAdditiveConstant (B (0,eta)))) K := by
    intro eta heta
    have hl : ContinuousAt (fun eta => Real.log ‖B (0,eta)‖) eta :=
      (((hB eta heta).continuousAt.comp
        (continuous_const.prodMk continuous_id).continuousAt).norm).log
          (norm_ne_zero_iff.mpr (hB0 eta heta))
    exact (((continuousAt_const.add hl).sub continuousAt_const).add continuousAt_const).prodMk
      ((continuousAt_const.sub (hl.div_const 2)).sub continuousAt_const) |>.continuousWithinAt
  obtain ⟨M,hM⟩ := hK.exists_bound_of_continuousOn hc
  refine ⟨max M 0+1,by positivity,?_⟩
  intro eta heta
  have hh := (hM eta heta).trans (show M≤max M 0+1 by linarith [le_max_left M 0])
  simpa only [Prod.norm_def,Real.norm_eq_abs,max_le_iff] using hh

end
end IsingBulk.Joint.Negative
