import IsingBulk.Anisotropic.NegativeNormalForm.UniformCorrectedEnergy
import IsingBulk.Anisotropic.NegativeNormalForm.UniformNearIdentity

namespace IsingBulk.Anisotropic.NegativeNormalForm
noncomputable section
open Set Metric Filter
open scoped Topology

/-- Full actual pole normal form on a common ball, not merely a local inverse germ. -/
theorem exists_dimension_uniform_exact_normal_form (B : ℂ → ℂ) (phi : ℝ)
    (hphi : Real.sin phi≠0) (hB : AnalyticAt ℂ B 0) (hB0 : B 0≠0) :
    ∃ δ R r C : ℝ, 0<δ ∧ 0<R ∧ 0<r ∧ 0<C ∧ δ≤R/2 ∧ 4*R≤r ∧
      ∀ n : ℕ, n≠0 → ∀ d : ℂ, ‖d‖<δ →
      ∃ P : UniformProjectedWitness B phi hphi n d r C,
      ∃ J : UniformCorrectionWitness B phi hphi n d r C P R,
        AnalyticOnNhd ℂ (fun y => P.V (J.W y)) (ball 0 δ) ∧ P.V (J.W 0)=0 ∧
        HasFDerivAt (fun y => P.V (J.W y)) (ContinuousLinearMap.id ℂ (Config n)) 0 ∧
        (∀ e y, P.V (J.W (permute e y))=permute e (P.V (J.W y))) ∧
        (∀ y, ‖y‖≤δ → ‖P.V (J.W y)‖≤4*‖y‖ ∧ ‖P.V (J.W y)-y‖≤(3/32)*‖y‖ ∧
          (ZeroMean y → ZeroMean (P.V (J.W y)) ∧
            P.T (P.V (J.W y))=1-Complex.cos d+centralHessian B phi d/(2*n)*quadratic y)) := by
  obtain ⟨R,r,C,hR,hr,hC,hRr,hex⟩ := exists_uniform_correction_witness B phi hphi hB hB0
  have hqa := phaseParameterQuotient_joint_origin_analyticAt B phi hphi hB
  have hq0 : phaseParameterQuotient B phi hphi 0 0≠0 := by
    have hc := phaseParameterQuotient_center B phi hphi 0 (by simpa using hB)
    simp only [Complex.cos_zero,sub_self] at hc
    rw [hc]
    exact mul_ne_zero (inv_ne_zero (mul_ne_zero (by exact_mod_cast hphi) Complex.I_ne_zero)) hB0
  obtain ⟨a,ha,hqn⟩ := Metric.mem_nhds_iff.mp (hqa.continuousAt.eventually_ne hq0)
  have htau : Tendsto (fun d : ℂ => 1-Complex.cos d) (𝓝 0) (𝓝 0) := by
    have hh : ContinuousAt (fun d : ℂ => 1-Complex.cos d) 0 := by fun_prop
    simpa using hh.tendsto
  have hb : ∀ᶠ d : ℂ in 𝓝 0, ‖1-Complex.cos d‖<a/2 ∧ centralHessian B phi d≠0 := by
    filter_upwards [htau.eventually (Metric.ball_mem_nhds (0:ℂ) (by positivity : 0<a/2)),
      centralHessian_eventually_nonzero B phi hB] with d hd hh
    exact ⟨by simpa using hd,hh⟩
  obtain ⟨b,hb,hbs⟩ := Metric.mem_nhds_iff.mp hb
  let δ := min R (min a b)/16
  have hδ : 0<δ := div_pos (lt_min hR (lt_min ha hb)) (by norm_num)
  have hδR : 16*δ≤R := by dsimp [δ]; linarith [min_le_left R (min a b)]
  have hδa : 16*δ≤a := by
    have hh := (min_le_right R (min a b)).trans (min_le_left a b)
    dsimp [δ]; linarith
  have hδb : δ≤b := by
    have hh := (min_le_right R (min a b)).trans (min_le_right a b)
    dsimp [δ]; linarith
  refine ⟨δ,R,r,C,hδ,hR,hr,hC,by linarith,hRr,?_⟩
  intro n hn d hd
  obtain ⟨P,⟨J⟩⟩ := hex n hn d (by linarith)
  have hbd := hbs (show d∈ball (0:ℂ) b by simpa using hd.trans_le hδb)
  obtain ⟨hFa,hFs⟩ := J.corrected_bounds B phi hphi d r C R P hr hR (by linarith)
  have hD : HasFDerivAt P.V (ContinuousLinearMap.id ℂ (Config n)) (J.W 0) := by rw [J.w_zero]; exact P.v_deriv
  refine ⟨P,J,hFa.mono (ball_subset_ball (by linarith)),by rw [J.w_zero,P.v_zero],?_,?_,?_⟩
  · simpa using hD.comp 0 J.w_deriv
  · intro e y
    rw [J.w_perm,P.v_perm]
  · intro y hy
    have hys : ‖y‖≤R/2 := by linarith
    have hf := hFs y hys
    refine ⟨hf.1,hf.2,?_⟩
    intro hm
    have hvsource : ‖P.V (J.W y)‖<2*r := by linarith [hf.1]
    have hT := P.t_lip (P.V (J.W y)) 0 hvsource (by simpa using (show 0<2*r by positivity))
    rw [P.t_zero,sub_zero] at hT
    have ht : ‖P.T (P.V (J.W y))‖<a := by
      have ht' := norm_le_norm_sub_add (P.T (P.V (J.W y))) (1-Complex.cos d)
      linarith [hbd.1,hf.1]
    have hq := hqn (show (P.T (P.V (J.W y)),d)∈ball (0 : ℂ × ℂ) a by
      simpa only [mem_ball,dist_zero_right,Prod.norm_def] using max_lt ht (by linarith : ‖d‖<a))
    exact J.exact_energy hn B phi hphi d r C R P hr (by linarith) y hys hm hbd.2 hq

end
end IsingBulk.Anisotropic.NegativeNormalForm
