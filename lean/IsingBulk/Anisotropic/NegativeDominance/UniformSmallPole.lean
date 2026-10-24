import IsingBulk.Anisotropic.NegativeNormalForm.UniformProjectedWitness

namespace IsingBulk.Anisotropic.NegativeDominance
noncomputable section
open IsingBulk.Anisotropic.NegativeNormalForm Set Metric Filter
open scoped Topology

/-- Construct the actual analytic pole in an arbitrarily small prescribed
parameter neighborhood, with a radius chosen before every dimension. -/
theorem exists_uniform_small_pole (B : ℂ→ℂ) (phi : ℝ)
    (hphi : Real.sin phi≠0) (hB : AnalyticAt ℂ B 0) (hB0 : B 0≠0)
    (δ : ℝ) (hδ : 0<δ) :
    ∃ r : ℝ,0<r ∧ r≤δ ∧ ∀n : ℕ,n≠0 → ∀d : ℂ,‖d‖<r →
      ∃T : Config n→ℂ, AnalyticOnNhd ℂ T (ball 0 r) ∧ T 0=1-Complex.cos d ∧
        ∀v : Config n,‖v‖<r → poleEquation B phi hphi d (T v) v=0 ∧ ‖T v‖<δ := by
  obtain ⟨r0,C,hr0,_hC,hP⟩ := exists_uniform_projected_witness B phi hphi hB hB0
  have he : ∀ᶠ d : ℂ in 𝓝 0,‖1-Complex.cos d‖<δ/2 := by
    have hh : ContinuousAt (fun d : ℂ => ‖1-Complex.cos d‖) 0 :=
      (continuousAt_const.sub Complex.continuous_cos.continuousAt).norm
    exact hh.eventually_lt_const (by simpa using half_pos hδ)
  obtain ⟨rd,hrd,hd⟩ := Metric.mem_nhds_iff.mp he
  let r := min r0 (min rd (δ/2))
  have hr : 0<r := lt_min hr0 (lt_min hrd (half_pos hδ))
  have hr0' : r≤r0 := min_le_left _ _
  have hrd' : r≤rd := (min_le_right _ _).trans (min_le_left _ _)
  have hrδ : r≤δ/2 := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨r,hr,by linarith,?_⟩
  intro n hn d hdn
  obtain ⟨P⟩ := hP n hn d (hdn.trans_le hr0')
  refine ⟨P.T,P.t_analytic.mono (ball_subset_ball (by linarith)),P.t_zero,?_⟩
  intro v hv
  have hv0 : ‖v‖<2*r0 := by linarith
  refine ⟨(P.t_pole v hv0).1,?_⟩
  have hτ : ‖1-Complex.cos d‖<δ/2 := hd (by simpa using hdn.trans_le hrd')
  have hl := P.t_lip v 0 hv0 (by simpa using mul_pos (by norm_num : (0 : ℝ)<2) hr0)
  rw [sub_zero,P.t_zero] at hl
  have ht := norm_le_norm_sub_add (P.T v) (1-Complex.cos d)
  linarith

end
end IsingBulk.Anisotropic.NegativeDominance
