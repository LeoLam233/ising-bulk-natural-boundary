import IsingBulk.Tail.OriginalLowerIntegralBound
import IsingBulk.Tail.SelectorDerivativeDistribution

/-! Cauchy for the complete actual K integral, with radius fixed before
all s derivatives. No estimated angular assignment is differentiated. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch Set Metric
open scoped Topology
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

theorem original_lower_derivative_gaussian_bound (d : LocalBranchData)
    (hcsmall : d.c₀ < Real.sin d.theta/2) :
    ∃ η₀ : ℝ, 0 < η₀ ∧ ∀ η : ℝ, 0 < η → η < η₀ →
      ∃ α₀ c e C K κ : ℝ, 0 < α₀ ∧ 0 < c ∧ 0 < e ∧ 0 < C ∧ 0 < K ∧ 0 < κ ∧
      ∀ α : ℝ, 0 < α → α < α₀ → ∀ (j N : ℕ) (eps τ : ℝ),
        2 ≤ N → 0 < eps → eps < e → 0 ≤ τ →
        ‖iteratedDeriv j (originalLowerIntegral N (constructedSelector d.thetaB η α)
          (Real.exp (-d.c₀*eps)) τ) (radialParameter d.theta eps)‖ ≤
          ((j.factorial:ℝ)*c⁻¹^j*K)*C^N*eps⁻¹^(j+2)*Real.exp (-κ*(N:ℝ)^2) := by
  obtain ⟨ηI,hηI,hint⟩ := original_lower_integral_gaussian_bound d hcsmall
  have hsint : 0 < Real.sin d.theta := Real.sin_pos_of_pos_of_lt_pi d.theta_pos
    (by linarith [d.theta_lt,Real.pi_pos])
  obtain ⟨cG,eG,hcG,_hcG1,heG,_heG1,hmargin⟩ := original_disk_trace_margin d.theta d.c₀ hsint d.c₀_pos hcsmall
  refine ⟨min ηI (Real.sin d.thetaB/4),lt_min hηI (by positivity [d.a_pos]),?_⟩
  intro η hη hηlt
  have hηsmall := hηlt.le.trans (min_le_right _ _)
  obtain ⟨α₀,cI,eI,C,K,κ,hα₀,hcI,heI,hC,hK,hκ,hI⟩ := hint η hη (hηlt.trans_le (min_le_left _ _))
  let c := min cI cG
  refine ⟨α₀,c,min eI eG,C,K,κ,hα₀,lt_min hcI hcG,lt_min heI heG,hC,hK,hκ,?_⟩
  intro α hα hαlt j N eps τ hN heps hepslt hτ
  let r := Real.exp (-d.c₀*eps)
  let f := constructedSelector d.thetaB η α
  have hr : 0 < r := Real.exp_pos _
  have hr1 : r < 1 := Real.exp_lt_one_iff.mpr (by nlinarith [d.c₀_pos])
  have hf := constructedSelector_regular d.thetaB η α d.a_pos hη hηsmall hα
  have hhol := (selected_and_lower_analytic N (by omega) f hf hr hr1 hτ).2
  have hsub : closedBall (radialParameter d.theta eps) (c*eps) ⊆ dampingDomain r := by
    intro s hs
    have hs' : ‖s-radialParameter d.theta eps‖ ≤ c*eps := by simpa only [mem_closedBall,dist_eq_norm] using hs
    have hm := hmargin eps heps (hepslt.trans_le (min_le_right _ _)) s
      (hs'.trans (mul_le_mul_of_nonneg_right (min_le_right cI cG) heps.le))
    apply dampingDomain_of_margin hr hr1
    simpa only [r,neg_mul,Real.exp_neg,inv_inv] using hm
  have hb : ∀ s ∈ closedBall (radialParameter d.theta eps) (c*eps),
      ‖originalLowerIntegral N f r τ s‖ ≤ K*C^N*eps⁻¹^2*Real.exp (-κ*(N:ℝ)^2) := by
    intro s hs
    apply hI α hα hαlt N eps τ s hN heps (hepslt.trans_le (min_le_left _ _))
    have hs' : ‖s-radialParameter d.theta eps‖ ≤ c*eps := by simpa only [mem_closedBall,dist_eq_norm] using hs
    exact hs'.trans (mul_le_mul_of_nonneg_right (min_le_left cI cG) heps.le)
  have hh := cauchy_bound_on_subdisk (hhol.mono hsub) hb
    (mul_pos (lt_min hcI hcG) heps) (Subset.rfl) j
  convert hh using 1
  rw [mul_pow,pow_add]
  simp only [div_eq_mul_inv,mul_inv_rev,inv_pow]
  ring

end
end IsingBulk.Tail
