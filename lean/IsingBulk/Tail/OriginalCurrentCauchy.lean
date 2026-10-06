import IsingBulk.Tail.OriginalCurrentEnvelope
import IsingBulk.Tail.OriginalCurrentCauchyTransfer

/-! Actual small-current contribution on a fixed real subinterval. All
parameter derivatives precede the epsilon-dependent choice of its endpoint. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch Set Metric MeasureTheory
open scoped Topology
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

theorem original_current_small_integral_gaussian_bound (d : LocalBranchData)
    (hcsmall : d.c₀ < Real.sin d.theta/2) :
    ∃ η₀ : ℝ, 0 < η₀ ∧ ∀ η : ℝ, 0 < η → η < η₀ →
      ∃ α₀ τ₀ : ℝ, 0 < α₀ ∧ 0 < τ₀ ∧ ∀ α τ : ℝ,
        0 < α → α < α₀ → 0 < τ → τ < τ₀ →
        ∃ c e K D κ : ℝ, 0 < c ∧ 0 < e ∧ 0 < K ∧ 0 < D ∧ 0 < κ ∧
        ∀ (j N : ℕ) (eps lamStar : ℝ), 1 ≤ N → 0 < eps → eps < e →
          0 ≤ lamStar → lamStar ≤ 1 →
          IntervalIntegrable (fun lam => differentiatedCurrentSlice N (constructedSelector d.thetaB η α)
            (Real.exp (-d.c₀*eps)) τ lam j (radialParameter d.theta eps)) volume 0 lamStar ∧
          ‖∫ lam in 0..lamStar, differentiatedCurrentSlice N (constructedSelector d.thetaB η α)
            (Real.exp (-d.c₀*eps)) τ lam j (radialParameter d.theta eps)‖ ≤
            ((j.factorial:ℝ)*c⁻¹^j*K)*D^N*eps⁻¹^(j+2)*Real.exp (-κ*(N:ℝ)^2) := by
  obtain ⟨ηA,hηA,hmain⟩ := original_current_complete_envelope d hcsmall
  refine ⟨min ηA (Real.sin d.thetaB/4),lt_min hηA (by positivity [d.a_pos]),?_⟩
  intro η hη hηlt
  have hηsmall := hηlt.le.trans (min_le_right _ _)
  obtain ⟨α₀,τ₀,hα₀,hτ₀,hsetup⟩ := hmain η hη (hηlt.trans_le (min_le_left _ _))
  refine ⟨α₀,τ₀,hα₀,hτ₀,?_⟩
  intro α τ hα hαlt hτ hτlt
  obtain ⟨c,e,K,D,κ,hc,he,hK,hD,hκ,hbound⟩ := hsetup α τ hα hαlt hτ hτlt
  refine ⟨c,e,K,D,κ,hc,he,hK,hD,hκ,?_⟩
  intro j N eps lamStar hN heps hepslt hls0 hls1
  let r := Real.exp (-d.c₀*eps)
  let f := constructedSelector d.thetaB η α
  have hr : 0 < r := Real.exp_pos _
  have hr1 : r < 1 := Real.exp_lt_one_iff.mpr (by nlinarith [d.c₀_pos])
  have hf := constructedSelector_regular d.thetaB η α d.a_pos hη hηsmall hα
  have hsub : closedBall (radialParameter d.theta eps) (c*eps) ⊆ dampingDomain r := by
    intro s hs
    have hs' : ‖s-radialParameter d.theta eps‖ ≤ c*eps := by simpa only [mem_closedBall,dist_eq_norm] using hs
    exact dampingDomain_of_margin hr hr1 (hbound N eps 0 s hN heps hepslt (by norm_num) (by norm_num) hs').1
  have hb : ∀ lam ∈ Icc (0:ℝ) 1, ∀ s ∈ closedBall (radialParameter d.theta eps) (c*eps),
      ‖continuedCurrentSlice N f r τ lam s‖ ≤ (K/eps^2)*D^N*Real.exp (-κ*(N:ℝ)^2) := by
    intro lam hlam s hs
    exact (hbound N eps lam s hN heps hepslt hlam.1 hlam.2
      (by simpa only [mem_closedBall,dist_eq_norm] using hs)).2
  obtain ⟨hi,hh⟩ := actual_small_current_original_disk_integral N (by omega) f hf hr hr1 hτ.le
    (mul_pos hc heps) (by positivity) hls0 hls1 hsub hb j
  refine ⟨hi,?_⟩
  convert hh using 1
  rw [mul_pow,pow_add]
  simp only [div_eq_mul_inv,mul_inv_rev,inv_pow]
  ring

end
end IsingBulk.Tail
