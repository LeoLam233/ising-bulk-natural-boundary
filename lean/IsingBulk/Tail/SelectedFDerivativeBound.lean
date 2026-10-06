import IsingBulk.Tail.SelectedFIntegralBound
import IsingBulk.Tail.SelectedFDiskHolomorphic

/-! Actual selected-F derivatives: complete-integral Cauchy followed by the
source-normalized matching/factorial estimate. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch Set Filter Metric
open scoped Topology
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

theorem selected_actual_derivative_factorial_bound (d : LocalBranchData)
    (hcsmall : d.c₀ < Real.sin d.theta/2) :
    ∃ η₀ τ₀ : ℝ, 0 < η₀ ∧ 0 < τ₀ ∧
      ∀ η α τ : ℝ, 0 < η → η < η₀ → 0 < α → α < Real.sin d.thetaB/4 →
        0 < τ → τ < τ₀ → ∃ c eps₀ C K a : ℝ,
        0 < c ∧ 0 < eps₀ ∧ 0 < C ∧ 0 < K ∧ 0 < a ∧
        ∀ (j n : ℕ) (eps L : ℝ), 0 < n → 0 < eps → eps < eps₀ →
          1+|Real.log eps| ≤ L →
          ‖iteratedDeriv j (selectedIntegral (2*n) (constructedSelector d.thetaB η α)
            (Real.exp (-d.c₀*eps)) τ) (radialParameter d.theta eps)‖ ≤
            ((j.factorial:ℝ)*c⁻¹^j*K)*Real.exp ((Real.log L)^2/(4*a))*
              selectedFactorialEnvelope C j n := by
  obtain ⟨ηI,τI,hηI,hτI,hint⟩ := selected_actual_integral_factorial_bound d hcsmall
  obtain ⟨ηH,τH,hηH,hτH,hhol⟩ := selected_actual_holomorphic_disk d hcsmall
  refine ⟨min ηI ηH,min τI τH,lt_min hηI hηH,lt_min hτI hτH,?_⟩
  intro η α τ hη hηlt hα hαsmall hτ hτlt
  obtain ⟨cI,eI,C,K,a,hcI,heI,hC,hK,ha,hI⟩ := hint η α τ hη
    (hηlt.trans_le (min_le_left _ _)) hα hαsmall hτ (hτlt.trans_le (min_le_left _ _))
  obtain ⟨cH,eH,hcH,heH,hH⟩ := hhol η α τ hη
    (hηlt.trans_le (min_le_right _ _)) hα hαsmall hτ (hτlt.trans_le (min_le_right _ _))
  let c := min cI cH
  refine ⟨c,min eI eH,C,K,a,lt_min hcI hcH,lt_min heI heH,hC,hK,ha,?_⟩
  intro j n eps L hn heps hepslt hL
  have hn0 : (0:ℝ)<((2*n:ℕ):ℝ) := by exact_mod_cast (show 0<2*n by omega)
  obtain ⟨hh,heq⟩ := hH (2*n) eps (by omega) heps (hepslt.trans_le (min_le_right _ _))
  have hsmallH : closedBall (radialParameter d.theta eps) (c/((2*n:ℕ):ℝ)) ⊆
      closedBall (radialParameter d.theta eps) (cH/((2*n:ℕ):ℝ)) :=
    closedBall_subset_closedBall (div_le_div_of_nonneg_right (min_le_right _ _) hn0.le)
  have hb : ∀ s ∈ closedBall (radialParameter d.theta eps) (c/((2*n:ℕ):ℝ)),
      ‖continuedSelectedIntegral (2*n) (constructedSelector d.thetaB η α) (Real.exp (-d.c₀*eps)) τ s‖ ≤
        K*Real.exp ((Real.log L)^2/(4*a))*selectedFactorialEnvelope C 0 n := by
    intro s hs
    apply hI n eps L s hn heps (hepslt.trans_le (min_le_left _ _)) hL
    have hs' : ‖s-radialParameter d.theta eps‖ ≤ c/((2*n:ℕ):ℝ) := by
      simpa only [mem_closedBall,dist_eq_norm] using hs
    exact hs'.trans (div_le_div_of_nonneg_right (min_le_left _ _) hn0.le)
  have hout := selectedIntegral_iteratedDeriv_cauchy (by omega : 0<2*n)
    (constructedSelector d.thetaB η α) (Real.exp (-d.c₀*eps)) τ
    (lt_min hcI hcH) (hh.mono hsmallH) heq hb j
  convert hout using 1
  unfold selectedFactorialEnvelope
  simp only [pow_zero,mul_one,div_pow,inv_pow]
  ring

end
end IsingBulk.Tail
