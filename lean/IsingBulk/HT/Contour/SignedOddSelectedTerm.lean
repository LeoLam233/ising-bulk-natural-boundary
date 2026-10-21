import IsingBulk.HT.Contour.OddSelectedTerm
import IsingBulk.HT.Contour.SignedSelectedNormalized
import IsingBulk.HT.Contour.SignedSelectedDisk

/-! Complete actual odd selected integral and Cauchy derivative bounds for
both HT signs. The augmented matching estimate retains coupled occupancy. -/
namespace IsingBulk.HT.Contour
noncomputable section
open IsingBulk.First IsingBulk.Tail IsingBulk.Branch Set MeasureTheory Metric
open scoped BigOperators Topology
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

theorem signed_odd_selected_actual_integral_factorial_bound (σ : ℂ) (hσ : ‖σ‖=1) (d : LocalBranchData)
    (hcsmall : d.c₀ < Real.sin d.theta/2) :
    ∃ η₀ τ₀ : ℝ, 0 < η₀ ∧ 0 < τ₀ ∧
      ∀ η α τ : ℝ, 0 < η → η < η₀ → 0 < α → α < Real.sin d.thetaB/4 →
        0 < τ → τ < τ₀ → ∃ c eps₀ C K a : ℝ,
        0 < c ∧ 0 < eps₀ ∧ 0 < C ∧ 0 < K ∧ 0 < a ∧
        ∀ (n : ℕ) (eps L : ℝ) (s : ℂ), 0 < eps → eps < eps₀ →
          1+|Real.log eps| ≤ L →
          ‖s-radialParameter d.theta eps‖ ≤ c/((2*n+1:ℕ):ℝ) →
          ‖signedContinuedSelectedIntegral σ (2*n+1) (constructedSelector d.thetaB η α)
            (Real.exp (-d.c₀*eps)) τ s‖ ≤
            K*L*Real.exp ((Real.log L)^2/(4*a))*oddSelectedEnvelope C 0 n := by
  obtain ⟨ηA,τ₀,hηA,hτ₀,hmain⟩ := signed_selected_actual_normalized_discount σ hσ d hcsmall
  refine ⟨min ηA (Real.sin d.thetaB/4),τ₀,lt_min hηA (by positivity [d.a_pos]),hτ₀,?_⟩
  intro η α τ hη hηlt hα hαsmall hτ hτlt
  have hηsmall := hηlt.le.trans (min_le_right _ _)
  obtain ⟨c,e,C,D,K,a,hc,he,hC,hD,hK,ha,hbound⟩ := hmain η α τ hη
    (hηlt.trans_le (min_le_left _ _)) hα hαsmall hτ hτlt
  let V := (selectedYPairConstant d.thetaB τ+1)*
    (4*C*Real.sqrt (2*Real.pi)+C*(2*Real.pi))^2+
      C^2*(2*Real.pi)*selectedExceptionalConstant d.c₀ τ
  have hV : 0 < V := by
    have hK0 : 0 ≤ selectedYPairConstant d.thetaB τ := by
      unfold selectedYPairConstant
      exact div_nonneg (by positivity) (selectedYPairGap_pos d.a_pos hτ).le
    have hE := selectedExceptionalConstant_pos d.c₀ τ
    dsimp [V]
    positivity
  let C' := D*Real.sqrt V
  let K' := K*Real.sqrt V*(2*Real.pi+1)/((2*Real.pi)*C)
  refine ⟨c,min e (min 1 (1/(2*d.c₀))),C',K',a,hc,
    lt_min he (lt_min zero_lt_one (by positivity [d.c₀_pos])),
    by dsimp [C']; positivity, by dsimp [K']; positivity,ha,?_⟩
  intro n eps L s heps hepslt hL hsd
  have hL1 : 1 ≤ L := by linarith [abs_nonneg (Real.log eps)]
  have hL0 : 0 < L := by linarith
  have hepsE := hepslt.trans_le (min_le_left _ _)
  have heps1 : eps ≤ 1 := hepslt.le.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hsmall : 2*d.c₀*eps ≤ 1 := by
    have hh := (lt_div_iff₀ (by positivity [d.c₀_pos] : 0 < 2*d.c₀)).mp
      (hepslt.trans_le ((min_le_right _ _).trans (min_le_right _ _)))
    linarith
  let w := fun θ : Fin (2*n+1) → ℝ =>
    (∏ i, discountedSelectedWeight d.thetaB η C eps L (θ i))*
      ‖First.pairProduct (deformedPoint (constructedSelector d.thetaB η α)
        (Real.exp (-d.c₀*eps)) τ 1 θ)‖
  obtain ⟨hi,hb⟩ := odd_selected_y_weighted_integrable_and_bound n d.thetaB_pos.le
    (by linarith [d.thetaB_lt,Real.pi_pos]) d.a_pos hη hηsmall hα hαsmall
    hC heps heps1 hL1 hτ (Real.exp_pos _).le
    (Real.exp_lt_one_iff.mpr (by nlinarith [d.c₀_pos]))
    (selectedExceptionalConstant_pos d.c₀ τ).le
    (selectedExceptionalKernel_log_bound d.c₀_pos heps hsmall hL τ)
  rw [← angleBox_restrict_pi] at hi hb
  change IntegrableOn w (angleBox (2*n+1)) at hi
  change (∫ θ in angleBox (2*n+1),w θ) ≤
    (matchingCount (n+1):ℝ)*V^(n+1)*(L*(2*Real.pi+1)/((2*Real.pi)*C)) at hb
  let P := (((2*n+1).factorial:ℝ)⁻¹*K*D^(2*n+1)*Real.exp ((Real.log L)^2/(4*a)))
  have hP : 0 ≤ P := by dsimp [P]; positivity
  have hn : ‖signedContinuedSelectedIntegral σ (2*n+1) (constructedSelector d.thetaB η α)
      (Real.exp (-d.c₀*eps)) τ s‖ ≤
      P*((matchingCount (n+1):ℝ)*V^(n+1)*(L*(2*Real.pi+1)/((2*Real.pi)*C))) := by
    apply (norm_integral_le_of_norm_le (hi.const_mul P) ?_).trans
      ((integral_const_mul P w).trans_le (mul_le_mul_of_nonneg_left hb hP))
    filter_upwards [ae_restrict_mem measurableSet_Icc] with θ hθ
    exact hbound (2*n+1) eps L θ s (by omega) heps hepsE hL0 hθ hsd
  have hf : (matchingCount (n+1):ℝ)*((2:ℝ)^n*(n.factorial:ℝ)) =
      ((2*n+1).factorial:ℝ) := by exact_mod_cast odd_matchingCount_factorial n
  have hsqrt : Real.sqrt V ^ (2*n+1) * Real.sqrt V = V^(n+1) := by
    rw [← pow_succ, show 2*n+1+1 = 2*(n+1) by omega, pow_mul, Real.sq_sqrt hV.le]
  have hratio : (((2*n+1).factorial:ℝ)⁻¹)*(matchingCount (n+1):ℝ) =
      ((2:ℝ)^n*(n.factorial:ℝ))⁻¹ := by
    have hden : ((2:ℝ)^n*(n.factorial:ℝ)) ≠ 0 := by positivity
    have hfac : ((2*n+1).factorial:ℝ) ≠ 0 := by positivity
    apply (mul_eq_one_iff_eq_inv₀ hden).mp
    calc
      _ = (((2*n+1).factorial:ℝ)⁻¹)*
          ((matchingCount (n+1):ℝ)*((2:ℝ)^n*(n.factorial:ℝ))) := by ring
      _ = 1 := by rw [hf, inv_mul_cancel₀ hfac]
  apply hn.trans_eq
  calc
    _ = ((((2*n+1).factorial:ℝ)⁻¹)*(matchingCount (n+1):ℝ))*
        (K*D^(2*n+1)*Real.exp ((Real.log L)^2/(4*a))*V^(n+1)*
          (L*(2*Real.pi+1)/((2*Real.pi)*C))) := by dsimp [P]; ring
    _ = ((2:ℝ)^n*(n.factorial:ℝ))⁻¹*
        (K*D^(2*n+1)*Real.exp ((Real.log L)^2/(4*a))*V^(n+1)*
          (L*(2*Real.pi+1)/((2*Real.pi)*C))) := by rw [hratio]
    _ = _ := by
      dsimp [K',C',oddSelectedEnvelope]
      rw [← hsqrt]
      simp only [pow_zero,mul_one,mul_pow]
      ring

/-- Cauchy is applied to the complete selected integral, on the established
all-N disk, with the contour radius fixed during differentiation. -/
theorem signed_odd_selected_actual_derivative_factorial_bound (σ : ℂ) (hσ : ‖σ‖=1) (d : LocalBranchData)
    (hcsmall : d.c₀ < Real.sin d.theta/2) :
    ∃ η₀ τ₀ : ℝ, 0 < η₀ ∧ 0 < τ₀ ∧
      ∀ η α τ : ℝ, 0 < η → η < η₀ → 0 < α → α < Real.sin d.thetaB/4 →
        0 < τ → τ < τ₀ → ∃ c eps₀ C K a : ℝ,
        0 < c ∧ 0 < eps₀ ∧ 0 < C ∧ 0 < K ∧ 0 < a ∧
        ∀ (j n : ℕ) (eps L : ℝ), 0 < eps → eps < eps₀ →
          1+|Real.log eps| ≤ L →
          ‖iteratedDeriv j (signedSelectedIntegral σ (2*n+1) (constructedSelector d.thetaB η α)
            (Real.exp (-d.c₀*eps)) τ) (radialParameter d.theta eps)‖ ≤
            ((j.factorial:ℝ)*c⁻¹^j*K)*L*Real.exp ((Real.log L)^2/(4*a))*
              oddSelectedEnvelope C j n := by
  obtain ⟨ηI,τI,hηI,hτI,hint⟩ := signed_odd_selected_actual_integral_factorial_bound σ hσ d hcsmall
  obtain ⟨ηH,τH,hηH,hτH,hhol⟩ := signed_selected_actual_holomorphic_disk σ hσ d hcsmall
  refine ⟨min ηI ηH,min τI τH,lt_min hηI hηH,lt_min hτI hτH,?_⟩
  intro η α τ hη hηlt hα hαsmall hτ hτlt
  obtain ⟨cI,eI,C,K,a,hcI,heI,hC,hK,ha,hI⟩ := hint η α τ hη
    (hηlt.trans_le (min_le_left _ _)) hα hαsmall hτ (hτlt.trans_le (min_le_left _ _))
  obtain ⟨cH,eH,hcH,heH,hH⟩ := hhol η α τ hη
    (hηlt.trans_le (min_le_right _ _)) hα hαsmall hτ (hτlt.trans_le (min_le_right _ _))
  let c := min cI cH
  refine ⟨c,min eI eH,C,K,a,lt_min hcI hcH,lt_min heI heH,hC,hK,ha,?_⟩
  intro j n eps L heps hepslt hL
  have hn0 : (0:ℝ)<((2*n+1:ℕ):ℝ) := by positivity
  obtain ⟨hh,heq⟩ := hH (2*n+1) eps (by omega) heps (hepslt.trans_le (min_le_right _ _))
  have hsmallH : closedBall (radialParameter d.theta eps) (c/((2*n+1:ℕ):ℝ)) ⊆
      closedBall (radialParameter d.theta eps) (cH/((2*n+1:ℕ):ℝ)) :=
    closedBall_subset_closedBall (div_le_div_of_nonneg_right (min_le_right _ _) hn0.le)
  have hb : ∀ s ∈ closedBall (radialParameter d.theta eps) (c/((2*n+1:ℕ):ℝ)),
      ‖signedContinuedSelectedIntegral σ (2*n+1) (constructedSelector d.thetaB η α)
        (Real.exp (-d.c₀*eps)) τ s‖ ≤
        K*L*Real.exp ((Real.log L)^2/(4*a))*oddSelectedEnvelope C 0 n := by
    intro s hs
    apply hI n eps L s heps (hepslt.trans_le (min_le_left _ _)) hL
    have hs' : ‖s-radialParameter d.theta eps‖ ≤ c/((2*n+1:ℕ):ℝ) := by
      simpa only [mem_closedBall,dist_eq_norm] using hs
    exact hs'.trans (div_le_div_of_nonneg_right (min_le_left _ _) hn0.le)
  have hout := signed_selectedIntegral_iteratedDeriv_cauchy σ (by omega : 0<2*n+1)
    (constructedSelector d.thetaB η α) (Real.exp (-d.c₀*eps)) τ
    (lt_min hcI hcH) (hh.mono hsmallH) heq hb j
  convert hout using 1
  unfold oddSelectedEnvelope
  simp only [pow_zero,mul_one,div_pow,inv_pow]
  ring


end
end IsingBulk.HT.Contour
