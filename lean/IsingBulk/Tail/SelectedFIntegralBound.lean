import IsingBulk.Tail.SelectedFNormalizedDensity
import IsingBulk.Tail.SelectedFWeightedIntegral
import IsingBulk.Tail.SelectedContourSeries

/-! Complete selected-F integral estimate from actual coupled matchings.
The factorial normalization cancels exactly one matching count. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch Set MeasureTheory
open scoped BigOperators Topology
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

theorem selected_actual_integral_factorial_bound (d : LocalBranchData)
    (hcsmall : d.c₀ < Real.sin d.theta/2) :
    ∃ η₀ τ₀ : ℝ, 0 < η₀ ∧ 0 < τ₀ ∧
      ∀ η α τ : ℝ, 0 < η → η < η₀ → 0 < α → α < Real.sin d.thetaB/4 →
        0 < τ → τ < τ₀ → ∃ c eps₀ C K a : ℝ,
        0 < c ∧ 0 < eps₀ ∧ 0 < C ∧ 0 < K ∧ 0 < a ∧
        ∀ (n : ℕ) (eps L : ℝ) (s : ℂ), 0 < n → 0 < eps → eps < eps₀ →
          1+|Real.log eps| ≤ L →
          ‖s-radialParameter d.theta eps‖ ≤ c/((2*n:ℕ):ℝ) →
          ‖continuedSelectedIntegral (2*n) (constructedSelector d.thetaB η α)
            (Real.exp (-d.c₀*eps)) τ s‖ ≤
            K*Real.exp ((Real.log L)^2/(4*a))*selectedFactorialEnvelope C 0 n := by
  obtain ⟨ηA,τ₀,hηA,hτ₀,hmain⟩ := selected_actual_normalized_discount d hcsmall
  refine ⟨min ηA (Real.sin d.thetaB/4),τ₀,lt_min hηA (by positivity [d.a_pos]),hτ₀,?_⟩
  intro η α τ hη hηlt hα hαsmall hτ hτlt
  have hηsmall := hηlt.le.trans (min_le_right _ _)
  obtain ⟨c,e,C,D,K,a,hc,he,hC,hD,hK,ha,hbound⟩ := hmain η α τ hη
    (hηlt.trans_le (min_le_left _ _)) hα hαsmall hτ hτlt
  let V := selectedYPairConstant d.thetaB τ*(4*C*Real.sqrt (2*Real.pi)+C*(2*Real.pi))^2+
    C^2*(2*Real.pi)*selectedExceptionalConstant d.c₀ τ
  have hV : 0 < V := by
    have hK0 : 0 ≤ selectedYPairConstant d.thetaB τ := by
      unfold selectedYPairConstant
      exact div_nonneg (by positivity) (selectedYPairGap_pos d.a_pos hτ).le
    have hE := selectedExceptionalConstant_pos d.c₀ τ
    dsimp [V]
    positivity
  refine ⟨c,min e (1/(2*d.c₀)),D*Real.sqrt V,K,a,hc,
    lt_min he (by positivity [d.c₀_pos]),mul_pos hD (Real.sqrt_pos.mpr hV),hK,ha,?_⟩
  intro n eps L s hn heps hepslt hL hsd
  have hnN : 1 ≤ 2*n := by omega
  have hL0 : 0 < L := by linarith [abs_nonneg (Real.log eps)]
  have hepsE := hepslt.trans_le (min_le_left _ _)
  have hsmall : 2*d.c₀*eps ≤ 1 := by
    have hh := (lt_div_iff₀ (by positivity [d.c₀_pos] : 0<2*d.c₀)).mp (hepslt.trans_le (min_le_right _ _))
    nlinarith
  let w := fun θ : Fin (2*n) → ℝ =>
    (∏ i, discountedSelectedWeight d.thetaB η C eps L (θ i))*
      ‖First.pairProduct (deformedPoint (constructedSelector d.thetaB η α) (Real.exp (-d.c₀*eps)) τ 1 θ)‖
  have hi := selected_actual_y_weighted_radial_integrable hn d.thetaB_pos.le
    (by linarith [d.thetaB_lt,Real.pi_pos] : d.thetaB ≤ 2*Real.pi) d.a_pos hη hηsmall hα hαsmall
    hC.le d.c₀_pos heps hsmall hL hτ
  have hb := selected_actual_y_weighted_radial_integral hn d.thetaB_pos.le
    (by linarith [d.thetaB_lt,Real.pi_pos] : d.thetaB ≤ 2*Real.pi) d.a_pos hη hηsmall hα hαsmall
    hC.le d.c₀_pos heps hsmall hL hτ
  rw [← angleBox_restrict_pi] at hi hb
  change IntegrableOn w (angleBox (2*n)) at hi
  change (∫ θ in angleBox (2*n),w θ) ≤ (matchingCount n:ℝ)*V^n at hb
  let P := ((2*n).factorial:ℝ)⁻¹*K*D^(2*n)*Real.exp ((Real.log L)^2/(4*a))
  have hP : 0 ≤ P := by dsimp [P]; positivity
  have hnorm : ‖continuedSelectedIntegral (2*n) (constructedSelector d.thetaB η α)
      (Real.exp (-d.c₀*eps)) τ s‖ ≤ P*((matchingCount n:ℝ)*V^n) := by
    apply (norm_integral_le_of_norm_le (hi.const_mul P) ?_).trans
      ((integral_const_mul P w).trans_le (mul_le_mul_of_nonneg_left hb hP))
    filter_upwards [ae_restrict_mem measurableSet_Icc] with θ hθ
    exact hbound (2*n) eps L θ s hnN heps hepsE hL0 hθ hsd
  have hf : (matchingCount n:ℝ)*((2:ℝ)^n*(n.factorial:ℝ))=((2*n).factorial:ℝ) := by
    exact_mod_cast matchingCount_factorial n
  have heq : P*((matchingCount n:ℝ)*V^n)=
      K*Real.exp ((Real.log L)^2/(4*a))*selectedFactorialEnvelope (D*Real.sqrt V) 0 n := by
    unfold P selectedFactorialEnvelope
    simp only [pow_zero,mul_one,mul_pow,pow_mul,Real.sq_sqrt hV.le]
    have hf0 : ((2*n).factorial:ℝ) ≠ 0 := by positivity
    have hn0 : (n.factorial:ℝ) ≠ 0 := by positivity
    have ht0 : (2:ℝ)^n ≠ 0 := by positivity
    field_simp
    nlinarith [hf]
  exact hnorm.trans_eq heq

end
end IsingBulk.Tail
