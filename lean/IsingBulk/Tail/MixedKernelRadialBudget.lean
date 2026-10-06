import IsingBulk.Tail.MixedPositiveSourceIntegral
import IsingBulk.Tail.MixedNegativeSupportedIntegral
import IsingBulk.Tail.AllBranchExteriorKernelRadialCost

namespace IsingBulk.Tail
noncomputable section

theorem mixed_constant_le_exponential (A : ℝ) {N : ℕ} (hN : 1≤N) : A≤(max 1 A)^N := by
  apply (le_max_right 1 A).trans
  simpa only [pow_one] using pow_le_pow_right₀ (le_max_left 1 A) hN

theorem mixed_spectator_power_le {P : ℝ} (hP : 0≤P) (N : ℕ) : P^(N-2)≤(max 1 P)^N :=
  (pow_le_pow_left₀ hP (le_max_right _ _) _).trans
    (pow_le_pow_right₀ (le_max_left _ _) (Nat.sub_le _ _))

theorem mixed_radial_ratio_log (H : ℝ) (hH : 0≤H) :
    Real.log ((2*Real.pi+Real.exp (-H))/Real.exp (-H))≤
      (1+|Real.log (2*Real.pi+1)|)*(H+1) := by
  have he : Real.exp (-H)≤1 := Real.exp_le_one_iff.mpr (by linarith)
  have hpos : 0<2*Real.pi+Real.exp (-H) := by positivity
  have hl := Real.log_le_log hpos (show 2*Real.pi+Real.exp (-H)≤2*Real.pi+1 by linarith)
  rw [Real.log_div hpos.ne' (Real.exp_pos _).ne',Real.log_exp]
  nlinarith [le_abs_self (Real.log (2*Real.pi+1)),abs_nonneg (Real.log (2*Real.pi+1))]

/-- The positive source coarea budget has only a dimension-exponential
constant, a quadratic particle factor and a quadratic radial logarithm. -/
theorem mixed_positive_kernel_radial_budget (c a P : ℝ) (hc : 0<c) (ha : 0<a) (hP : 0≤P) :
    ∃ K : ℝ,0<K ∧ ∀ (N : ℕ) (H : ℝ),1≤N → 0≤H →
      mixedPositiveIntegralBudget N (c*Real.exp (-H)) (a*Real.exp (-H)) P≤
        K^N*(N:ℝ)^2*(H+1)^2 := by
  let A := (48/5:ℝ)*simpleKernelConstant^2*(1+|Real.log c|)*(1+|Real.log a|)
  let K := max 1 A*max 1 P
  have hsk := simpleKernelConstant_pos
  have hA : 0≤A := by dsimp [A]; positivity
  have hK : 0<K := mul_pos (zero_lt_one.trans_le (le_max_left _ _)) (zero_lt_one.trans_le (le_max_left _ _))
  refine ⟨K,hK,?_⟩
  intro N H hN hH
  have hcLog := allBranchExterior_radial_log_factor c H hc hH
  have haLog := allBranchExterior_radial_log_factor a H ha hH
  have hPow := mixed_spectator_power_le hP N
  have hConst := mixed_constant_le_exponential A hN
  calc
    _ ≤ (48/5:ℝ)*(((N:ℝ)*simpleKernelConstant*((1+|Real.log c|)*(H+1)))*
        ((N:ℝ)*simpleKernelConstant*((1+|Real.log a|)*(H+1)))*(max 1 P)^N) := by
      unfold mixedPositiveIntegralBudget
      gcongr
    _ = A*((N:ℝ)^2*(max 1 P)^N*(H+1)^2) := by dsimp [A]; ring
    _ ≤ (max 1 A)^N*((N:ℝ)^2*(max 1 P)^N*(H+1)^2) :=
      mul_le_mul_of_nonneg_right hConst (by positivity)
    _ = _ := by dsimp [K]; rw [mul_pow]; ring

/-- The negative source phase and attenuation costs satisfy the same
scalar budget, with no epsilon-dependent geometric constant. -/
theorem mixed_negative_kernel_radial_budget (c P : ℝ) (hc : 0<c) (hP : 0≤P) :
    ∃ K : ℝ,0<K ∧ ∀ (N : ℕ) (H : ℝ),1≤N → 0≤H →
      mixedNegativeIntegralBudget N (c*Real.exp (-H)) (Real.exp (-H)) P≤
        K^N*(N:ℝ)^2*(H+1)^2 := by
  let A := 2*simpleKernelConstant*(1+|Real.log c|)*(1+|Real.log (2*Real.pi+1)|)
  let K := max 1 A*max 1 P
  have hsk := simpleKernelConstant_pos
  have hA : 0≤A := by dsimp [A]; positivity
  have hK : 0<K := mul_pos (zero_lt_one.trans_le (le_max_left _ _)) (zero_lt_one.trans_le (le_max_left _ _))
  refine ⟨K,hK,?_⟩
  intro N H hN hH
  have hcLog := allBranchExterior_radial_log_factor c H hc hH
  have hRatio := mixed_radial_ratio_log H hH
  have hPow := mixed_spectator_power_le hP N
  have hConst := mixed_constant_le_exponential A hN
  have hn : 1≤(N:ℝ) := by exact_mod_cast hN
  have hRatio0 : 0≤Real.log ((2*Real.pi+Real.exp (-H))/Real.exp (-H)) :=
    Real.log_nonneg ((one_le_div (Real.exp_pos _)).mpr (by linarith [Real.pi_pos]))
  calc
    _ ≤ ((N:ℝ)*simpleKernelConstant*((1+|Real.log c|)*(H+1)))*
        (2*((1+|Real.log (2*Real.pi+1)|)*(H+1)))*(max 1 P)^N := by
      unfold mixedNegativeIntegralBudget
      gcongr
    _ = A*(N:ℝ)*(max 1 P)^N*(H+1)^2 := by dsimp [A]; ring
    _ ≤ A*(N:ℝ)^2*(max 1 P)^N*(H+1)^2 := by gcongr; nlinarith
    _ = A*((N:ℝ)^2*(max 1 P)^N*(H+1)^2) := by ring
    _ ≤ (max 1 A)^N*((N:ℝ)^2*(max 1 P)^N*(H+1)^2) :=
      mul_le_mul_of_nonneg_right hConst (by positivity)
    _ = _ := by dsimp [K]; rw [mul_pow]; ring

end
end IsingBulk.Tail
