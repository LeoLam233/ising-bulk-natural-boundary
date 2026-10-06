import IsingBulk.Tail.MixedKernelRadialBudget
import IsingBulk.Tail.AllBranchExteriorAsymptotic

namespace IsingBulk.Tail
noncomputable section
open Filter Asymptotics
open scoped Topology

theorem mixed_density_radial_cost_bound {C M K κ H Q : ℝ} {N order : ℕ}
    (hC : 0≤C) (hM : 0≤M) (hK : 0≤K) (hN : 1≤N)
    (hQ : Q≤K^N*(N:ℝ)^2*(H+1)^2) :
    (C^N*(N:ℝ)^(5*order)*Real.exp (-κ*(N:ℝ)^2))*(M*Q)≤
      (C*max 1 M*K)^N*(N:ℝ)^(5*order+2)*Real.exp (-κ*(N:ℝ)^2)*(H+1)^2 := by
  have hD : 0≤C^N*(N:ℝ)^(5*order)*Real.exp (-κ*(N:ℝ)^2) := by positivity
  have hMpow := mixed_constant_le_exponential M hN
  calc
    _ ≤ (C^N*(N:ℝ)^(5*order)*Real.exp (-κ*(N:ℝ)^2))*(M*(K^N*(N:ℝ)^2*(H+1)^2)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hQ hM) hD
    _ ≤ (C^N*(N:ℝ)^(5*order)*Real.exp (-κ*(N:ℝ)^2))*
        ((max 1 M)^N*(K^N*(N:ℝ)^2*(H+1)^2)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hMpow (by positivity)) hD
    _ = _ := by simp only [mul_pow,pow_add]; ring

theorem mixed_gaussian_bounds_add {A B κ₁ κ₂ H : ℝ} {N m : ℕ}
    (hA : 0≤A) (hB : 0≤B) (hN : 1≤N) :
    A^N*(N:ℝ)^m*Real.exp (-κ₁*(N:ℝ)^2)*(H+1)^2+
      B^N*(N:ℝ)^m*Real.exp (-κ₂*(N:ℝ)^2)*(H+1)^2≤
      (2*max A B)^N*(N:ℝ)^m*Real.exp (-(min κ₁ κ₂)*(N:ℝ)^2)*(H+1)^2 := by
  have hP : A^N≤(max A B)^N := pow_le_pow_left₀ hA (le_max_left _ _) N
  have hQ : B^N≤(max A B)^N := pow_le_pow_left₀ hB (le_max_right _ _) N
  have he₁ : Real.exp (-κ₁*(N:ℝ)^2)≤Real.exp (-(min κ₁ κ₂)*(N:ℝ)^2) := by
    apply Real.exp_le_exp.mpr
    nlinarith [min_le_left κ₁ κ₂,sq_nonneg (N:ℝ)]
  have he₂ : Real.exp (-κ₂*(N:ℝ)^2)≤Real.exp (-(min κ₁ κ₂)*(N:ℝ)^2) := by
    apply Real.exp_le_exp.mpr
    nlinarith [min_le_right κ₁ κ₂,sq_nonneg (N:ℝ)]
  have htwo : (2:ℝ)≤2^N := by simpa only [pow_one] using pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) hN
  calc
    _ ≤ (max A B)^N*(N:ℝ)^m*Real.exp (-(min κ₁ κ₂)*(N:ℝ)^2)*(H+1)^2+
        (max A B)^N*(N:ℝ)^m*Real.exp (-(min κ₁ κ₂)*(N:ℝ)^2)*(H+1)^2 := by gcongr
    _ = 2*((max A B)^N*(N:ℝ)^m*Real.exp (-(min κ₁ κ₂)*(N:ℝ)^2)*(H+1)^2) := by ring
    _ ≤ 2^N*((max A B)^N*(N:ℝ)^m*Real.exp (-(min κ₁ κ₂)*(N:ℝ)^2)*(H+1)^2) :=
      mul_le_mul_of_nonneg_right htwo (by positivity)
    _ = _ := by rw [mul_pow]; ring

/-- A summable Gaussian particle envelope with the two logarithmic costs
is negligible at the FIRST singular scale, even before a window cutoff. -/
theorem mixed_gaussian_log_majorant_littleO (E : ℝ → ℕ → ℝ) {C κ : ℝ} (m : ℕ)
    (hC : 0≤C) (hκ : 0<κ) (hE : ∀ eps N,0≤E eps N)
    (hmajor : ∀ᶠ eps : ℝ in 𝓝[>] 0,∀ N,E eps N≤
      (C^N*(N:ℝ)^m*Real.exp (-κ*(N:ℝ)^2))*(Real.log (1/eps)+1)^2) :
    (∀ᶠ eps : ℝ in 𝓝[>] 0,Summable (E eps)) ∧
      (fun eps : ℝ => ∑' N,E eps N) =o[𝓝[>] 0] (fun eps : ℝ => (Real.sqrt eps)⁻¹) := by
  let S := fun N : ℕ => C^N*(N:ℝ)^m*Real.exp (-κ*(N:ℝ)^2)
  have hS : Summable S := summable_source_gaussian hC hκ m
  have hsum : ∀ᶠ eps : ℝ in 𝓝[>] 0,Summable (E eps) := by
    filter_upwards [hmajor] with eps hh
    exact Summable.of_nonneg_of_le (hE eps) hh (hS.mul_right _)
  refine ⟨hsum,?_⟩
  have hO : (fun eps : ℝ => ∑' N,E eps N) =O[𝓝[>] 0] (fun eps : ℝ => (Real.log (1/eps)+1)^2) := by
    apply IsBigO.of_bound (∑' N,S N)
    filter_upwards [hmajor,hsum] with eps hh he
    have hbound := Summable.tsum_le_tsum hh he (hS.mul_right _)
    rw [tsum_mul_right] at hbound
    simpa only [Real.norm_eq_abs,abs_of_nonneg (tsum_nonneg (hE eps)),
      abs_of_nonneg (sq_nonneg (Real.log (1/eps)+1))] using hbound
  exact hO.trans_isLittleO radial_log_polynomial_littleO

end
end IsingBulk.Tail
