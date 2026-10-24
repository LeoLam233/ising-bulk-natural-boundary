import IsingBulk.Anisotropic.NegativeNormalForm.BetaDensityDimension
import IsingBulk.Anisotropic.NegativeDominance.PhysicalSequences

namespace IsingBulk.Anisotropic.NegativeNormalForm
noncomputable section
open Filter IsingBulk.Anisotropic.NegativeDominance
open scoped Topology

theorem beta_absorption_of_linear_cutoff (N j : ℕ) (hj : 8*N^2≤j)
    (C A L : ℝ) (hC : 0≤C) (hL : 1≤L) (hLA : L≤A*N)
    (hCA : C*A≤(N:ℝ)*Real.log 2) :
    C*(Real.sqrt L+L)≤(j/4:ℕ)*Real.log 2 := by
  have hsqrt : Real.sqrt L≤L := (Real.sqrt_le_iff).2 ⟨by linarith,by nlinarith⟩
  have hk : 2*N^2≤j/4 := by omega
  have hkr : 2*(N:ℝ)^2≤(j/4:ℕ) := by exact_mod_cast hk
  have hlog : 0≤Real.log 2 := (Real.log_pos (by norm_num : (1:ℝ)<2)).le
  have h1 := mul_le_mul_of_nonneg_left hLA hC
  have h2 := mul_le_mul_of_nonneg_right hCA (show 0≤(N:ℝ) by positivity)
  have h3 := mul_le_mul_of_nonneg_right hkr hlog
  have h4 := mul_le_mul_of_nonneg_left hsqrt hC
  nlinarith

/-- The cutoff beta-tail absorption is automatic for all j≥8N², uniformly
in the order, eventually in N. The cutoff is a fixed physical Euclidean ball. -/
theorem actual_beta_absorption_eventually (B : ℂ → ℂ) (phi : ℝ)
    (hB : AnalyticAt ℂ B 0) (C s : ℝ) (hC : 0≤C) (hs : 0<s) :
    ∀ᶠ N : ℕ in atTop, ∀ j : ℕ, 8*N^2≤j →
      let H := centralHessian B phi ((Real.pi/(N:ℝ):ℝ):ℂ)
      let c := H/((2*(N:ℝ):ℝ):ℂ)
      let L := 1+c.re*s/tau N
      1≤L ∧ C*(Real.sqrt L+L)≤(j/4:ℕ)*Real.log 2 := by
  have hlim : Tendsto (fun N : ℕ => centralHessian B phi ((Real.pi/(N:ℝ):ℝ):ℂ)) atTop (𝓝 (1:ℂ)) := by
    have he := (centralHessian_analyticAt_zero B phi hB).continuousAt.tendsto.comp winding_angle_complex_tendsto_zero
    simpa only [Function.comp_def,centralHessian_zero] using he
  have hnear := hlim (Metric.ball_mem_nhds (1:ℂ) (by norm_num : (0:ℝ)<1/2))
  change ∀ᶠ N : ℕ in atTop,centralHessian B phi ((Real.pi/(N:ℝ):ℝ):ℂ)∈Metric.ball 1 (1/2) at hnear
  simp only [Metric.mem_ball,dist_eq_norm] at hnear
  obtain ⟨N0,hN0⟩ := exists_nat_ge (C*(1+s/2)/Real.log 2)
  filter_upwards [hnear,eventually_ge_atTop N0,eventually_ge_atTop (3:ℕ)] with N hn hNN0 hN j hj
  dsimp only
  let H := centralHessian B phi ((Real.pi/(N:ℝ):ℝ):ℂ)
  let c := H/((2*(N:ℝ):ℝ):ℂ)
  let L := 1+c.re*s/tau N
  have hNpos : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have hN1 : (1:ℝ)≤N := by exact_mod_cast (show 1≤N by omega)
  have ht := tau_pos N (by omega)
  have hre : (1:ℝ)/2≤H.re ∧ H.re≤2 := by
    have h1 := Complex.re_le_norm (H-1)
    have h2 := Complex.re_le_norm (1-H)
    rw [norm_sub_rev] at h2
    simp only [Complex.sub_re,Complex.one_re] at h1 h2
    change ‖H-1‖<1/2 at hn
    constructor <;> linarith
  have hc : 0<c.re := by
    dsimp [c]
    rw [Complex.div_ofReal_re]
    exact div_pos (by linarith [hre.1]) (by positivity)
  have hct : c.re/tau N≤(N:ℝ)/2 := by
    have hlow := (tau_bounds N (by omega)).1
    have hlow' := (div_le_iff₀ (show 0<(N:ℝ)^2 by positivity)).mp hlow
    apply (div_le_iff₀ ht).2
    dsimp [c]
    rw [Complex.div_ofReal_re]
    apply (div_le_iff₀ (show 0<2*(N:ℝ) by positivity)).2
    nlinarith [hre.2]
  have hL : 1≤L := by
    dsimp [L]
    have hp : 0≤c.re*s/tau N := by positivity
    linarith
  have hLA : L≤(1+s/2)*(N:ℝ) := by
    have he := mul_le_mul_of_nonneg_left hct hs.le
    dsimp [L]
    rw [show c.re*s/tau N=s*(c.re/tau N) by ring]
    nlinarith
  have hlog : 0<Real.log 2 := Real.log_pos (by norm_num)
  have hCA : C*(1+s/2)≤(N:ℝ)*Real.log 2 := by
    apply (div_le_iff₀ hlog).mp
    exact hN0.trans (by exact_mod_cast hNN0)
  exact ⟨hL,beta_absorption_of_linear_cutoff N j hj C (1+s/2) L hC hL hLA hCA⟩

end
end IsingBulk.Anisotropic.NegativeNormalForm
