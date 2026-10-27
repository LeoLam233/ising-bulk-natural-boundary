import IsingBulk.Preferred22.RadialFiniteLimits
import IsingBulk.Preferred22.Prefactors
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-! The exact Leibniz step for the physical leading coefficient. Lower
derivative terms vanish after square-root scaling because their finite
radial limits have already been proved by integrable radial calculus. -/
namespace IsingBulk.Preferred22
noncomputable section
open Set Filter
open scoped Topology BigOperators
set_option backward.isDefEq.respectTransparency false

theorem preferred_radialPath_tendsto (ζ : ℂ) :
    Tendsto (fun t : ℝ => (1+(t:ℂ))*ζ) (𝓝[>] 0) (𝓝 ζ) := by
  have hc : Continuous (fun t : ℝ => (1+(t:ℂ))*ζ) := by fun_prop
  simpa using (hc.tendsto (0:ℝ)).mono_left nhdsWithin_le_nhds

/-- The physical prefactor multiplies the actual leading coefficient;
every other term of Leibniz's formula is proved negligible. -/
theorem preferred_radial_product_leading_limit {A R : ℂ → ℂ} {ζ : ℂ}
    (hζ : ‖ζ‖ = 1) (hA : AnalyticAt ℂ A ζ)
    (hR : ∀ t : ℝ, 0 < t → AnalyticAt ℂ R ((1+(t:ℂ))*ζ))
    (k : ℕ) {L : ℂ}
    (hlim : Tendsto (fun t : ℝ => Real.sqrt t •
      iteratedDeriv k R ((1+(t:ℂ))*ζ)) (𝓝[>] 0) (𝓝 L)) :
    Tendsto (fun t : ℝ => Real.sqrt t •
      iteratedDeriv k (fun s => A s * R s) ((1+(t:ℂ))*ζ))
      (𝓝[>] 0) (𝓝 (A ζ * L)) := by
  have hp := preferred_radialPath_tendsto ζ
  have hs : Tendsto Real.sqrt (𝓝[>] (0:ℝ)) (𝓝 0) := by
    simpa using (Real.continuous_sqrt.tendsto (0:ℝ)).mono_left nhdsWithin_le_nhds
  have hlower := preferred_lower_radial_limits_of_sqrt_limit hζ hR k hlim
  let T : ℕ → ℝ → ℂ := fun i t => (k.choose i : ℂ) *
    iteratedDeriv i A ((1+(t:ℂ))*ζ) *
      (Real.sqrt t • iteratedDeriv (k-i) R ((1+(t:ℂ))*ζ))
  have hterm (i : ℕ) (hi : i ∈ Finset.range (k+1)) :
      Tendsto (T i) (𝓝[>] 0) (𝓝 (if i=0 then A ζ * L else 0)) := by
    have hAi := (IsingBulk.First.analyticAt_iteratedDeriv hA i).continuousAt.tendsto.comp hp
    by_cases hi0 : i=0
    · subst i
      simpa only [T,Nat.choose_zero_right,Nat.cast_one,one_mul,Nat.sub_zero,
        iteratedDeriv_zero,ite_true,Function.comp_apply] using hAi.mul hlim
    · have hki : k-i < k := by
        have := Finset.mem_range.mp hi
        omega
      obtain ⟨Lj,hLj⟩ := hlower (k-i) hki
      have hzero : Tendsto (fun t : ℝ => Real.sqrt t •
          iteratedDeriv (k-i) R ((1+(t:ℂ))*ζ)) (𝓝[>] 0) (𝓝 0) := by
        simpa using hs.smul hLj
      simpa only [T,ite_eq_right hi0,mul_zero,Function.comp_apply] using
        (hAi.const_mul (k.choose i : ℂ)).mul hzero
  have hsum := tendsto_finsetSum (Finset.range (k+1)) hterm
  have hsum' : Tendsto (fun t : ℝ => ∑ i ∈ Finset.range (k+1), T i t)
      (𝓝[>] 0) (𝓝 (A ζ * L)) := by
    simpa only [Finset.sum_ite_eq',Finset.mem_range,Nat.zero_lt_succ,ite_true] using hsum
  apply hsum'.congr'
  filter_upwards [self_mem_nhdsWithin,hp.eventually hA.eventually_analyticAt] with t ht hAt
  have heq := iteratedDeriv_fun_mul (hAt.contDiffAt) ((hR t ht).contDiffAt) (n := k)
  rw [heq,Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i _
  dsimp only [T]
  simp only [Complex.real_smul]
  ring

end
end IsingBulk.Preferred22
