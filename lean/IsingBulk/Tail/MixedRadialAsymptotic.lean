import IsingBulk.Tail.MixedSectorNorm
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First Set Filter Asymptotics
open scoped Topology

theorem originalMixedSectorNorm_zero (f : SelectorFunctions) (r τ b outer inner : ℝ)
    (ho : 0<outer) (hi : 0< inner) (k : ℕ) (s : ℂ) :
    originalMixedSectorNorm 0 f r τ b outer inner ho hi k s=0 := by
  simp [originalMixedSectorNorm]

theorem integratedMixedSectorNorm_zero (f : SelectorFunctions) (r τ b outer inner : ℝ)
    (ho : 0<outer) (hi : 0< inner) (k : ℕ) (s : ℂ) (cut : ℝ) :
    integratedMixedSectorNorm 0 f r τ b outer inner ho hi k s cut=0 := by
  simp [integratedMixedSectorNorm]

theorem radial_power_cutoff_eventually {β t : ℝ} (hβ : 0<β) (τ : ℝ) (ht : 0<t) :
    ∀ᶠ eps : ℝ in 𝓝[>] 0,eps^β∈Icc (0:ℝ) 1 ∧ eps^β*τ<t := by
  have hp : Tendsto (fun eps : ℝ => eps^β) (𝓝[>] 0) (𝓝 0) := by
    have hh := (Real.continuous_rpow_const hβ.le).continuousAt.tendsto.mono_left
      (show 𝓝[>] (0:ℝ)≤𝓝 0 from nhdsWithin_le_nhds)
    simpa only [Real.zero_rpow hβ.ne'] using hh
  have hm : Tendsto (fun eps : ℝ => eps^β*τ) (𝓝[>] 0) (𝓝 0) := by
    simpa only [zero_mul] using hp.mul_const τ
  filter_upwards [self_mem_nhdsWithin,hp.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1)),
    hm.eventually (gt_mem_nhds ht)] with eps heps hp hm
  exact ⟨⟨Real.rpow_nonneg heps.le _,hp.le⟩,hm⟩

theorem mixed_atTop_gaussian_littleO (E : ℝ → ℕ → ℝ) {C κ : ℝ} (m : ℕ)
    (hC : 0≤C) (hκ : 0<κ) (hE : ∀ eps N,0≤E eps N) (hzero : ∀ eps,E eps 0=0)
    (hbound : ∀ᶠ H : ℝ in atTop,∀ n,E (Real.exp (-H)) (n+1)≤
      C^(n+1)*((n+1:ℕ):ℝ)^m*Real.exp (-κ*((n+1:ℕ):ℝ)^2)*(H+1)^2) :
    (∀ᶠ eps : ℝ in 𝓝[>] 0,Summable (E eps)) ∧
      (fun eps : ℝ => ∑' N,E eps N) =o[𝓝[>] 0] (fun eps : ℝ => (Real.sqrt eps)⁻¹) := by
  apply mixed_gaussian_log_majorant_littleO E m hC hκ hE
  filter_upwards [log_inverse_tendsto_atTop.eventually hbound,self_mem_nhdsWithin] with eps hh heps
  intro N
  cases N with
  | zero => rw [hzero]; positivity
  | succ n =>
    have heq : Real.exp (-Real.log (1/eps))=eps := by
      rw [one_div,Real.log_inv,neg_neg,Real.exp_log heps]
    simpa only [heq] using hh n

end
end IsingBulk.Tail
