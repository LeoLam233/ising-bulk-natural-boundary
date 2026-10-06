import IsingBulk.Tail.MixedSectorSumGaussian
import IsingBulk.Tail.MixedRadialAsymptotic

namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch Set Filter Asymptotics
open scoped Topology

/-- The entire positive-particle sum of original sectors containing a
true branch is negligible, and hence so is every source particle window. -/
theorem original_mixed_sector_sum_littleO (d : LocalBranchData)
    (hcsmall : d.c₀<Real.sin d.theta/2) :
    ∃ η₀ : ℝ,0<η₀ ∧ ∀ η : ℝ,0<η → η<η₀ →
      ∃ α₀ : ℝ,0<α₀ ∧ ∀ α : ℝ,0<α → α<α₀ →
      ∀ (order : ℕ) (outer cap : ℝ) (ho : 0<outer),0<cap →
      ∃ inner₀ : ℝ,0< inner₀ ∧ inner₀≤cap ∧ ∀ (inner : ℝ) (hi : 0< inner),inner≤ inner₀ →
      ∀ (τ : ℝ) (k : ℕ),0≤τ → k≤order →
      let E := fun eps N => originalMixedSectorNorm N (constructedSelector d.thetaB η α)
        (Real.exp (-d.c₀*eps)) τ d.thetaB outer inner ho hi k (radialParameter d.theta eps)
      (∀ᶠ eps : ℝ in 𝓝[>] 0,Summable (E eps)) ∧
        (fun eps : ℝ => ∑' N,E eps N) =o[𝓝[>] 0] (fun eps : ℝ => (Real.sqrt eps)⁻¹) := by
  obtain ⟨η₀,hη₀,hBound⟩ := original_mixed_sector_sum_gaussian_bound d hcsmall
  refine ⟨η₀,hη₀,?_⟩
  intro η hη hηlt
  obtain ⟨α₀,κ,hα₀,hκ,hBound⟩ := hBound η hη hηlt
  refine ⟨α₀,hα₀,?_⟩
  intro α hα hαlt order outer cap ho hcap
  obtain ⟨inner₀,hi₀,hicap,hBound⟩ := hBound α hα hαlt order outer cap ho hcap
  refine ⟨inner₀,hi₀,hicap,?_⟩
  intro inner hi hinner τ k hτ hk
  obtain ⟨C,hC,hBound⟩ := hBound inner hi hinner
  apply mixed_atTop_gaussian_littleO _ (5*order+2) hC.le hκ
    (fun eps N => originalMixedSectorNorm_nonneg N _ _ _ _ _ _ _ _ _ _)
    (fun eps => originalMixedSectorNorm_zero _ _ _ _ _ _ _ _ _ _)
  filter_upwards [hBound] with H hh
  intro n
  exact hh n k τ hk hτ

/-- The actual small-homotopy current sectors containing a branch have
an absolutely summable particle majorant negligible at the FIRST scale.
The cutoff is epsilon^beta and all real homotopy integration is retained. -/
theorem current_mixed_sector_sum_littleO (d : LocalBranchData)
    (hcsmall : d.c₀<Real.sin d.theta/2) :
    ∃ η₀ : ℝ,0<η₀ ∧ ∀ η : ℝ,0<η → η<η₀ →
      ∃ α₀ : ℝ,0<α₀ ∧ ∀ α : ℝ,0<α → α<α₀ →
      ∃ τ₀ : ℝ,0<τ₀ ∧ ∀ τ : ℝ,0<τ → τ<τ₀ →
      ∀ (order : ℕ) (outer cap : ℝ) (ho : 0<outer),0<cap →
      ∃ inner₀ : ℝ,0< inner₀ ∧ inner₀≤cap ∧ ∀ (inner : ℝ) (hi : 0< inner),inner≤ inner₀ →
      ∀ (k : ℕ) (β : ℝ),k≤order → 0<β →
      let E := fun eps N => integratedMixedSectorNorm N (constructedSelector d.thetaB η α)
        (Real.exp (-d.c₀*eps)) τ d.thetaB outer inner ho hi k (radialParameter d.theta eps) (eps^β)
      (∀ᶠ eps : ℝ in 𝓝[>] 0,Summable (E eps)) ∧
        (fun eps : ℝ => ∑' N,E eps N) =o[𝓝[>] 0] (fun eps : ℝ => (Real.sqrt eps)⁻¹) := by
  obtain ⟨η₀,hη₀,hBound⟩ := current_mixed_sector_sum_gaussian_bound d hcsmall
  refine ⟨η₀,hη₀,?_⟩
  intro η hη hηlt
  obtain ⟨α₀,hα₀,hBound⟩ := hBound η hη hηlt
  refine ⟨α₀,hα₀,?_⟩
  intro α hα hαlt
  obtain ⟨τ₀,hτ₀,hBound⟩ := hBound α hα hαlt
  refine ⟨τ₀,hτ₀,?_⟩
  intro τ hτ hτlt
  obtain ⟨κ,hκ,hBound⟩ := hBound τ hτ hτlt
  intro order outer cap ho hcap
  obtain ⟨inner₀,hi₀,hicap,hBound⟩ := hBound order outer cap ho hcap
  refine ⟨inner₀,hi₀,hicap,?_⟩
  intro inner hi hinner k β hk hβ
  obtain ⟨t,C,ht,hC,hBound⟩ := hBound inner hi hinner
  apply mixed_gaussian_log_majorant_littleO _ (5*order+2) hC.le hκ
    (fun eps N => integratedMixedSectorNorm_nonneg N _ _ _ _ _ _ _ _ _ _ _)
  filter_upwards [log_inverse_tendsto_atTop.eventually hBound,self_mem_nhdsWithin,
    radial_power_cutoff_eventually hβ τ ht] with eps hh heps hcut
  intro N
  cases N with
  | zero => rw [integratedMixedSectorNorm_zero]; positivity
  | succ n =>
    have heq : Real.exp (-Real.log (1/eps))=eps := by
      rw [one_div,Real.log_inv,neg_neg,Real.exp_log heps]
    simpa only [heq] using hh n k (eps^β) hk hcut.1 hcut.2

end
end IsingBulk.Tail
