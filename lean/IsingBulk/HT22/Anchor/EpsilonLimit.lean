import IsingBulk.HT22.Anchor.AbsoluteSummation
namespace IsingBulk.HT22.Anchor
noncomputable section
open Set Filter IsingBulk.Preferred22
open scoped Topology ContDiff BigOperators
set_option backward.isDefEq.respectTransparency false

theorem epsilon_tsum_zero_of_uniform_majorant (f : ℝ → ℕ → ℝ) (M : ℕ → ℝ)
    (hM : Summable M) {ε₀ : ℝ} (hε₀ : 0<ε₀)
    (hf : ∀ ε,0<ε → ε<ε₀ → ∀ k,0≤f ε k ∧ f ε k≤M k) :
    Tendsto (fun ε : ℝ => ε*(∑' k,f ε k)) (𝓝[>] 0) (𝓝 0) := by
  have he : ∀ᶠ ε : ℝ in 𝓝[>] 0,0<ε ∧ ε<ε₀ := by
    have hp : ∀ᶠ ε : ℝ in 𝓝[>] 0,0<ε := self_mem_nhdsWithin
    exact hp.and (mem_nhdsWithin_of_mem_nhds (eventually_lt_nhds hε₀))
  have hpos : ∀ᶠ ε : ℝ in 𝓝[>] 0,0≤ε*(∑' k,f ε k) := by
    filter_upwards [he] with ε hε
    exact mul_nonneg hε.1.le (tsum_nonneg (fun k => (hf ε hε.1 hε.2 k).1))
  have hbound : ∀ᶠ ε : ℝ in 𝓝[>] 0,ε*(∑' k,f ε k)≤ε*(∑' k,M k) := by
    filter_upwards [he] with ε hε
    have hs := hM.of_nonneg_of_le (fun k => (hf ε hε.1 hε.2 k).1)
      (fun k => (hf ε hε.1 hε.2 k).2)
    exact mul_le_mul_of_nonneg_left (hs.tsum_le_tsum (fun k => (hf ε hε.1 hε.2 k).2) hM) hε.1.le
  have hi : Tendsto (fun ε : ℝ => ε) (𝓝[>] 0) (𝓝 0) := tendsto_id.mono_left nhdsWithin_le_nhds
  exact squeeze_zero' hpos hbound (by simpa only [zero_mul] using hi.mul_const (∑' k,M k))

/-- Uniformly controlled absolute anchor tail: epsilon times the sum over
ALL named anchors and all odd N beyond any fixed cutoff tends to zero.
N=1 is separately retained by the physical one-particle computation. -/
theorem actual_anchor_epsilon_limit (d : PreferredBranchData) :
    ∃ cap : ℝ,0<cap ∧ cap<d.alpha ∧
      ∀ B : PreferredCoareaBump d,B.delta<cap → ∀ δB : ℝ,0<δB →
      ∃ ε₀ τ₀ : ℝ,0<ε₀ ∧ 0<τ₀ ∧
      ∀ r : ℝ → ℝ,PreferredRightCutoffData d B δB r →
      ∀ J : ℕ,∀ negative : Bool,∀ τ : ℝ,0≤τ → τ<τ₀ → ∀ j≤J,∀ cutoff : ℕ,
      Tendsto (fun ε : ℝ => ε*(∑' k,if cutoff≤k then
        derivativeMass negative k τ B.p B.m r j (IsingBulk.Branch.radialParameter d.alpha ε) else 0))
        (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨cap,hcap,hcapa,hmajor⟩ := actual_anchor_absolute_majorant d
  refine ⟨cap,hcap,hcapa,?_⟩
  intro B hB δB hδB
  obtain ⟨ε₀,τ₀,hε₀,hτ₀,hb⟩ := hmajor B hB δB hδB
  refine ⟨ε₀,τ₀,hε₀,hτ₀,?_⟩
  intro r hcut J negative τ hτ hτr j hj cutoff
  obtain ⟨C,hC,hCs,hbound⟩ := hb r hcut J
  apply epsilon_tsum_zero_of_uniform_majorant _ (oddAnchorEnvelope C J) hCs hε₀
  intro ε hε hεr k
  by_cases hk : cutoff≤k
  · simp only [ite_eq_left hk]
    exact ⟨derivativeMass_nonneg negative k τ B.p B.m r j _,hbound negative k ε τ hε hεr hτ hτr j hj⟩
  · simp only [ite_eq_right hk]
    constructor
    · exact le_rfl
    · unfold oddAnchorEnvelope shellOrderEnvelope
      positivity
end
end IsingBulk.HT22.Anchor
