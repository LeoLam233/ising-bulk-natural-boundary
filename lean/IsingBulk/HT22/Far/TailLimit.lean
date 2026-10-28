import IsingBulk.HT22.Far.WholeTail

namespace IsingBulk.HT22.Far
noncomputable section
open IsingBulk.Preferred22 IsingBulk.HT22.Tail Set MeasureTheory Filter
open scoped BigOperators Topology ContDiff ENNReal
set_option backward.isDefEq.respectTransparency false

theorem epsilon_zero_of_log_bound (f : ℝ → ℝ) {e C : ℝ} (he : 0<e)
    (hf : ∀ ε,0<ε → ε<e → 0≤f ε ∧ f ε≤C*(1+|Real.log ε|)) :
    Tendsto (fun ε => ε*f ε) (𝓝[>] 0) (𝓝 0) := by
  have hevent : ∀ᶠ ε : ℝ in 𝓝[>] 0,0<ε ∧ ε<e :=
    (show ∀ᶠ ε : ℝ in 𝓝[>] 0,0<ε from self_mem_nhdsWithin).and
      (mem_nhdsWithin_of_mem_nhds (eventually_lt_nhds he))
  apply squeeze_zero' (g := fun ε => C*(ε*(1+|Real.log ε|)))
  · filter_upwards [hevent] with ε hε
    exact mul_nonneg hε.1.le (hf ε hε.1 hε.2).1
  · filter_upwards [hevent] with ε hε
    have hh := mul_le_mul_of_nonneg_left (hf ε hε.1 hε.2).2 hε.1.le
    simpa only [mul_left_comm] using hh
  · simpa only [mul_zero] using logarithmic_factor_times_parameter_tendsto_zero.const_mul C

theorem complex_epsilon_zero_of_absolute_log_bound (f : ℝ → ℕ → ℂ) {e C : ℝ} (he : 0<e)
    (hf : ∀ ε,0<ε → ε<e → Summable (fun n => ‖f ε n‖) ∧
      (∑' n,‖f ε n‖)≤C*(1+|Real.log ε|)) :
    Tendsto (fun ε : ℝ => (ε:ℂ)*(∑' n,f ε n)) (𝓝[>] 0) (𝓝 0) := by
  have hnorm := epsilon_zero_of_log_bound (fun ε => ‖∑' n,f ε n‖) he (by
    intro ε hε hεr
    exact ⟨norm_nonneg _,(norm_tsum_le_tsum_norm (hf ε hε hεr).1).trans (hf ε hε hεr).2⟩)
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply hnorm.congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hε]

theorem actual_high_odd_epsilon_zero (b : PreferredBranchData) :
    ∃ cap : ℝ, 0<cap ∧ cap<b.alpha ∧ ∀ B : PreferredCoareaBump b, B.delta<cap →
    ∃ ε₀ τ₀ δB : ℝ, 0<ε₀ ∧ 0<τ₀ ∧ 0<δB ∧ δB<B.delta ∧
    ∀ rcut : ℝ → ℝ, ContDiff ℝ ∞ rcut → Function.Periodic rcut (2*Real.pi) →
    ∀ p : ℕ, 5≤p → Odd p → ∀ j : ℕ, j≤IsingBulk.HT.First.derivativeOrder p →
    ∀ a η : ℝ, |a|≤Real.pi → ∀ τ : ℝ, 0≤τ → τ<τ₀ →
    ∀ δ : ℝ, δ≤δB → PreferredRightCutoffData b B δ rcut →
    Tendsto (fun ε : ℝ => ε*(∑' n,‖wholeTransportedIntegral b B rcut j a η (p/2+n) ε τ‖))
      (𝓝[>] 0) (𝓝 0) ∧
    Tendsto (fun ε : ℝ => (ε:ℂ)*(∑' n,wholeTransportedIntegral b B rcut j a η (p/2+n) ε τ))
      (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨cap,hcap,hcapa,hsource⟩ := actual_high_odd_mass_sum b
  refine ⟨cap,hcap,hcapa,?_⟩
  intro B hB
  obtain ⟨e,t,d,he,ht,hd,hdB,hsource⟩ := hsource B hB
  refine ⟨e,t,d,he,ht,hd,hdB,?_⟩
  intro rcut hrcut hrper p hp5 hp j hj a η ha τ hτ hτr δ hδ hcut
  obtain ⟨C,_hC,hsource⟩ := hsource rcut hrcut hrper p hp5 hp j hj
  have hb (ε : ℝ) (hε : 0<ε) (hεr : ε<e) :=
    (hsource a η ha ε τ hε hεr hτ hτr δ hδ hcut).2
  constructor
  · apply epsilon_zero_of_log_bound _ he
    intro ε hε hεr
    exact ⟨tsum_nonneg (fun _ => norm_nonneg _),(hb ε hε hεr).2⟩
  · exact complex_epsilon_zero_of_absolute_log_bound _ he hb

end
end IsingBulk.HT22.Far
