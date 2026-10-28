import IsingBulk.HT22.FullTail.Actual
import IsingBulk.HT22.Tail.NumericalEnvelopes
namespace IsingBulk.HT22.FullTail
noncomputable section
open Filter Set IsingBulk.HT22.Physical
open scoped Topology BigOperators

theorem epsilon_limit_of_log_bound (f : ℝ → ℝ) {e C : ℝ} (he : 0<e)
    (hf : ∀ ε,0<ε → ε<e → 0≤f ε ∧ f ε≤C*(1+|Real.log ε|)) :
    Tendsto (fun ε : ℝ => ε*f ε) (𝓝[>] 0) (𝓝 0) := by
  have hev : ∀ᶠ ε : ℝ in 𝓝[>] 0,0<ε ∧ ε<e :=
    (show ∀ᶠ ε : ℝ in 𝓝[>] 0,0<ε from self_mem_nhdsWithin).and
      (mem_nhdsWithin_of_mem_nhds (eventually_lt_nhds he))
  have hlo : ∀ᶠ ε : ℝ in 𝓝[>] 0,0≤ε*f ε := by
    filter_upwards [hev] with ε hε
    exact mul_nonneg hε.1.le (hf ε hε.1 hε.2).1
  have hup : ∀ᶠ ε : ℝ in 𝓝[>] 0,ε*f ε≤C*(ε*(1+|Real.log ε|)) := by
    filter_upwards [hev] with ε hε
    simpa only [mul_left_comm] using mul_le_mul_of_nonneg_left (hf ε hε.1 hε.2).2 hε.1.le
  exact squeeze_zero' hlo hup (by simpa using logarithmic_factor_times_parameter_tendsto_zero.const_mul C)

/-- Epsilon annihilates the entire absolute infinite upper odd tail, with no
moving order threshold and no remaining analytic estimate premise. -/
theorem actual_absolute_tail_epsilon_zero (d : IsingBulk.Preferred22.PreferredBranchData)
    {p : ℕ} (hp5 : 5≤p) (hp : Odd p) {j : ℕ}
    (hj : j≤IsingBulk.HT.First.derivativeOrder p) (negative : Bool) :
    Tendsto (fun ε : ℝ => ε*(∑' n,coefficientMass negative p j d.alpha ε n))
      (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨e,he,hsource⟩ := actual_absolute_tail d
  obtain ⟨C,_hC,hsource⟩ := hsource p hp5 hp j hj
  apply epsilon_limit_of_log_bound _ he
  intro ε hε hεe
  exact ⟨tsum_nonneg (fun n => norm_nonneg _),(hsource negative ε hε hεe).2⟩

/-- The corresponding complex sum vanishes after epsilon multiplication.
The actual absolute coefficient tail, not a termwise limit, supplies control. -/
theorem actual_tail_epsilon_zero (d : IsingBulk.Preferred22.PreferredBranchData)
    {p : ℕ} (hp5 : 5≤p) (hp : Odd p) {j : ℕ}
    (hj : j≤IsingBulk.HT.First.derivativeOrder p) (negative : Bool) :
    Tendsto (fun ε : ℝ => ε • (∑' n : ℕ,
      iteratedDeriv j (signedCoefficient negative (2*(p/2+n)+3))
        (IsingBulk.Branch.radialParameter d.alpha ε))) (𝓝[>] 0) (𝓝 (0:ℂ)) := by
  obtain ⟨e,he,hsource⟩ := actual_absolute_tail d
  obtain ⟨C,_hC,hsource⟩ := hsource p hp5 hp j hj
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall (fun ε => norm_nonneg _)) _
    (actual_absolute_tail_epsilon_zero d hp5 hp hj negative)
  filter_upwards [self_mem_nhdsWithin,
    mem_nhdsWithin_of_mem_nhds (eventually_lt_nhds he)] with ε hε hεe
  have hε : 0<ε := hε
  rw [norm_smul,Real.norm_eq_abs,abs_of_pos hε]
  apply mul_le_mul_of_nonneg_left _ hε.le
  exact norm_tsum_le_tsum_norm (hsource negative ε hε hεe).1

/-- Direct index adapter for Final.signedOddSeries_derivative_split. -/
theorem actual_tail_epsilon_zero_split (d : IsingBulk.Preferred22.PreferredBranchData)
    {p : ℕ} (hp5 : 5≤p) (hp : Odd p) {j : ℕ}
    (hj : j≤IsingBulk.HT.First.derivativeOrder p) (negative : Bool) :
    Tendsto (fun ε : ℝ => ε • (∑' n : ℕ,
      iteratedDeriv j (signedCoefficient negative (2*(p/2)+3+2*n))
        (IsingBulk.Branch.radialParameter d.alpha ε))) (𝓝[>] 0) (𝓝 (0:ℂ)) := by
  simpa only [Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    actual_tail_epsilon_zero d hp5 hp hj negative
end
end IsingBulk.HT22.FullTail
