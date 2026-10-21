import IsingBulk.HT.Tail.AbsoluteOddTailAssembly

/-!
# Infinite-tail input to HT noncancellation

The complex tail and its inverse-epsilon scaled limit follow from the
constructed absolute infinite-tail theorem. No physical-series or FIRST
asymptotic is asserted here. In particular the offsite limitation remains
explicit; the onsite and signed/reflected conclusions require their own
source estimates.
-/
namespace IsingBulk.HT.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch Filter Asymptotics
open scoped Topology

/-- Conversion between the stronger tail scale and the HT leading scale.
The full function may itself be an infinite sum. -/
theorem epsilon_smul_tendsto_zero_of_invSqrt_littleO {F : ℝ → ℂ}
    (h : IsLittleO (𝓝[>] (0 : ℝ)) F (fun eps => (Real.sqrt eps : ℂ)⁻¹)) :
    Tendsto (fun eps : ℝ => eps • F eps) (𝓝[>] 0) (𝓝 (0 : ℂ)) := by
  have hs : Tendsto (fun eps : ℝ => Real.sqrt eps • F eps)
      (𝓝[>] 0) (𝓝 (0 : ℂ)) := by
    apply IsingBulk.Final.sqrt_limit_of_isLittleO
    simpa only [mul_zero, sub_zero] using h
  have hr : Tendsto (fun eps : ℝ => Real.sqrt eps) (𝓝[>] 0) (𝓝 (0 : ℝ)) := by
    simpa only [Real.sqrt_zero] using
      (Real.continuous_sqrt.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
  have hz : Tendsto (fun eps : ℝ => Real.sqrt eps • (Real.sqrt eps • F eps))
      (𝓝[>] 0) (𝓝 (0 : ℂ)) := by
    simpa only [zero_smul] using hr.smul hs
  apply hz.congr'
  filter_upwards [self_mem_nhdsWithin] with eps heps
  rw [smul_smul, Real.mul_self_sqrt heps.le]

/-- The entire actual higher odd offsite series, not the individual
summands, is negligible. Absolute convergence has already been proved. -/
theorem selected_complex_upper_odd_tail_small {p : ℕ} (hp : p.Prime) (hp11 : 11 ≤ p)
    {a b : ℤ} (ha : IsingBulk.PrimeFamily.Admissible p a)
    (hb : IsingBulk.PrimeFamily.Admissible p b) (hab : a ≠ b)
    (j : ℕ) (hj : j ≤ (p ^ 2 - 1) / 2) :
    IsLittleO (𝓝[>] (0 : ℝ))
      (fun eps => ∑' n : ℕ, iteratedDeriv j (upperFormFactor (oddTailParticle p n))
        (radialParameter (selectedOrderedChart ha hb).theta eps))
      (fun eps => (Real.sqrt eps : ℂ)⁻¹) := by
  exact complex_odd_tail_small_of_absolute (hp.odd_of_ne_two (by omega))
    (selectedOrderedChart ha hb).sin_theta_pos j
    (selected_absolute_upper_odd_tail_small hp hp11 ha hb hab j hj)

/-- All orders through the HT ceiling contribute zero to the inverse-epsilon
scaled noncancellation limit, with the infinite sum inside that limit. -/
theorem selected_upper_odd_tail_epsilon_zero {p : ℕ} (hp : p.Prime) (hp11 : 11 ≤ p)
    {a b : ℤ} (ha : IsingBulk.PrimeFamily.Admissible p a)
    (hb : IsingBulk.PrimeFamily.Admissible p b) (hab : a ≠ b)
    (j : ℕ) (hj : j ≤ (p ^ 2 - 1) / 2) :
    Tendsto (fun eps : ℝ => eps •
      ∑' n : ℕ, iteratedDeriv j (upperFormFactor (oddTailParticle p n))
        (radialParameter (selectedOrderedChart ha hb).theta eps))
      (𝓝[>] 0) (𝓝 (0 : ℂ)) :=
  epsilon_smul_tendsto_zero_of_invSqrt_littleO
    (selected_complex_upper_odd_tail_small hp hp11 ha hb hab j hj)

end
end IsingBulk.HT.Tail
