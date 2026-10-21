import IsingBulk.HT.Tail.OnsiteReflection
import IsingBulk.HT.Tail.FullSiteDomination
import IsingBulk.HT.Tail.NegativeOriginalOddTailAssembly

/-! The actual full-site higher odd tail C_N=f_N+2T_N. The whole onsite
boundary series and the whole offsite tail are combined, without truncation.
Both selected families match their original FIRST integer-angle charts. -/
namespace IsingBulk.HT.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch IsingBulk.Tail IsingBulk.HT.Final
open Filter Asymptotics
open scoped Topology

def AbsoluteUpperFullOddTailSmall (p : ℕ) (theta : ℝ) (j : ℕ) : Prop :=
  (fun eps : ℝ => ∑' n : ℕ,‖iteratedDeriv j (upperFullCoefficient (oddTailParticle p n))
    (radialParameter theta eps)‖) =o[𝓝[>] 0] (fun eps : ℝ => (Real.sqrt eps)⁻¹)

theorem inverse_half_power_littleO_inv_sqrt {F : ℝ → ℝ}
    (h : F =o[𝓝[>] 0] (fun eps : ℝ => eps^(-(1/2:ℝ)))) :
    F =o[𝓝[>] 0] (fun eps : ℝ => (Real.sqrt eps)⁻¹) := by
  apply h.congr'
  · exact Eventually.of_forall (fun _ => rfl)
  · filter_upwards [self_mem_nhdsWithin] with eps heps
    rw [Real.rpow_neg heps.le,Real.sqrt_eq_rpow]

/-- A numerical comparison of actual full-site coefficients. Selected
endpoints below discharge both whole-series hypotheses internally. -/
theorem full_odd_tail_small_of_onsite_offsite {p : ℕ} (hp : Odd p)
    {theta : ℝ} (htheta : 0 < Real.sin theta) (j : ℕ)
    (honsite : (fun eps : ℝ => ∑' n : ℕ,
      ‖iteratedDeriv j (upperOnsiteFormFactor (2*n+1)) (radialParameter theta eps)‖)
      =o[𝓝[>] 0] (fun eps : ℝ => eps^(-(1/2:ℝ))))
    (hoffsite : AbsoluteUpperOddTailSmall p theta j) :
    AbsoluteUpperFullOddTailSmall p theta j := by
  have hoff : (fun eps : ℝ => ∑' n : ℕ,‖iteratedDeriv j
      (upperFormFactor (oddTailParticle p n)) (radialParameter theta eps)‖)
      =o[𝓝[>] 0] (fun eps : ℝ => (Real.sqrt eps)⁻¹) := hoffsite
  have htotal := (inverse_half_power_littleO_inv_sqrt honsite).add
    (hoff.const_mul_left (2:ℝ))
  apply radial_tsum_littleO_of_nonnegative_domination (fun _ _ => norm_nonneg _) _ htotal
  filter_upwards [self_mem_nhdsWithin] with eps heps
  exact upper_full_odd_tail_norm_domination hp j
    (IsingBulk.Final.sourceRadialTrace_pos htheta heps)

theorem selected_positive_absolute_upper_full_odd_tail_small
    {p : ℕ} (hp : p.Prime) (hp11 : 11 ≤ p) {a b : ℤ}
    (ha : IsingBulk.PrimeFamily.Admissible p a)
    (hb : IsingBulk.PrimeFamily.Admissible p b) (hab : a ≠ b)
    (j : ℕ) (hj : j ≤ (p^2-1)/2) :
    AbsoluteUpperFullOddTailSmall p (selectedOrderedChart ha hb).theta j :=
  full_odd_tail_small_of_onsite_offsite (hp.odd_of_ne_two (by omega))
    (selectedOrderedChart ha hb).sin_theta_pos j
    (selected_positive_onsite_odd_series_subpower ha hb j (1/2) (by norm_num))
    (selected_absolute_upper_odd_tail_small hp hp11 ha hb hab j hj)

theorem negative_original_family_absolute_upper_full_odd_tail_small
    {p : ℕ} (hp : p.Prime) (hp11 : 11 ≤ p) {a b : ℤ}
    (ha : IsingBulk.HT.First.NegativeAdmissible p a)
    (hb : IsingBulk.HT.First.NegativeAdmissible p b)
    (j : ℕ) (hj : j ≤ (p^2-1)/2) :
    AbsoluteUpperFullOddTailSmall p
      (IsingBulk.HT.First.negativeSelectedRegularChart ha hb).theta j :=
  full_odd_tail_small_of_onsite_offsite (hp.odd_of_ne_two (by omega))
    (IsingBulk.HT.First.negativeSelectedRegularChart ha hb).sin_theta_pos j
    (negative_original_family_onsite_odd_series_subpower ha hb j (1/2) (by norm_num))
    (negative_original_family_absolute_upper_odd_tail_small hp hp11 ha hb j hj)

/-- The full-site tail is absolutely summable at every positive epsilon,
independently of the asymptotic estimate and its derivative ceiling. -/
theorem actual_upper_full_odd_tail_summable {p : ℕ} (hp : Odd p) (j : ℕ)
    {theta eps : ℝ} (htheta : 0 < Real.sin theta) (heps : 0 < eps) :
    Summable (fun n : ℕ => ‖iteratedDeriv j (upperFullCoefficient (oddTailParticle p n))
      (radialParameter theta eps)‖) :=
  upper_full_odd_tail_summable hp j (IsingBulk.Final.sourceRadialTrace_pos htheta heps)

theorem complex_full_odd_tail_small_of_absolute {p : ℕ} (hp : Odd p)
    {theta : ℝ} (htheta : 0 < Real.sin theta) (j : ℕ)
    (hTail : AbsoluteUpperFullOddTailSmall p theta j) :
    (fun eps : ℝ => ∑' n : ℕ,iteratedDeriv j (upperFullCoefficient (oddTailParticle p n))
      (radialParameter theta eps)) =o[𝓝[>] 0] (fun eps : ℝ => (Real.sqrt eps:ℂ)⁻¹) := by
  apply IsingBulk.Final.complex_tail_isLittleO_of_absolute _ hTail
  filter_upwards [self_mem_nhdsWithin] with eps heps
  exact actual_upper_full_odd_tail_summable hp j htheta heps

theorem selected_positive_complex_upper_full_odd_tail_small
    {p : ℕ} (hp : p.Prime) (hp11 : 11 ≤ p) {a b : ℤ}
    (ha : IsingBulk.PrimeFamily.Admissible p a)
    (hb : IsingBulk.PrimeFamily.Admissible p b) (hab : a ≠ b)
    (j : ℕ) (hj : j ≤ (p^2-1)/2) :
    (fun eps : ℝ => ∑' n : ℕ,iteratedDeriv j (upperFullCoefficient (oddTailParticle p n))
      (radialParameter (selectedOrderedChart ha hb).theta eps))
      =o[𝓝[>] 0] (fun eps : ℝ => (Real.sqrt eps:ℂ)⁻¹) :=
  complex_full_odd_tail_small_of_absolute (hp.odd_of_ne_two (by omega))
    (selectedOrderedChart ha hb).sin_theta_pos j
    (selected_positive_absolute_upper_full_odd_tail_small hp hp11 ha hb hab j hj)

theorem negative_original_family_complex_upper_full_odd_tail_small
    {p : ℕ} (hp : p.Prime) (hp11 : 11 ≤ p) {a b : ℤ}
    (ha : IsingBulk.HT.First.NegativeAdmissible p a)
    (hb : IsingBulk.HT.First.NegativeAdmissible p b)
    (j : ℕ) (hj : j ≤ (p^2-1)/2) :
    (fun eps : ℝ => ∑' n : ℕ,iteratedDeriv j (upperFullCoefficient (oddTailParticle p n))
      (radialParameter (IsingBulk.HT.First.negativeSelectedRegularChart ha hb).theta eps))
      =o[𝓝[>] 0] (fun eps : ℝ => (Real.sqrt eps:ℂ)⁻¹) :=
  complex_full_odd_tail_small_of_absolute (hp.odd_of_ne_two (by omega))
    (IsingBulk.HT.First.negativeSelectedRegularChart ha hb).sin_theta_pos j
    (negative_original_family_absolute_upper_full_odd_tail_small hp hp11 ha hb j hj)

theorem selected_positive_upper_full_odd_tail_epsilon_zero
    {p : ℕ} (hp : p.Prime) (hp11 : 11 ≤ p) {a b : ℤ}
    (ha : IsingBulk.PrimeFamily.Admissible p a)
    (hb : IsingBulk.PrimeFamily.Admissible p b) (hab : a ≠ b)
    (j : ℕ) (hj : j ≤ (p^2-1)/2) :
    Tendsto (fun eps : ℝ => eps • ∑' n : ℕ,
      iteratedDeriv j (upperFullCoefficient (oddTailParticle p n))
        (radialParameter (selectedOrderedChart ha hb).theta eps)) (𝓝[>] 0) (𝓝 (0:ℂ)) :=
  epsilon_smul_tendsto_zero_of_invSqrt_littleO
    (selected_positive_complex_upper_full_odd_tail_small hp hp11 ha hb hab j hj)

theorem negative_original_family_upper_full_odd_tail_epsilon_zero
    {p : ℕ} (hp : p.Prime) (hp11 : 11 ≤ p) {a b : ℤ}
    (ha : IsingBulk.HT.First.NegativeAdmissible p a)
    (hb : IsingBulk.HT.First.NegativeAdmissible p b)
    (j : ℕ) (hj : j ≤ (p^2-1)/2) :
    Tendsto (fun eps : ℝ => eps • ∑' n : ℕ,
      iteratedDeriv j (upperFullCoefficient (oddTailParticle p n))
        (radialParameter (IsingBulk.HT.First.negativeSelectedRegularChart ha hb).theta eps))
      (𝓝[>] 0) (𝓝 (0:ℂ)) :=
  epsilon_smul_tendsto_zero_of_invSqrt_littleO
    (negative_original_family_complex_upper_full_odd_tail_small hp hp11 ha hb j hj)

end
end IsingBulk.HT.Tail
