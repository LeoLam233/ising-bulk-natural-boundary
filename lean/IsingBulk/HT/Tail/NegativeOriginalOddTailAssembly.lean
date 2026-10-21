import IsingBulk.HT.Tail.NegativeOriginalFamilyData
import IsingBulk.HT.Tail.NegativeGeneralCommonParameters
import IsingBulk.HT.Tail.NegativeAbsoluteOddTailAssembly

/-! The complete odd offsite tail at the original negative integer-angle
prime family. This family is distinct from reflected positive integer angles.
All arithmetic and analytic hypotheses are discharged internally. -/
namespace IsingBulk.HT.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch IsingBulk.Tail
open Filter Asymptotics
open scoped Topology

/-- Every differentiated higher odd particle, at the actual negative FIRST
point. One common deformation covers all orders through the HT ceiling. -/
theorem negative_original_family_absolute_upper_odd_tail_small
    {p : ℕ} (hp : p.Prime) (hp11 : 11 ≤ p) {a b : ℤ}
    (ha : IsingBulk.HT.First.NegativeAdmissible p a)
    (hb : IsingBulk.HT.First.NegativeAdmissible p b) :
    ∀ j : ℕ,j ≤ (p^2-1)/2 →
      AbsoluteUpperOddTailSmall p
        (IsingBulk.HT.First.negativeSelectedRegularChart ha hb).theta j := by
  obtain ⟨tau,alpha,htau,halpha,⟨cfg⟩⟩ :=
    negative_ht_general_common_all_sector_parameters (negativeOriginalReflectedData ha hb)
      (negativeOriginalReflectedData_c0_small ha hb)
      (negativeOriginalReflectedData_algebraic hp ha hb)
      (negativeOriginalReflectedData_nonresonant hp hp11 ha hb)
      p (by omega) ((p^2-1)/2) le_rfl
  intro j hj
  have h := negative_ht_common_absoluteUpperOddTailSmall cfg
    (hp.odd_of_ne_two (by omega)) j hj
  change AbsoluteUpperOddTailSmall p
    (Real.pi-(negativeOriginalReflectedData ha hb).theta) j at h
  rwa [negativeOriginalReflectedData_theta] at h

/-- Absolute convergence is unconditional for every positive radial parameter
and every finite derivative order; it is not inferred from a tsum value. -/
theorem negative_original_family_upper_odd_tail_summable
    {p : ℕ} (hp : p.Prime) (hp11 : 11 ≤ p) {a b : ℤ}
    (ha : IsingBulk.HT.First.NegativeAdmissible p a)
    (hb : IsingBulk.HT.First.NegativeAdmissible p b) (j : ℕ)
    {ε : ℝ} (hε : 0 < ε) :
    Summable (fun n : ℕ => ‖iteratedDeriv j (upperFormFactor (oddTailParticle p n))
      (radialParameter (IsingBulk.HT.First.negativeSelectedRegularChart ha hb).theta ε)‖) :=
  actual_upper_odd_tail_summable (hp.odd_of_ne_two (by omega)) j
    (IsingBulk.HT.First.negativeSelectedRegularChart ha hb).sin_theta_pos hε

theorem negative_original_family_complex_upper_odd_tail_small
    {p : ℕ} (hp : p.Prime) (hp11 : 11 ≤ p) {a b : ℤ}
    (ha : IsingBulk.HT.First.NegativeAdmissible p a)
    (hb : IsingBulk.HT.First.NegativeAdmissible p b)
    (j : ℕ) (hj : j ≤ (p^2-1)/2) :
    (fun ε : ℝ => ∑' n : ℕ,iteratedDeriv j (upperFormFactor (oddTailParticle p n))
      (radialParameter (IsingBulk.HT.First.negativeSelectedRegularChart ha hb).theta ε))
      =o[𝓝[>] 0] (fun ε : ℝ => (Real.sqrt ε:ℂ)⁻¹) :=
  complex_odd_tail_small_of_absolute (hp.odd_of_ne_two (by omega))
    (IsingBulk.HT.First.negativeSelectedRegularChart ha hb).sin_theta_pos j
    (negative_original_family_absolute_upper_odd_tail_small hp hp11 ha hb j hj)

theorem negative_original_family_upper_odd_tail_epsilon_zero
    {p : ℕ} (hp : p.Prime) (hp11 : 11 ≤ p) {a b : ℤ}
    (ha : IsingBulk.HT.First.NegativeAdmissible p a)
    (hb : IsingBulk.HT.First.NegativeAdmissible p b)
    (j : ℕ) (hj : j ≤ (p^2-1)/2) :
    Tendsto (fun ε : ℝ => ε • ∑' n : ℕ,
      iteratedDeriv j (upperFormFactor (oddTailParticle p n))
        (radialParameter (IsingBulk.HT.First.negativeSelectedRegularChart ha hb).theta ε))
      (𝓝[>] 0) (𝓝 (0:ℂ)) :=
  epsilon_smul_tendsto_zero_of_invSqrt_littleO
    (negative_original_family_complex_upper_odd_tail_small hp hp11 ha hb j hj)

end
end IsingBulk.HT.Tail
