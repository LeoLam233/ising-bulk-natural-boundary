import IsingBulk.AnisoF002.C03.NegativeArbitraryOrderTail

/-!
# Whole-radius integration of the central and outer pole errors

This comparison retains the exact physical particle exponent, all
positive radii and every sufficiently large integer Taylor order.  The
central angular error and the absorbed outer angular error can therefore
be integrated without an exceptional-direction cutoff or a congruence
restriction on the derivative order.
-/

namespace IsingBulk.AnisoF002.NegativeHT
noncomputable section
open MeasureTheory Set

set_option maxHeartbeats 1000000 in
theorem integrated_full_beta_error (n k : ℕ) (hn : 2 ≤ n) (hk : 64 * n ^ 2 ≤ k)
    {ε : ℝ} (hε : 0 ≤ ε) {E : ℝ → ℂ}
    (hEm : AEStronglyMeasurable E (volume.restrict (Ioi (0 : ℝ))))
    (hcentral : ∀ x : ℝ, 0 < x → x ≤ 32 * (n : ℝ) ^ 2 / (k : ℝ) →
      ‖E x‖ ≤ ε / (1 + x) ^ k)
    (htail : ∀ x : ℝ, 32 * (n : ℝ) ^ 2 / (k : ℝ) < x →
      ‖E x‖ ≤ 1 / (1 + x) ^ (k / 2 + k / 4 + 1)) :
    IntegrableOn (fun x : ℝ => x ^ (particleExponent n - 1) • E x) (Ioi (0 : ℝ)) ∧
    ‖∫ x in Ioi (0 : ℝ), x ^ (particleExponent n - 1) • E x‖ ≤
      (ε + Real.exp (-(n : ℝ) ^ 2 / 4)) * radialBeta (particleExponent n) (k - 1) := by
  have hn2 : 4 ≤ n ^ 2 := by nlinarith
  have hk1 : 1 ≤ k := by omega
  have hα0 : 0 < particleExponent n := by unfold particleExponent; omega
  have hαk : particleExponent n ≤ k - 1 := by
    have h := particleExponent_le_sq n
    omega
  have hαs : particleExponent n ≤ k / 2 + k / 4 := by
    have h := particleExponent_le_sq n
    omega
  let R : ℝ := 32 * (n : ℝ) ^ 2 / (k : ℝ)
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hsub : Ioi R ⊆ Ioi (0 : ℝ) := Ioi_subset_Ioi hR
  let M : ℝ → ℝ := fun x => ε * radialBetaDensity (particleExponent n) (k - 1) x +
    (Ioi R).indicator (radialBetaDensity (particleExponent n) (k / 2 + k / 4)) x
  have hi := integrableOn_radialBetaDensity (particleExponent n) (k - 1) hα0 hαk
  have his := integrableOn_radialBetaDensity (particleExponent n) (k / 2 + k / 4) hα0 hαs
  have hMi : IntegrableOn M (Ioi (0 : ℝ)) :=
    (hi.const_mul ε).add (his.indicator measurableSet_Ioi)
  have hb : ∀ x ∈ Ioi (0 : ℝ),
      ‖x ^ (particleExponent n - 1) • E x‖ ≤ M x := by
    intro x hx
    have hx0 : 0 ≤ x := hx.le
    rw [norm_smul, Real.norm_of_nonneg (pow_nonneg hx0 _)]
    by_cases hr : x ≤ R
    · have hh := mul_le_mul_of_nonneg_left (hcentral x hx hr)
        (pow_nonneg hx0 (particleExponent n - 1))
      have hnR : x ∉ Ioi R := not_lt.mpr hr
      dsimp [M]
      rw [indicator_of_notMem hnR, add_zero]
      convert hh using 1
      simp only [radialBetaDensity, Nat.sub_add_cancel hk1]
      ring
    · have hxR : x ∈ Ioi R := lt_of_not_ge hr
      have hh := mul_le_mul_of_nonneg_left (htail x hxR)
        (pow_nonneg hx0 (particleExponent n - 1))
      have hh' : x ^ (particleExponent n - 1) * ‖E x‖ ≤
          radialBetaDensity (particleExponent n) (k / 2 + k / 4) x := by
        simpa only [radialBetaDensity, div_eq_mul_inv, one_mul, mul_assoc] using hh
      dsimp [M]
      rw [indicator_of_mem hxR]
      exact hh'.trans (le_add_of_nonneg_left
        (mul_nonneg hε (radialBetaDensity_nonneg _ _ hx0)))
  have hbi : IntegrableOn (fun x : ℝ => x ^ (particleExponent n - 1) • E x)
      (Ioi (0 : ℝ)) := by
    apply hMi.mono' ((continuous_id.pow _).aestronglyMeasurable.smul hEm)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx using hb x hx
  refine ⟨hbi, ?_⟩
  have hnorm := norm_integral_le_of_norm_le hMi
    (by filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx using hb x hx)
  have hMval : (∫ x in Ioi (0 : ℝ), M x) =
      ε * radialBeta (particleExponent n) (k - 1) +
        ∫ x in Ioi R, radialBetaDensity (particleExponent n) (k / 2 + k / 4) x := by
    dsimp [M]
    rw [integral_add (hi.const_mul ε) (his.indicator measurableSet_Ioi),
      integral_const_mul, setIntegral_indicator measurableSet_Ioi,
      inter_eq_right.mpr hsub]
    rfl
  rw [hMval] at hnorm
  have htailI := (div_le_iff₀ (radialBeta_pos (particleExponent n) (k - 1) hα0 hαk)).mp
    (arbitrary_order_radial_tail_gaussian n k hn hk)
  calc
    _ ≤ ε * radialBeta (particleExponent n) (k - 1) +
        ∫ x in Ioi R, radialBetaDensity (particleExponent n) (k / 2 + k / 4) x := hnorm
    _ ≤ ε * radialBeta (particleExponent n) (k - 1) +
        Real.exp (-(n : ℝ) ^ 2 / 4) * radialBeta (particleExponent n) (k - 1) :=
      add_le_add le_rfl htailI
    _ = _ := by ring

end
end IsingBulk.AnisoF002.NegativeHT
