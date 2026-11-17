import IsingBulk.AnisoF002.C03.NegativeHighParticleTail

/-!
# The actual upper edge of the negative-HT central window

The high-particle cutoff is `N² ≥ j / sqrt(log j)`.  At this precise
cutoff the complete geometric-tail hypotheses are automatic for large
Taylor order, and the leading exponent loses a positive multiple of
`j sqrt(log j)`.  No finite-particle truncation is introduced.
-/

namespace IsingBulk.AnisoF002.NegativeHT
noncomputable section
open Filter
open scoped BigOperators

def highParticleThreshold (j : ℕ) : ℝ := (j : ℝ) / Real.sqrt (Real.log (j : ℝ))

theorem log_le_half_of_pos {x : ℝ} (hx : 0 < x) : Real.log x ≤ x / 2 := by
  have h := Real.log_le_sub_one_of_pos (half_pos hx)
  have h2 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
  rw [Real.log_div hx.ne' (by norm_num : (2 : ℝ) ≠ 0)] at h
  linarith

theorem highParticleThreshold_pos {j : ℕ} (hj : 0 < j)
    (ht : 0 < Real.log (j : ℝ)) : 0 < highParticleThreshold j := by
  unfold highParticleThreshold
  exact div_pos (by exact_mod_cast hj) (Real.sqrt_pos.2 ht)

theorem highParticleThreshold_log {j : ℕ} (hj : 0 < j)
    (ht : 0 < Real.log (j : ℝ)) :
    Real.log (highParticleThreshold j) =
      Real.log (j : ℝ) - Real.log (Real.log (j : ℝ)) / 2 := by
  rw [highParticleThreshold, Real.log_div (by exact_mod_cast hj.ne')
    (Real.sqrt_pos.2 ht).ne', Real.log_sqrt ht.le]

theorem highParticleThreshold_ratio {j : ℕ} (hj : 0 < j)
    (ht : 0 < Real.log (j : ℝ)) :
    (j : ℝ) / highParticleThreshold j = Real.sqrt (Real.log (j : ℝ)) := by
  unfold highParticleThreshold
  field_simp

theorem highParticleThreshold_decrease_gate {j : ℕ} {C : ℝ}
    (hj : 0 < j) (ht : 256 ≤ Real.log (j : ℝ))
    (hC : 16 * (C + 1) ≤ Real.log (j : ℝ)) :
    (j : ℝ) / highParticleThreshold j + C + 1 ≤
      Real.log (highParticleThreshold j) / 4 := by
  have ht0 : 0 < Real.log (j : ℝ) := by linarith
  have hs0 := Real.sqrt_nonneg (Real.log (j : ℝ))
  have hs2 := Real.sq_sqrt ht0.le
  have hs16 : 16 ≤ Real.sqrt (Real.log (j : ℝ)) := by nlinarith
  have hsle : Real.sqrt (Real.log (j : ℝ)) ≤ Real.log (j : ℝ) / 16 := by
    nlinarith
  have hl := log_le_half_of_pos ht0
  rw [highParticleThreshold_ratio hj ht0, highParticleThreshold_log hj ht0]
  linarith

theorem highParticleThreshold_exponent {j : ℕ} {C : ℝ}
    (hj : 0 < j) (ht : 256 ≤ Real.log (j : ℝ))
    (hC : 16 * (C + 1) ≤ Real.log (j : ℝ)) :
    highParticleExponent j C (highParticleThreshold j) ≤
      (j : ℝ) * Real.log (j : ℝ) -
        (j : ℝ) / 2 * Real.log (Real.log (j : ℝ)) -
        (j : ℝ) / 8 * Real.sqrt (Real.log (j : ℝ)) := by
  have hj0 : (0 : ℝ) < j := by exact_mod_cast hj
  have ht0 : 0 < Real.log (j : ℝ) := by linarith
  have hs0 := Real.sqrt_pos.2 ht0
  have hs2 := Real.sq_sqrt ht0.le
  have hX0 := highParticleThreshold_pos hj ht0
  have hl := log_le_half_of_pos ht0
  have hc : -Real.log (j : ℝ) / 4 +
      Real.log (Real.log (j : ℝ)) / 8 + C ≤ -Real.log (j : ℝ) / 8 := by
    linarith
  have he := mul_le_mul_of_nonneg_left hc hX0.le
  have hprod : highParticleThreshold j * Real.log (j : ℝ) =
      (j : ℝ) * Real.sqrt (Real.log (j : ℝ)) := by
    unfold highParticleThreshold
    apply (div_mul_eq_mul_div _ _ _).trans
    apply (div_eq_iff hs0.ne').mpr
    nlinarith
  rw [highParticleExponent, highParticleThreshold_log hj ht0]
  nlinarith

theorem complete_high_particle_window_tail {j N : ℕ} {C : ℝ}
    (hj : 0 < j) (ht : 256 ≤ Real.log (j : ℝ))
    (hC : 16 * (C + 1) ≤ Real.log (j : ℝ))
    (hN : 1 ≤ N) (hstart : highParticleThreshold j ≤ (N : ℝ) ^ 2) :
    Summable (fun m : ℕ => Real.exp (highParticleExponent j C (((N + m : ℕ) : ℝ) ^ 2))) ∧
      (∑' m : ℕ, Real.exp (highParticleExponent j C (((N + m : ℕ) : ℝ) ^ 2))) ≤
        Real.exp ((j : ℝ) * Real.log (j : ℝ) -
          (j : ℝ) / 2 * Real.log (Real.log (j : ℝ)) -
          (j : ℝ) / 8 * Real.sqrt (Real.log (j : ℝ))) *
            ∑' m : ℕ, Real.exp (-(m : ℝ)) := by
  have ht0 : 0 < Real.log (j : ℝ) := by linarith
  obtain ⟨hs, hb⟩ := complete_high_particle_tail_bound hN
    (highParticleThreshold_pos hj ht0) hstart (highParticleThreshold_decrease_gate hj ht hC)
  refine ⟨hs, hb.trans ?_⟩
  exact mul_le_mul_of_nonneg_right
    (Real.exp_le_exp.mpr (highParticleThreshold_exponent hj ht hC))
    (tsum_nonneg (fun _ => (Real.exp_pos _).le))

end
end IsingBulk.AnisoF002.NegativeHT
