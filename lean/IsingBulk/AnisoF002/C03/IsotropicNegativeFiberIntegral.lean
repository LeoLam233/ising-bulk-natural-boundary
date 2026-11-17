import IsingBulk.AnisoF002.C03.IsotropicPeriodicIntegral

/-!
# The negative-minimum reciprocal integral

The exact two-depth inequality reduces the negative extreme pair to
two reciprocal angular depths. Each has a logarithmic integral on the
bounded slice, including the maximum coordinate with its reversed
orientation. No phase monotonicity is required on this half.
-/

noncomputable section

namespace IsingBulk.AnisoF002.Isotropic

open scoped Topology
open Set Metric MeasureTheory

theorem reciprocal_pair_depth_bound (a c r : ℝ) (ha : 0 < a) (hc : 0 < c)
    (hr : 0 < r) (hsum : r ≤ a + c) :
    1 / (a * Real.sqrt c) ≤ (1 / Real.sqrt r) * (1 / a + 1 / c) := by
  have hroot : Real.sqrt r * Real.sqrt c ≤ a + c := by
    rw [← Real.sqrt_mul hr.le]
    apply (Real.sqrt_le_iff).mpr
    refine ⟨by positivity, ?_⟩
    have hh := mul_le_mul_of_nonneg_right hsum hc.le
    nlinarith only [hh, mul_pos ha hc, sq_nonneg a]
  have he : (1 / Real.sqrt r) * (1 / a + 1 / c) =
      (a + c) / (a * c * Real.sqrt r) := by field_simp; ring
  rw [he]
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  rw [one_mul]
  have hm := mul_le_mul_of_nonneg_left hroot (mul_nonneg ha.le (Real.sqrt_nonneg c))
  have hid : (a * Real.sqrt c) * (Real.sqrt r * Real.sqrt c) = a * c * Real.sqrt r := by
    calc
      _ = a * (Real.sqrt c ^ 2) * Real.sqrt r := by ring
      _ = _ := by rw [Real.sq_sqrt hc.le]
  rw [hid] at hm
  simpa only [mul_comm] using hm

def reciprocalAngularDepth (ε u : ℝ) : ℝ := 1 / (|u| + ε)

theorem reciprocalAngularDepth_continuous (ε : ℝ) (hε : 0 < ε) :
    Continuous (reciprocalAngularDepth ε) :=
  continuous_const.div (continuous_abs.add continuous_const)
    (fun u => (add_pos_of_nonneg_of_pos (abs_nonneg u) hε).ne')

theorem exists_reciprocalAngularDepth_log_integral (L : ℝ) (hL : 0 < L) :
    ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      ∀ A B : ℝ, A ≤ B → -L ≤ A → B ≤ L →
        (∫ u in A..B, reciprocalAngularDepth ε u) ≤ C * (1 + |Real.log ε|) := by
  obtain ⟨C₀, hC₀, hkernel⟩ := exists_periodicKernel_log_integral_bound (2 * L) (by positivity)
  refine ⟨C₀ * (1 + 2 * L), by positivity, ?_⟩
  intro ε hε hε1 A B hAB hA hB
  have he : (∫ u in A..B, reciprocalAngularDepth ε u) =
      ∫ u in A..B, periodicKernel (2 * L) ε u := by
    apply intervalIntegral.integral_congr
    intro u hu
    rw [uIcc_of_le hAB] at hu
    have habs : |u| ≤ (2 * L) / 2 := by
      apply abs_le.mpr
      constructor <;> linarith only [hA, hB, hu.1, hu.2]
    rw [periodicKernel, periodicDistance_fundamental (2 * L) u (by positivity) habs,
      reciprocalAngularDepth, add_comm ε |u|]
  rw [he]
  apply (hkernel ε hε hε1 A B hAB).trans
  have hlen : 1 + (B - A) ≤ 1 + 2 * L := by linarith only [hA, hB]
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlen hC₀.le) (by positivity)

/-- The two affine extreme coordinates integrate with the same
logarithmic cost, including the reversed maximum coordinate. -/
theorem exists_reciprocal_extreme_slice_integral (L : ℝ) (hL : 0 < L) :
    ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      ∀ x y A B : ℝ, A ≤ B →
        (∀ t ∈ Icc A B, |x + t| ≤ L ∧ |y - t| ≤ L) →
        (∫ t in A..B, reciprocalAngularDepth ε (x + t) + reciprocalAngularDepth ε (y - t)) ≤
          C * (1 + |Real.log ε|) := by
  obtain ⟨C₀, hC₀, hbound⟩ := exists_reciprocalAngularDepth_log_integral L hL
  refine ⟨2 * C₀, by positivity, ?_⟩
  intro ε hε hε1 x y A B hAB hslice
  have hcont := reciprocalAngularDepth_continuous ε hε
  have hcontL : Continuous (fun t : ℝ => reciprocalAngularDepth ε (x + t)) :=
    hcont.comp (continuous_const.add continuous_id)
  have hcontR : Continuous (fun t : ℝ => reciprocalAngularDepth ε (y - t)) :=
    hcont.comp (continuous_const.sub continuous_id)
  rw [intervalIntegral.integral_add (hcontL.intervalIntegrable A B) (hcontR.intervalIntegrable A B),
    intervalIntegral.integral_comp_add_left, intervalIntegral.integral_comp_sub_left]
  have hleft := hbound ε hε hε1 (x + A) (x + B) (by linarith only [hAB])
    (abs_le.mp (hslice A (left_mem_Icc.mpr hAB)).1).1
    (abs_le.mp (hslice B (right_mem_Icc.mpr hAB)).1).2
  have hright := hbound ε hε hε1 (y - B) (y - A) (by linarith only [hAB])
    (abs_le.mp (hslice B (right_mem_Icc.mpr hAB)).2).1
    (abs_le.mp (hslice A (left_mem_Icc.mpr hAB)).2).2
  linarith only [hleft, hright]

end IsingBulk.AnisoF002.Isotropic
