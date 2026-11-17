import IsingBulk.AnisoF002.C03.RegularConstrainedCoefficient

/-!
# The entire differentiated regular-edge coefficient tail

Both possible complementary particle parities are included with no gap.
The summable bounds apply to derivatives of the actual complete constrained
coefficients and are uniform down the physical inward path.
-/

namespace IsingBulk.AnisoF002.RegularTail.C03
noncomputable section
open scoped Topology BigOperators

theorem factorial_inv_mul_le {M : ℝ} (hM : 0 ≤ M) (N : ℕ) :
    (N.factorial : ℝ)⁻¹ * M ≤ M := by
  have hfac : (1 : ℝ) ≤ (N.factorial : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero N)
  have hi : (N.factorial : ℝ)⁻¹ ≤ 1 := by
    simpa only [one_div, inv_one] using
      one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hfac
  exact (mul_le_mul_of_nonneg_right hi hM).trans_eq (one_mul M)

namespace RegularEdgeCompleteControl
variable {b : ℝ} {a : ℂ → ℂ} (d : RegularEdgeCompleteControl b a)

/-- All complementary odd counts 2n+1 and even counts 2n+2, including
their first admissible values.  Every coefficient retains its factorial. -/
theorem complete_coefficient_tail_majorants {m j : ℕ}
    (hm : 0 < m) (hbudget : 2 * (j + 1) < m ^ 2) :
    ∃ Hodd Heven : ℕ → ℝ, Summable Hodd ∧ Summable Heven ∧
      (∀ n, 0 ≤ Hodd n) ∧ (∀ n, 0 ≤ Heven n) ∧
      ∀ eps : ℝ, 0 < eps → eps ≤ d.eps0 → ∀ n : ℕ,
        (‖iteratedDeriv j (edgeConstrainedCoefficient (affineEdgeCenter b) a m (2 * n))
            ((eps : ℂ) * Complex.I)‖ ≤
          ((m + (2 * n + 1)).factorial : ℝ)⁻¹ * Hodd n) ∧
        (‖iteratedDeriv j (edgeConstrainedCoefficient (affineEdgeCenter b) a m (2 * n + 1))
            ((eps : ℂ) * Complex.I)‖ ≤
          ((m + (2 * n + 1 + 1)).factorial : ℝ)⁻¹ * Heven n) := by
  obtain ⟨Ho, hso, hno, hbo⟩ := d.fullDensity_odd_jet_majorant hm j 0
  obtain ⟨He, hse, hne, hbe⟩ := d.fullDensity_even_jet_majorant hm j 0
  simp only [pow_zero, one_mul] at hso hse
  let I := d.collisionIntegral m j
  refine ⟨fun n => Ho n * I, fun n => He (n + 1) * I,
    hso.mul_right I, ?_, ?_, ?_, ?_⟩
  · exact (hse.comp_injective (fun n k h => Nat.add_right_cancel h)).mul_right I
  · intro n
    exact mul_nonneg (hno n) (d.collisionIntegral_nonneg m j)
  · intro n
    exact mul_nonneg (hne (n + 1)) (d.collisionIntegral_nonneg m j)
  · intro eps he he0 n
    constructor
    · exact d.constrained_coefficient_jet_bound hm hbudget he he0 (hbo eps he he0 n)
    · apply d.constrained_coefficient_jet_bound hm hbudget he he0
      have hh := hbe eps he he0 (n + 1)
      have hc : 2 * (n + 1) = 2 * n + 1 + 1 := by omega
      rw [hc] at hh
      exact hh

/-- A single finite bound controls the sum of norms of every derivative
of every larger particle coefficient, uniformly as the inward parameter
tends to zero.  No finite intermediate range is removed. -/
theorem complete_differentiated_tail_uniform {m j : ℕ}
    (hm : 0 < m) (hbudget : 2 * (j + 1) < m ^ 2) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ eps : ℝ, 0 < eps → eps ≤ d.eps0 →
      Summable (fun n : ℕ =>
        ‖iteratedDeriv j (edgeConstrainedCoefficient (affineEdgeCenter b) a m (2 * n))
          ((eps : ℂ) * Complex.I)‖) ∧
      Summable (fun n : ℕ =>
        ‖iteratedDeriv j (edgeConstrainedCoefficient (affineEdgeCenter b) a m (2 * n + 1))
          ((eps : ℂ) * Complex.I)‖) ∧
      (∑' n : ℕ, ‖iteratedDeriv j (edgeConstrainedCoefficient (affineEdgeCenter b) a m (2 * n))
          ((eps : ℂ) * Complex.I)‖) +
        (∑' n : ℕ, ‖iteratedDeriv j (edgeConstrainedCoefficient (affineEdgeCenter b) a m (2 * n + 1))
          ((eps : ℂ) * Complex.I)‖) ≤ M := by
  obtain ⟨Ho, He, hso, hse, hno, hne, hb⟩ := d.complete_coefficient_tail_majorants hm hbudget
  refine ⟨(∑' n, Ho n) + ∑' n, He n, add_nonneg (tsum_nonneg hno) (tsum_nonneg hne), ?_⟩
  intro eps he he0
  have hbo (n : ℕ) := ((hb eps he he0 n).1).trans (factorial_inv_mul_le (hno n) _)
  have hbe (n : ℕ) := ((hb eps he he0 n).2).trans (factorial_inv_mul_le (hne n) _)
  have ho := Summable.of_nonneg_of_le (fun n => norm_nonneg _) hbo hso
  have he' := Summable.of_nonneg_of_le (fun n => norm_nonneg _) hbe hse
  exact ⟨ho, he', add_le_add (ho.tsum_le_tsum hbo hso) (he'.tsum_le_tsum hbe hse)⟩

end RegularEdgeCompleteControl
end
end IsingBulk.AnisoF002.RegularTail.C03
