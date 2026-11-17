import IsingBulk.AnisoF002.C03.RegularEdgeNumerator
import IsingBulk.AnisoF002.C03.RegularMatchedGaussian

/-!
# The complete regular-edge numerator in the printed Gaussian form

This theorem quantifies a common edge-dependent rate before the derivative
order, every positive particle number, and all real angular tuples.  The
function bounded is the complete branch numerator with its exact finite
physical normalization, not an assumed envelope or replacement series.
-/

namespace IsingBulk.AnisoF002.RegularTail.C03
noncomputable section
open scoped Topology

namespace RegularEdgeControl
variable {c a : ℂ → ℂ} (d : RegularEdgeControl c a)

theorem fullNumerator_gaussian {M kappa : ℝ}
    (hmatched : ∀ n : ℕ,
      evenMatchedBound (d.prefactorBound * d.bodyBound) d.pairBound d.rho n ≤
        M * Real.exp (-kappa * (2 * (n : ℝ)) ^ 2) ∧
      oddMatchedBound (d.prefactorBound * d.bodyBound) d.pairBound d.rho n ≤
        M * Real.exp (-kappa * (2 * (n : ℝ) + 1) ^ 2))
    {N : ℕ} (x : Fin N → ℝ) {t : ℂ}
    (ht : t ∈ Metric.closedBall (0 : ℂ) (d.radius / 2)) (r : ℕ) :
    ‖iteratedDeriv r (fun u => edgeFullNumerator c a u x) t‖ ≤
      (r.factorial * M / (d.radius / 2) ^ r) * Real.exp (-kappa * (N : ℝ) ^ 2) := by
  have hh : ∀ n : ℕ, ∀ V : ℝ, ∀ v : ℝ,
      v ≤ M * Real.exp (-kappa * V ^ 2) →
        (r.factorial : ℝ) * v / (d.radius / 2) ^ r ≤
          (r.factorial * M / (d.radius / 2) ^ r) * Real.exp (-kappa * V ^ 2) := by
    intro _ V v hv
    calc
      (r.factorial : ℝ) * v / (d.radius / 2) ^ r ≤
          r.factorial * (M * Real.exp (-kappa * V ^ 2)) / (d.radius / 2) ^ r :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hv (Nat.cast_nonneg _))
          (pow_nonneg (half_pos d.radius_pos).le _)
      _ = _ := by ring
  rcases Nat.mod_two_eq_zero_or_one N with he | ho
  · obtain ⟨n, rfl⟩ : ∃ n : ℕ, N = 2 * n := ⟨N / 2, by omega⟩
    have h := (d.fullNumerator_even_jet_bound ht r n x).trans
      (hh n (2 * (n : ℝ)) _ (hmatched n).1)
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using h
  · obtain ⟨n, rfl⟩ : ∃ n : ℕ, N = 2 * n + 1 := ⟨N / 2, by omega⟩
    have h := (d.fullNumerator_odd_jet_bound ht r n x).trans
      (hh n (2 * (n : ℝ) + 1) _ (hmatched n).2)
    simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] using h

/-- Frozen Lemma 3.1's precise displayed form for the actual continued
regular-edge numerator.  Construction of the physical local chart is a
separate attachment, not a new physical premise of the terminal target. -/
theorem matched_pfaffian_numerator_estimate :
    ∃ kappa C : ℝ, 0 < kappa ∧ 0 < C ∧ ∀ r : ℕ, ∃ Cr : ℝ, 0 < Cr ∧
      ∀ N : ℕ, 0 < N → ∀ x : Fin N → ℝ,
        ∀ t ∈ Metric.closedBall (0 : ℂ) (d.radius / 2),
          ‖iteratedDeriv r (fun u => edgeFullNumerator c a u x) t‖ ≤
            Cr * Real.exp (-kappa * (N : ℝ) ^ 2 + C * (N : ℝ) * Real.log ((N : ℝ) + 1)) := by
  obtain ⟨M, kappa, hM, hk, hmatched⟩ := exists_matched_gaussian
    (mul_nonneg d.prefactorBound_pos.le d.bodyBound_pos.le) d.pairBound_pos.le
    d.rho_pos d.rho_lt_one
  refine ⟨kappa, 1, hk, by norm_num, ?_⟩
  intro r
  let Cr : ℝ := r.factorial * M / (d.radius / 2) ^ r
  have hCr : 0 < Cr := div_pos (mul_pos (Nat.cast_pos.mpr (Nat.factorial_pos r)) hM)
    (pow_pos (half_pos d.radius_pos) r)
  refine ⟨Cr, hCr, ?_⟩
  intro N _ x t ht
  have hlog : 0 ≤ Real.log ((N : ℝ) + 1) := Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) N])
  calc
    ‖iteratedDeriv r (fun u => edgeFullNumerator c a u x) t‖ ≤
        Cr * Real.exp (-kappa * (N : ℝ) ^ 2) := d.fullNumerator_gaussian hmatched x ht r
    _ ≤ Cr * Real.exp (-kappa * (N : ℝ) ^ 2 + 1 * (N : ℝ) * Real.log ((N : ℝ) + 1)) := by
      apply mul_le_mul_of_nonneg_left _ hCr.le
      apply Real.exp_le_exp.mpr
      have h := mul_nonneg (Nat.cast_nonneg (α := ℝ) N) hlog
      linarith

end RegularEdgeControl
end
end IsingBulk.AnisoF002.RegularTail.C03
