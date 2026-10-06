import IsingBulk.First.NormalizedContour

/-! Norm estimates retain one factor of the radius for each normalized circle. -/
namespace IsingBulk.First
noncomputable section
open Set Metric

theorem normalizedCircleIntegral_norm_le {r C : ℝ} (hr : 0 ≤ r)
    (f : ℂ → ℂ) (hf : ∀ z, ‖z‖ = r → ‖f z‖ ≤ C) :
    ‖normalizedCircleIntegral r f‖ ≤ r*C := by
  apply circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const hr
  intro z hz
  exact hf z (by simpa [mem_sphere_iff_norm] using hz)

theorem multiCircleIntegral_norm_le (N : ℕ) {r C : ℝ} (hr : 0 ≤ r)
    (f : (Fin N → ℂ) → ℂ) (hf : ∀ x ∈ productCircle N r, ‖f x‖ ≤ C) :
    ‖multiCircleIntegral r N f‖ ≤ r^N*C := by
  induction N generalizing C with
  | zero => simpa [multiCircleIntegral] using hf Fin.elim0 (fun i => Fin.elim0 i)
  | succ n ih =>
    have h := ih (C := r*C) (fun x => normalizedCircleIntegral r
      (fun z => f (Fin.cons z x))) (by
        intro x hx
        apply normalizedCircleIntegral_norm_le hr
        intro z hz
        apply hf
        intro i
        exact Fin.cases hz (fun j => hx j) i)
    simpa [multiCircleIntegral, pow_succ, mul_assoc] using h

theorem doubleFormFactor_norm_le (N : ℕ) {r C : ℝ} (hr : 0 ≤ r) (s : ℂ)
    (hC : ∀ x ∈ productCircle N r, ∀ y ∈ productCircle N r,
      ‖doubleDensity s x y‖ ≤ C) :
    ‖doubleFormFactor N r s‖ ≤ (N.factorial:ℝ)⁻¹ * (r^N*(r^N*C)) := by
  have h := multiCircleIntegral_norm_le N hr
    (fun y => multiCircleIntegral r N (fun x => doubleDensity s x y)) (by
      intro y hy
      exact multiCircleIntegral_norm_le N hr _ (fun x hx => hC x hx y hy))
  simpa only [doubleFormFactor, norm_mul, norm_inv, Complex.norm_natCast] using
    mul_le_mul_of_nonneg_left h (inv_nonneg.mpr (Nat.cast_nonneg N.factorial))

end
end IsingBulk.First
