import IsingBulk.HT.Final.UpperFullSeries
import IsingBulk.HT.Tail.OddIndexing

/-!
# Exact full-site infinite-tail reduction

All sums here are the actual canonical onsite/full-site coefficients,
identified with the fixed-radius contours by `HT.Final.UpperFullSeries`.
Their absolute convergence is proved before any sum is compared or split.
The norm domination below is unconditional on the upper-trace domain. It
does not itself assert the boundary-uniform onsite estimate, supplied
separately by OnsiteReflection and assembled in FullOddTailAssembly.
-/
namespace IsingBulk.HT.Tail
noncomputable section
open IsingBulk.First IsingBulk.HT.Final
open scoped Topology

theorem upper_onsite_odd_tail_summable {p : ℕ} (hp : Odd p) (j : ℕ)
    {s : ℂ} (hs : 0 < (sourceS s).im) :
    Summable (fun n : ℕ =>
      ‖iteratedDeriv j (upperOnsiteFormFactor (oddTailParticle p n)) s‖) := by
  have h := (upperOnsiteOdd_derivative_summable j hs).comp_injective
    (show Function.Injective (fun n : ℕ => n + (p+1)/2) from
      fun _ _ h => Nat.add_right_cancel h)
  simpa only [Function.comp_def, oddTailParticle_eq_index hp] using h

theorem upper_full_odd_tail_summable {p : ℕ} (hp : Odd p) (j : ℕ)
    {s : ℂ} (hs : 0 < (sourceS s).im) :
    Summable (fun n : ℕ =>
      ‖iteratedDeriv j (upperFullCoefficient (oddTailParticle p n)) s‖) := by
  have h := (upperFullOdd_derivative_summable j hs).comp_injective
    (show Function.Injective (fun n : ℕ => n + (p+1)/2) from
      fun _ _ h => Nat.add_right_cancel h)
  simpa only [Function.comp_def, oddTailParticle_eq_index hp] using h

/-- The coefficient identity extends to the complete differentiated
infinite tail because both source series converge absolutely. -/
theorem upper_full_odd_complex_tail_decomposition {p : ℕ} (hp : Odd p) (j : ℕ)
    {s : ℂ} (hs : 0 < (sourceS s).im) :
    (∑' n : ℕ, iteratedDeriv j (upperFullCoefficient (oddTailParticle p n)) s) =
      (∑' n : ℕ, iteratedDeriv j (upperOnsiteFormFactor (oddTailParticle p n)) s) +
      2 * ∑' n : ℕ, iteratedDeriv j (upperFormFactor (oddTailParticle p n)) s := by
  have hO := (upper_onsite_odd_tail_summable hp j hs).of_norm
  have hD : Summable (fun n : ℕ =>
      iteratedDeriv j (upperFormFactor (oddTailParticle p n)) s) := by
    have h := (upperOdd_derivative_summable j hs).of_norm.comp_injective
      (show Function.Injective (fun n : ℕ => n + (p+1)/2) from
        fun _ _ h => Nat.add_right_cancel h)
    simpa only [Function.comp_def, oddTailParticle_eq_index hp] using h
  calc
    _ = ∑' n : ℕ,
        (iteratedDeriv j (upperOnsiteFormFactor (oddTailParticle p n)) s +
          2 * iteratedDeriv j (upperFormFactor (oddTailParticle p n)) s) := by
      apply tsum_congr
      intro n
      exact upperFullCoefficient_iteratedDeriv _
        (by have := oddTailParticle_gt p n; omega) j hs
    _ = _ := by rw [hO.tsum_add (hD.mul_left 2), tsum_mul_left]

/-- Exact onsite comparison: the full-site tail is dominated by
the whole onsite derivative norm series plus twice the already-controlled
offsite tail. The onsite series is kept literally on the right-hand side;
neither pointwise smoothness nor compact-interior bounds are used to claim
its boundary asymptotic. -/
theorem upper_full_odd_tail_norm_domination {p : ℕ} (hp : Odd p) (j : ℕ)
    {s : ℂ} (hs : 0 < (sourceS s).im) :
    (∑' n : ℕ, ‖iteratedDeriv j (upperFullCoefficient (oddTailParticle p n)) s‖) ≤
      (∑' n : ℕ, ‖iteratedDeriv j (upperOnsiteFormFactor (2*n+1)) s‖) +
      2 * ∑' n : ℕ, ‖iteratedDeriv j (upperFormFactor (oddTailParticle p n)) s‖ := by
  have hO := upper_onsite_odd_tail_summable hp j hs
  have hC := upper_full_odd_tail_summable hp j hs
  have hD : Summable (fun n : ℕ =>
      ‖iteratedDeriv j (upperFormFactor (oddTailParticle p n)) s‖) := by
    have h := (upperOdd_derivative_summable j hs).comp_injective
      (show Function.Injective (fun n : ℕ => n + (p+1)/2) from
        fun _ _ h => Nat.add_right_cancel h)
    simpa only [Function.comp_def, oddTailParticle_eq_index hp] using h
  have hpoint (n : ℕ) :
      ‖iteratedDeriv j (upperFullCoefficient (oddTailParticle p n)) s‖ ≤
      ‖iteratedDeriv j (upperOnsiteFormFactor (oddTailParticle p n)) s‖ +
        2 * ‖iteratedDeriv j (upperFormFactor (oddTailParticle p n)) s‖ := by
    rw [upperFullCoefficient_iteratedDeriv _
      (by have := oddTailParticle_gt p n; omega) j hs]
    simpa only [norm_mul, Complex.norm_ofNat] using norm_add_le
      (iteratedDeriv j (upperOnsiteFormFactor (oddTailParticle p n)) s)
      (2 * iteratedDeriv j (upperFormFactor (oddTailParticle p n)) s)
  have hsum := Summable.tsum_le_tsum hpoint hC (hO.add (hD.mul_left 2))
  rw [hO.tsum_add (hD.mul_left 2), tsum_mul_left] at hsum
  have hOle :
      (∑' n : ℕ, ‖iteratedDeriv j (upperOnsiteFormFactor (oddTailParticle p n)) s‖) ≤
      ∑' n : ℕ, ‖iteratedDeriv j (upperOnsiteFormFactor (2*n+1)) s‖ := by
    apply hO.tsum_le_tsum_of_inj (fun n : ℕ => n + (p+1)/2)
      (fun _ _ h => Nat.add_right_cancel h) (fun _ _ => norm_nonneg _)
      (fun n => ?_) (upperOnsiteOdd_derivative_summable j hs)
    rw [oddTailParticle_eq_index hp]
  exact hsum.trans (add_le_add hOle le_rfl)

end
end IsingBulk.HT.Tail
