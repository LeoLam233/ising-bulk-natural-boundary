import IsingBulk.Tail.ExteriorReducedMajorant
import IsingBulk.Tail.RightExteriorRoots

/-! The same exact one-Pfaffian normal-convergence majorant on charts
crossing the positive real exterior axis. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First
open scoped BigOperators

theorem compact_rightRoot_inverse_bound {K : Set ℂ} (hK : IsCompact K)
    {r : ℝ} (hr : 0 < r) (hr1 : r < 1) (hs : ∀ s ∈ K, s ≠ 0)
    (hm : ∀ s ∈ K, 1+r⁻¹ < (sourceS s).re) :
    ∃ A, 0 < A ∧ ∀ s ∈ K, ∀ y : ℂ, ‖y‖=r → ‖(rightRoot s y)⁻¹‖ ≤ A := by
  obtain ⟨M,hM0,hM⟩ := compact_sourceW_bound hK hr hs
  refine ⟨2*M+r, by positivity, ?_⟩
  intro s hsk y hy
  exact quadratic_inverse_norm_bound (compactLeftRoot_quadratic (sourceW s y))
    (hM s hsk y hy) (rightRoot_inside_radius hr hr1 (hm s hsk) hy).le

theorem right_even_doubleFormFactor_matching_bound (n : ℕ) (hn : 0 < n)
    {r A : ℝ} (hr : 0 < r) (hr1 : r < 1) (hA : 0 ≤ A) {s : ℂ}
    (hm : 1+r⁻¹ < (sourceS s).re)
    (hi : ∀ y : ℂ, ‖y‖=r → ‖(rightRoot s y)⁻¹‖ ≤ A) :
    ‖doubleFormFactor (2*n) r s‖ ≤ ((2*n).factorial:ℝ)⁻¹ *
      (r^(2*n)*((2*(max A r⁻¹)^(2*n)/(1-r^2)^2)*
        ((matchingCount n:ℝ)*(2*r/(1-r^2))^n)*(2*r^2/(1-r^2))^(2*n))) := by
  have hg : 0 < 1-r^2 := by nlinarith
  have ha := rightRoot_admissible hr hr1 hm
  rw [residue_reduction (2*n) (by omega) r hr s (rightRoot s)
    (fun y hy => ha.toTuple (2*n) y hy)]
  have hb := multiCircleIntegral_norm_le (2*n) hr.le
    (fun y => reducedDensity (fun i => rightRoot s (y i)) y) (by
      intro y hy
      exact reducedDensity_upper_bound (by omega) hr hr1 hA (by positivity)
        _ y (fun i => (rightRoot_inside_radius hr hr1 hm (hy i)).le) hy
        (fun i => hi (y i) (hy i)) (rightRoot_pairProduct_norm hr hr1 hm y hy)
        (circle_pairProduct_matching_bound n hr.le hr1 y hy))
  simpa only [reducedFormFactor, norm_mul, norm_inv, Complex.norm_natCast] using
    mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr (Nat.cast_nonneg (2*n).factorial))

theorem right_even_doubleFormFactor_exponential_bound (n : ℕ) (hn : 0 < n)
    {r A : ℝ} (hr : 0 < r) (hr1 : r < 1) (hA : 0 ≤ A) {s : ℂ}
    (hm : 1+r⁻¹ < (sourceS s).re)
    (hi : ∀ y : ℂ, ‖y‖=r → ‖(rightRoot s y)⁻¹‖ ≤ A) :
    ‖doubleFormFactor (2*n) r s‖ ≤ (2/(1-r^2)^2)*
      (((r*(max A r⁻¹)*(2*r^2/(1-r^2)))^2*(2*r/(1-r^2))/2)^n/(n.factorial:ℝ)) := by
  have hb := right_even_doubleFormFactor_matching_bound n hn hr hr1 hA hm hi
  rw [matching_majorant_identity] at hb
  exact hb

end
end IsingBulk.Tail
