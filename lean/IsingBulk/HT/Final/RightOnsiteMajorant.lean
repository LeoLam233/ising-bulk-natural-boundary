import IsingBulk.HT.Final.UpperOnsiteMajorant
import IsingBulk.Tail.RightReducedMajorant

namespace IsingBulk.HT.Final
noncomputable section
open IsingBulk.First IsingBulk.Tail IsingBulk.HT.Tail
open scoped BigOperators

/-- Uniform in all odd particle orders, including the physical N=1 term. -/
theorem right_odd_onsiteFormFactor_exponential_bound (n : ℕ)
    {r A : ℝ} (hr : 0 < r) (hr1 : r < 1) (hA : 0 ≤ A) {s : ℂ}
    (hm : 1+r⁻¹ < (sourceS s).re)
    (hi : ∀ y : ℂ, ‖y‖=r → ‖(rightRoot s y)⁻¹‖ ≤ A) :
    let D := max 1 (2*r/(1-r^2))
    let X := r*(A*r⁻¹)*(2*r^2/(1-r^2))
    ‖onsiteFormFactor (2*n+1) r s‖ ≤
      (X*D)*((X^2*D/2)^n/(n.factorial:ℝ)) := by
  dsimp only
  have ha := rightRoot_admissible hr hr1 hm
  rw [onsite_residue_reduction (2*n+1) r hr s (rightRoot s)
    (fun y hy => ha.toTuple (2*n+1) y hy)]
  have hb := multiCircleIntegral_norm_le (2*n+1) hr.le
    (fun y => reducedOnsiteDensity (fun i => rightRoot s (y i)) y) (by
      intro y hy
      exact reducedOnsiteDensity_upper_bound hr hr1 hA (by positivity)
        _ y (fun i => (rightRoot_inside_radius hr hr1 hm (hy i)).le) hy
        (fun i => hi (y i) (hy i)) (rightRoot_pairProduct_norm hr hr1 hm y hy)
        (odd_circle_pairProduct_matching_bound n hr.le hr1 y hy))
  have hnorm := mul_le_mul_of_nonneg_left hb
    (inv_nonneg.mpr (Nat.cast_nonneg (2*n+1).factorial))
  simp only [reducedOnsiteFormFactor, norm_mul, norm_inv, Complex.norm_natCast]
  rw [odd_onsite_matching_majorant_identity] at hnorm
  exact hnorm

end
end IsingBulk.HT.Final
