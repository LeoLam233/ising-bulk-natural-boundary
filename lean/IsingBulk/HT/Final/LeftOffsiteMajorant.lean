import IsingBulk.HT.Tail.OddExteriorMajorant
import IsingBulk.HT.Final.LeftOffsiteGeometry

/-! The actual odd offsite coefficients on left-trace charts use the
proved odd ghost majorant and actual unsigned global product gap. The root contraction,
residue identity and compact root bounds are the established all-N right
chart results. N=1 is retained with its physical normalization. -/
namespace IsingBulk.HT.Final
noncomputable section
open IsingBulk.First IsingBulk.Tail IsingBulk.HT.Tail
open scoped BigOperators

/-- The actual residue-reduced odd coefficients admit an exponential-series
majorant at every fixed admissible circle, including N=1. -/
theorem left_odd_doubleFormFactor_exponential_bound (n : ℕ)
    {r A : ℝ} (hr : 0 < r) (hr1 : r < 1) (hA : 0 ≤ A) {s : ℂ}
    (hm : 1 + r⁻¹ < -(sourceS s).re)
    (hi : ∀ y : ℂ, ‖y‖ = r → ‖(leftRoot s y)⁻¹‖ ≤ A) :
    let D := max 1 (2 * r / (1 - r ^ 2))
    let X := r * (max A r⁻¹) * (2 * r ^ 2 / (1 - r ^ 2))
    ‖doubleFormFactor (2 * n + 1) r s‖ ≤
      (2 * X * D / (1 - r) ^ 2) * ((X ^ 2 * D / 2) ^ n / (n.factorial : ℝ)) := by
  dsimp only
  have ha := leftRoot_admissible hr hr1 hm
  rw [residue_reduction (2 * n + 1) (by omega) r hr s (leftRoot s)
    (fun y hy => ha.toTuple (2 * n + 1) y hy)]
  have hb := multiCircleIntegral_norm_le (2 * n + 1) hr.le
    (fun y => reducedDensity (fun i => leftRoot s (y i)) y) (by
      intro y hy
      exact positive_reducedDensity_upper_bound (by omega) hr hr1 hA (by positivity)
        _ y (fun i => (leftRoot_inside_radius hr hr1 hm (hy i)).le) hy
        (fun i => hi (y i) (hy i)) (leftRoot_pairProduct_norm hr hr1 hm y hy)
        (odd_circle_pairProduct_matching_bound n hr.le hr1 y hy))
  have hnorm := mul_le_mul_of_nonneg_left hb
    (inv_nonneg.mpr (Nat.cast_nonneg (2 * n + 1).factorial))
  simp only [reducedFormFactor, norm_mul, norm_inv, Complex.norm_natCast]
  rw [odd_matching_majorant_identity] at hnorm
  convert hnorm using 1
  ring

end
end IsingBulk.HT.Final
