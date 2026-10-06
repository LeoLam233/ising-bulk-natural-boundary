import IsingBulk.First.ContourDefinitions
import Mathlib.Tactic

/-! Exact dispersion factorization and complete-pair algebra. These support,
but do not replace, the integral residue theorem. -/
namespace IsingBulk.First
noncomputable section
open scoped BigOperators
open Complex

theorem quadratic_root_ne_zero {W z : ℂ} (h : z^2 - 2*W*z + 1 = 0) : z ≠ 0 := by
  intro hz
  simp [hz] at h

theorem quadratic_root_trace {W z : ℂ} (h : z^2 - 2*W*z + 1 = 0) :
    z + z⁻¹ = 2*W := by
  have hz := quadratic_root_ne_zero h
  apply (mul_left_cancel₀ hz)
  rw [mul_add, mul_inv_cancel₀ hz]
  linear_combination h

theorem quadratic_root_unique {W z w : ℂ}
    (hz : z^2 - 2*W*z + 1 = 0) (hw : w^2 - 2*W*w + 1 = 0)
    (hzn : ‖z‖ < 1) (hwn : ‖w‖ < 1) : z = w := by
  have hz0 := quadratic_root_ne_zero hz
  have hw0 := quadratic_root_ne_zero hw
  have ht := quadratic_root_trace hz
  have ht' := quadratic_root_trace hw
  have hf : (z-w)*(z*w-1) = 0 := by
    field_simp at ht ht'
    linear_combination w * ht - z * ht'
  rcases mul_eq_zero.mp hf with h | h
  · exact sub_eq_zero.mp h
  · have he : z*w = 1 := sub_eq_zero.mp h
    have hlt : ‖z*w‖ < 1 := by
      rw [norm_mul]
      nlinarith [norm_nonneg z, norm_nonneg w]
    simp [he] at hlt

theorem ResidueAdmissible.root_ne_zero {N : ℕ} {r : ℝ} {s : ℂ}
    {y z : Fin N → ℂ} (h : ResidueAdmissible r s y z) (i : Fin N) : z i ≠ 0 := by
  intro hz
  have hi := h.root_quadratic i
  simp [hz] at hi

theorem ResidueAdmissible.y_ne_zero {N : ℕ} {r : ℝ} {s : ℂ}
    {y z : Fin N → ℂ} (h : ResidueAdmissible r s y z) (i : Fin N) : y i ≠ 0 := by
  intro hy
  have hi := h.y_on_circle i
  simp [hy] at hi
  linarith [h.radius_pos]

theorem dispersion_factorization {x y z s : ℂ} (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0)
    (hroot : z^2 - (2*sourceS s-y-y⁻¹)*z + 1 = 0) :
    dispersion x y s = -(x-z)*(x-z⁻¹)/(2*x) := by
  have hroot' := hroot
  field_simp at hroot'
  unfold dispersion
  field_simp
  linear_combination -x * hroot'

theorem source_pair_identity {a b z w s : ℂ}
    (ha : a ≠ 0) (hb : b ≠ 0) (_hz : z ≠ 0) (_hw : w ≠ 0)
    (hzq : z^2 - (2*sourceS s-a-a⁻¹)*z + 1 = 0)
    (hwq : w^2 - (2*sourceS s-b-b⁻¹)*w + 1 = 0)
    (hab : 1-a*b ≠ 0) (hzw : 1-z*w ≠ 0) :
    pairKernel z w * pairKernel a b = -(a-b)^2*z*w/(a*b*(1-z*w)^2) := by
  have hzq' := hzq
  have hwq' := hwq
  field_simp at hzq' hwq'
  have hsub : (z-w)*(1-z*w)*a*b = -z*w*(a-b)*(1-a*b) := by
    linear_combination a*z*hwq' - b*w*hzq'
  unfold pairKernel
  field_simp
  linear_combination (a-b) * hsub

theorem normalization_numerator_identity {X Y : ℂ}
    (hX : X ≠ 0) (hY : Y ≠ 0) (h1X : 1-X ≠ 0) (h1Y : 1-Y ≠ 0) :
    (1+X⁻¹)*(1+Y⁻¹)/((1-X)*(1-Y)) =
      (X*Y)⁻¹ + 2*(X⁻¹+Y⁻¹)/((1-X)*(1-Y)) := by
  field_simp
  ring

theorem standardDensity_eq_onsite_add_double {N : ℕ} (s : ℂ) (x y : Fin N → ℂ)
    (hX : coordinateProduct x ≠ 0) (hY : coordinateProduct y ≠ 0)
    (h1X : 1-coordinateProduct x ≠ 0) (h1Y : 1-coordinateProduct y ≠ 0) :
    standardDensity s x y = onsiteDensity s x y + 2 * doubleDensity s x y := by
  unfold standardDensity onsiteDensity doubleDensity
  rw [normalization_numerator_identity hX hY h1X h1Y]
  ring

end
end IsingBulk.First
