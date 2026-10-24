import IsingBulk.Anisotropic.Geometry.Definitions
import Mathlib.Tactic

namespace IsingBulk.Anisotropic
noncomputable section

theorem unit_trace (x : ℂ) (hx : ‖x‖ = 1) : x + x⁻¹ = 2 * (x.re : ℂ) := by
  rw [Complex.inv_eq_conj hx]
  apply Complex.ext <;> simp
  ring

theorem unit_re_mem_Icc (x : ℂ) (hx : ‖x‖ = 1) : x.re ∈ Set.Icc (-1 : ℝ) 1 := by
  have h := Complex.abs_re_le_norm x
  rw [hx, abs_le] at h
  exact h

/-- Nonvanishing of the literal two-circle spectral polynomial on the complement. -/
theorem torus_polynomial_ne_zero {lam : ℝ} {z : ℂ} (hz : z ∉ spectralSet lam)
    {x y : ℂ} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    spectralA lam z - spectralS z / 2 * (x + x⁻¹) -
      spectralT lam z / 2 * (y + y⁻¹) ≠ 0 := by
  intro h
  apply hz
  refine ⟨x.re, unit_re_mem_Icc x hx, y.re, unit_re_mem_Icc y hy, ?_⟩
  rw [unit_trace x hx, unit_trace y hy] at h
  linear_combination h

end
end IsingBulk.Anisotropic
