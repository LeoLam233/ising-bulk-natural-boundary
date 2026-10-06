import IsingBulk.First.SmallRadiusDensityBounds
import IsingBulk.First.FarExteriorAnnularDensity

/-! The actual quarter-radius double-contour density has a uniform geometric
majorant throughout the far exterior. This concerns the symmetry germ only. -/
namespace IsingBulk.First
noncomputable section

/-- No dispersion or majorant premise remains in the far-exterior bound. -/
theorem farExterior_doubleDensity_quarter_bound (N : ℕ) (hN : 0 < N)
    {s : ℂ} (hs : 16 < ‖s‖) (x y : Fin N → ℂ)
    (hx : ∀ i, ‖x i‖ = (1/4:ℝ)) (hy : ∀ i, ‖y i‖ = (1/4:ℝ)) :
    ‖doubleDensity s x y‖ ≤ 8*(4:ℝ)^N := by
  apply doubleDensity_quarter_norm_bound_of_dispersion hN s x y hx hy
  intro i
  apply farExterior_dispersion_norm_lower hs
  · rw [hx i]
    norm_num
  · rw [hy i]
    norm_num

end
end IsingBulk.First
