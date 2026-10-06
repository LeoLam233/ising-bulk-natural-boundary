import IsingBulk.First.ResidueBranch
import IsingBulk.First.SymmetryAlgebra

/-! The same admissible contour radius is valid on the symmetry orbit.
No global fixed radius on the entire exterior is postulated. -/
namespace IsingBulk.First
noncomputable section

structure ScalarResidueAdmissible (r : ℝ) (s : ℂ) (z : ℂ → ℂ) : Prop where
  radius_pos : 0 < r
  radius_lt_one : r < 1
  root_quadratic : ∀ y : ℂ, ‖y‖ = r → (z y)^2-(2*sourceS s-y-y⁻¹)*z y+1=0
  root_inside : ∀ y : ℂ, ‖y‖ = r → ‖z y‖ < r

theorem ScalarResidueAdmissible.toTuple {r : ℝ} {s : ℂ} {z : ℂ → ℂ}
    (h : ScalarResidueAdmissible r s z) (N : ℕ) (y : Fin N → ℂ)
    (hy : y ∈ productCircle N r) : ResidueAdmissible r s y (fun i => z (y i)) :=
  ⟨h.radius_pos, h.radius_lt_one, hy,
    fun i => h.root_quadratic (y i) (hy i), fun i => h.root_inside (y i) (hy i)⟩

theorem ScalarResidueAdmissible.neg {r : ℝ} {s : ℂ} {z : ℂ → ℂ}
    (h : ScalarResidueAdmissible r s z) :
    ScalarResidueAdmissible r (-s) (fun y => -z (-y)) := by
  refine ⟨h.radius_pos, h.radius_lt_one, ?_, ?_⟩
  · intro y hy
    have hh := h.root_quadratic (-y) (by simpa using hy)
    simp only [inv_neg] at hh
    simp only [sourceS_neg]
    linear_combination hh
  · intro y hy
    simpa only [norm_neg] using h.root_inside (-y) (by simpa using hy)

theorem ScalarResidueAdmissible.conjugate {r : ℝ} {s : ℂ} {z : ℂ → ℂ}
    (h : ScalarResidueAdmissible r s z) :
    ScalarResidueAdmissible r (star s) (fun y => star (z (star y))) := by
  refine ⟨h.radius_pos, h.radius_lt_one, ?_, ?_⟩
  · intro y hy
    have hh := congrArg (starRingEnd ℂ) (h.root_quadratic (star y) (by simpa using hy))
    simpa [sourceS, map_ofNat] using hh
  · intro y hy
    simpa using h.root_inside (star y) (by simpa using hy)

theorem admissible_common_radius {r : ℝ} {s : ℂ} {z : ℂ → ℂ}
    (h : ScalarResidueAdmissible r s z) :
    ScalarResidueAdmissible r (-s) (fun y => -z (-y)) ∧
    ScalarResidueAdmissible r (star s) (fun y => star (z (star y))) :=
  ⟨h.neg, h.conjugate⟩

end
end IsingBulk.First
