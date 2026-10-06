import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Determinant

/-! Explicit two-phase determinants in the real product basis. -/
namespace IsingBulk.Tail
noncomputable section
open Module

theorem det_two_coordinate_map (L : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)) (a b c d : ℝ)
    (hL : ∀ x : ℝ × ℝ, L x=(a*x.1+b*x.2,c*x.1+d*x.2)) :
    L.det=a*d-b*c := by
  have he : L.toLinearMap=Matrix.toLin (Basis.finTwoProd ℝ) (Basis.finTwoProd ℝ) !![a,b;c,d] := by
    apply LinearMap.ext
    intro x
    change L x = _
    rw [Matrix.toLin_finTwoProd_apply]
    exact hL x
  change LinearMap.det L.toLinearMap=_
  rw [he,LinearMap.det_toLin,Matrix.det_fin_two]
  rfl

theorem det_sum_slope_map (L : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)) (a b : ℝ)
    (hL : ∀ x : ℝ × ℝ, L x=(x.1+x.2,a*x.1+b*x.2)) : L.det=b-a := by
  simpa using det_two_coordinate_map L 1 1 a b (by simpa using hL)

theorem det_triangular_phase_map (L : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)) (N a b : ℝ)
    (hL : ∀ x : ℝ × ℝ, L x=(N*x.1,a*x.1+b*x.2)) : L.det=N*b := by
  simpa using det_two_coordinate_map L N 0 a b (by simpa using hL)

end
end IsingBulk.Tail
