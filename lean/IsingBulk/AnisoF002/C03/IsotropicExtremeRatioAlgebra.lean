import IsingBulk.AnisoF002.C03.IsotropicCurvatureIntegral

/-!
# Exact cancellation in the extreme-coordinate Jacobian ratio

The two square-root Jacobian factors cancel against the integrated
curvature denominator. This algebra retains the correct gap power and
only one square root of the upper extreme scale.
-/

noncomputable section

namespace IsingBulk.AnisoF002.Isotropic

theorem extreme_jacobian_curvature_ratio {m M E A c F P : ℝ}
    (hm : 0 ≤ m) (hmM : m < M) (hE : 0 < E) (hc : 0 < c)
    (hF : F ≤ A ^ 2 / (Real.sqrt (m + E) * Real.sqrt (M + E)))
    (hP : c * positiveCurvatureScale m M E ≤ P) :
    0 < P ∧ F / P ≤ (A ^ 2 / c) * Real.sqrt (M + E) / (M - m) := by
  have hL := positiveCurvatureScale_pos hm hmM hE
  have hden : 0 < c * positiveCurvatureScale m M E := mul_pos hc hL
  have hPpos : 0 < P := hden.trans_le hP
  have ha : 0 < Real.sqrt (m + E) := Real.sqrt_pos.mpr (by linarith only [hm, hE])
  have hb : 0 < Real.sqrt (M + E) := Real.sqrt_pos.mpr (by linarith only [hm, hmM, hE])
  have hgap : 0 < M - m := sub_pos.mpr hmM
  have hab : Real.sqrt (m + E) ≤ Real.sqrt (M + E) := Real.sqrt_le_sqrt (by linarith only [hmM])
  have hs : Real.sqrt (m + E) + Real.sqrt (M + E) ≠ 0 := by positivity
  refine ⟨hPpos, ?_⟩
  calc
    _ ≤ (A ^ 2 / (Real.sqrt (m + E) * Real.sqrt (M + E))) /
        (c * positiveCurvatureScale m M E) :=
      div_le_div₀ (by positivity) hF hden hP
    _ = (A ^ 2 / c) * ((Real.sqrt (m + E) + Real.sqrt (M + E)) / (2 * (M - m))) := by
      unfold positiveCurvatureScale
      field_simp
    _ ≤ (A ^ 2 / c) * ((2 * Real.sqrt (M + E)) / (2 * (M - m))) :=
      mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_right (by linarith only [hab]) (by positivity)) (by positivity)
    _ = _ := by field_simp

end IsingBulk.AnisoF002.Isotropic
