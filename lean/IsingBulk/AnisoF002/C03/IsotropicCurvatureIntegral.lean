import IsingBulk.AnisoF002.C03.IsotropicCorrectionCurvature
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# The exact extreme-coordinate curvature integral

The inverse-cubic square-root density is integrated by a genuine
antiderivative. Its endpoint expression is the same rational curvature
scale already controlling the full population correction.
-/

noncomputable section

namespace IsingBulk.AnisoF002.Isotropic

open scoped Topology
open Set Metric MeasureTheory

def positiveCurvatureWeight (E u : ℝ) : ℝ := 1 / Real.sqrt (u + E) ^ 3

theorem positiveCurvatureWeight_continuousOn {m M E : ℝ} (hm : 0 ≤ m) (hE : 0 < E) :
    ContinuousOn (positiveCurvatureWeight E) (Icc m M) := by
  apply continuousOn_const.div ((Real.continuous_sqrt.comp (continuous_id.add_const E)).continuousOn.pow 3)
  intro u hu
  apply pow_ne_zero
  change Real.sqrt (u + E) ≠ 0
  exact (Real.sqrt_pos.mpr (by linarith only [hm, hE, hu.1])).ne'

theorem positiveCurvatureWeight_hasAntideriv (E u : ℝ) (hu : 0 < u + E) :
    HasDerivAt (fun x : ℝ => -2 / Real.sqrt (x + E)) (positiveCurvatureWeight E u) u := by
  have hs : 0 < Real.sqrt (u + E) := Real.sqrt_pos.mpr hu
  have hd := (((hasDerivAt_id u).add_const E).sqrt hu.ne').inv hs.ne'
  convert! hd.const_mul (-2) using 1
  unfold positiveCurvatureWeight
  simp only [id_eq]
  field_simp

theorem positiveCurvatureScale_integral {m M E : ℝ}
    (hm : 0 ≤ m) (hM : m ≤ M) (hE : 0 < E) :
    (∫ u in m..M, positiveCurvatureWeight E u) = positiveCurvatureScale m M E := by
  have hcont := positiveCurvatureWeight_continuousOn (M := M) hm hE
  have hint : IntervalIntegrable (positiveCurvatureWeight E) volume m M := by
    apply ContinuousOn.intervalIntegrable
    simpa only [uIcc_of_le hM] using hcont
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun x : ℝ => -2 / Real.sqrt (x + E))
    (f' := positiveCurvatureWeight E) (a := m) (b := M)
    (by
      intro u hu
      rw [uIcc_of_le hM] at hu
      exact positiveCurvatureWeight_hasAntideriv E u (by linarith only [hm, hE, hu.1])) hint
  rw [hi]
  have hmE : 0 < m + E := by linarith only [hm, hE]
  have hME : 0 < M + E := by linarith only [hm, hM, hE]
  have ha : 0 < Real.sqrt (m + E) := Real.sqrt_pos.mpr hmE
  have hb : 0 < Real.sqrt (M + E) := Real.sqrt_pos.mpr hME
  have hs : Real.sqrt (m + E) + Real.sqrt (M + E) ≠ 0 := by positivity
  unfold positiveCurvatureScale
  field_simp
  nlinarith only [Real.sq_sqrt hmE.le, Real.sq_sqrt hME.le]

end IsingBulk.AnisoF002.Isotropic
