import IsingBulk.First.MeanSeparatedIntegral
import IsingBulk.First.MeanPhysicalDecomposition
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-! The three actual displaced sides lie in the separated annulus. -/
namespace IsingBulk.First
noncomputable section
open Set Complex MeasureTheory
open scoped Topology

def meanBottomCurve (delta : ℝ) (x : ℝ) : ℂ := (x:ℂ)-(delta:ℂ)*I
def meanRightCurve (delta : ℝ) (y : ℝ) : ℂ := (delta:ℂ)+(y:ℂ)*I
def meanLeftCurve (delta : ℝ) (y : ℝ) : ℂ := -(delta:ℂ)+(y:ℂ)*I

theorem meanBottomCurve_annulus {delta : ℝ} (hd : 0 < delta) :
    MapsTo (meanBottomCurve delta) (Icc (-delta) delta) (meanSeparatedAnnulus delta) := by
  intro x hx
  have hlo := abs_im_le_norm (meanBottomCurve delta x)
  have he : (meanBottomCurve delta x).im = -delta := by simp [meanBottomCurve]
  rw [he,abs_neg,abs_of_pos hd] at hlo
  have hup : ‖meanBottomCurve delta x‖ ≤ |x|+delta := by
    unfold meanBottomCurve
    simpa [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hd] using
      norm_sub_le (x:ℂ) ((delta:ℂ)*I)
  exact ⟨by linarith,by linarith [abs_le.mpr hx]⟩

theorem meanRightCurve_annulus {delta : ℝ} (hd : 0 < delta) :
    MapsTo (meanRightCurve delta) (Icc (-delta) 0) (meanSeparatedAnnulus delta) := by
  intro y hy
  have hlo := abs_re_le_norm (meanRightCurve delta y)
  have he : (meanRightCurve delta y).re = delta := by simp [meanRightCurve]
  rw [he,abs_of_pos hd] at hlo
  have hup : ‖meanRightCurve delta y‖ ≤ delta+|y| := by
    unfold meanRightCurve
    simpa [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hd] using
      norm_add_le (delta:ℂ) ((y:ℂ)*I)
  have habs : |y| ≤ delta := abs_le.mpr ⟨hy.1,by linarith [hy.2]⟩
  exact ⟨by linarith,by linarith⟩

theorem meanLeftCurve_annulus {delta : ℝ} (hd : 0 < delta) :
    MapsTo (meanLeftCurve delta) (Icc (-delta) 0) (meanSeparatedAnnulus delta) := by
  intro y hy
  have hlo := abs_re_le_norm (meanLeftCurve delta y)
  have he : (meanLeftCurve delta y).re = -delta := by simp [meanLeftCurve]
  rw [he,abs_neg,abs_of_pos hd] at hlo
  have hup : ‖meanLeftCurve delta y‖ ≤ delta+|y| := by
    unfold meanLeftCurve
    simpa [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hd] using
      norm_add_le (-(delta:ℂ)) ((y:ℂ)*I)
  have habs : |y| ≤ delta := abs_le.mpr ⟨hy.1,by linarith [hy.2]⟩
  exact ⟨by linarith,by linarith⟩

def meanBottomIntegral {n : ℕ} (s : ℂ) (rho alpha delta : ℝ) (t : Fin n → ℝ) : ℂ :=
  ∫ x in Icc (-delta) delta, meanLocalDensity s rho alpha t (meanBottomCurve delta x)
def meanRightIntegral {n : ℕ} (s : ℂ) (rho alpha delta : ℝ) (t : Fin n → ℝ) : ℂ :=
  ∫ x in Icc (-delta) 0, meanLocalDensity s rho alpha t (meanRightCurve delta x)
def meanLeftIntegral {n : ℕ} (s : ℂ) (rho alpha delta : ℝ) (t : Fin n → ℝ) : ℂ :=
  ∫ x in Icc (-delta) 0, meanLocalDensity s rho alpha t (meanLeftCurve delta x)

theorem displacedMeanSides_eq_compact {n : ℕ} (s : ℂ) (rho alpha delta : ℝ)
    (hd : 0 < delta) (t : Fin n → ℝ) :
    displacedMeanSides s rho alpha delta delta t =
      meanBottomIntegral s rho alpha delta t + I*meanRightIntegral s rho alpha delta t -
        I*meanLeftIntegral s rho alpha delta t := by
  unfold displacedMeanSides meanBottomIntegral meanRightIntegral meanLeftIntegral
    meanBottomCurve meanRightCurve meanLeftCurve
  simp only [intervalIntegral.integral_of_le (show -delta ≤ delta by linarith),
    intervalIntegral.integral_of_ge (show -delta ≤ 0 by linarith)]
  simp only [integral_Icc_eq_integral_Ioc]
  ring

theorem analytic_three_sides_iterated_bound {B R L : ℂ → ℂ} {s : ℂ}
    (hB : AnalyticAt ℂ B s) (hR : AnalyticAt ℂ R s) (hL : AnalyticAt ℂ L s)
    (j : ℕ) {CB CR CL : ℝ}
    (hb : ‖(deriv^[j] B) s‖ ≤ CB) (hr : ‖(deriv^[j] R) s‖ ≤ CR)
    (hl : ‖(deriv^[j] L) s‖ ≤ CL) :
    ‖(deriv^[j] (fun z => B z + I*R z-I*L z)) s‖ ≤ CB+CR+CL := by
  simp only [← iteratedDeriv_eq_iterate] at *
  have hBR : ContDiffAt ℂ j (fun z => B z+I*R z) s :=
    (hB.add ((analyticAt_const (v := I)).mul hR)).contDiffAt
  have hRI : ContDiffAt ℂ j (fun z => I*R z) s :=
    ((analyticAt_const (v := I)).mul hR).contDiffAt
  have hLI : ContDiffAt ℂ j (fun z => I*L z) s :=
    ((analyticAt_const (v := I)).mul hL).contDiffAt
  rw [iteratedDeriv_fun_sub hBR hLI,
    iteratedDeriv_fun_add hB.contDiffAt hRI,
    iteratedDeriv_const_mul_field,iteratedDeriv_const_mul_field]
  have hn := norm_sub_le (iteratedDeriv j B s+I*iteratedDeriv j R s) (I*iteratedDeriv j L s)
  have hn' := norm_add_le (iteratedDeriv j B s) (I*iteratedDeriv j R s)
  simp only [norm_mul,norm_I,one_mul] at hn hn'
  linarith

end
end IsingBulk.First
