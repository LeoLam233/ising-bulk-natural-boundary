import IsingBulk.Anisotropic.NegativeNormalForm.RemovableEnergy
import Mathlib.Analysis.Complex.Schwarz
import Mathlib.Analysis.Calculus.MeanValue

namespace IsingBulk.Anisotropic.NegativeCycles
noncomputable section
open Set Metric Filter NegativeNormalForm
open scoped Topology

theorem analyticOnNhd_dslope {U : Set ℂ} {f : ℂ → ℂ} {T : ℂ}
    (hf : AnalyticOnNhd ℂ f U) (hT : T∈U) : AnalyticOnNhd ℂ (dslope f T) U := by
  intro t ht
  by_cases he : t=T
  · subst t
    exact analyticAt_dslope_center (hf T hT)
  · have ha : AnalyticAt ℂ (fun z => (f z-f T)/(z-T)) t :=
      ((hf t ht).sub analyticAt_const).div (analyticAt_id.sub analyticAt_const) (sub_ne_zero.mpr he)
    apply ha.congr
    filter_upwards [(dslope_eventuallyEq_slope_of_ne f he).symm] with w hw
    simpa only [slope_def_field] using hw

theorem analytic_disk_derivative_bound {f : ℂ → ℂ} {r M : ℝ} (hr : 0<r)
    (hf : AnalyticOnNhd ℂ f (ball 0 r)) (hb : ∀ z∈ball 0 r, ‖f z‖≤M)
    {x : ℂ} (hx : ‖x‖≤r/2) : ‖deriv f x‖≤4*M/r := by
  have hx' : x∈ball (0:ℂ) r := by simpa only [mem_ball,dist_zero_right] using (show ‖x‖<r by linarith)
  have hsub : ball x (r/2)⊆ball (0:ℂ) r := by
    intro z hz
    have hh : ‖z-x‖<r/2 := by simpa only [mem_ball,dist_eq_norm] using hz
    have hn := norm_le_norm_sub_add z x
    simpa only [mem_ball,dist_zero_right] using (show ‖z‖<r by linarith)
  have hdiff : DifferentiableOn ℂ f (ball x (r/2)) :=
    fun z hz => (hf z (hsub hz)).differentiableAt.differentiableWithinAt
  have hmaps : MapsTo f (ball x (r/2)) (closedBall (f x) (2*M)) := by
    intro z hz
    change dist (f z) (f x)≤2*M
    rw [dist_eq_norm]
    exact (norm_sub_le _ _).trans (by linarith [hb z (hsub hz),hb x hx'])
  have hh := Complex.norm_deriv_le_div_of_mapsTo_ball hdiff hmaps (by positivity : 0<r/2)
  convert hh using 1
  ring

theorem analytic_disk_dslope_bound {f : ℂ → ℂ} {r M : ℝ} (hr : 0<r)
    (hf : AnalyticOnNhd ℂ f (ball 0 r)) (hb : ∀ z∈ball 0 r, ‖f z‖≤M)
    {T t : ℂ} (hT : ‖T‖≤r/2) (ht : ‖t‖≤r/2) :
    ‖dslope f T t‖≤4*M/r := by
  by_cases he : t=T
  · subst t
    rw [dslope_same]
    exact analytic_disk_derivative_bound hr hf hb hT
  · have ha (z : ℂ) (hz : z∈closedBall 0 (r/2)) : DifferentiableAt ℂ f z := by
      have hz' : ‖z‖≤r/2 := by simpa only [mem_closedBall,dist_zero_right] using hz
      exact (hf z (by simpa only [mem_ball,dist_zero_right] using (show ‖z‖<r by linarith))).differentiableAt
    have hd (z : ℂ) (hz : z∈closedBall 0 (r/2)) : ‖deriv f z‖≤4*M/r :=
      analytic_disk_derivative_bound hr hf hb (by simpa only [mem_closedBall,dist_zero_right] using hz)
    have hh := Convex.norm_image_sub_le_of_norm_deriv_le ha hd (convex_closedBall (0:ℂ) (r/2))
      (show T∈closedBall 0 (r/2) by simpa using hT) (show t∈closedBall 0 (r/2) by simpa using ht)
    rw [dslope_of_ne _ he,slope_def_field,norm_div]
    exact (div_le_iff₀ (norm_pos_iff.mpr (sub_ne_zero.mpr he))).mpr hh

end
end IsingBulk.Anisotropic.NegativeCycles
