import IsingBulk.First.InteriorRoot
import IsingBulk.First.MixedRadiusDamping
import IsingBulk.First.ResidueAdmissibility

/-! Constructed admissible interior roots on the entire original y circle. -/
namespace IsingBulk.First
noncomputable section

/-- The actual global root uses the continued interior quadratic branch. -/
def globalRoot (s y : ℂ) : ℂ := interiorRoot (sourceW s y)

theorem sourceW_upper_of_margin {r : ℝ} (hr : 0 < r) (hr1 : r < 1) {s y : ℂ}
    (hmargin : r⁻¹-r < (sourceS s).im) (hy : ‖y‖=r) : 0 < (sourceW s y).im := by
  have hh := dispersion_im_positive_on_annulus hr (x := (1:ℂ)) (y := y)
    (by simpa using hr1.le) (by rw [hy]) (by simp) (by rw [hy]; exact hr1.le) hmargin
  simpa [dispersion, sourceW] using hh

theorem globalRoot_quadratic (s y : ℂ) :
    (globalRoot s y)^2-(2*sourceS s-y-y⁻¹)*globalRoot s y+1=0 := by
  have h := interiorRoot_quadratic (sourceW s y)
  dsimp only [globalRoot]
  unfold sourceW at *
  linear_combination h

theorem globalRoot_nonzero (s y : ℂ) : globalRoot s y ≠ 0 := interiorRoot_nonzero _

theorem globalRoot_dispersion (s y : ℂ) : dispersion (globalRoot s y) y s = 0 := by
  have ht := interiorRoot_trace (sourceW s y)
  change globalRoot s y+(globalRoot s y)⁻¹=2*sourceW s y at ht
  unfold dispersion sourceW at *
  linear_combination -ht/2

/-- Strict enclosure follows from the actual annulus damping, rather than
assuming a stronger norm bound as setup. -/
theorem globalRoot_inside_radius {r : ℝ} (hr : 0 < r) (hr1 : r < 1) {s y : ℂ}
    (hmargin : r⁻¹-r < (sourceS s).im) (hy : ‖y‖=r) : ‖globalRoot s y‖ < r := by
  have hW := sourceW_upper_of_margin hr hr1 hmargin hy
  have hn : ‖globalRoot s y‖ < 1 := interiorRoot_norm_lt_one hW
  by_contra hinside
  have hh := dispersion_im_positive_on_annulus hr (le_of_not_gt hinside) (by rw [hy])
    hn.le (by rw [hy]; exact hr1.le) hmargin
  rw [globalRoot_dispersion] at hh
  exact lt_irrefl (0:ℝ) hh

/-- Complete source admissibility is constructed from an explicit parameter/radius
margin, uniformly over every point of the y circle. -/
theorem globalRoot_admissible {r : ℝ} (hr : 0 < r) (hr1 : r < 1) {s : ℂ}
    (hmargin : r⁻¹-r < (sourceS s).im) : ScalarResidueAdmissible r s (globalRoot s) :=
  ⟨hr, hr1, fun y _ => globalRoot_quadratic s y,
    fun _y hy => globalRoot_inside_radius hr hr1 hmargin hy⟩

theorem globalRoot_y_differentiableAt {s y : ℂ} (hy : y ≠ 0)
    (hW : 0 < (sourceW s y).im) : DifferentiableAt ℂ (globalRoot s) y := by
  have hinner : DifferentiableAt ℂ (sourceW s) y := by
    unfold sourceW
    exact ((differentiableAt_id.add (differentiableAt_inv hy)).div_const 2).const_sub _
  exact (interiorRoot_differentiableAt hW).comp y hinner

theorem globalRoot_parameter_differentiableAt {s y : ℂ} (hs : s ≠ 0)
    (hW : 0 < (sourceW s y).im) : DifferentiableAt ℂ (fun t => globalRoot t y) s := by
  have hinner : DifferentiableAt ℂ (fun t => sourceW t y) s := by
    unfold sourceW sourceS
    exact (differentiableAt_id.add (differentiableAt_inv hs)).sub_const _
  exact (interiorRoot_differentiableAt hW).comp s hinner

/-- The global root is continuous jointly on its actual regular upper domain. -/
theorem globalRoot_joint_continuousAt {s y : ℂ} (hs : s ≠ 0) (hy : y ≠ 0)
    (hW : 0 < (sourceW s y).im) :
    ContinuousAt (fun p : ℂ × ℂ => globalRoot p.1 p.2) (s,y) := by
  have hin : ContinuousAt (fun p : ℂ × ℂ => sourceW p.1 p.2) (s,y) := by
    unfold sourceW sourceS
    exact (continuousAt_fst.add (continuousAt_fst.inv₀ hs)).sub
      ((continuousAt_snd.add (continuousAt_snd.inv₀ hy)).div_const 2)
  have hout : ContinuousAt interiorRoot (sourceW s y) :=
    (interiorRoot_differentiableAt hW).continuousAt
  exact hout.comp_of_eq hin rfl

end
end IsingBulk.First
