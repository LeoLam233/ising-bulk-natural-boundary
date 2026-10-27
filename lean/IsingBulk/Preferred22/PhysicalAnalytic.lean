import IsingBulk.Preferred22.PhysicalKernel
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

/-! Local analytic identification of the globally selected interior root.
The auxiliary square root is centered at 1, so this proof does not exclude
imaginary dispersion values or introduce an artificial global square-root cut. -/
namespace IsingBulk.Preferred22
noncomputable section
open Complex Filter Set
open scoped Topology

theorem physicalRoot_quadratic (W : ℂ) :
    (physicalRoot W)^2 - 2*W*physicalRoot W + 1 = 0 := by
  have h := congrArg (fun u : ℂ => u * physicalRoot W) (physicalRoot_trace W)
  rw [add_mul, inv_mul_cancel₀ (physicalRoot_ne_zero W)] at h
  linear_combination h

theorem physicalRoot_discriminant (W : ℂ) : (physicalRoot W-W)^2 = W^2-1 := by
  linear_combination physicalRoot_quadratic W

theorem offRealSegment_discriminant_ne_zero {W : ℂ} (hW : OffRealSegment W) : W^2-1 ≠ 0 := by
  intro h
  have hp : (W-1)*(W+1) = 0 := by linear_combination h
  rcases mul_eq_zero.mp hp with h | h
  · have he : W=1 := sub_eq_zero.mp h
    subst W
    norm_num [OffRealSegment] at hW
  · have he : W= -1 := eq_neg_of_add_eq_zero_left h
    subst W
    norm_num [OffRealSegment] at hW

theorem isOpen_offRealSegment : IsOpen {W : ℂ | OffRealSegment W} := by
  exact (isOpen_ne_fun Complex.continuous_im continuous_const).union
    (isOpen_lt continuous_const (continuous_abs.comp Complex.continuous_re))

def localPhysicalRoot (W V : ℂ) : ℂ :=
  V + (physicalRoot W-W) * Complex.sqrt ((V^2-1)/(W^2-1))

theorem localPhysicalRoot_at {W : ℂ} (hD : W^2-1 ≠ 0) : localPhysicalRoot W W = physicalRoot W := by
  simp only [localPhysicalRoot, div_self hD, Complex.sqrt, Complex.one_cpow, mul_one]
  ring

theorem localPhysicalRoot_quadratic {W : ℂ} (hD : W^2-1 ≠ 0) (V : ℂ) :
    (localPhysicalRoot W V)^2 - 2*V*localPhysicalRoot W V + 1 = 0 := by
  have h : (localPhysicalRoot W V-V)^2 = V^2-1 := by
    simp only [localPhysicalRoot, add_sub_cancel_left, mul_pow,
      physicalRoot_discriminant, complex_sqrt_sq]
    exact mul_div_cancel₀ _ hD
  linear_combination h

theorem localPhysicalRoot_ne_zero {W : ℂ} (hD : W^2-1 ≠ 0) (V : ℂ) : localPhysicalRoot W V ≠ 0 := by
  intro hz
  have h := localPhysicalRoot_quadratic hD V
  simp [hz] at h

theorem localPhysicalRoot_trace {W : ℂ} (hD : W^2-1 ≠ 0) (V : ℂ) :
    localPhysicalRoot W V + (localPhysicalRoot W V)⁻¹ = 2*V := by
  apply (mul_right_cancel₀ (localPhysicalRoot_ne_zero hD V))
  rw [add_mul, inv_mul_cancel₀ (localPhysicalRoot_ne_zero hD V)]
  linear_combination localPhysicalRoot_quadratic hD V

theorem localPhysicalRoot_analyticAt {W : ℂ} (hD : W^2-1 ≠ 0) :
    AnalyticAt ℂ (localPhysicalRoot W) W := by
  have hg : AnalyticAt ℂ (fun V : ℂ => (V^2-1)/(W^2-1)) W :=
    ((analyticAt_id.pow 2).sub analyticAt_const).div_const
  have hp : (W^2-1)/(W^2-1) ∈ Complex.slitPlane := by
    rw [div_self hD]
    exact Or.inl (by norm_num)
  have hsq : AnalyticAt ℂ (fun V : ℂ => Complex.sqrt ((V^2-1)/(W^2-1))) W := by
    exact hg.cpow analyticAt_const hp
  exact analyticAt_id.add (analyticAt_const.mul hsq)

/-- The unique interior root is complex analytic on the entire complement
of the forbidden real segment, including W with real part zero. -/
theorem physicalRoot_analyticAt {W : ℂ} (hW : OffRealSegment W) : AnalyticAt ℂ physicalRoot W := by
  have hD := offRealSegment_discriminant_ne_zero hW
  have ha := localPhysicalRoot_analyticAt hD
  have hcenter : ‖localPhysicalRoot W W‖ < 1 := by
    rw [localPhysicalRoot_at hD]
    exact physicalRoot_inside hW
  have hnorm : ∀ᶠ V in 𝓝 W, ‖localPhysicalRoot W V‖ < 1 :=
    ha.continuousAt.norm.eventually_lt continuousAt_const hcenter
  apply ha.congr
  filter_upwards [hnorm, isOpen_offRealSegment.eventually_mem hW] with V hV hOff
  exact root_unique_in_disk (localPhysicalRoot_trace hD V) (physicalRoot_trace V)
    (localPhysicalRoot_ne_zero hD V) (physicalRoot_ne_zero V) hV (physicalRoot_inside hOff)

theorem angularRoot_analyticAt {s : ℂ} (hs : 1 < ‖s‖) (θ : ℝ) :
    AnalyticAt ℂ (fun t : ℂ => physicalRoot (angularW t θ)) s := by
  have hs0 : s ≠ 0 := by intro he; norm_num [he] at hs
  have hW : AnalyticAt ℂ (fun t : ℂ => angularW t θ) s :=
    (analyticAt_id.add (analyticAt_id.inv hs0)).sub analyticAt_const
  exact (physicalRoot_analyticAt (angularW_off_segment hs θ)).comp
    (f := fun t : ℂ => angularW t θ) hW

theorem physicalRoot_continuousOn : ContinuousOn physicalRoot {W : ℂ | OffRealSegment W} :=
  fun _ hW => (physicalRoot_analyticAt hW).continuousAt.continuousWithinAt

end
end IsingBulk.Preferred22
