import IsingBulk.First.MeanRectanglePhysical
import Mathlib.Analysis.Complex.RemovableSingularity

/-! The simple-pole rectangular Cauchy formula for the actual oriented
four-side integral. Regularity assumptions concern the numerator itself. -/
namespace IsingBulk.First
noncomputable section
open Complex MeasureTheory Set intervalIntegral
open scoped Topology

def rectangleSet (delta top bottom : ℝ) : Set ℂ :=
  {z | z.re ∈ uIcc (-delta) delta ∧ z.im ∈ uIcc top bottom}

/-- Ordinary integrability of the four actual side pullbacks. -/
def RectangleSideIntegrable (delta top bottom : ℝ) (f : ℂ → ℂ) : Prop :=
  IntervalIntegrable (fun x : ℝ => f ((x:ℂ)+(top:ℂ)*I)) volume (-delta) delta ∧
  IntervalIntegrable (fun x : ℝ => f ((x:ℂ)+(bottom:ℂ)*I)) volume (-delta) delta ∧
  IntervalIntegrable (fun y : ℝ => f ((delta:ℂ)+(y:ℂ)*I)) volume top bottom ∧
  IntervalIntegrable (fun y : ℝ => f (-(delta:ℂ)+(y:ℂ)*I)) volume top bottom

theorem rectangleSideIntegrable_of_continuousOn {delta top bottom : ℝ} {f : ℂ → ℂ}
    (hc : ContinuousOn f (rectangleSet delta top bottom)) :
    RectangleSideIntegrable delta top bottom f := by
  have hor (a : ℝ) (ha : a ∈ uIcc top bottom) :
      IntervalIntegrable (fun x : ℝ => f ((x:ℂ)+(a:ℂ)*I)) volume (-delta) delta := by
    apply ContinuousOn.intervalIntegrable
    apply hc.comp (by fun_prop)
    intro x hx
    simpa [rectangleSet] using And.intro hx ha
  have ver (a : ℝ) (ha : a ∈ uIcc (-delta) delta) :
      IntervalIntegrable (fun y : ℝ => f ((a:ℂ)+(y:ℂ)*I)) volume top bottom := by
    apply ContinuousOn.intervalIntegrable
    apply hc.comp (by fun_prop)
    intro y hy
    simpa [rectangleSet] using And.intro ha hy
  exact ⟨hor top left_mem_uIcc, hor bottom right_mem_uIcc,
    ver delta right_mem_uIcc, by simpa only [ofReal_neg] using ver (-delta) left_mem_uIcc⟩

theorem clockwiseRectangle_add {delta top bottom : ℝ} {f g : ℂ → ℂ}
    (hf : RectangleSideIntegrable delta top bottom f)
    (hg : RectangleSideIntegrable delta top bottom g) :
    clockwiseRectangle delta top bottom (fun z => f z+g z) =
      clockwiseRectangle delta top bottom f + clockwiseRectangle delta top bottom g := by
  unfold clockwiseRectangle
  rw [intervalIntegral.integral_add hf.1 hg.1,
    intervalIntegral.integral_add hf.2.1 hg.2.1,
    intervalIntegral.integral_add hf.2.2.1 hg.2.2.1,
    intervalIntegral.integral_add hf.2.2.2 hg.2.2.2]
  ring

theorem clockwiseRectangle_zero {delta top bottom : ℝ} {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (rectangleSet delta top bottom)) :
    clockwiseRectangle delta top bottom f = 0 := by
  have hh := Complex.integral_boundary_rect_eq_zero_of_differentiableOn f
    (-(delta:ℂ)+(top:ℂ)*I) ((delta:ℂ)+(bottom:ℂ)*I)
    (by
      convert! hf using 1
      ext z
      simp [rectangleSet, Complex.mem_reProdIm])
  simpa [clockwiseRectangle, smul_eq_mul] using hh

/-- The pole is genuinely interior; the full closed rectangle is its neighborhood. -/
theorem rectangleSet_mem_nhds_zero {delta top bottom : ℝ}
    (hd : 0 < delta) (ht : 0 < top) (hb : bottom < 0) :
    rectangleSet delta top bottom ∈ 𝓝 (0:ℂ) := by
  have hx : uIcc (-delta) delta ∈ 𝓝 (0:ℝ) := by
    rw [uIcc_of_le (by linarith)]
    exact Icc_mem_nhds (by linarith) hd
  have hy : uIcc top bottom ∈ 𝓝 (0:ℝ) := by
    rw [uIcc_of_ge (by linarith)]
    exact Icc_mem_nhds hb ht
  have hx' : Complex.re ⁻¹' uIcc (-delta) delta ∈ 𝓝 (0:ℂ) :=
    (Complex.continuous_re.continuousAt : ContinuousAt Complex.re (0:ℂ)).preimage_mem_nhds
      (by simpa using hx)
  have hy' : Complex.im ⁻¹' uIcc top bottom ∈ 𝓝 (0:ℂ) :=
    (Complex.continuous_im.continuousAt : ContinuousAt Complex.im (0:ℂ)).preimage_mem_nhds
      (by simpa using hy)
  exact Filter.inter_mem hx' hy' 

/-- The exact removable principal-part subtraction, at every nonpole point. -/
theorem numerator_div_eq_dslope_add (f : ℂ → ℂ) {z : ℂ} (hz : z ≠ 0) :
    f z / z = dslope f 0 z + f 0 * z⁻¹ := by
  have hh := sub_smul_dslope f 0 z
  simp only [sub_zero, smul_eq_mul] at hh
  field_simp
  linear_combination -hh

theorem RectangleSideIntegrable.const_mul {delta top bottom : ℝ} {f : ℂ → ℂ}
    (hf : RectangleSideIntegrable delta top bottom f) (c : ℂ) :
    RectangleSideIntegrable delta top bottom (fun z => c*f z) :=
  ⟨hf.1.const_mul c, hf.2.1.const_mul c, hf.2.2.1.const_mul c, hf.2.2.2.const_mul c⟩

theorem rectangleSideIntegrable_inv {delta top bottom : ℝ}
    (hd : delta ≠ 0) (ht : top ≠ 0) (hb : bottom ≠ 0) :
    RectangleSideIntegrable delta top bottom (fun z => z⁻¹) := by
  have hhor (a : ℝ) (ha : a ≠ 0) : Continuous (fun x : ℝ => ((x:ℂ)+(a:ℂ)*I)⁻¹) := by
    apply (Complex.continuous_ofReal.add continuous_const).inv₀
    intro x hx
    apply ha
    simpa using congrArg Complex.im hx
  have hver (a : ℝ) (ha : a ≠ 0) : Continuous (fun y : ℝ => ((a:ℂ)+(y:ℂ)*I)⁻¹) := by
    apply (continuous_const.add (Complex.continuous_ofReal.mul continuous_const)).inv₀
    intro y hy
    apply ha
    simpa using congrArg Complex.re hy
  exact ⟨(hhor top ht).intervalIntegrable _ _, (hhor bottom hb).intervalIntegrable _ _,
    (hver delta hd).intervalIntegrable _ _, by
      simpa only [ofReal_neg] using (hver (-delta) (neg_ne_zero.mpr hd)).intervalIntegrable top bottom⟩

theorem clockwiseRectangle_congr_off_zero {delta top bottom : ℝ} {f g : ℂ → ℂ}
    (hd : delta ≠ 0) (ht : top ≠ 0) (hb : bottom ≠ 0)
    (he : ∀ z : ℂ, z ≠ 0 → f z = g z) :
    clockwiseRectangle delta top bottom f = clockwiseRectangle delta top bottom g := by
  have hor (a : ℝ) (ha : a ≠ 0) :
      (∫ x : ℝ in -delta..delta, f ((x:ℂ)+(a:ℂ)*I)) =
        ∫ x : ℝ in -delta..delta, g ((x:ℂ)+(a:ℂ)*I) := by
    apply intervalIntegral.integral_congr
    intro x _
    apply he
    intro hz
    apply ha
    simpa using congrArg Complex.im hz
  have ver (a : ℝ) (ha : a ≠ 0) :
      (∫ y : ℝ in top..bottom, f ((a:ℂ)+(y:ℂ)*I)) =
        ∫ y : ℝ in top..bottom, g ((a:ℂ)+(y:ℂ)*I) := by
    apply intervalIntegral.integral_congr
    intro y _
    apply he
    intro hz
    apply ha
    simpa using congrArg Complex.re hz
  unfold clockwiseRectangle
  rw [hor top ht, hor bottom hb, ver delta hd]
  rw [show -(delta:ℂ)=((-delta:ℝ):ℂ) by simp, ver (-delta) (neg_ne_zero.mpr hd)]

/-- Full rectangular simple-pole formula with an actual holomorphic numerator. -/
theorem clockwiseRectangle_simplePole {delta top bottom : ℝ} {f : ℂ → ℂ}
    (hd : 0 < delta) (ht : 0 < top) (hb : bottom < 0)
    (hf : DifferentiableOn ℂ f (rectangleSet delta top bottom)) :
    clockwiseRectangle delta top bottom (fun z => f z/z) =
      -2*(Real.pi:ℂ)*I*f 0 := by
  have hds : DifferentiableOn ℂ (dslope f 0) (rectangleSet delta top bottom) :=
    (Complex.differentiableOn_dslope (rectangleSet_mem_nhds_zero hd ht hb)).mpr hf
  have hInv := rectangleSideIntegrable_inv (ne_of_gt hd) (ne_of_gt ht) (ne_of_lt hb)
  have he := clockwiseRectangle_congr_off_zero (ne_of_gt hd) (ne_of_gt ht) (ne_of_lt hb)
    (fun z hz => numerator_div_eq_dslope_add f hz)
  rw [he, clockwiseRectangle_add (rectangleSideIntegrable_of_continuousOn hds.continuousOn)
    (hInv.const_mul (f 0)), clockwiseRectangle_zero hds, zero_add,
    clockwiseRectangle_const_mul, clockwiseRectangle_inv delta top bottom hd ht hb]
  ring

end
end IsingBulk.First
