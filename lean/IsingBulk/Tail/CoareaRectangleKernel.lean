import IsingBulk.Tail.SimpleKernelBounds
import IsingBulk.Tail.CoareaDeterminant
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Group.Measure

/-! Injective two-phase coarea with an explicit rectangle and period count.
Image multiplicity is proved by the caller's actual injectivity; translated
period boxes are counted once, inside the one-dimensional kernel bounds. -/
namespace IsingBulk.Tail
noncomputable section
open Set MeasureTheory Filter
open scoped Topology

 theorem injective_weighted_coarea_le {S R : Set (ℝ × ℝ)}
    (hS : MeasurableSet S) (f : (ℝ × ℝ) → (ℝ × ℝ))
    (f' : (ℝ × ℝ) → ((ℝ × ℝ) →L[ℝ] (ℝ × ℝ)))
    (hf' : ∀ x ∈ S, HasFDerivWithinAt f (f' x) S x) (hf : InjOn f S)
    (himage : f '' S ⊆ R) (a k : (ℝ × ℝ) → ℝ)
    (ha : ContinuousOn a S) (hk : Continuous k) (hk0 : ∀ x, 0≤k x)
    (hki : IntegrableOn k R) {C : ℝ} (hC : 0≤C)
    (ha0 : ∀ x ∈ S, 0≤a x) (hratio : ∀ x ∈ S, a x≤C*|(f' x).det|) :
    IntegrableOn (fun x => a x*k (f x)) S ∧
      (∫ x in S, a x*k (f x))≤C*(∫ y in R, k y) := by
  let : (volume : Measure (ℝ × ℝ)).IsAddHaarMeasure := by
    change (volume.prod volume).IsAddHaarMeasure
    infer_instance
  have hkimage : IntegrableOn k (f '' S) := hki.mono_set himage
  have hdet := (integrableOn_image_iff_integrableOn_abs_det_fderiv_smul (volume : Measure (ℝ × ℝ)) hS hf' hf k).mp hkimage
  have hdom : IntegrableOn (fun x => C*(|(f' x).det| *k (f x))) S := by
    simpa only [smul_eq_mul,IntegrableOn] using hdet.const_mul C
  have hfc : ContinuousOn f S := fun x hx => (hf' x hx).continuousWithinAt
  have hw : ContinuousOn (fun x => a x*k (f x)) S := ha.mul (hk.comp_continuousOn hfc)
  have hpoint : ∀ x ∈ S, ‖a x*k (f x)‖≤C*(|(f' x).det| *k (f x)) := by
    intro x hx
    rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (ha0 x hx) (hk0 _))]
    have hh := mul_le_mul_of_nonneg_right (hratio x hx) (hk0 (f x))
    simpa only [mul_assoc] using hh
  have hi : IntegrableOn (fun x => a x*k (f x)) S :=
    hdom.mono' (hw.aestronglyMeasurable hS) ((ae_restrict_iff' hS).mpr (Eventually.of_forall hpoint))
  refine ⟨hi,?_⟩
  calc
    _ ≤ ∫ x in S, C*(|(f' x).det| *k (f x)) :=
      setIntegral_mono_on hi hdom hS (fun x hx => (le_abs_self _).trans (by simpa [Real.norm_eq_abs] using hpoint x hx))
    _ = C*(∫ x in S, |(f' x).det| *k (f x)) := integral_const_mul _ _
    _ = C*(∫ y in f '' S, k y) := by
      rw [integral_image_eq_integral_abs_det_fderiv_smul (volume : Measure (ℝ × ℝ)) hS hf' hf k]
      rfl
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (setIntegral_mono_set hki (Eventually.of_forall hk0) (Eventually.of_forall himage)) hC

 def twoPhaseKernel (a b : ℝ) (x : ℝ × ℝ) : ℝ :=
  (phaseDenominator (Real.exp (-a)) x.1)⁻¹*(phaseDenominator (Real.exp (-b)) x.2)⁻¹

 theorem twoPhaseKernel_nonneg (a b : ℝ) (x : ℝ × ℝ) : 0≤twoPhaseKernel a b x := by
  unfold twoPhaseKernel phaseDenominator
  positivity

 theorem twoPhaseKernel_continuous {a b : ℝ} (ha : 0<a) (hb : 0<b) :
    Continuous (twoPhaseKernel a b) :=
  ((simple_kernel_continuous ha).comp continuous_fst).mul ((simple_kernel_continuous hb).comp continuous_snd)

 theorem two_simple_kernel_rectangle {a b x₀ x₁ y₀ y₁ : ℝ}
    (ha : 0<a) (ha1 : a≤1) (hb : 0<b) (hb1 : b≤1)
    (nx ny : ℕ) (hx : x₀≤x₁) (hy : y₀≤y₁)
    (hlenx : x₁≤x₀+(nx:ℝ)*(2*Real.pi)) (hleny : y₁≤y₀+(ny:ℝ)*(2*Real.pi)) :
    IntegrableOn (twoPhaseKernel a b) (Icc x₀ x₁ ×ˢ Icc y₀ y₁) ∧
      (∫ x in Icc x₀ x₁ ×ˢ Icc y₀ y₁, twoPhaseKernel a b x)≤
        ((nx:ℝ)*simpleKernelConstant*(1+|Real.log a|))*
        ((ny:ℝ)*simpleKernelConstant*(1+|Real.log b|)) := by
  refine ⟨(twoPhaseKernel_continuous ha hb).continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc),?_⟩
  change (∫ x in Icc x₀ x₁ ×ˢ Icc y₀ y₁,
    (phaseDenominator (Real.exp (-a)) x.1)⁻¹*(phaseDenominator (Real.exp (-b)) x.2)⁻¹ ∂volume.prod volume)≤_
  rw [setIntegral_prod_mul (μ := volume) (ν := volume)
    (fun x : ℝ => (phaseDenominator (Real.exp (-a)) x)⁻¹)
    (fun y : ℝ => (phaseDenominator (Real.exp (-b)) y)⁻¹) (Icc x₀ x₁) (Icc y₀ y₁)]
  have hxint := simple_kernel_interval_integral ha ha1 nx hx hlenx
  have hyint := simple_kernel_interval_integral hb hb1 ny hy hleny
  rw [intervalIntegral.integral_of_le hx,← integral_Icc_eq_integral_Ioc] at hxint
  rw [intervalIntegral.integral_of_le hy,← integral_Icc_eq_integral_Ioc] at hyint
  exact mul_le_mul hxint hyint (integral_nonneg (fun _ => inv_nonneg.mpr (norm_nonneg _)))
    (by have := simpleKernelConstant_pos; positivity)

end
end IsingBulk.Tail
