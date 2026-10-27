import IsingBulk.Preferred22.CircleYoung
import Mathlib.MeasureTheory.Integral.Pi

/-! Exact constrained angular convolution and its four-factor smoothing bound.
The last angle remains the negative sum of the genuine free angles. -/
namespace IsingBulk.Preferred22
noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators Topology ENNReal Convolution

variable {T : ℝ} [Fact (0<T)]

/-- Genuine first-coordinate Fubini on the finite angular torus. -/
theorem preferredCircle_integral_fin_cons {n : ℕ}
    (f : (Fin (n+1) → AddCircle T) → ℝ) (hf : Continuous f) :
    (∫ θ,f θ)=∫ y : AddCircle T, ∫ z : Fin n → AddCircle T,f (Fin.cons y z) := by
  let e := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => AddCircle T) 0).symm
  have he : MeasurePreserving e volume volume :=
    (volume_preserving_piFinSuccAbove (fun _ : Fin (n+1) => AddCircle T) 0).symm
  rw [←he.integral_comp' f]
  have hc : Continuous (fun x : AddCircle T × (Fin n → AddCircle T) => f (e x)) := by
    apply hf.comp
    simp only [e,MeasurableEquiv.piFinSuccAbove_symm_apply,Fin.insertNthEquiv,
      Fin.insertNth_zero]
    exact continuous_pi (fun i => Fin.cases continuous_fst (fun j => (continuous_apply j).comp continuous_snd) i)
  have hi : Integrable (fun x : AddCircle T × (Fin n → AddCircle T) => f (e x)) volume :=
    hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  rw [Measure.volume_eq_prod] at hi ⊢
  rw [integral_prod _ hi]
  simp only [e,MeasurableEquiv.piFinSuccAbove_symm_apply,Fin.insertNthEquiv,Fin.insertNth_zero]
  rfl

theorem preferredCircleConvolution_assoc {f g h : AddCircle T → ℝ}
    (hf : Continuous f) (hg : Continuous g) (hh : Continuous h) :
    preferredCircleConvolution (preferredCircleConvolution f g) h=
      preferredCircleConvolution f (preferredCircleConvolution g h) := by
  funext x
  apply convolution_assoc' (ContinuousLinearMap.mul ℝ ℝ) (ContinuousLinearMap.mul ℝ ℝ)
    (ContinuousLinearMap.mul ℝ ℝ) (ContinuousLinearMap.mul ℝ ℝ)
  · intro a b c
    exact mul_assoc a b c
  · exact Filter.Eventually.of_forall (fun y => preferredCircle_integrable (by fun_prop))
  · exact Filter.Eventually.of_forall (fun y => preferredCircle_integrable (by fun_prop))
  · have hc : Continuous (fun z : AddCircle T × AddCircle T => f z.2*(g (z.1-z.2)*h (x-z.1))) := by fun_prop
    exact hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/-- Index n means n free angles and exactly n+1 constrained factors. -/
def preferredCircleConvolutionPower (f : AddCircle T → ℝ) : ℕ → AddCircle T → ℝ
  | 0 => f
  | n+1 => preferredCircleConvolution f (preferredCircleConvolutionPower f n)

theorem preferredCircleConvolutionPower_continuous {f : AddCircle T → ℝ}
    (hf : Continuous f) (n : ℕ) : Continuous (preferredCircleConvolutionPower f n) := by
  induction n with
  | zero => exact hf
  | succ n hn => exact preferredCircleConvolution_continuous hf hn

theorem preferredCircleConvolutionPower_nonneg {f : AddCircle T → ℝ}
    (hf0 : ∀ x,0≤f x) (n : ℕ) (x : AddCircle T) :
    0≤preferredCircleConvolutionPower f n x := by
  induction n generalizing x with
  | zero => exact hf0 x
  | succ n hn => exact preferredCircleConvolution_nonneg hf0 hn x

/-- Every dependent factor is retained in the exact constrained identity. -/
theorem preferredCircleConvolutionPower_eq_constrained {f : AddCircle T → ℝ}
    (hf : Continuous f) (n : ℕ) (x : AddCircle T) :
    preferredCircleConvolutionPower f n x=
      ∫ θ : Fin n → AddCircle T,(∏ i,f (θ i))*f (x-∑ i,θ i) := by
  induction n generalizing x with
  | zero => simp [preferredCircleConvolutionPower,Measure.real,volume_pi,Measure.pi_empty_univ]
  | succ n hn =>
    rw [preferredCircle_integral_fin_cons _ (by fun_prop)]
    simp_rw [Fin.prod_univ_succ,Fin.sum_univ_succ,Fin.cons_zero,Fin.cons_succ]
    change (∫ y,f y*preferredCircleConvolutionPower f n (x-y))=_
    apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro y
    dsimp only
    rw [hn,←integral_const_mul]
    apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro z
    dsimp only
    rw [sub_add_eq_sub_sub,mul_assoc]

/-- Convolution against one more nonnegative factor consumes only its true L1 mass. -/
theorem preferredCircleConvolution_le_mass_mul {f g : AddCircle T → ℝ} {M : ℝ}
    (hf : Continuous f) (hg : Continuous g) (hf0 : ∀ x,0≤f x) (hgM : ∀ x,g x≤M)
    (x : AddCircle T) : preferredCircleConvolution f g x≤(∫ y,f y)*M := by
  rw [preferredCircleConvolution_apply,←integral_mul_const]
  exact integral_mono (preferredCircle_integrable (by fun_prop))
    ((preferredCircle_integrable hf).mul_const M) (fun y => mul_le_mul_of_nonneg_left (hgM (x-y)) (hf0 y))

/-- The source's all-order constrained convolution inequality, after exactly
four true constrained factors have supplied the 4/3 smoothing. -/
theorem preferredCircleConvolutionPower_bound {f : AddCircle T → ℝ}
    (hf : Continuous f) (hf0 : ∀ x,0≤f x) (n : ℕ) (x : AddCircle T) :
    preferredCircleConvolutionPower f (n+3) x≤
      (∫ y,(f y)^(4/3:ℝ))^3*(∫ y,f y)^n := by
  induction n generalizing x with
  | zero =>
    simp only [zero_add,pow_zero,mul_one]
    have hfour : preferredCircleConvolutionPower f 3=
        preferredCircleConvolution (preferredCircleConvolution f f) (preferredCircleConvolution f f) := by
      simp only [preferredCircleConvolutionPower]
      exact (preferredCircleConvolution_assoc hf hf (preferredCircleConvolution_continuous hf hf)).symm
    rw [hfour]
    exact preferredCircle_fourfold_convolution_bound hf hf0 x
  | succ n hn =>
    have h := preferredCircleConvolution_le_mass_mul hf
      (preferredCircleConvolutionPower_continuous hf (n+3)) hf0 hn x
    change preferredCircleConvolution f (preferredCircleConvolutionPower f (n+3)) x≤_
    refine h.trans_eq ?_
    rw [pow_succ]
    ring

/-- The exact finite-dimensional torus integral used by the selected sector. -/
theorem preferredCircle_constrained_four_thirds_bound {f : AddCircle T → ℝ}
    (hf : Continuous f) (hf0 : ∀ x,0≤f x) (n : ℕ) (x : AddCircle T) :
    (∫ θ : Fin (n+3) → AddCircle T,(∏ i,f (θ i))*f (x-∑ i,θ i))≤
      (∫ y,(f y)^(4/3:ℝ))^3*(∫ y,f y)^n := by
  rw [←preferredCircleConvolutionPower_eq_constrained hf]
  exact preferredCircleConvolutionPower_bound hf hf0 n x

end
end IsingBulk.Preferred22
